
/* TCP Prague congestion control.
 *
 * This congestion-control, part of the L4S architecture, achieves low loss,
 * low latency and scalable throughput when used in combination with AQMs such
 * as DualPI2, CurvyRED, or even fq_codel with a low ce_threshold for the
 * L4S flows.
 *
 * This is similar to DCTCP, albeit aimed to be used over the public
 * internet over paths supporting the L4S codepoint---ECT(1), and thus
 * implements the safety requirements listed in Appendix A of:
 * https://tools.ietf.org/html/draft-ietf-tsvwg-ecn-l4s-id-08#page-23
 *
 * Notable changes from DCTCP:
 *
 * 1/ Updated EWMA:
 * The resolution of alpha has been increased to ensure that a low amount of
 * marks over high-BDP paths can be accurately taken into account in the
 * computation.
 *
 * Orthogonally, the value of alpha that is kept in the connection state is
 * stored upscaled, in order to preserve its remainder over the course of its
 * updates (similarly to how tp->srtt_us is maintained, as opposed to
 * dctcp->alpha).
 *
 * 2/ Updated cwnd management code
 * In order to operate with a permanent, (very) low, marking probability, the
 * arithmetic around cwnd has been updated to track its decimals alongside its
 * integer part. This both improve the precision, avoiding avalanche effects as
 * remainders are carried over the next operation, as well as responsiveness as
 * the AQM at the bottleneck can effectively control the operation of the flow
 * without drastic marking probability increase.
 *
 * Finally, when deriving the cwnd reduction from alpha, we ensure that the
 * computed value is unbiased wrt. integer rounding.
 *
 * 3/ Additive Increase uses unsaturated marking
 * Given that L4S AQM may induce randomly applied CE marks (e.g., from the PI2
 * part of dualpi2), instead of full RTTs of marks once in a while that a step
 * AQM would cause, cwnd is updated for every ACK, regardless of the congestion
 * status of the connection (i.e., it is expected to spent most of its time in
 * TCP_CA_CWR when used over dualpi2).
 *
 * To ensure that it can operate properly in environment where the marking level
 * is close to saturation, its increase also unsature the marking, i.e., the
 * total increase over a RTT is proportional to (1-p)/p.
 *
 * See https://arxiv.org/abs/1904.07605 for more details around saturation.
 *
 * 4/ Pacing/tso sizing
 * mprague aims to keep queuing delay as low as possible. To that end, it is in
 * its best interest to pace outgoing segments (i.e., to smooth its traffic),
 * as well as impose a maximal GSO burst size to avoid instantaneous queue
 * buildups in the bottleneck link.
 */

#define pr_fmt(fmt) "TCP-Prague " fmt

#include <linux/module.h>
#include <linux/mm.h>
#include <net/tcp.h>
#include <net/mptcp.h>
#include <linux/inet_diag.h>
#include <linux/inet.h>

#define MIN_CWND		2U
#define MPRAGUE_ALPHA_BITS	20U
#define MPRAGUE_MAX_ALPHA	(1ULL << MPRAGUE_ALPHA_BITS)
#define CWND_UNIT		20U
#define ONE_CWND		(1LL << CWND_UNIT) /* Must be signed */
#define MPRAGUE_SHIFT_G		4		/* EWMA gain g = 1/2^4 */

static u32 mprague_burst_shift __read_mostly = 12; /* 1/2^12 sec ~=.25ms */
MODULE_PARM_DESC(mprague_burst_shift,
		 "maximal GSO burst duration as a base-2 negative exponent");
module_param(mprague_burst_shift, uint, 0644);

static unsigned int beta_scale __read_mostly = 1024;
module_param(beta_scale, uint, 0644);
MODULE_PARM_DESC(beta_scale, "scale beta for precision");

struct mprague {
	u64  beta;
	bool forced_update;
	u64 cwr_stamp;
	u64 alpha_stamp;	/* EWMA update timestamp */
	u64 upscaled_alpha;	/* Congestion-estimate EWMA */
	u64 ai_ack_increase;	/* AI increase per non-CE ACKed MSS */
	s64 cwnd_cnt;		/* cwnd update carry */
	s64 loss_cwnd_cnt;
	u32 loss_cwnd;
	u32 max_tso_burst;
	u32 old_delivered;	/* tp->delivered at round start */
	u32 old_delivered_ce;	/* tp->delivered_ce at round start */
	u32 acked_ce;		/* tp->delivered_ce at last ack */
	u32 next_seq;		/* tp->snd_nxt at round start */
	int saw_ce:1; 		/* Is there an AQM on the path? */
	    
};


/* Fallback struct ops if we fail to negotiate AccECN */
static struct tcp_congestion_ops mprague_reno;

static void __mprague_connection_id(struct sock *sk, char *str, size_t len)
{
	u16 dport = ntohs(inet_sk(sk)->inet_dport),
	    sport = ntohs(inet_sk(sk)->inet_sport);
	if (sk->sk_family == AF_INET)
		snprintf(str, len, "%pI4:%u-%pI4:%u", &sk->sk_rcv_saddr, sport,
			&sk->sk_daddr, dport);
	else if (sk->sk_family == AF_INET6)
		snprintf(str, len, "[%pI6c]:%u-[%pI6c]:%u",
			 &sk->sk_v6_rcv_saddr, sport, &sk->sk_v6_daddr, dport);
}
#define LOG(sk, fmt, ...) do {						\
	char __tmp[2 * (INET6_ADDRSTRLEN + 9) + 1] = {0};		\
	__mprague_connection_id(sk, __tmp, sizeof(__tmp));		\
	/* pr_fmt expects the connection ID*/				\
	pr_info("(%s) : " fmt "\n", __tmp, ##__VA_ARGS__);			\
} while (0)

static inline int mprague_sk_can_send(const struct sock *sk)
{
	return mptcp_sk_can_send(sk) && tcp_sk(sk)->srtt_us;
}

static inline u64 mprague_get_beta(const struct sock *meta_sk)
{
	return ((struct mprague *)inet_csk_ca(meta_sk))->beta;
}

static inline void mprague_set_beta(const struct sock *meta_sk, u64 beta)
{
	((struct mprague *)inet_csk_ca(meta_sk))->beta = beta;
}

static inline bool mprague_get_forced(const struct sock *meta_sk)
{
	return ((struct mprague *)inet_csk_ca(meta_sk))->forced_update;
}

static inline void mprague_set_forced(const struct sock *meta_sk, bool force)
{
	((struct mprague *)inet_csk_ca(meta_sk))->forced_update = force;
}

static struct mprague *mprague_ca(struct sock *sk)
{
	return (struct mprague*)inet_csk_ca(sk);
}

static bool mprague_e2e_rtt_elapsed(struct sock *sk)
{
	return !before(tcp_sk(sk)->snd_una, mprague_ca(sk)->next_seq);
}

/* RTT independence will scale the classical 1/W per ACK increase. */
static void mprague_ai_ack_increase(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	u64 increase;
	increase = 1 << CWND_UNIT;
	WRITE_ONCE(ca->ai_ack_increase, increase);
}

/* Ensure mprague sends traffic as smoothly as possible:
 * - Pacing is set to 100% during AI
 * - The max GSO burst size is bounded in time at the pacing rate.
 *
 *   We keep the 200% pacing rate during SS, as we need to send 2 MSS back to
 *   back for every received ACK.
 */
static void mprague_update_pacing_rate(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	u32 max_inflight;
	u64 rate, burst;
	int mtu;

	mtu = tcp_mss_to_mtu(sk, tp->mss_cache);
	// Must also set tcp_ecn=512+256 to disable the safer heuristic and the
	// option...
	max_inflight = max(tp->snd_cwnd, tcp_packets_in_flight(tp));

	rate = (u64)((u64)USEC_PER_SEC << 3) * mtu;
	if (tp->snd_cwnd < tp->snd_ssthresh / 2)
		rate <<= 1;
	if (likely(tp->srtt_us))
		rate = div64_u64(rate, tp->srtt_us);
	rate *= max_inflight;
	rate = min_t(u64, rate, sk->sk_max_pacing_rate);
	/* TODO(otilmans) rewrite the max_tso_burst hook to bytes to avoid this
	 * division. It will somehow need to be able to take hdr sizes into
	 * account */
	burst = div_u64(rate, tcp_mss_to_mtu(sk, tp->mss_cache));

	WRITE_ONCE(mprague_ca(sk)->max_tso_burst,
		   max_t(u32, 1, burst >> mprague_burst_shift));
	WRITE_ONCE(sk->sk_pacing_rate, rate);
}

static void mprague_new_round(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	ca->next_seq = tp->snd_nxt;
	ca->old_delivered_ce = tp->delivered_ce;
	ca->old_delivered = tp->delivered;
	mprague_ai_ack_increase(sk);
}

static void mprague_cwnd_changed(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tp->snd_cwnd_stamp = tcp_jiffies32;
	mprague_ai_ack_increase(sk);
}

static void mprague_update_alpha(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u64 ecn_segs, alpha;

	/* Do not update alpha before we have proof that there's an AQM on
	 * the path.
	 */
	if (unlikely(!ca->saw_ce))
		goto skip;


	alpha = ca->upscaled_alpha;
	ecn_segs = tp->delivered_ce - ca->old_delivered_ce;
	/* We diverge from the original EWMA, i.e.,
	 * alpha = (1 - g) * alpha + g * F
	 * by working with (and storing)
	 * upscaled_alpha = alpha * (1/g) [recall that 0<g<1]
	 *
	 * This enables to carry alpha's residual value to the next EWMA round.
	 *
	 * We first compute F, the fraction of ecn segments.
	 */
	if (ecn_segs) {
		u32 acked_segs = tp->delivered - ca->old_delivered;

		ecn_segs <<= MPRAGUE_ALPHA_BITS;
		ecn_segs = div_u64(ecn_segs, max(1U, acked_segs));
	}
	alpha = alpha - (alpha >> MPRAGUE_SHIFT_G) + ecn_segs;
	ca->alpha_stamp = tp->tcp_mstamp;

	WRITE_ONCE(ca->upscaled_alpha,
		   min(MPRAGUE_MAX_ALPHA << MPRAGUE_SHIFT_G, alpha));

skip:
	mprague_new_round(sk);
}
static void mprague_recalc_beta( const struct sock *sk)
{

	const struct mptcp_cb *mpcb = tcp_sk(sk)->mpcb;
	const struct mptcp_tcp_sock *mptcp;

	u64 beta = 1;
	u32 best_rtt = 0xffffffff;
	int can_send = 0;

	if (!mpcb)
		return;

	mptcp_for_each_sub(mpcb, mptcp) {
		const struct sock *sub_sk = mptcp_to_sock(mptcp);
		struct tcp_sock *sub_tp = tcp_sk(sub_sk);

		if (!mprague_sk_can_send(sub_sk))
			continue;
		can_send++;
		/* We need to look for the path that provides the minimum RTT*/
		if (sub_tp->srtt_us < best_rtt)
			best_rtt = sub_tp->srtt_us;
	}

	/* No subflow is able to send - we don't care anymore */
	if (unlikely(!can_send)){
		goto exit;
	}

	mptcp_for_each_sub(mpcb, mptcp) {
		const struct sock *sub_sk = mptcp_to_sock(mptcp);
		struct tcp_sock *sub_tp = tcp_sk(sub_sk);
		if (!mprague_sk_can_send(sub_sk))
			continue;
		beta += div_u64((u64)beta_scale * sub_tp->snd_cwnd * best_rtt, sub_tp->srtt_us);
	}

	if (unlikely(!beta))
		beta = beta_scale;

exit:  
	mprague_set_beta(mptcp_meta_sk(sk), beta);

}

static void mprague_update_cwnd(struct sock *sk, const struct rate_sample *rs)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	int snd_cwnd = 0;
	u64 increase, beta;
	s64 acked;

	acked = rs->acked_sacked;

	if (!mptcp(tp) ) {
		tcp_reno_cong_avoid(sk, 0, acked);
		return;
	}

	if (rs->is_ece) {
		ca->saw_ce = 1;
		acked -= (u32)(tp->delivered_ce - ca->acked_ce);
		ca->acked_ce = tp->delivered_ce;
	}

	if (acked <= 0)
		goto adjust;

	if (!tcp_is_cwnd_limited(sk)) {
		if (tcp_needs_internal_pacing(sk)) {
			/* TCP internal pacing could preempt the cwnd limited
			 * check. This is a poor man's attempt at bypassing
			 * this, but will fail to account for rwnd/sndbuf
			 * limited cases. */
			if (tcp_write_queue_empty(sk))
				goto adjust;
			/* else: keep going */
		} else {
			goto adjust;
		}
	}

	if (tcp_in_slow_start(tp)) {
		acked = tcp_slow_start(tp, acked);
		mprague_recalc_beta(sk);
		if (!acked) {
			mprague_cwnd_changed(sk);
			return;
		}
	}

	/*Implement cwnd coupling here*/

	if (mprague_get_forced(mptcp_meta_sk(sk)) ) {
		mprague_recalc_beta(sk);
		mprague_set_forced(mptcp_meta_sk(sk), 0);
	}

	beta = mprague_get_beta(mptcp_meta_sk(sk));

	/* This may happen, if at the initialization, the mpcb
	 * was not yet attached to the sock, and thus  initializing beta failed.
	 */

	if (unlikely(!beta))
		beta = beta_scale;
	snd_cwnd = (int) div_u64(beta, beta_scale);
	// cwnd_old = tp->snd_cwnd;

	if (snd_cwnd < tp->snd_cwnd)
		tp->snd_cwnd = snd_cwnd;
		

	increase = acked * ca->ai_ack_increase;
	if (likely(tp->snd_cwnd))
		increase = div_u64(increase + (tp->snd_cwnd >> 1),
				   tp->snd_cwnd);
	ca->cwnd_cnt += max_t(u64, increase, acked);

adjust:
	if (ca->cwnd_cnt <= -ONE_CWND) {
		ca->cwnd_cnt += ONE_CWND;
		--tp->snd_cwnd;
		if (tp->snd_cwnd < MIN_CWND) {
			tp->snd_cwnd = MIN_CWND;
			/* No point in applying further reductions */
			ca->cwnd_cnt = 0;
		}
		tp->snd_ssthresh = tp->snd_cwnd;
		mprague_cwnd_changed(sk);
	} else if (ca->cwnd_cnt >= ONE_CWND) {
		ca->cwnd_cnt -= ONE_CWND;
		++tp->snd_cwnd;
		tp->snd_cwnd = min(tp->snd_cwnd, tp->snd_cwnd_clamp);
		mprague_cwnd_changed(sk);
	}

	mprague_recalc_beta(sk);
	return;
}

static void mprague_enter_loss(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	ca->loss_cwnd = tp->snd_cwnd;
	ca->loss_cwnd_cnt = ca->cwnd_cnt;
	ca->cwnd_cnt -=
		(((u64)tp->snd_cwnd) << (CWND_UNIT - 1)) + (ca->cwnd_cnt >> 1);
	mprague_cwnd_changed(sk);
}

static void mprague_enter_cwr(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u64 reduction;
	u64 alpha;
	ca->cwr_stamp = tp->tcp_mstamp;
	alpha = ca->upscaled_alpha >> MPRAGUE_SHIFT_G;
	reduction = (alpha * ((u64)tp->snd_cwnd << CWND_UNIT) +
			 /* Unbias the rounding by adding 1/2 */
			 MPRAGUE_MAX_ALPHA) >>
		(MPRAGUE_ALPHA_BITS + 1U);
	ca->cwnd_cnt -= reduction;

	return;
}

static void mprague_state(struct sock *sk, u8 new_state)
{   
	if (!mptcp(tcp_sk(sk)))
		return;

	if (new_state == inet_csk(sk)->icsk_ca_state)
		return;

	switch (new_state) {
	case TCP_CA_Recovery:
		mprague_enter_loss(sk);
		mprague_set_forced(mptcp_meta_sk(sk), 1);
		break;
	case TCP_CA_CWR:
		mprague_enter_cwr(sk);
		mprague_set_forced(mptcp_meta_sk(sk), 1);
		break;
	}
}

static void mprague_cwnd_event(struct sock *sk, enum tcp_ca_event ev)
{
	struct tcp_sock *tp = tcp_sk(sk);
	if (!mptcp(tp))
		return;

	if (ev == CA_EVENT_LOSS){
		mprague_enter_loss(sk);
		mprague_set_forced(mptcp_meta_sk(sk),1);
	}
}

static u32 mprague_cwnd_undo(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);

	/* We may have made some progress since then, account for it. */
	ca->cwnd_cnt += ca->cwnd_cnt - ca->loss_cwnd_cnt;
	return max(ca->loss_cwnd, tcp_sk(sk)->snd_cwnd);
}

static void mprague_cong_control(struct sock *sk, const struct rate_sample *rs)
{
	mprague_update_cwnd(sk, rs);
	if (mprague_e2e_rtt_elapsed(sk))
		    mprague_update_alpha(sk);
	mprague_update_pacing_rate(sk);
}

static u32 mprague_ssthresh(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	return max_t(u32, tp->snd_cwnd, tp->snd_ssthresh);
}

static u32 mprague_max_tso_seg(struct sock *sk)
{
	return mprague_ca(sk)->max_tso_burst;
}

static void mprague_release(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	cmpxchg(&sk->sk_pacing_status, SK_PACING_NEEDED, SK_PACING_NONE);
	tp->ecn_flags &= ~TCP_ECN_ECT_1;
	if (!tcp_ecn_ok(tp))
		/* We forced the use of ECN, but failed to negotiate it */
		INET_ECN_dontxmit(sk);

	LOG(sk, "Released [delivered_ce=%u,received_ce=%u,received_ce_tx: %u]",
	    tp->delivered_ce, tp->received_ce, tp->received_ce_tx);
}

static void mprague_init(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* We're stuck in TCP_ACCECN_PENDING before the 3rd ACK */
	if ((!mptcp(tp) || !tcp_ecn_ok(tp)) &&
	    sk->sk_state != TCP_LISTEN && sk->sk_state != TCP_CLOSE) {
		mprague_release(sk);
		LOG(sk, "Switching to pure reno [ecn_status=%u,sk_state=%u]",
		    tcp_ecn_status(tp), sk->sk_state);
		inet_csk(sk)->icsk_ca_ops = &mprague_reno;
		return;
	}

	tp->ecn_flags |= TCP_ECN_ECT_1;
	cmpxchg(&sk->sk_pacing_status, SK_PACING_NONE, SK_PACING_NEEDED);
	mprague_set_forced(mptcp_meta_sk(sk), 0);
	mprague_set_beta(mptcp_meta_sk(sk), beta_scale);

	ca->alpha_stamp = tp->tcp_mstamp;
	ca->upscaled_alpha = MPRAGUE_MAX_ALPHA << MPRAGUE_SHIFT_G;
	ca->cwnd_cnt = 0;
	ca->loss_cwnd_cnt = 0;
	ca->loss_cwnd = 0;
	ca->max_tso_burst = 1;
	ca->saw_ce = tp->delivered_ce != TCP_ACCECN_CEP_INIT;
	ca->acked_ce = tp->delivered_ce;
	mprague_new_round(sk);
}

static struct tcp_congestion_ops mprague __read_mostly = {
	.init		= mprague_init,
	.release	= mprague_release,
	.cong_control	= mprague_cong_control,
	.cwnd_event	= mprague_cwnd_event,
	.ssthresh	= mprague_ssthresh,
	.undo_cwnd	= mprague_cwnd_undo,
	.set_state	= mprague_state,
	
	.max_tso_segs	= mprague_max_tso_seg,
	.flags		= TCP_CONG_NEEDS_ECN | TCP_CONG_NEEDS_ACCECN |
		TCP_CONG_WANTS_ECT_1 | TCP_CONG_NON_RESTRICTED,
	.owner		= THIS_MODULE,
	.name		= "mprague",
};

static struct tcp_congestion_ops mprague_reno __read_mostly = {
	.ssthresh	= tcp_reno_ssthresh,
	.cong_avoid	= tcp_reno_cong_avoid,
	.undo_cwnd	= tcp_reno_undo_cwnd,
	.owner		= THIS_MODULE,
	.name		= "mprague-reno",
};

static int __init mprague_register(void)
{
	BUILD_BUG_ON(sizeof(struct mprague) > ICSK_CA_PRIV_SIZE);
	return tcp_register_congestion_control(&mprague);
}

static void __exit mprague_unregister(void)
{
	tcp_unregister_congestion_control(&mprague);
}

module_init(mprague_register);
module_exit(mprague_unregister);

MODULE_AUTHOR("Olivier Tilmans <olivier.tilmans@nokia-bell-labs.com>");
MODULE_AUTHOR("Koen De Schepper <koen.de_schepper@nokia-bell-labs.com>");
MODULE_AUTHOR("Bob briscoe <research@bobbriscoe.net>");

MODULE_LICENSE("GPL v2");
MODULE_DESCRIPTION("TCP Prague");
