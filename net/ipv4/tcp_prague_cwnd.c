
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
 * prague aims to keep queuing delay as low as possible. To that end, it is in
 * its best interest to pace outgoing segments (i.e., to smooth its traffic),
 * as well as impose a maximal GSO burst size to avoid instantaneous queue
 * buildups in the bottleneck link.
 */

#define pr_fmt(fmt) "TCP-Prague " fmt

#include <linux/module.h>
#include <linux/mm.h>
#include <net/tcp.h>
#include <linux/inet_diag.h>
#include <linux/inet.h>

#define MIN_CWND		2U
#define PRAGUE_ALPHA_BITS	20U
#define PRAGUE_MAX_ALPHA	(1ULL << PRAGUE_ALPHA_BITS)
#define CWND_UNIT		20U
#define ONE_CWND		(1LL << CWND_UNIT) /* Must be signed */
#define PRAGUE_SHIFT_G		4		/* EWMA gain g = 1/2^4 */

static u32 prague_burst_shift __read_mostly = 12; /* 1/2^12 sec ~=.25ms */
MODULE_PARM_DESC(prague_burst_shift,
		"maximal GSO burst duration as a base-2 negative exponent");
module_param(prague_burst_shift, uint, 0644);

struct prague {
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
	int saw_ce:1;		/* Is there an AQM on the path? */

};


/* Fallback struct ops if we fail to negotiate AccECN */
static struct tcp_congestion_ops prague_reno;

static void __prague_connection_id(struct sock *sk, char *str, size_t len)
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
	__prague_connection_id(sk, __tmp, sizeof(__tmp));		\
	/* pr_fmt expects the connection ID*/				\
	pr_info("(%s) : " fmt "\n", __tmp, ##__VA_ARGS__);			\
} while (0)

static struct prague *prague_ca(struct sock *sk)
{
	return (struct prague*)inet_csk_ca(sk);
}

static bool prague_e2e_rtt_elapsed(struct sock *sk)
{
	return !before(tcp_sk(sk)->snd_una, prague_ca(sk)->next_seq);
}


static u64 prague_unscaled_ai_ack_increase(struct sock *sk)
{
	return 1 << CWND_UNIT;
}

/* RTT independence will scale the classical 1/W per ACK increase. */
static void prague_ai_ack_increase(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);
	u64 increase;
	increase = prague_unscaled_ai_ack_increase(sk);
	WRITE_ONCE(ca->ai_ack_increase, increase);
}

/* Ensure prague sends traffic as smoothly as possible:
 * - Pacing is set to 100% during AI
 * - The max GSO burst size is bounded in time at the pacing rate.
 *
 *   We keep the 200% pacing rate during SS, as we need to send 2 MSS back to
 *   back for every received ACK.
 */
static void prague_update_pacing_rate(struct sock *sk)
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

	WRITE_ONCE(prague_ca(sk)->max_tso_burst,
			max_t(u32, 1, burst >> prague_burst_shift));
	WRITE_ONCE(sk->sk_pacing_rate, rate);
}

static void prague_new_round(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	ca->next_seq = tp->snd_nxt;
	ca->old_delivered_ce = tp->delivered_ce;
	ca->old_delivered = tp->delivered;
	prague_ai_ack_increase(sk);
}

static void prague_cwnd_changed(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tp->snd_cwnd_stamp = tcp_jiffies32;
	prague_ai_ack_increase(sk);
}

static void prague_update_alpha(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);
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

		ecn_segs <<= PRAGUE_ALPHA_BITS;
		ecn_segs = div_u64(ecn_segs, max(1U, acked_segs));
	}
	alpha = alpha - (alpha >> PRAGUE_SHIFT_G) + ecn_segs;
	ca->alpha_stamp = tp->tcp_mstamp;

	WRITE_ONCE(ca->upscaled_alpha,
			min(PRAGUE_MAX_ALPHA << PRAGUE_SHIFT_G, alpha));

skip:
	prague_new_round(sk);
}

static void prague_update_cwnd(struct sock *sk, const struct rate_sample *rs)
{
	struct prague *ca = prague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u64 increase;
	s64 acked;

	acked = rs->acked_sacked;
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
		if (!acked) {
			prague_cwnd_changed(sk);
			return;
		}
	}

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
		prague_cwnd_changed(sk);
	} else if (ca->cwnd_cnt >= ONE_CWND) {
		ca->cwnd_cnt -= ONE_CWND;
		++tp->snd_cwnd;
		tp->snd_cwnd = min(tp->snd_cwnd, tp->snd_cwnd_clamp);
		prague_cwnd_changed(sk);
	}
	return;
}

static void prague_enter_loss(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	ca->loss_cwnd = tp->snd_cwnd;
	ca->loss_cwnd_cnt = ca->cwnd_cnt;
	ca->cwnd_cnt -=
		(((u64)tp->snd_cwnd) << (CWND_UNIT - 1)) + (ca->cwnd_cnt >> 1);
	prague_cwnd_changed(sk);
}

static void prague_enter_cwr(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u64 reduction;
	u64 alpha;
	ca->cwr_stamp = tp->tcp_mstamp;
	alpha = ca->upscaled_alpha >> PRAGUE_SHIFT_G;
	reduction = (alpha * ((u64)tp->snd_cwnd << CWND_UNIT) +
			/* Unbias the rounding by adding 1/2 */
			PRAGUE_MAX_ALPHA) >>
		(PRAGUE_ALPHA_BITS + 1U);
	ca->cwnd_cnt -= reduction;

	return;
}

static void prague_state(struct sock *sk, u8 new_state)
{
	if (new_state == inet_csk(sk)->icsk_ca_state)
		return;

	switch (new_state) {
		case TCP_CA_Recovery:
			prague_enter_loss(sk);
			break;
		case TCP_CA_CWR:
			prague_enter_cwr(sk);
			break;
	}
}

static void prague_cwnd_event(struct sock *sk, enum tcp_ca_event ev)
{
	if (ev == CA_EVENT_LOSS)
		prague_enter_loss(sk);
}

static u32 prague_cwnd_undo(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);

	/* We may have made some progress since then, account for it. */
	ca->cwnd_cnt += ca->cwnd_cnt - ca->loss_cwnd_cnt;
	return max(ca->loss_cwnd, tcp_sk(sk)->snd_cwnd);
}

static void prague_cong_control(struct sock *sk, const struct rate_sample *rs)
{
	prague_update_cwnd(sk, rs);
	if (prague_e2e_rtt_elapsed(sk))
		prague_update_alpha(sk);
	prague_update_pacing_rate(sk);
}

static u32 prague_ssthresh(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	return max_t(u32, tp->snd_cwnd, tp->snd_ssthresh);
}

static u32 prague_max_tso_seg(struct sock *sk)
{
	return prague_ca(sk)->max_tso_burst;
}

static size_t prague_get_info(struct sock *sk, u32 ext, int *attr,
		union tcp_cc_info *info)
{
	const struct prague *ca = prague_ca(sk);

	if (ext & (1 << (INET_DIAG_PRAGUEINFO - 1)) ||
			ext & (1 << (INET_DIAG_VEGASINFO - 1))) {
		memset(&info->prague, 0, sizeof(info->prague));
		if (inet_csk(sk)->icsk_ca_ops != &prague_reno) {
			info->prague.prague_alpha =
				ca->upscaled_alpha >> PRAGUE_SHIFT_G;
			info->prague.prague_max_burst = ca->max_tso_burst;
			//info->prague.prague_rtt_cwnd = READ_ONCE(ca->ai_ack_increase);

		}
		*attr = INET_DIAG_PRAGUEINFO;
		return sizeof(info->prague);
	}
	return 0;
}

static void prague_release(struct sock *sk)
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

static void prague_init(struct sock *sk)
{
	struct prague *ca = prague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* We're stuck in TCP_ACCECN_PENDING before the 3rd ACK */
	if (!tcp_ecn_ok(tp) &&
			sk->sk_state != TCP_LISTEN && sk->sk_state != TCP_CLOSE) {
		prague_release(sk);
		LOG(sk, "Switching to pure reno [ecn_status=%u,sk_state=%u]",
				tcp_ecn_status(tp), sk->sk_state);
		inet_csk(sk)->icsk_ca_ops = &prague_reno;
		return;
	}

	tp->ecn_flags |= TCP_ECN_ECT_1;
	cmpxchg(&sk->sk_pacing_status, SK_PACING_NONE, SK_PACING_NEEDED);

	ca->alpha_stamp = tp->tcp_mstamp;
	ca->upscaled_alpha = PRAGUE_MAX_ALPHA << PRAGUE_SHIFT_G;
	ca->cwnd_cnt = 0;
	ca->loss_cwnd_cnt = 0;
	ca->loss_cwnd = 0;
	ca->max_tso_burst = 1;
	ca->saw_ce = tp->delivered_ce != TCP_ACCECN_CEP_INIT;
	ca->acked_ce = tp->delivered_ce;
	prague_new_round(sk);
}

static struct tcp_congestion_ops prague __read_mostly = {
	.init		= prague_init,
	.release	= prague_release,
	.cong_control	= prague_cong_control,
	.cwnd_event	= prague_cwnd_event,
	.ssthresh	= prague_ssthresh,
	.undo_cwnd	= prague_cwnd_undo,
	.set_state	= prague_state,
	.get_info	= prague_get_info,
	.max_tso_segs	= prague_max_tso_seg,
	.flags		= TCP_CONG_NEEDS_ECN | TCP_CONG_NEEDS_ACCECN |
		TCP_CONG_WANTS_ECT_1 | TCP_CONG_NON_RESTRICTED,
	.owner		= THIS_MODULE,
	.name		= "prague",
};

static struct tcp_congestion_ops prague_reno __read_mostly = {
	.ssthresh	= tcp_reno_ssthresh,
	.cong_avoid	= tcp_reno_cong_avoid,
	.undo_cwnd	= tcp_reno_undo_cwnd,
	.get_info	= prague_get_info,
	.owner		= THIS_MODULE,
	.name		= "prague-reno",
};

static int __init prague_register(void)
{
	BUILD_BUG_ON(sizeof(struct prague) > ICSK_CA_PRIV_SIZE);
	return tcp_register_congestion_control(&prague);
}

static void __exit prague_unregister(void)
{
	tcp_unregister_congestion_control(&prague);
}

module_init(prague_register);
module_exit(prague_unregister);

MODULE_AUTHOR("Olivier Tilmans <olivier.tilmans@nokia-bell-labs.com>");
MODULE_AUTHOR("Koen De Schepper <koen.de_schepper@nokia-bell-labs.com>");
MODULE_AUTHOR("Bob briscoe <research@bobbriscoe.net>");

MODULE_LICENSE("GPL v2");
MODULE_DESCRIPTION("TCP Prague");


