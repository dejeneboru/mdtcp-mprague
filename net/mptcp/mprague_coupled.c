/*
 *  Multipath Datacenter TCP(MDTCP)-a Coupled Congestion Control for Datacenter
 *  Initial Design & Implementation: Sébastien Barré <sebastien.barre@uclouvain.be>
 *  Current Maintainer & Author:
 *  Christoph Paasch <christoph.paasch@uclouvain.be>
 *
 *  Additional authors:
 *  Jaakko Korkeaniemi <jaakko.korkeaniemi@aalto.fi>
 *  Gregory Detal <gregory.detal@uclouvain.be>
 *  Fabien Duchêne <fabien.duchene@uclouvain.be>
 *  Andreas Seelinger <Andreas.Seelinger@rwth-aachen.de>
 *  Lavkesh Lahngir <lavkesh51@gmail.com>
 *  Andreas Ripke <ripke@neclab.eu>
 *  Vlad Dogaru <vlad.dogaru@intel.com>
 *  Octavian Purdila <octavian.purdila@intel.com>
 *  John Ronan <jronan@tssg.org>
 *  Catalin Nicutar <catalin.nicutar@gmail.com>
 *  Brandon Heller <brandonh@stanford.edu>
 *  Dejene Boru Oljira <oljideje@kau.se>
 *   This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License
 *   as published by the Free Software Foundation; either version 2 of the License, or (at your option) any later version.
 */

#define pr_fmt(fmt) "MPTCP-MPrague: " fmt

#include <linux/module.h>
#include <linux/mm.h>
#include <net/tcp.h>
#include <net/mptcp.h>
#include <linux/inet_diag.h>
#include <linux/inet.h>

#define MPRAGUE_ALPHA_BITS   31
#define MPRAGUE_MAX_ALPHA	((u64)(1U << MPRAGUE_ALPHA_BITS))
static struct tcp_congestion_ops mprague_reno;

struct mprague {
	u64  beta;
	bool forced_update;
	u64 upscaled_alpha;
	u32 old_delivered;
	u32 old_delivered_ce;
	u32 prior_rcv_nxt;
	u32 next_seq;
	u32 loss_cwnd;
	u32 max_tso_burst;
	bool was_ce;
	bool saw_ce;
};


static u32  mprague_shift_g __read_mostly = 4; /* g = 1/2^4 */
static int mprague_ect __read_mostly = 1;
static int mprague_ecn_plus_plus __read_mostly = 1;
static u32 mprague_burst_usec __read_mostly = 250; /* .25ms */	

MODULE_PARM_DESC(mprague_shift_g, "gain parameter for alpha EWMA");
module_param(mprague_shift_g, uint, 0644);

MODULE_PARM_DESC(mprague_burst_usec, "maximal TSO burst duration");
module_param(mprague_burst_usec, uint, 0644);

MODULE_PARM_DESC(mprague_ect, "send packet with ECT(mprague_ect)");
/* We currently do not allow this to change through sysfs */
module_param(mprague_ect, int, 0444);

MODULE_PARM_DESC(mprague_ecn_plus_plus, "set ECT on control packets");
module_param(mprague_ecn_plus_plus, int, 0444);

static unsigned int beta_scale __read_mostly = 1024;
module_param(beta_scale, uint, 0644);
MODULE_PARM_DESC(beta_scale, "scale beta for precision");

static unsigned int mprague_debug __read_mostly = 0;
module_param(mprague_debug, uint, 0644);
MODULE_PARM_DESC(mprague_debug, "mprague_debug debug parameter default 0");

static u32 mprague_burst_shift __read_mostly = 12; /* 1/2^12 sec ~=.25ms */
MODULE_PARM_DESC(mprague_burst_shift,
		"maximal GSO burst duration as a base-2 negative exponent");
module_param(mprague_burst_shift, uint, 0644);

static struct tcp_congestion_ops mprague_reno;

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

static u32 mprague_max_tso_seg(struct sock *sk)
{
	return mprague_ca(sk)->max_tso_burst;
}

static bool mprague_rtt_complete(struct sock *sk)
{
	/* At the moment, we detect expired RTT using cwnd completion */
	return !before(tcp_sk(sk)->snd_una, mprague_ca(sk)->next_seq);
}


static void mprague_reset(const struct tcp_sock *tp, struct mprague *ca)
{
	ca->next_seq = tp->snd_nxt;
	ca->old_delivered_ce = tp->delivered_ce;
	ca->old_delivered = tp->delivered;
	ca->was_ce = false;
}


static u32 mprague_ssthresh(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u64 reduction;

	ca->loss_cwnd = tp->snd_cwnd;

	reduction = ((ca->upscaled_alpha >> mprague_shift_g) * tp->snd_cwnd
			/* Unbias the rounding by adding 1/2 */
			+ MPRAGUE_MAX_ALPHA) >> (MPRAGUE_ALPHA_BITS  + 1U);
	return max(tp->snd_cwnd - (u32)reduction, 2U);
}


/* Scale pacing rate based on the number of consecutive segments
 * that can be sent, i.e., rate is 200% for high BDPs
 * that are perfectly ACK-paced (i.e., where packets_out is
 * almost max_inflight), but decrease to 100% if a full
 * RTT is aggregated into a single ACK or if we have more in
 * flight data than our cwnd allows.
 */
/* pacing_rate = rate + rate * (1 + tp->packets_out) / max_inflight; */

static void mprague_update_pacing_rate(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	u64 max_burst, rate, pacing_rate;
	u32 max_inflight;
	max_inflight = max(tp->snd_cwnd, tp->packets_out);
	rate = (u64)tp->mss_cache * (USEC_PER_SEC << 3) * max_inflight;
	if (likely(tp->srtt_us))
		do_div(rate, tp->srtt_us);
	pacing_rate = rate;
	if (tp->snd_cwnd < tp->snd_ssthresh / 2)
		pacing_rate *= sock_net(sk)->ipv4.sysctl_tcp_pacing_ss_ratio;
	else if (tp->packets_out < tp->snd_cwnd)
		pacing_rate *= sock_net(sk)->ipv4.sysctl_tcp_pacing_ca_ratio;
	do_div(pacing_rate, 100);
	rate = min_t(u64, pacing_rate, sk->sk_max_pacing_rate);
	WRITE_ONCE(sk->sk_pacing_rate, rate);

	max_burst = div_u64(rate * mprague_burst_usec,
			tp->mss_cache * USEC_PER_SEC);
	if (likely(pacing_rate)) {
		max_burst *= rate;
		do_div(max_burst, pacing_rate);
	}

	max_burst = max_t(u32, 1, max_burst);
	WRITE_ONCE(mprague_ca(sk)->max_tso_burst, max_burst);
}


static void mprague_rtt_expired(struct sock *sk)
{
	struct mprague *ca = mprague_ca(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u64 ecn_segs, alpha;

	/* Do not update alpha before we have proof that there's an AQM on
	 * the path.
	 */
	if (unlikely(!ca->saw_ce))
		goto reset;

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
		do_div(ecn_segs, max(1U, acked_segs));
	}
	alpha = alpha - (alpha >> mprague_shift_g) + ecn_segs;

	WRITE_ONCE(ca->upscaled_alpha, alpha);

reset:
	mprague_reset(tp, ca);
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


static void mprague_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{

	struct tcp_sock *tp = tcp_sk(sk);
	int snd_cwnd = 0,cwnd_old = 0;
	u64 beta;

	if (!mptcp(tp) ) {
		tcp_reno_cong_avoid(sk, ack, acked);
		return;
	}

	if (!tcp_is_cwnd_limited(sk))
	{      
		return;
	}
	if (tcp_in_slow_start(tp)) {
		/* In "safe" area, increase. */
		tcp_slow_start(tp, acked);
		mprague_recalc_beta(sk);
		return;
	}

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
	if (snd_cwnd < tp->snd_cwnd)
		snd_cwnd = tp->snd_cwnd;

	cwnd_old = tp->snd_cwnd;
	tcp_cong_avoid_ai(tp, snd_cwnd, acked);
	if (tp->snd_cwnd > cwnd_old)
		mprague_recalc_beta(sk);
}

static void mprague_update_window(struct sock *sk,
		const struct rate_sample *rs)
{
	/* Do not increase cwnd for ACKs indicating congestion */
	if (rs->is_ece ) {
		mprague_ca(sk)->saw_ce = true;
		//return; /*commented in prague*/
	}
	/* We don't implement PRR at the moment... */
	/* if (inet_csk(sk)->icsk_ca_state != TCP_CA_Open)
	   return; */

	mprague_cong_avoid(sk, 0, rs->acked_sacked);
}


static void mprague_cong_control(struct sock *sk, const struct rate_sample *rs)
{
	mprague_update_window(sk, rs);
	if (mprague_rtt_complete(sk))
		mprague_rtt_expired(sk);
	mprague_update_pacing_rate(sk);
}


static void mprague_react_to_loss(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);	

	mprague_ca(sk)->loss_cwnd = tp->snd_cwnd;
	/* Stay fair with reno (RFC-style) */
	tp->snd_ssthresh = max(tp->snd_cwnd >> 1U, 2U);
	tp->snd_cwnd = tp->snd_ssthresh;
	tp->snd_cwnd_stamp = tcp_jiffies32;
}

static void mprague_enter_cwr(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	/* prague_ssthresh() has already been applied to snd_ssthresh in
	 * tcp_init_cwnd_reduction()
	 */
	tp->snd_cwnd = tp->snd_ssthresh;
	tp->snd_ssthresh = tp->snd_cwnd;
	tp->snd_cwnd_stamp = tcp_jiffies32;

}

static void mprague_state(struct sock *sk, u8 new_state)
{

	u8 old_state = inet_csk(sk)->icsk_ca_state;

	if (!mptcp(tcp_sk(sk)))
		return;

	if (new_state == old_state)
		return;
	switch (new_state) {
		case TCP_CA_Recovery:
			mprague_react_to_loss(sk);
			mprague_set_forced(mptcp_meta_sk(sk), 1);
			break;
		case TCP_CA_CWR:
			mprague_enter_cwr(sk);
			mprague_set_forced(mptcp_meta_sk(sk), 1);
			break;
		default:
			break;
	}

}


static void mprague_cwnd_event(struct sock *sk, enum tcp_ca_event ev)
{  
	struct tcp_sock *tp = tcp_sk(sk);
	if (!mptcp(tp))
		return;

	switch(ev) {
		case CA_EVENT_ECN_IS_CE:
			mprague_ca(sk)->was_ce = true;
			break;
		case CA_EVENT_ECN_NO_CE:
			if (mprague_ca(sk)->was_ce)
				/* Immediately ACK a trail of CE packets */
				inet_csk(sk)->icsk_ack.pending |= ICSK_ACK_NOW;
			mprague_ca(sk)->was_ce = false;
			break;
		case CA_EVENT_LOSS:
			/* React to a RTO if no other loss-related events happened
			 * during this window.
			 */
			mprague_react_to_loss(sk);
			mprague_set_forced(mptcp_meta_sk(sk),1);
			break;
		default:
			/* Ignore everything else */
			break;
	}
}

static u32 mprague_cwnd_undo(struct sock *sk)
{
	const struct mprague *ca = inet_csk_ca(sk);

	return max(tcp_sk(sk)->snd_cwnd, ca->loss_cwnd);
}



static void mprague_release(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	cmpxchg(&sk->sk_pacing_status, SK_PACING_NEEDED, SK_PACING_NONE);
	/* We forced the use of ECT(x), disable this before switching CC */
	INET_ECN_dontxmit(sk);
	/* TODO(otilmans) if we allow that param to be 0644 then we'll
	 * need to deal with that here and not unconditionally reset
	 * the flag (e.g., could have been set by bpf prog)
	 */
	tp->ecn_flags &= ~TCP_ECN_ECT_1;
	//LOG(sk, "Releasing: delivered_ce=%u, received_ce=%u, " "received_ce_tx: %u\n", tp->delivered_ce, tp->received_ce,tp->received_ce_tx);
}


static void mprague_init(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (mptcp(tcp_sk(sk)) && ( tcp_ecn_ok(tp) || ( (sk->sk_state == TCP_LISTEN || sk->sk_state == TCP_CLOSE)))) {
		struct mprague *ca = mprague_ca(sk);
		mprague_set_forced(mptcp_meta_sk(sk), 0);
		mprague_set_beta(mptcp_meta_sk(sk), beta_scale);

		ca->prior_rcv_nxt = tp->rcv_nxt;

		ca->upscaled_alpha = MPRAGUE_MAX_ALPHA << mprague_shift_g;
		ca->loss_cwnd = 0;
		ca->saw_ce = tp->delivered_ce != TCP_ACCECN_CEP_INIT;
		/* Conservatively start with a very low TSO limit */
		ca->max_tso_burst = 1;
		if (mprague_ect)
			tp->ecn_flags |= TCP_ECN_ECT_1;

		cmpxchg(&sk->sk_pacing_status, SK_PACING_NONE, SK_PACING_NEEDED);
		mprague_reset(tp, ca);
		return;
	} 

	/* Cannot use Prague without AccECN
	 * TODO(otilmans) If TCP_ECN_OK, we can trick the receiver to echo few
	 * ECEs per CE received by setting CWR at most once every two segments.
	 * This is however quite sensitive to ACK thinning...
	 */
	mprague_release(sk);
	inet_csk(sk)->icsk_ca_ops = &mprague_reno;
}


static struct tcp_congestion_ops mprague __read_mostly = {
	.init       = mprague_init,
	.release    = mprague_release,
	.cong_control = mprague_cong_control,
	.cwnd_event = mprague_cwnd_event,
	.ssthresh   = mprague_ssthresh,
	.undo_cwnd  = mprague_cwnd_undo,
	.set_state  = mprague_state,
	.max_tso_segs   = mprague_max_tso_seg,
	.flags      = TCP_CONG_NEEDS_ECN | TCP_CONG_NON_RESTRICTED,
	.owner      = THIS_MODULE,
	.name       = "mprague",
};

static struct tcp_congestion_ops mprague_reno __read_mostly = {
	.ssthresh   = tcp_reno_ssthresh,
	.cong_avoid = tcp_reno_cong_avoid,
	.undo_cwnd  = tcp_reno_undo_cwnd,
	.owner      = THIS_MODULE,
	.name       = "mprague-reno",
};

static int __init mprague_register(void)
{
	BUILD_BUG_ON(sizeof(struct mprague) > ICSK_CA_PRIV_SIZE);

	if (mprague_ect)
		mprague.flags |= TCP_CONG_WANTS_ECT_1;
	if (!mprague_ecn_plus_plus)
		mprague.flags &= ~TCP_CONG_NEEDS_ECN;

	return tcp_register_congestion_control(&mprague);
}

static void __exit mprague_unregister(void)
{
	tcp_unregister_congestion_control(&mprague);
}

module_init(mprague_register);
module_exit(mprague_unregister);

MODULE_AUTHOR("Olivier Tilmans <olivier.tilmans@nokia-bell-labs.com>");
MODULE_AUTHOR("Koen de Schepper <koen.de_schepper@nokia-bell-labs.com>");
MODULE_AUTHOR("Bob briscoe <research@bobbriscoe.net>");

MODULE_LICENSE("GPL v2");
MODULE_DESCRIPTION("MPTCP Prague");


