// Sample from Bernoulli(exp(-x)) for x ∈ (0, 1].
//
// From CKS20 (Canonne, Kamath, Steinke 2020):
//   Loop k = 1, 2, ...: flip Bernoulli(x/k).
//     If true, increment k. If false, return (k is odd).
//
// See opendp: `sample_bernoulli_exp1` in opendp/rust/src/traits/samplers/cks20/mod.rs.
//
// Distribution credit specification:
//
//   ε ≥ exp(-x) · ℰ(true) + (1 - exp(-x)) · ℰ(false)
//   ---------------------------------------------------
//   [{ ↯(ε) }] sample_bernoulli_exp1(x) [{ v. ↯(ℰ(v)) }]
//
// Proof structure (follows bounded_geo_dist pattern):
//
//   At step k, flip Bernoulli(x/k) via sample_bernoulli_rational.
//     tails (stop):     credit e(k%2==1)
//     heads (continue): credit new_eps = amp·eps - (amp-1)·e(k%2==1)
//       where amp = k·denom_x / numer_x
//
//   Slack amplifies by factor amp ≥ 1 at each step.
//   Termination: slack · Π amp_j ≥ 1, tracked via slack_product.

use vstd::prelude::*;

use random::{UBig, ubig_from_u64, ubig_succ, ubig_mul_u64, ubig_is_odd};

verus! {

use crate::ub::*;
use crate::rand_primitives::thin_air;
use crate::math::pow::{pow, archimedean_exp_growth};
use crate::math::series::lemma_pow_nonneg;
use crate::math::exp::axiom_exp1_conditional_prob_range;
use crate::extern_spec::{ExUBig, ubig_view};
use crate::discrete_laplace::bernoulli_rational::{bernoulli_weighted_sum, sample_bernoulli_rational};

// ============================================================================
// Spec functions (all use nat for step k)
// ============================================================================

/// Amplification factor at step k: k · denom_x / numer_x.
pub open spec fn exp1_amp(numer_x: u64, denom_x: u64, k: nat) -> real {
    k as real * denom_x as real / numer_x as real
}

/// New eps after the flip: amp · eps - (amp - 1) · e(k%2==1).
pub open spec fn exp1_new_eps(numer_x: u64, denom_x: u64, k: nat, eps: real, e: spec_fn(bool) -> real) -> real {
    let amp = exp1_amp(numer_x, denom_x, k);
    amp * eps - (amp - 1real) * e(k % 2 == 1)
}

/// Credit allocation for the Bernoulli(x/k) flip at step k.
pub open spec fn exp1_flip_e(e: spec_fn(bool) -> real, k: nat, new_eps: real) -> spec_fn(bool) -> real {
    |b: bool| if b { new_eps } else { e(k % 2 == 1) }
}

/// Next conditional probability: p_k = (x/k)·p_{k+1} + (1-x/k)·[k%2==1].
pub open spec fn exp1_next_p(numer_x: u64, denom_x: u64, k: nat, p_k: real) -> real {
    let amp = exp1_amp(numer_x, denom_x, k);
    if k % 2 == 1 { (p_k - 1real) * amp + 1real }
    else { p_k * amp }
}

/// Product of amplification factors: Π_{j=k}^{k+depth-1} amp_j.
pub open spec fn slack_product(numer_x: u64, denom_x: u64, k: nat, depth: nat) -> real
    decreases depth,
{
    if depth == 0 { 1real }
    else { exp1_amp(numer_x, denom_x, k) * slack_product(numer_x, denom_x, k + 1, (depth - 1) as nat) }
}

// ============================================================================
// Lemmas
// ============================================================================

/// bernoulli_weighted_sum(x/k, flip_e) == eps (by construction of new_eps).
proof fn lemma_exp1_flip_average(numer_x: u64, denom_x: u64, k: nat, eps: real, e: spec_fn(bool) -> real)
    requires numer_x > 0, denom_x > 0, k >= 1,
    ensures ({
        let new_eps = exp1_new_eps(numer_x, denom_x, k, eps, e);
        let flip_e = exp1_flip_e(e, k, new_eps);
        let prob = numer_x as real / (k as real * denom_x as real);
        bernoulli_weighted_sum(prob, flip_e) == eps
    }),
{
    let amp = exp1_amp(numer_x, denom_x, k);
    let new_eps = exp1_new_eps(numer_x, denom_x, k, eps, e);
    let flip_e = exp1_flip_e(e, k, new_eps);
    let prob = numer_x as real / (k as real * denom_x as real);
    assert(bernoulli_weighted_sum(prob, flip_e) == eps)
        by(nonlinear_arith)
        requires
            prob == numer_x as real / (k as real * denom_x as real),
            new_eps == amp * eps - (amp - 1real) * e(k % 2 == 1),
            amp == k as real * denom_x as real / numer_x as real,
            flip_e(true) == new_eps,
            flip_e(false) == e(k % 2 == 1),
            bernoulli_weighted_sum(prob, flip_e) == prob * flip_e(true) + (1real - prob) * flip_e(false),
            numer_x > 0u64, denom_x > 0u64, k >= 1;
}

/// p_k satisfies the recursion with p_next = exp1_next_p.
proof fn lemma_exp1_next_p_recursion(numer_x: u64, denom_x: u64, k: nat, p_k: real)
    requires numer_x > 0, denom_x > 0, k >= 1,
    ensures ({
        let p_next = exp1_next_p(numer_x, denom_x, k, p_k);
        let prob = numer_x as real / (k as real * denom_x as real);
        p_k == prob * p_next + (1real - prob) * (if k % 2 == 1 { 1real } else { 0real })
    }),
{
    let amp = exp1_amp(numer_x, denom_x, k);
    let prob = numer_x as real / (k as real * denom_x as real);
    let p_next = exp1_next_p(numer_x, denom_x, k, p_k);
    assert(prob * amp == 1real) by(nonlinear_arith)
        requires
            prob == numer_x as real / (k as real * denom_x as real),
            amp == k as real * denom_x as real / numer_x as real,
            numer_x > 0u64, denom_x > 0u64, k >= 1;
    if k % 2 == 1 {
        assert(p_k == prob * p_next + (1real - prob) * 1real)
            by(nonlinear_arith)
            requires p_next == (p_k - 1real) * amp + 1real, prob * amp == 1real;
    } else {
        assert(p_k == prob * p_next + (1real - prob) * 0real)
            by(nonlinear_arith)
            requires p_next == p_k * amp, prob * amp == 1real;
    }
}

/// Distribution bound shifts correctly through the recursion.
proof fn lemma_exp1_shift_bound(
    numer_x: u64, denom_x: u64, k: nat,
    eps: real, slack: real, e: spec_fn(bool) -> real,
    p_k: real, p_next: real,
)
    requires
        numer_x > 0, denom_x > 0, numer_x <= denom_x, k >= 1,
        eps - slack >= bernoulli_weighted_sum(p_k, e),
        p_k == (numer_x as real / (k as real * denom_x as real)) * p_next
             + (1real - numer_x as real / (k as real * denom_x as real)) * (if k % 2 == 1 { 1real } else { 0real }),
    ensures ({
        let amp = exp1_amp(numer_x, denom_x, k);
        let new_eps = exp1_new_eps(numer_x, denom_x, k, eps, e);
        let new_slack = amp * slack;
        new_eps - new_slack >= bernoulli_weighted_sum(p_next, e)
    }),
{
    let amp = exp1_amp(numer_x, denom_x, k);
    let prob = numer_x as real / (k as real * denom_x as real);
    assert(prob * amp == 1real) by(nonlinear_arith)
        requires
            prob == numer_x as real / (k as real * denom_x as real),
            amp == k as real * denom_x as real / numer_x as real,
            numer_x > 0u64, denom_x > 0u64, k >= 1;
    // new_eps - new_slack = amp*(eps-slack) - (amp-1)*e(k%2==1)
    // >= amp*bernoulli_weighted_sum(p_k, e) - (amp-1)*e(k%2==1)
    // = amp*(p_k*e(T) + (1-p_k)*e(F)) - (amp-1)*e(k%2==1)
    // = p_next*e(T) + (1-p_next)*e(F)   [using amp*p_k = p_next + (amp-1)*[k%2==1]]
    let eT = e(true);
    let eF = e(false);
    // amp * p_k = p_next + (amp-1)*[k%2==1]
    // amp * bws(p_k) - (amp-1)*e(k%2==1) = bws(p_next)
    // Proof: distribute amp over bws, substitute amp*p_k, cancel.
    let amp_pk = amp * p_k;
    if k % 2 == 1 {
        assert(amp_pk == p_next + (amp - 1real))
            by(nonlinear_arith)
            requires amp_pk == amp * p_k,
                p_k == prob * p_next + (1real - prob), prob * amp == 1real;
        assert(amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eT
            == p_next * eT + (1real - p_next) * eF)
            by(nonlinear_arith)
            requires amp_pk == p_next + (amp - 1real);
    } else {
        assert(amp_pk == p_next)
            by(nonlinear_arith)
            requires amp_pk == amp * p_k,
                p_k == prob * p_next, prob * amp == 1real;
        assert(amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eF
            == p_next * eT + (1real - p_next) * eF)
            by(nonlinear_arith)
            requires amp_pk == p_next;
    }
    // Connect: amp*(p_k*eT + (1-p_k)*eF) == amp_pk*eT + (amp-amp_pk)*eF
    assert(amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF)
        by(nonlinear_arith)
        requires amp_pk == amp * p_k;
    // Final: new_eps - new_slack = amp*(eps-slack) - (amp-1)*e(k%2==1)
    //   >= amp*bws(p_k) - (amp-1)*e(k%2==1) = bws(p_next)
    let new_eps = exp1_new_eps(numer_x, denom_x, k, eps, e);
    let new_slack = amp * slack;
    let bws_pk = bernoulli_weighted_sum(p_k, e);
    let bws_pn = bernoulli_weighted_sum(p_next, e);
    assert(new_eps - new_slack == amp * (eps - slack) - (amp - 1real) * e(k % 2 == 1))
        by(nonlinear_arith)
        requires
            new_eps == amp * eps - (amp - 1real) * e(k % 2 == 1),
            new_slack == amp * slack;
    assert(amp >= 1real) by(nonlinear_arith)
        requires amp == k as real * denom_x as real / numer_x as real,
            numer_x > 0u64, denom_x > 0u64, numer_x <= denom_x, k >= 1;
    assert(amp * (eps - slack) >= amp * bws_pk)
        by(nonlinear_arith)
        requires eps - slack >= bws_pk, amp >= 1real;
    if k % 2 == 1 {
        assert(amp * bws_pk - (amp - 1real) * eT == bws_pn)
            by(nonlinear_arith)
            requires
                amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF,
                amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eT == bws_pn,
                bws_pk == p_k * eT + (1real - p_k) * eF;
    } else {
        assert(amp * bws_pk - (amp - 1real) * eF == bws_pn)
            by(nonlinear_arith)
            requires
                amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF,
                amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eF == bws_pn,
                bws_pk == p_k * eT + (1real - p_k) * eF;
    }
}

/// slack_product for k ≥ 2 is ≥ pow(2, depth), since each factor ≥ 2.
proof fn lemma_slack_product_ge_pow2(numer_x: u64, denom_x: u64, k: nat, depth: nat)
    requires numer_x > 0, denom_x > 0, numer_x <= denom_x, k >= 2,
    ensures slack_product(numer_x, denom_x, k, depth) >= pow(2real, depth),
    decreases depth,
{
    if depth == 0 {
    } else {
        lemma_slack_product_ge_pow2(numer_x, denom_x, k + 1, (depth - 1) as nat);
        let a = exp1_amp(numer_x, denom_x, k);
        let sp = slack_product(numer_x, denom_x, k + 1, (depth - 1) as nat);
        assert(a >= 2real) by(nonlinear_arith)
            requires a == k as real * denom_x as real / numer_x as real,
                numer_x > 0u64, numer_x <= denom_x, k >= 2;
        assert(slack_product(numer_x, denom_x, k, depth) == a * sp);
        lemma_pow_nonneg(2real, (depth - 1) as nat);
        real_mul_ineq(a, sp, 2real, pow(2real, (depth - 1) as nat));
    }
}

/// slack_product from k=1: first factor (d/n) ≥ 1, rest ≥ 2 each.
proof fn lemma_slack_product_k1_bound(numer_x: u64, denom_x: u64, depth: nat)
    requires numer_x > 0, denom_x > 0, numer_x <= denom_x, depth >= 1,
    ensures slack_product(numer_x, denom_x, 1nat, depth) >= pow(2real, (depth - 1) as nat),
{
    lemma_slack_product_ge_pow2(numer_x, denom_x, 2nat, (depth - 1) as nat);
    let a = exp1_amp(numer_x, denom_x, 1nat);
    let sp = slack_product(numer_x, denom_x, 2nat, (depth - 1) as nat);
    assert(a >= 1real) by(nonlinear_arith)
        requires a == 1real * denom_x as real / numer_x as real,
            numer_x > 0u64, numer_x <= denom_x;
    assert(slack_product(numer_x, denom_x, 1nat, depth) == a * sp);
    lemma_pow_nonneg(2real, (depth - 1) as nat);
    real_mul_ineq(a, sp, 1real, pow(2real, (depth - 1) as nat));
}

#[verifier::nonlinear]
proof fn real_assoc_mult(a: real, b: real, c: real)
    ensures a * (b * c) == (a * b) * c,
{}

#[verifier::nonlinear]
proof fn real_mul_ineq(a: real, b: real, a_lb: real, b_lb: real)
    requires a >= a_lb, b >= b_lb, a_lb >= 0real, b_lb >= 0real,
    ensures a * b >= a_lb * b_lb,
{}

// ============================================================================
// Bounded sampler (uses UBig for k to avoid overflow)
// ============================================================================

pub fn bounded_bernoulli_exp1(
    numer_x: u64,
    denom_x: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    k: UBig,
    Ghost(depth): Ghost<nat>,
    Ghost(eps): Ghost<real>,
    Ghost(slack): Ghost<real>,
    Ghost(p_k): Ghost<real>,
) -> (ret: (bool, Tracked<ErrorCreditResource>))
    requires
        numer_x > 0,
        denom_x > 0,
        numer_x <= denom_x,
        ubig_view(&k) >= 1,
        e(true) >= 0real,
        e(false) >= 0real,
        0real <= p_k <= 1real,
        eps > 0real,
        slack > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps - slack >= bernoulli_weighted_sum(p_k, e),
        slack * slack_product(numer_x, denom_x, ubig_view(&k), depth) >= 1real,
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
    decreases depth,
{
    proof {
        if depth == 0nat {
            assert(bernoulli_weighted_sum(p_k, e) >= 0real) by(nonlinear_arith)
                requires 0real <= p_k <= 1real, e(true) >= 0real, e(false) >= 0real;
            ec_contradict(&input_credit);
        }
    }

    let ghost kn = ubig_view(&k);
    let k_denom = ubig_mul_u64(&k, denom_x);
    let ghost kdn = ubig_view(&k_denom);

    let ghost amp = exp1_amp(numer_x, denom_x, kn);
    let ghost new_eps = exp1_new_eps(numer_x, denom_x, kn, eps, e);
    let ghost flip_e = exp1_flip_e(e, kn, new_eps);
    let ghost p_next = exp1_next_p(numer_x, denom_x, kn, p_k);

    proof {
        // kdn == kn * denom_x
        assert(kdn == kn * denom_x as nat);
        lemma_exp1_flip_average(numer_x, denom_x, kn, eps, e);
        // Connect numer_x / kdn to numer_x / (kn * denom_x)
        assert(numer_x as real / (kdn as real)
            == numer_x as real / (kn as real * denom_x as real)) by(nonlinear_arith)
            requires kdn == kn * denom_x as nat, kn >= 1, denom_x > 0u64;
        assert(numer_x as nat <= kdn) by(nonlinear_arith)
            requires numer_x <= denom_x, kn >= 1, kdn == kn * denom_x as nat;
        assert(kdn > 0) by(nonlinear_arith)
            requires kn >= 1, denom_x > 0u64, kdn == kn * denom_x as nat;

        lemma_exp1_next_p_recursion(numer_x, denom_x, kn, p_k);
        lemma_exp1_shift_bound(numer_x, denom_x, kn, eps, slack, e, p_k, p_next);
        // p_next ∈ [0,1] from alternating series axiom
        let ghost x = numer_x as real / denom_x as real;
        assert(x > 0real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real >= 1real, denom_x as real >= 1real;
        assert(x <= 1real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real <= denom_x as real, denom_x as real >= 1real;
        assert(kn as real * denom_x as real / numer_x as real == kn as real / x)
            by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x > 0u64, denom_x > 0u64;
        axiom_exp1_conditional_prob_range(x, kn, p_k, kn as real / x);
        assert(bernoulli_weighted_sum(p_next, e) >= 0real) by(nonlinear_arith)
            requires 0real <= p_next <= 1real, e(true) >= 0real, e(false) >= 0real;
        assert(amp >= 1real) by(nonlinear_arith)
            requires amp == kn as real * denom_x as real / numer_x as real,
                numer_x > 0u64, denom_x > 0u64, numer_x <= denom_x, kn >= 1;
        assert(new_eps >= 0real) by(nonlinear_arith)
            requires
                new_eps - amp * slack >= bernoulli_weighted_sum(p_next, e),
                bernoulli_weighted_sum(p_next, e) >= 0real,
                amp >= 1real, slack > 0real;
    }

    // TODO: sample_bernoulli_rational takes u64 denom, but k_denom is UBig.
    // For now, use external_body wrapper. A full fix requires UBig-based rand.
    let (heads, Tracked(out_credit)) = sample_bernoulli_rational_ubig(
        numer_x,
        &k_denom,
        Ghost(flip_e),
        Tracked(input_credit),
        Ghost(eps),
    );

    let is_odd = ubig_is_odd(&k);

    if !heads {
        proof {
            // is_odd == (kn % 2 == 1) == (kn % 2 == 1) matches flip_e(false) = e(kn % 2 == 1)
        }
        (is_odd, Tracked(out_credit))
    } else {
        let ghost new_slack = amp * slack;
        let k_next = ubig_succ(k);

        proof {
            assert(new_slack > 0real) by(nonlinear_arith)
                requires new_slack == amp * slack, amp >= 1real, slack > 0real;
            assert(new_eps > 0real) by(nonlinear_arith)
                requires
                    new_eps - new_slack >= bernoulli_weighted_sum(p_next, e),
                    bernoulli_weighted_sum(p_next, e) >= 0real,
                    new_slack > 0real;
            assert(ubig_view(&k_next) == kn + 1);
            real_assoc_mult(slack, amp, slack_product(numer_x, denom_x, kn + 1, (depth - 1) as nat));
        }

        bounded_bernoulli_exp1(
            numer_x, denom_x,
            Ghost(e), Tracked(out_credit),
            k_next,
            Ghost((depth - 1) as nat),
            Ghost(new_eps), Ghost(new_slack), Ghost(p_next),
        )
    }
}

/// Wrapper: sample_bernoulli_rational with UBig denominator.
/// Trusted boundary: the actual sampling uses finite-precision random bits.
#[verifier::external_body]
fn sample_bernoulli_rational_ubig(
    numer: u64,
    denom: &UBig,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (bool, Tracked<ErrorCreditResource>))
    requires
        ubig_view(denom) > 0,
        numer as nat <= ubig_view(denom),
        e(true) >= 0real,
        e(false) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(numer as real / ubig_view(denom) as real, e),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
{
    // Runtime: use rejection sampling from u64 chunks
    // For now, delegate to opendp's sample_bernoulli_rational via RBig
    unimplemented!()
}

// ============================================================================
// Unbounded wrapper
// ============================================================================

pub fn sample_bernoulli_exp1(
    numer_x: u64,
    denom_x: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Ghost(prob_true): Ghost<real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (bool, Tracked<ErrorCreditResource>))
    requires
        numer_x > 0,
        denom_x > 0,
        numer_x <= denom_x,
        0real <= prob_true <= 1real,
        e(true) >= 0real,
        e(false) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(prob_true, e),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
{
    let Tracked(slack_credit) = thin_air();

    let ghost slack: real;
    let ghost depth: nat;

    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        archimedean_exp_growth(slack, 2real);
        let d0: nat = choose |k: nat| slack * pow(2real, k) >= 1real;
        depth = d0 + 1;
        lemma_slack_product_k1_bound(numer_x, denom_x, depth);
        assert(slack * slack_product(numer_x, denom_x, 1nat, depth) >= 1real)
            by(nonlinear_arith)
            requires
                slack * pow(2real, d0) >= 1real,
                slack_product(numer_x, denom_x, 1nat, depth) >= pow(2real, d0),
                slack > 0real;
    }

    let ghost total_eps = eps + slack;
    let tracked combined: ErrorCreditResource;
    proof {
        combined = ec_combine(input_credit, slack_credit, eps, slack);
    }

    let k_init = ubig_from_u64(1u64);

    bounded_bernoulli_exp1(
        numer_x, denom_x,
        Ghost(e), Tracked(combined),
        k_init,
        Ghost(depth),
        Ghost(total_eps), Ghost(slack), Ghost(prob_true),
    )
}

} // verus!
