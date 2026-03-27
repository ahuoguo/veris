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
use crate::math::series::{lemma_pow_nonneg, partial_sum};
use crate::math::exp::{exp, axiom_exp_neg_range, axiom_exp_neg_strict,
    factorial, exp_taylor_term, exp_taylor_seq, axiom_exp_taylor_bounds};
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
// Connection between p_k and Taylor partial sums
//
// The CKS20 conditional probability at step k can be expressed as:
//   p_k = [k odd] + (k-1)!/x^{k-1} · R_k
// where R_k = exp(-x) - T_k(x) is the Taylor remainder and
// T_k(x) = Σ_{j=0}^{k-1} (-x)^j/j! is the partial sum.
//
// Since |R_k| ≤ x^k/k! (alternating series), we get
//   |(k-1)!/x^{k-1} · R_k| ≤ x/k
// and therefore p_k ∈ [0, 1].
// ============================================================================

// Helper lemmas for factorial, pow positivity, and pow parity.

/// factorial(n) > 0 for all n.
proof fn lemma_factorial_pos(n: nat)
    ensures factorial(n) > 0real,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_factorial_pos((n - 1) as nat);
        assert(factorial(n) == n as real * factorial((n - 1) as nat));
        assert(factorial(n) > 0real) by(nonlinear_arith)
            requires n >= 1, factorial((n - 1) as nat) > 0real,
                factorial(n) == n as real * factorial((n - 1) as nat);
    }
}

/// pow(x, n) > 0 for x > 0.
proof fn lemma_pow_pos(x: real, n: nat)
    requires x > 0real,
    ensures pow(x, n) > 0real,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_pow_pos(x, (n - 1) as nat);
        assert(pow(x, n) == x * pow(x, (n - 1) as nat));
        assert(pow(x, n) > 0real) by(nonlinear_arith)
            requires x > 0real, pow(x, (n - 1) as nat) > 0real,
                pow(x, n) == x * pow(x, (n - 1) as nat);
    }
}

/// pow(-x, k) = pow(x, k) when k is even, pow(-x, k) = -pow(x, k) when k is odd.
/// Equivalently: pow(-x, k) / pow(x, k) = (-1)^k.
proof fn lemma_pow_neg_parity(x: real, k: nat)
    requires x > 0real,
    ensures
        k % 2 == 0 ==> pow(-x, k) == pow(x, k),
        k % 2 == 1 ==> pow(-x, k) == -pow(x, k),
    decreases k,
{
    if k == 0 {
    } else if k == 1 {
        assert(pow(-x, 1nat) == (-x) * pow(-x, 0nat));
        assert(pow(-x, 0nat) == 1real);
        assert(pow(x, 1nat) == x * pow(x, 0nat));
        assert(pow(x, 0nat) == 1real);
    } else {
        lemma_pow_neg_parity(x, (k - 2) as nat);
        // pow(-x, k) = (-x)·(-x)·pow(-x, k-2) = x²·pow(-x, k-2)
        assert(pow(-x, k) == (-x) * pow(-x, (k - 1) as nat));
        assert(pow(-x, (k - 1) as nat) == (-x) * pow(-x, (k - 2) as nat));
        assert(pow(x, k) == x * pow(x, (k - 1) as nat));
        assert(pow(x, (k - 1) as nat) == x * pow(x, (k - 2) as nat));
        // k and k-2 have the same parity
        if k % 2 == 0 {
            // k-2 is even, so pow(-x, k-2) = pow(x, k-2) by IH
            assert(pow(-x, k) == pow(x, k))
                by(nonlinear_arith)
                requires
                    pow(-x, k) == (-x) * ((-x) * pow(-x, (k - 2) as nat)),
                    pow(x, k) == x * (x * pow(x, (k - 2) as nat)),
                    pow(-x, (k - 2) as nat) == pow(x, (k - 2) as nat);
        } else {
            // k-2 is odd, so pow(-x, k-2) = -pow(x, k-2) by IH
            assert(pow(-x, k) == -pow(x, k))
                by(nonlinear_arith)
                requires
                    pow(-x, k) == (-x) * ((-x) * pow(-x, (k - 2) as nat)),
                    pow(x, k) == x * (x * pow(x, (k - 2) as nat)),
                    pow(-x, (k - 2) as nat) == -pow(x, (k - 2) as nat);
        }
    }
}

/// scale_k · term_k = (-1)^k · x/k, i.e., x/k for k even and -x/k for k odd.
/// Where scale_k = (k-1)!/x^{k-1} and term_k = (-x)^k/k!.
///
/// Proof strategy: avoid division in nonlinear_arith by cross-multiplying.
/// scale * term_k = (fk1/pk1) * (pow(-x,k)/fk). Multiply both sides by pk1*fk:
///   LHS * pk1 * fk = fk1 * pow(-x,k)
///   RHS * pk1 * fk = (±x/k) * pk1 * fk = (±x/k) * pk1 * k * fk1 = ±x * pk1 * fk1
/// And fk1 * pow(-x,k) = fk1 * (±pk) = ±fk1 * x * pk1. Equal. QED.
proof fn lemma_scale_term_product(x: real, k: nat)
    requires x > 0real, k >= 1,
    ensures ({
        let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
        let term_k = exp_taylor_term(x, k);
        &&& k % 2 == 0 ==> scale * term_k == x / k as real
        &&& k % 2 == 1 ==> scale * term_k == -x / k as real
    }),
{
    let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
    let term_k = exp_taylor_term(x, k);
    let fk1 = factorial((k - 1) as nat);
    let pk1 = pow(x, (k - 1) as nat);
    let fk = factorial(k);
    let pk = pow(x, k);
    lemma_factorial_pos((k - 1) as nat);
    lemma_factorial_pos(k);
    lemma_pow_pos(x, (k - 1) as nat);
    lemma_pow_pos(x, k);
    lemma_pow_neg_parity(x, k);

    assert(fk == k as real * fk1);
    assert(pk == x * pk1);

    // Step 1: scale * pk1 = fk1 (clear denominator of scale = fk1/pk1)
    assert(scale * pk1 == fk1)
        by(nonlinear_arith) requires scale == fk1 / pk1, pk1 > 0real;
    // Step 2: term_k * fk = pow(-x, k) (clear denominator of term_k = pow(-x,k)/fk)
    assert(term_k * fk == pow(-x, k))
        by(nonlinear_arith) requires term_k == pow(-x, k) / fk, fk > 0real;
    // Step 3: scale * term_k * pk1 * fk = fk1 * pow(-x, k)
    assert(scale * term_k * pk1 * fk == fk1 * pow(-x, k))
        by(nonlinear_arith)
        requires scale * pk1 == fk1, term_k * fk == pow(-x, k);

    // Step 3 gave: scale * term_k * pk1 * fk == fk1 * pow(-x, k)
    // Substitute pow(-x,k) = ±pk = ±x*pk1 and cancel to get scale*term_k = ±x/k.

    if k % 2 == 0 {
        // pow(-x,k) = pk, so scale*term_k * pk1 * fk = fk1 * x * pk1
        assert(scale * term_k * pk1 * fk == fk1 * x * pk1)
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == fk1 * pow(-x, k),
                pow(-x, k) == pk, pk == x * pk1;
        // (x/k) * pk1 * fk = x * pk1 * fk1 (since fk = k * fk1)
        assert((x / k as real) * pk1 * fk == fk1 * x * pk1)
            by(nonlinear_arith) requires fk == k as real * fk1, k >= 1;
        // Both equal fk1*x*pk1 and pk1*fk > 0, so scale*term_k = x/k
        assert(scale * term_k == x / k as real)
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == fk1 * x * pk1,
                (x / k as real) * pk1 * fk == fk1 * x * pk1,
                pk1 > 0real, fk > 0real;
    } else {
        assert(scale * term_k * pk1 * fk == -(fk1 * x * pk1))
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == fk1 * pow(-x, k),
                pow(-x, k) == -pk, pk == x * pk1;
        assert((-x / k as real) * pk1 * fk == -(fk1 * x * pk1))
            by(nonlinear_arith) requires fk == k as real * fk1, k >= 1;
        assert(scale * term_k == -x / k as real)
            by(nonlinear_arith)
            requires scale * term_k * pk1 * fk == -(fk1 * x * pk1),
                (-x / k as real) * pk1 * fk == -(fk1 * x * pk1),
                pk1 > 0real, fk > 0real;
    }
}

/// The CKS20 conditional probability at step k, expressed via Taylor remainder.
///   p_k = [k odd] + (k-1)! / x^{k-1} · (exp(-x) - T_k(x))
pub open spec fn exp1_p_formula(x: real, k: nat) -> real {
    if k == 0 { 0real }
    else {
        let remainder = exp(-x) - partial_sum(exp_taylor_seq(x), k);
        let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
        (if k % 2 == 1 { 1real } else { 0real }) + scale * remainder
    }
}

/// Base case: exp1_p_formula(x, 1) == exp(-x).
///
/// T_1 = 1, R_1 = exp(-x) - 1, scale = 0!/x^0 = 1, so p_1 = 1 + (exp(-x) - 1) = exp(-x).
proof fn lemma_exp1_p_formula_base(x: real)
    requires 0real < x <= 1real,
    ensures exp1_p_formula(x, 1) == exp(-x),
{
    let seq = exp_taylor_seq(x);
    // Unfold T_1 = partial_sum(seq, 1) = 0 + seq(0) = pow(-x,0)/factorial(0) = 1
    assert(partial_sum(seq, 1nat) == partial_sum(seq, 0nat) + seq(0nat));
    assert(partial_sum(seq, 0nat) == 0real);
    assert(pow(-x, 0nat) == 1real);
    assert(factorial(0nat) == 1real);
    assert(pow(x, 0nat) == 1real);
    // p_1 = 1 + (1/1)·(exp(-x) - 1) = exp(-x)
    let remainder = exp(-x) - partial_sum(seq, 1nat);
    let scale = factorial(0nat) / pow(x, 0nat);
    assert(1real + scale * remainder == exp(-x))
        by(nonlinear_arith)
        requires scale == 1real, remainder == exp(-x) - 1real;
}

/// The recursion preserves the formula:
///   exp1_next_p(x, k, exp1_p_formula(x, k)) == exp1_p_formula(x, k+1)
///
/// Uses the telescoping identity: T_{k+1} = T_k + (-x)^k/k!,
/// so R_{k+1} = R_k - (-x)^k/k!.
proof fn lemma_exp1_p_formula_step(numer_x: u64, denom_x: u64, k: nat, x: real)
    requires
        numer_x > 0, denom_x > 0, numer_x <= denom_x, k >= 1,
        x == numer_x as real / denom_x as real,
    ensures
        exp1_next_p(numer_x, denom_x, k, exp1_p_formula(x, k))
            == exp1_p_formula(x, k + 1),
{
    let seq = exp_taylor_seq(x);
    let amp = exp1_amp(numer_x, denom_x, k);
    let t_k = partial_sum(seq, k);
    let t_k1 = partial_sum(seq, k + 1);
    let r_k = exp(-x) - t_k;
    let r_k1 = exp(-x) - t_k1;
    let s_k = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
    let s_k1 = factorial(k) / pow(x, k);
    let p_k = exp1_p_formula(x, k);
    let term_k = exp_taylor_term(x, k);

    // Telescoping: T_{k+1} = T_k + term_k, so R_{k+1} = R_k - term_k
    assert(t_k1 == t_k + seq(k));
    assert(seq(k) == term_k);
    assert(r_k1 == r_k - term_k);

    // amp = k/x
    assert(amp == k as real / x)
        by(nonlinear_arith)
        requires amp == k as real * denom_x as real / numer_x as real,
            x == numer_x as real / denom_x as real,
            numer_x > 0u64, denom_x > 0u64;

    // Positivity of factorial and pow
    lemma_factorial_pos((k - 1) as nat);
    lemma_factorial_pos(k);
    assert(x > 0real) by(nonlinear_arith)
        requires x == numer_x as real / denom_x as real, numer_x > 0u64, denom_x > 0u64;
    lemma_pow_pos(x, (k - 1) as nat);
    lemma_pow_pos(x, k);

    // s_k1 = amp · s_k via cross-multiplication (avoids division in solver)
    let fk1 = factorial((k - 1) as nat);
    let pk1 = pow(x, (k - 1) as nat);
    let fk = factorial(k);
    let pk = pow(x, k);
    assert(fk == k as real * fk1);
    assert(pk == x * pk1);
    assert(s_k1 * pk == fk)
        by(nonlinear_arith) requires s_k1 == fk / pk, pk > 0real;
    assert(s_k * pk1 == fk1)
        by(nonlinear_arith) requires s_k == fk1 / pk1, pk1 > 0real;
    assert(amp * s_k * pk == amp * fk1 * x)
        by(nonlinear_arith) requires s_k * pk1 == fk1, pk == x * pk1;
    assert(amp * fk1 * x == fk)
        by(nonlinear_arith) requires amp == k as real / x, fk == k as real * fk1, x > 0real;
    assert(s_k1 == amp * s_k)
        by(nonlinear_arith) requires s_k1 * pk == fk, amp * s_k * pk == fk, pk > 0real;

    // s_k1 · term_k = ±1 (cross-multiply: s_k1·term_k·pk = pow(-x,k) = ±pk)
    lemma_pow_neg_parity(x, k);
    assert(s_k1 * term_k * pk == pow(-x, k))
        by(nonlinear_arith)
        requires s_k1 == fk / pk, term_k == pow(-x, k) / fk,
            fk > 0real, pk > 0real;

    if k % 2 == 1 {
        assert(s_k1 * term_k == -1real) by(nonlinear_arith)
            requires s_k1 * term_k * pk == pow(-x, k), pow(-x, k) == -pk, pk > 0real;
        // k odd: next = (p_k-1)·amp + 1 = s_k1·r_k + 1
        //        formula(k+1) [even] = s_k1·r_k1 = s_k1·r_k - s_k1·term_k = s_k1·r_k + 1
        let next = exp1_next_p(numer_x, denom_x, k, p_k);
        assert(next == s_k1 * r_k + 1real) by(nonlinear_arith)
            requires next == (p_k - 1real) * amp + 1real,
                p_k == 1real + s_k * r_k, s_k1 == amp * s_k;
        assert(exp1_p_formula(x, k + 1) == s_k1 * r_k1);
        assert(s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k)
            by(nonlinear_arith) requires r_k1 == r_k - term_k;
        assert(s_k1 * r_k1 == next) by(nonlinear_arith)
            requires s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k,
                s_k1 * term_k == -1real, next == s_k1 * r_k + 1real;
    } else {
        assert(s_k1 * term_k == 1real) by(nonlinear_arith)
            requires s_k1 * term_k * pk == pow(-x, k), pow(-x, k) == pk, pk > 0real;
        // k even: next = p_k·amp = s_k1·r_k
        //         formula(k+1) [odd] = 1 + s_k1·r_k1 = 1 + s_k1·r_k - 1 = s_k1·r_k
        let next = exp1_next_p(numer_x, denom_x, k, p_k);
        assert(next == s_k1 * r_k) by(nonlinear_arith)
            requires next == p_k * amp, p_k == s_k * r_k, s_k1 == amp * s_k;
        assert(exp1_p_formula(x, k + 1) == 1real + s_k1 * r_k1);
        assert(s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k)
            by(nonlinear_arith) requires r_k1 == r_k - term_k;
        assert(1real + s_k1 * r_k1 == next) by(nonlinear_arith)
            requires s_k1 * r_k1 == s_k1 * r_k - s_k1 * term_k,
                s_k1 * term_k == 1real, next == s_k1 * r_k;
    }
}

/// Range: exp1_p_formula(x, k) ∈ [0, 1] for x ∈ (0, 1] and k ≥ 1.
///
/// From axiom_exp_taylor_bounds:
///   k even: R_k ≥ 0 and R_k ≤ x^k/k! (since R_{k+1} ≤ 0)
///   k odd:  R_k ≤ 0 and |R_k| ≤ x^k/k! (since R_{k+1} ≥ 0)
/// Scaling: |(k-1)!/x^{k-1} · R_k| ≤ (k-1)!/x^{k-1} · x^k/k! = x/k ≤ 1.
proof fn lemma_exp1_p_formula_range(x: real, k: nat)
    requires 0real < x <= 1real, k >= 1,
    ensures
        0real <= exp1_p_formula(x, k),
        exp1_p_formula(x, k) <= 1real,
{
    let seq = exp_taylor_seq(x);
    let t_k = partial_sum(seq, k);
    let t_k1 = partial_sum(seq, k + 1);
    let r_k = exp(-x) - t_k;
    let r_k1 = exp(-x) - t_k1;
    let scale = factorial((k - 1) as nat) / pow(x, (k - 1) as nat);
    let term_k = exp_taylor_term(x, k);

    // Axiom: partial sums bracket exp(-x)
    axiom_exp_taylor_bounds(x, k);
    axiom_exp_taylor_bounds(x, k + 1);

    // Telescoping: R_{k+1} = R_k - term_k
    assert(t_k1 == t_k + seq(k));
    assert(seq(k) == term_k);
    assert(r_k1 == r_k - term_k);

    // Positivity
    lemma_factorial_pos((k - 1) as nat);
    lemma_pow_pos(x, (k - 1) as nat);
    assert(scale > 0real)
        by(nonlinear_arith)
        requires scale == factorial((k - 1) as nat) / pow(x, (k - 1) as nat),
            factorial((k - 1) as nat) > 0real, pow(x, (k - 1) as nat) > 0real;

    // scale · term_k = ±x/k depending on parity (from helper lemma)
    lemma_scale_term_product(x, k);

    if k % 2 == 0 {
        // k even: T_k ≤ exp(-x) (r_k ≥ 0), T_{k+1} ≥ exp(-x) (r_k1 ≤ 0)
        // So 0 ≤ r_k ≤ term_k, and scale·r_k ∈ [0, x/k] ⊂ [0, 1].
        // p_k = scale·r_k.
        assert(r_k >= 0real) by(nonlinear_arith) requires t_k <= exp(-x), r_k == exp(-x) - t_k;
        assert(r_k1 <= 0real) by(nonlinear_arith) requires exp(-x) <= t_k1, r_k1 == exp(-x) - t_k1;
        assert(r_k <= term_k) by(nonlinear_arith) requires r_k1 == r_k - term_k, r_k1 <= 0real;
        assert(scale * r_k <= scale * term_k) by(nonlinear_arith) requires r_k <= term_k, scale > 0real;
        assert(scale * r_k >= 0real) by(nonlinear_arith) requires r_k >= 0real, scale > 0real;
        assert(x / k as real <= 1real) by(nonlinear_arith) requires x <= 1real, k >= 1;
        assert(exp1_p_formula(x, k) == scale * r_k);
    } else {
        // k odd: T_k ≥ exp(-x) (r_k ≤ 0), T_{k+1} ≤ exp(-x) (r_k1 ≥ 0)
        // So term_k ≤ r_k ≤ 0, and scale·r_k ∈ [-x/k, 0].
        // p_k = 1 + scale·r_k ∈ [1-x/k, 1] ⊂ [0, 1].
        assert(r_k <= 0real) by(nonlinear_arith) requires exp(-x) <= t_k, r_k == exp(-x) - t_k;
        assert(r_k1 >= 0real) by(nonlinear_arith) requires t_k1 <= exp(-x), r_k1 == exp(-x) - t_k1;
        assert(r_k >= term_k) by(nonlinear_arith) requires r_k1 == r_k - term_k, r_k1 >= 0real;
        assert(scale * r_k >= scale * term_k) by(nonlinear_arith) requires r_k >= term_k, scale > 0real;
        assert(scale * r_k <= 0real) by(nonlinear_arith) requires r_k <= 0real, scale > 0real;
        assert(x / k as real <= 1real) by(nonlinear_arith) requires x <= 1real, k >= 1;
        assert(exp1_p_formula(x, k) == 1real + scale * r_k);
        assert(exp1_p_formula(x, k) <= 1real) by(nonlinear_arith)
            requires exp1_p_formula(x, k) == 1real + scale * r_k, scale * r_k <= 0real;
        assert(exp1_p_formula(x, k) >= 0real) by(nonlinear_arith)
            requires exp1_p_formula(x, k) == 1real + scale * r_k,
                scale * r_k >= scale * term_k, scale * term_k == -x / k as real,
                x / k as real <= 1real;
    }
}

// ============================================================================
// Credit conservation lemmas
// ============================================================================

/// The credit allocation for the Bernoulli(x/k) flip exactly consumes eps.
///
/// At step k, we flip Bernoulli(prob) where prob = x/k = numer_x/(k·denom_x).
/// We allocate credit:
///   - heads (continue): new_eps = amp·eps - (amp-1)·e(k%2==1)
///   - tails (stop):     e(k%2==1)
///
/// This lemma verifies: prob·new_eps + (1-prob)·e(k%2==1) == eps.
/// The key identity is prob·amp == 1 (since amp = 1/prob), so the
/// amplification and de-amplification cancel perfectly.
#[verifier::nonlinear]
proof fn lemma_exp1_flip_average(numer_x: u64, denom_x: u64, k: nat, eps: real, e: spec_fn(bool) -> real)
    requires numer_x > 0, denom_x > 0, k >= 1,
    ensures ({
        let new_eps = exp1_new_eps(numer_x, denom_x, k, eps, e);
        let flip_e = exp1_flip_e(e, k, new_eps);
        let prob = numer_x as real / (k as real * denom_x as real);
        bernoulli_weighted_sum(prob, flip_e) == eps
    }),
{
}

/// The CKS20 conditional probability recursion is self-consistent.
///
/// The conditional probability p_k = P[return true | reached step k] satisfies:
///   p_k = (x/k) · p_{k+1} + (1 - x/k) · [k is odd]
///
/// This says: at step k we flip Bernoulli(x/k).
///   - With prob x/k (heads), we continue to step k+1 where prob of true is p_{k+1}.
///   - With prob 1-x/k (tails), we return (k is odd).
///
/// Given p_next = exp1_next_p (the rearranged form solving for p_{k+1}),
/// this lemma verifies the recursion holds. The key identity is prob·amp == 1.
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
    // prob = x/k and amp = k/x, so prob · amp == 1.
    // This lets us substitute back: prob · (p_k - [k odd]) · amp + [k odd] · prob · amp
    // simplifies to p_k.
    assert(prob * amp == 1real) by(nonlinear_arith)
        requires
            prob == numer_x as real / (k as real * denom_x as real),
            amp == k as real * denom_x as real / numer_x as real,
            numer_x > 0u64, denom_x > 0u64, k >= 1;
    if k % 2 == 1 {
        // p_next = (p_k - 1) · amp + 1, so prob · p_next = p_k - 1 + prob, giving
        // prob · p_next + (1 - prob) · 1 = p_k
        assert(p_k == prob * p_next + (1real - prob) * 1real)
            by(nonlinear_arith)
            requires p_next == (p_k - 1real) * amp + 1real, prob * amp == 1real;
    } else {
        // p_next = p_k · amp, so prob · p_next = p_k
        assert(p_k == prob * p_next + (1real - prob) * 0real)
            by(nonlinear_arith)
            requires p_next == p_k * amp, prob * amp == 1real;
    }
}

/// The distribution bound (eps - slack >= bws(p_k)) shifts correctly through one step.
///
/// This is the core invariant-preservation lemma. At each step k, we need to show
/// that after amplifying by amp = k/x:
///   new_eps - new_slack >= bws(p_next, e)
///
/// where new_eps = amp·eps - (amp-1)·e(k%2==1) and new_slack = amp·slack.
///
/// The proof has three parts:
///   (A) Algebraic identity: amp·bws(p_k) - (amp-1)·e(k%2==1) == bws(p_next).
///       This uses amp·p_k = p_next + (amp-1)·[k odd] from the recursion.
///   (B) Monotonicity: new_eps - new_slack = amp·(eps-slack) - (amp-1)·e(k%2==1)
///                                         >= amp·bws(p_k) - (amp-1)·e(k%2==1)
///       since amp >= 1 and eps - slack >= bws(p_k).
///   (C) Combining (A) and (B): new_eps - new_slack >= bws(p_next).
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
        requires prob == numer_x as real / (k as real * denom_x as real),
            amp == k as real * denom_x as real / numer_x as real,
            numer_x > 0u64, denom_x > 0u64, k >= 1;

    let eT = e(true);
    let eF = e(false);
    let amp_pk = amp * p_k;

    // (A) amp·bws(p_k) - (amp-1)·e(k%2==1) == bws(p_next)
    //     Uses: amp·p_k = p_next + (amp-1)·[k odd] (from prob·amp == 1)
    if k % 2 == 1 {
        assert(amp_pk == p_next + (amp - 1real)) by(nonlinear_arith)
            requires amp_pk == amp * p_k,
                p_k == prob * p_next + (1real - prob), prob * amp == 1real;
        assert(amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eT
            == p_next * eT + (1real - p_next) * eF)
            by(nonlinear_arith) requires amp_pk == p_next + (amp - 1real);
    } else {
        assert(amp_pk == p_next) by(nonlinear_arith)
            requires amp_pk == amp * p_k,
                p_k == prob * p_next, prob * amp == 1real;
        assert(amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eF
            == p_next * eT + (1real - p_next) * eF)
            by(nonlinear_arith) requires amp_pk == p_next;
    }
    // Distribute amp over bws (split to avoid solver divergence on single step)
    assert(amp * (p_k * eT) == amp_pk * eT)
        by(nonlinear_arith) requires amp_pk == amp * p_k;
    assert(amp * ((1real - p_k) * eF) == (amp - amp_pk) * eF)
        by(nonlinear_arith) requires amp_pk == amp * p_k;
    assert(amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF)
        by(nonlinear_arith)
        requires amp * (p_k * eT) == amp_pk * eT,
            amp * ((1real - p_k) * eF) == (amp - amp_pk) * eF;

    // (B) new_eps - new_slack >= amp·bws(p_k) - (amp-1)·e(k%2==1)
    let new_eps = exp1_new_eps(numer_x, denom_x, k, eps, e);
    let new_slack = amp * slack;
    let bws_pk = bernoulli_weighted_sum(p_k, e);
    let bws_pn = bernoulli_weighted_sum(p_next, e);
    assert(new_eps - new_slack == amp * (eps - slack) - (amp - 1real) * e(k % 2 == 1))
        by(nonlinear_arith)
        requires new_eps == amp * eps - (amp - 1real) * e(k % 2 == 1),
            new_slack == amp * slack;
    assert(amp >= 1real) by(nonlinear_arith)
        requires amp == k as real * denom_x as real / numer_x as real,
            numer_x > 0u64, denom_x > 0u64, numer_x <= denom_x, k >= 1;
    assert(amp * (eps - slack) >= amp * bws_pk)
        by(nonlinear_arith) requires eps - slack >= bws_pk, amp >= 1real;

    // (C) Combine: new_eps - new_slack >= bws(p_next)
    if k % 2 == 1 {
        assert(amp * bws_pk - (amp - 1real) * eT == bws_pn) by(nonlinear_arith)
            requires amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF,
                amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eT == bws_pn,
                bws_pk == p_k * eT + (1real - p_k) * eF;
    } else {
        assert(amp * bws_pk - (amp - 1real) * eF == bws_pn) by(nonlinear_arith)
            requires amp * (p_k * eT + (1real - p_k) * eF) == amp_pk * eT + (amp - amp_pk) * eF,
                amp_pk * eT + (amp - amp_pk) * eF - (amp - 1real) * eF == bws_pn,
                bws_pk == p_k * eT + (1real - p_k) * eF;
    }
}

/// Lower bound on slack_product: Π_{j=k}^{k+depth-1} amp_j >= 2^depth for k >= 2.
///
/// Each amp_j = j·denom_x/numer_x >= j·1 >= 2 (since j >= k >= 2 and denom_x >= numer_x),
/// so the product of `depth` factors each >= 2 gives >= 2^depth.
/// Proved by induction: peel off the first factor (>= 2) and multiply by the
/// inductive bound on the remaining product (>= 2^{depth-1}).
proof fn lemma_slack_product_ge_pow2(numer_x: u64, denom_x: u64, k: nat, depth: nat)
    requires numer_x > 0, denom_x > 0, numer_x <= denom_x, k >= 2,
    ensures slack_product(numer_x, denom_x, k, depth) >= pow(2real, depth),
    decreases depth,
{
    if depth == 0 {
        // slack_product(..., 0) == 1 == pow(2, 0)
    } else {
        // IH: slack_product(k+1, depth-1) >= 2^{depth-1}
        lemma_slack_product_ge_pow2(numer_x, denom_x, k + 1, (depth - 1) as nat);
        let a = exp1_amp(numer_x, denom_x, k);
        let sp = slack_product(numer_x, denom_x, k + 1, (depth - 1) as nat);
        // a = k·d/n >= 2·1 = 2 since k >= 2 and d >= n
        assert(a >= 2real) by(nonlinear_arith)
            requires a == k as real * denom_x as real / numer_x as real,
                numer_x > 0u64, numer_x <= denom_x, k >= 2;
        // slack_product(k, depth) == a · sp
        assert(slack_product(numer_x, denom_x, k, depth) == a * sp);
        // a · sp >= 2 · 2^{depth-1} = 2^depth
        lemma_pow_nonneg(2real, (depth - 1) as nat);
        real_mul_ineq(a, sp, 2real, pow(2real, (depth - 1) as nat));
    }
}

/// Lower bound starting from k=1: slack_product(1, depth) >= 2^{depth-1}.
///
/// The first factor amp_1 = denom_x/numer_x >= 1 (not necessarily >= 2),
/// so we lose one factor of 2 compared to lemma_slack_product_ge_pow2.
/// Split: slack_product(1, depth) = amp_1 · slack_product(2, depth-1)
///                                >= 1 · 2^{depth-1}.
proof fn lemma_slack_product_k1_bound(numer_x: u64, denom_x: u64, depth: nat)
    requires numer_x > 0, denom_x > 0, numer_x <= denom_x, depth >= 1,
    ensures slack_product(numer_x, denom_x, 1nat, depth) >= pow(2real, (depth - 1) as nat),
{
    // The tail from k=2 onwards has each factor >= 2
    lemma_slack_product_ge_pow2(numer_x, denom_x, 2nat, (depth - 1) as nat);
    let a = exp1_amp(numer_x, denom_x, 1nat);
    let sp = slack_product(numer_x, denom_x, 2nat, (depth - 1) as nat);
    // amp_1 = denom_x/numer_x >= 1
    assert(a >= 1real) by(nonlinear_arith)
        requires a == 1real * denom_x as real / numer_x as real,
            numer_x > 0u64, numer_x <= denom_x;
    assert(slack_product(numer_x, denom_x, 1nat, depth) == a * sp);
    // a · sp >= 1 · 2^{depth-1}
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

/// Bounded (depth-decreasing) sampler for Bernoulli(exp(-x)), x ∈ (0, 1].
///
/// Implements the CKS20 algorithm: at step k, flip Bernoulli(x/k).
///   - Tails: return (k is odd).
///   - Heads: continue to step k+1.
///
/// Ghost state tracks three quantities through the recursion:
///   - eps:   current error credit (amplified by amp = k/x at each step)
///   - slack: gap between eps and the distribution bound (also amplified by amp)
///   - p_k:   conditional probability, tied to exp(-x) via exp1_p_formula
///
/// Termination argument: slack grows by factor amp >= 1 at each step.
/// slack_product(k, depth) tracks the cumulative growth; when
/// slack · slack_product >= 1, we have enough credit to derive contradiction
/// at depth == 0 (since eps > slack >= 1/slack_product, but eps must also
/// cover the distribution bound, which is nonneg).
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
        p_k == exp1_p_formula(numer_x as real / denom_x as real, ubig_view(&k)),
        eps > 0real,
        slack > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps - slack >= bernoulli_weighted_sum(p_k, e),
        slack * slack_product(numer_x, denom_x, ubig_view(&k), depth) >= 1real,
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
    decreases depth,
{
    let ghost x = numer_x as real / denom_x as real;

    // Derive p_k ∈ [0, 1] from the formula connection to Taylor partial sums
    proof {
        assert(x > 0real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real >= 1real, denom_x as real >= 1real;
        assert(x <= 1real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real <= denom_x as real, denom_x as real >= 1real;
        lemma_exp1_p_formula_range(x, ubig_view(&k));
    }

    // Base case: depth == 0 is unreachable.
    proof {
        if depth == 0nat {
            assert(bernoulli_weighted_sum(p_k, e) >= 0real) by(nonlinear_arith)
                requires 0real <= exp1_p_formula(x, ubig_view(&k)) <= 1real,
                    p_k == exp1_p_formula(x, ubig_view(&k)),
                    e(true) >= 0real, e(false) >= 0real;
            ec_contradict(&input_credit);
        }
    }

    let ghost kn = ubig_view(&k);
    let k_denom = ubig_mul_u64(&k, denom_x);  // k · denom_x (denominator for Bernoulli flip)
    let ghost kdn = ubig_view(&k_denom);

    let ghost amp = exp1_amp(numer_x, denom_x, kn);       // k/x = amplification factor
    let ghost new_eps = exp1_new_eps(numer_x, denom_x, kn, eps, e);  // credit after heads
    let ghost flip_e = exp1_flip_e(e, kn, new_eps);        // credit alloc for the flip
    let ghost p_next = exp1_next_p(numer_x, denom_x, kn, p_k);      // p_{k+1}

    proof {
        // Bernoulli flip setup
        assert(kdn == kn * denom_x as nat);
        lemma_exp1_flip_average(numer_x, denom_x, kn, eps, e);
        assert(numer_x as real / (kdn as real)
            == numer_x as real / (kn as real * denom_x as real)) by(nonlinear_arith)
            requires kdn == kn * denom_x as nat, kn >= 1, denom_x > 0u64;
        assert(numer_x as nat <= kdn) by(nonlinear_arith)
            requires numer_x <= denom_x, kn >= 1, kdn == kn * denom_x as nat;
        assert(kdn > 0) by(nonlinear_arith)
            requires kn >= 1, denom_x > 0u64, kdn == kn * denom_x as nat;

        // Shift distribution bound through the recursion step
        lemma_exp1_next_p_recursion(numer_x, denom_x, kn, p_k);
        lemma_exp1_shift_bound(numer_x, denom_x, kn, eps, slack, e, p_k, p_next);

        // p_next ∈ [0,1] via Taylor partial sum connection
        lemma_exp1_p_formula_step(numer_x, denom_x, kn, x);
        lemma_exp1_p_formula_range(x, kn + 1);
        assert(bernoulli_weighted_sum(p_next, e) >= 0real) by(nonlinear_arith)
            requires 0real <= exp1_p_formula(x, kn + 1) <= 1real,
                p_next == exp1_p_formula(x, kn + 1),
                e(true) >= 0real, e(false) >= 0real;
        assert(amp >= 1real) by(nonlinear_arith)
            requires amp == kn as real * denom_x as real / numer_x as real,
                numer_x > 0u64, denom_x > 0u64, numer_x <= denom_x, kn >= 1;
        assert(new_eps >= 0real) by(nonlinear_arith)
            requires new_eps - amp * slack >= bernoulli_weighted_sum(p_next, e),
                bernoulli_weighted_sum(p_next, e) >= 0real,
                amp >= 1real, slack > 0real;
    }

    // Flip Bernoulli(numer_x / k_denom) = Bernoulli(x/k)
    let numer_ubig = ubig_from_u64(numer_x);
    let (heads, Tracked(out_credit)) = sample_bernoulli_rational(
        &numer_ubig,
        &k_denom,
        Ghost(flip_e),
        Tracked(input_credit),
        Ghost(eps),
    );

    let is_odd = ubig_is_odd(&k);

    if !heads {
        // Tails: return (k is odd). Credit is flip_e(false) = e(k%2==1) = e(is_odd).
        (is_odd, Tracked(out_credit))
    } else {
        // Heads: continue to step k+1 with amplified credit and slack.
        let ghost new_slack = amp * slack;
        let k_next = ubig_succ(k);

        proof {
            assert(new_slack > 0real) by(nonlinear_arith)
                requires new_slack == amp * slack, amp >= 1real, slack > 0real;
            assert(new_eps > 0real) by(nonlinear_arith)
                requires new_eps - new_slack >= bernoulli_weighted_sum(p_next, e),
                    bernoulli_weighted_sum(p_next, e) >= 0real, new_slack > 0real;
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

// ============================================================================
// Unbounded wrapper
// ============================================================================

/// Sample from Bernoulli(exp(-x)) where x = numer_x/denom_x ∈ (0, 1].
///
/// This is the public entry point. It wraps bounded_bernoulli_exp1 by
/// manufacturing the initial slack and depth needed for termination.
///
/// The key trick: thin_air() gives us an infinitesimal slack > 0. By the
/// Archimedean property, there exists depth d such that slack · 2^d >= 1.
/// Since slack_product(1, d+1) >= 2^d (from lemma_slack_product_k1_bound),
/// we get slack · slack_product >= 1, satisfying bounded_bernoulli_exp1's
/// termination precondition.
///
/// The initial conditional probability is p_1 = exp(-x) ∈ (0, 1].
pub fn sample_bernoulli_exp1(
    numer_x: u64,
    denom_x: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (bool, Tracked<ErrorCreditResource>))
    requires
        numer_x > 0,
        denom_x > 0,
        numer_x <= denom_x,
        e(true) >= 0real,
        e(false) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(exp(-(numer_x as real / denom_x as real)), e),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
{
    let ghost x = numer_x as real / denom_x as real;
    let ghost p1 = exp(-x);  // initial conditional probability

    proof {
        assert(x > 0real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real >= 1real, denom_x as real >= 1real;
        assert(x <= 1real) by(nonlinear_arith)
            requires x == numer_x as real / denom_x as real,
                numer_x as real <= denom_x as real, denom_x as real >= 1real;
        axiom_exp_neg_range(x);  // 0 < exp(-x) <= 1
        // Establish p1 == exp1_p_formula(x, 1) for bounded_bernoulli_exp1's precondition
        lemma_exp1_p_formula_base(x);
    }

    let Tracked(slack_credit) = thin_air();
    let ghost slack: real;
    let ghost depth: nat;
    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        // Archimedean: exists d such that slack · 2^d >= 1
        archimedean_exp_growth(slack, 2real);
        let d0: nat = choose |k: nat| slack * pow(2real, k) >= 1real;
        depth = d0 + 1;
        lemma_slack_product_k1_bound(numer_x, denom_x, depth);
        assert(slack * slack_product(numer_x, denom_x, 1nat, depth) >= 1real)
            by(nonlinear_arith)
            requires slack * pow(2real, d0) >= 1real,
                slack_product(numer_x, denom_x, 1nat, depth) >= pow(2real, d0),
                slack > 0real;
    }

    let ghost total_eps = eps + slack;
    let tracked combined: ErrorCreditResource;
    proof { combined = ec_combine(input_credit, slack_credit, eps, slack); }

    let k_init = ubig_from_u64(1u64);

    bounded_bernoulli_exp1(
        numer_x, denom_x,
        Ghost(e), Tracked(combined),
        k_init,
        Ghost(depth),
        Ghost(total_eps), Ghost(slack), Ghost(p1),
    )
}

} // verus!
