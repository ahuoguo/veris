// Axiomatization of the exponential function exp(x) = e^x.
//
// We define exp as an uninterpreted function and axiomatize the properties
// needed for the CKS20 discrete Laplace sampler proofs:
//
//   1. exp(0) = 1
//   2. exp(-x) ∈ [0, 1] for x ≥ 0
//   3. exp(-(a+b)) = exp(-a) · exp(-b)  (multiplicativity)
//   4. Alternating series bounds on partial sums of exp(-x) = Σ (-x)^k/k!.

use vstd::prelude::*;

verus! {

use crate::math::pow::pow;
use crate::math::series::partial_sum;

/// The exponential function exp(x) = e^x, axiomatized as an uninterpreted function.
pub uninterp spec fn exp(x: real) -> real;

// ============================================================================
// Core axioms
// ============================================================================

// TODO: consider using the axiom keyword
/// exp(0) = 1.
#[verifier::external_body]
pub proof fn axiom_exp_zero()
    ensures exp(0real) == 1real,
{}

/// exp(-x) ∈ (0, 1] for x ≥ 0.
#[verifier::external_body]
pub proof fn axiom_exp_neg_range(x: real)
    requires x >= 0real,
    ensures
        0real < exp(-x),
        exp(-x) <= 1real,
{}

/// exp(-x) < 1 for x > 0.
#[verifier::external_body]
pub proof fn axiom_exp_neg_strict(x: real)
    requires x > 0real,
    ensures exp(-x) < 1real,
{}

/// Multiplicativity: exp(-(a + b)) = exp(-a) · exp(-b).
#[verifier::external_body]
pub proof fn axiom_exp_add(a: real, b: real)
    requires a >= 0real, b >= 0real,
    ensures exp(-(a + b)) == exp(-a) * exp(-b),
{}

// ============================================================================
// Taylor series for exp(-x)
//
// exp(-x) = Σ_{k=0}^∞ (-x)^k / k! = 1 - x + x²/2! - x³/3! + ...
//
// For x ∈ (0, 1], the terms alternate in sign and decrease in absolute
// value, so the alternating series estimation theorem gives: partial sums
// bracket exp(-x) and lie in [0, 1].
// ============================================================================

/// Factorial: n! = 1 · 2 · ... · n.
pub open spec fn factorial(n: nat) -> real
    decreases n,
{
    if n == 0 { 1real } else { n as real * factorial((n - 1) as nat) }
}

/// k-th term of the Taylor series for exp(-x): (-x)^k / k!
pub open spec fn exp_taylor_term(x: real, k: nat) -> real {
    pow(-x, k) / factorial(k)
}

/// The Taylor term sequence as a named spec_fn (avoids lambdas in triggers).
pub open spec fn exp_taylor_seq(x: real) -> spec_fn(nat) -> real {
    |k: nat| exp_taylor_term(x, k)
}

// TODO: formalize this in lean?
/// Alternating series bounds for the partial sums of exp(-x).
///
/// For x ∈ (0, 1] and n ≥ 1 terms, the partial sum T_n = Σ_{k=0}^{n-1} (-x)^k/k!
/// satisfies:
///   - T_n ∈ [0, 1]
///   - n even (even number of terms): T_n ≤ exp(-x)  (underestimate)
///   - n odd (odd number of terms):   exp(-x) ≤ T_n  (overestimate)
///
/// Proof: alternating series estimation theorem applied to exp(-x).
///
/// For x ∈ (0, 1], the terms (-x)^k/k! alternate in sign and decrease in
/// absolute value (since x^{k+1}/(k+1)! = (x/(k+1)) · x^k/k! ≤ x^k/k!).
/// By the alternating series estimation theorem, the remainder after n terms
///   R_n = exp(-x) - T_n = (-x)^n/n! + (-x)^{n+1}/(n+1)! + ...
/// has the same sign as its leading term (-x)^n/n! = (-1)^n · x^n/n!:
///   n even ⟹ R_n ≥ 0 ⟹ T_n ≤ exp(-x)
///   n odd  ⟹ R_n ≤ 0 ⟹ exp(-x) ≤ T_n
///
/// T_n ∈ [0, 1] follows from the bounding and exp(-x) ∈ (0, 1]:
///   n even: 0 ≤ T_n ≤ exp(-x) ≤ 1.
///   n odd:  0 < exp(-x) ≤ T_n ≤ T_1 = 1 (odd partial sums decrease toward exp(-x)).
///
/// Related mathlib4 lemma (gives error magnitude but not sign):
///   `Real.exp_bound`: |x| ≤ 1 ⟹ |exp(x) - Σ_{m<n} x^m/m!| ≤ |x|^n·(n+1)/(n!·n)
///   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Exponential.html#Real.exp_bound
#[verifier::external_body]
pub proof fn axiom_exp_taylor_bounds(x: real, n: nat)
    requires 0real < x <= 1real, n >= 1,
    ensures
        0real <= partial_sum(exp_taylor_seq(x), n),
        partial_sum(exp_taylor_seq(x), n) <= 1real,
        n % 2 == 0 ==> partial_sum(exp_taylor_seq(x), n) <= exp(-x),
        n % 2 == 1 ==> exp(-x) <= partial_sum(exp_taylor_seq(x), n),
{}

} // verus!
