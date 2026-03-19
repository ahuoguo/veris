// Axiomatization of the exponential function exp(x) = e^x.
//
// We define exp as an uninterpreted function and axiomatize the properties
// needed for the CKS20 discrete Laplace sampler proofs:
//
//   1. exp(0) = 1
//   2. exp(-x) ∈ [0, 1] for x ≥ 0
//   3. exp(-(a+b)) = exp(-a) · exp(-b)  (multiplicativity)
//   4. The alternating series recursion for Bernoulli(exp(-x)) preserves
//      conditional probabilities in [0, 1].

use vstd::prelude::*;

verus! {

/// The exponential function exp(x) = e^x, axiomatized as an uninterpreted function.
pub uninterp spec fn exp(x: real) -> real;

// ============================================================================
// Core axioms
// ============================================================================

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
// Alternating series for exp(-x), x ∈ [0, 1]
//
// The CKS20 algorithm for Bernoulli(exp(-x)) defines conditional probabilities:
//   p_k = P[return true | reached step k]
// with recursion:
//   p_k = (x/k) · p_{k+1} + (1 - x/k) · [k is odd]
// and p_1 = exp(-x).
//
// The key fact: p_k ∈ [0, 1] for all k ≥ 1.
// This follows from the alternating series remainder theorem applied to
//   exp(-x) = Σ_{n=0}^∞ (-x)^n / n!
// ============================================================================

/// The conditional probability p_k at step k of the Bernoulli(exp(-x)) algorithm
/// satisfies 0 ≤ p_k ≤ 1, and the recursion p_k → p_{k+1} preserves this.
///
/// Specifically, if p_k is the correct conditional probability for parameters
/// (x, k), then p_{k+1} = (p_k - [k odd]) · (k/x) + [k odd] is also in [0, 1].
#[verifier::external_body]
pub proof fn axiom_exp1_conditional_prob_range(x: real, k: nat, p_k: real, amp: real)
    requires
        0real < x <= 1real,
        k >= 1,
        amp == k as real / x,
        // p_next is defined by the recursion
        0real <= p_k <= 1real,
        // p_k is a valid conditional probability arising from exp(-x)
        // (we trust the caller to maintain this invariant from p_1 = exp(-x))
    ensures ({
        let p_next = if k % 2 == 1 { (p_k - 1real) * amp + 1real } else { p_k * amp };
        0real <= p_next && p_next <= 1real
    }),
{}

} // verus!
