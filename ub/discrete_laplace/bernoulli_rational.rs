// Sample from Bernoulli(p) for rational p = numer/denom.
//
// Implemented via: sample u ~ Uniform([0, denom)), return (numer > u).
// This gives P[true] = numer/denom = p exactly.
//
// Distribution credit specification:
//
//   ε ≥ p · ℰ(true) + (1 - p) · ℰ(false)
//   ----------------------------------------
//   [{ ↯(ε) }] sample_bernoulli_rational(numer, denom) [{ v. ↯(ℰ(v)) }]
//

// See opendp correspondence in `sample_bernoulli_rational` in opendp/rust/src/traits/samplers/bernoulli/mod.rs.
// Note: we don't do the checking for denom and numer as they are stated in the preconditions,
// we also directly take in two u64 instead of RBig

use vstd::prelude::*;

verus! {

use crate::ub::*;
use crate::rand_primitives::{rand_u64, average, sum_credit};

/// Weighted sum for Bernoulli(p): p · ℰ(true) + (1 - p) · ℰ(false).
pub open spec fn bernoulli_weighted_sum(
    prob: real,
    e: spec_fn(bool) -> real,
) -> real {
    prob * e(true) + (1real - prob) * e(false)
}

/// Credit allocation for the uniform sampler underlying Bernoulli(numer/denom):
///   outcome i < numer  → e(true)   (accepted: return true)
///   outcome i ≥ numer  → e(false)  (rejected: return false)
pub open spec fn bernoulli_credit_alloc(
    numer: u64,
    e: spec_fn(bool) -> real,
) -> spec_fn(real) -> real {
    |i: real| if i < numer as real { e(true) } else { e(false) }
}

/// Σ_{i<n} alloc(i) = numer·ℰ(true) + (n-numer)·ℰ(false)  when n ≥ numer,
///                  = n·ℰ(true)                           when n ≤ numer.
proof fn lemma_sum_bernoulli(numer: u64, e: spec_fn(bool) -> real, n: nat)
    ensures
        n <= numer as nat ==>
            sum_credit(bernoulli_credit_alloc(numer, e), n) == n as real * e(true),
        n >= numer as nat ==>
            sum_credit(bernoulli_credit_alloc(numer, e), n)
                == numer as real * e(true) + (n - numer as nat) as real * e(false),
    decreases n,
{
    let alloc = bernoulli_credit_alloc(numer, e);
    if n == 0 {
        assert(0real == 0nat as real * e(true)) by(nonlinear_arith);
        assert(0real == 0nat as real * e(true) + 0nat as real * e(false)) by(nonlinear_arith);
    } else {
        lemma_sum_bernoulli(numer, e, (n - 1) as nat);
        let k = (n - 1) as nat;
        assert(sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k as real));
        if n <= numer as nat {
            assert(sum_credit(alloc, n) == n as real * e(true))
                by(nonlinear_arith)
                requires
                    sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k as real),
                    sum_credit(alloc, k) == k as real * e(true),
                    alloc(k as real) == e(true),
                    n == k + 1;
        } else if k >= numer as nat {
            assert(sum_credit(alloc, n) ==
                numer as real * e(true) + (n - numer as nat) as real * e(false))
                by(nonlinear_arith)
                requires
                    sum_credit(alloc, n) == sum_credit(alloc, k) + alloc(k as real),
                    sum_credit(alloc, k) == numer as real * e(true)
                        + (k - numer as nat) as real * e(false),
                    alloc(k as real) == e(false),
                    n == k + 1,
                    k >= numer as nat;
        }
    }
}

proof fn lemma_bernoulli_average(numer: u64, denom: u64, e: spec_fn(bool) -> real)
    requires
        denom > 0,
        numer <= denom,
        e(true) >= 0real,
        e(false) >= 0real,
    ensures
        average(denom, bernoulli_credit_alloc(numer, e))
            == bernoulli_weighted_sum(numer as real / denom as real, e),
{
    lemma_sum_bernoulli(numer, e, denom as nat);
    let sum = sum_credit(bernoulli_credit_alloc(numer, e), denom as nat);
    assert(average(denom, bernoulli_credit_alloc(numer, e))
        == bernoulli_weighted_sum(numer as real / denom as real, e))
        by(nonlinear_arith)
        requires
            sum == numer as real * e(true)
                + (denom as nat - numer as nat) as real * e(false),
            average(denom, bernoulli_credit_alloc(numer, e)) == sum / denom as real,
            denom > 0u64,
            numer <= denom;
}

/// Sample from Bernoulli(numer/denom) with distribution credit.
pub fn sample_bernoulli_rational(
    numer: u64,
    denom: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (bool, Tracked<ErrorCreditResource>))
    requires
        denom > 0,
        numer <= denom,
        e(true) >= 0real,
        e(false) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(numer as real / denom as real, e),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
{
    let ghost alloc = bernoulli_credit_alloc(numer, e);

    proof {
        lemma_bernoulli_average(numer, denom, e);
    }

    let (val, Tracked(outcome_credit)) = rand_u64(denom, Tracked(input_credit), Ghost(alloc));
    (val < numer, Tracked(outcome_credit))
}

} // verus!
