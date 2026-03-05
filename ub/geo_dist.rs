// Geometric Distribution with BigNums and Distribution Credit
//
// This extends geo.rs with:
// 1. BigNum for unbounded output (geo.rs uses u64 with wrapping_add)
// 2. A distribution credit via the expectation rule:
// https://github.com/logsem/clutch/blob/cpp26-distributions/theories/eris/lib/sampling/geometric/implementation.v#L109-L116
//
//   ε ≥ Σ_{i=0}^∞ (1/2)^i * ℰ(i)
//   ------------------------------------
//   [{ ↯(ε) }] geo() [{ v. ↯(ℰ(v)) }]
//
// After geo() returns v, we own error credit ℰ(v).
//
// The input credit ε is split into two parts:
// - Distribution credit (ε - slack): covers the geometric series Σ (1/2)^i * ℰ(i)
// - Slack credit: reserved for termination, doubles at each recursive step
//
// This separation is necessary because the distribution part gets partially
// consumed by ℰ(0) at each level, so it can't serve double duty for termination.
//
// Representing infinite sums in Verus:
// We express "ε ≥ Σ_{i=0}^∞ (1/2)^i * ℰ(i)" as a universal bound over all
// finite partial sums: ∀ n. ε ≥ Σ_{i=0}^{n-1} (1/2)^i * ℰ(i).

// This diverges from clutch's usage of Coquelicot
// https://logsem.github.io/clutch/clutch.prob.countable_sum.html
// in SeriesC, since rocq is total, you need to pick a value for every entry n, but you still
// want some prove some property
// normally you want to define a / 0 = 0, to have this property without side conditoins: a1/b + a2/b = (a1 + a2) / b

use vstd::prelude::*;

verus! {

use crate::ub::*;
use crate::rand_primitives::{rand_1_u64, thin_air};
use crate::pure_fact::{pow, pure_fact_with_base};
use crate::math::*;

// ============================================================================
// BigNum: external wrapper for unbounded naturals
// ============================================================================

// TODO: replace the runtime representation with an actual bignum library
pub struct BigNum {
    val: u64,
}

impl BigNum {
    pub uninterp spec fn view(&self) -> nat;
}

// TODO: use assume_specification and use the actual bignum library
#[verifier::external_body]
pub fn bignum_zero() -> (ret: BigNum)
    ensures ret.view() == 0nat,
{ BigNum { val: 0 } }

#[verifier::external_body]
pub fn bignum_succ(n: BigNum) -> (ret: BigNum)
    ensures ret.view() == n.view() + 1,
{ BigNum { val: n.val.wrapping_add(1) } }

#[verifier::external_body]
pub fn bignum_add(a: BigNum, b: BigNum) -> (ret: BigNum)
    ensures ret.view() == a.view() + b.view(),
{ BigNum { val: a.val.wrapping_add(b.val) } }

// ============================================================================
// Geometric distribution precondition and credit allocation
// ============================================================================

/// Trigger helper for the two-variable existential in bounded_geo_dist precondition
pub open spec fn geo_dist_precond(
    e: spec_fn(nat) -> real,
    credit: ErrorCreditCarrier,
    depth: nat,
    eps: real,
    slack: real,
) -> bool {
    &&& eps > 0real
    &&& slack > 0real
    &&& credit =~= (ErrorCreditCarrier::Value { car: eps })
    &&& geo_series_bounded_by(e, eps - slack)
    &&& slack * pow(2real, depth) >= 1real
}

// ============================================================================
// Credit allocation for the distribution-aware coin flip
// ============================================================================

/// Credit allocation for geo_dist coin flip:
/// - Outcome 0 (stop):     ℰ(0)            — returned as the output credit
/// - Outcome 1 (continue): 2*ε - ℰ(0)      — feeds the recursive call
///
/// Average = (ℰ(0) + 2ε - ℰ(0)) / 2 = ε, so ε >= average always holds.
spec fn geo_dist_credit_alloc(e: spec_fn(nat) -> real, eps: real) -> spec_fn(real) -> real {
    |outcome: real|
        if outcome == 0real {
            e(0nat)
        } else {
            2real * eps - e(0nat)
        }
}

// ============================================================================
// Specification: bounded geometric distribution sampler
//
//   ε ≥ Σ_{i=0}^∞ (1/2)^i * ℰ(i)
//   ------------------------------------
//   [{ ↯(ε) }] geo() [{ v. ↯(ℰ(v)) }]
//
// For any ℰ with non-negative values, if ε covers the geometric series
// with slack for termination, then after geo() returns v, we own ↯(ℰ(v)).
// ============================================================================
///
/// Bounded geometric distribution sampler with distribution credit.
///
///   ε ≥ Σ_{i=0}^∞ (1/2)^i * ℰ(i)
///   ------------------------------------
///   [{ ↯(ε) }] geo() [{ v. ↯(ℰ(v)) }]
///
/// The precondition decomposes ε = (ε - slack) + slack:
/// - `ε - slack` bounds the geometric series: ∀n. ε - slack ≥ Σ_{i<n} (1/2)^i ℰ(i)
/// - `slack * 2^depth ≥ 1` ensures termination
///
/// Invariant through recursion (outcome 1, shift ℰ to ℰ' where ℰ'(i) = ℰ(i+1)):
/// - new_ε = 2ε - ℰ(0),  new_slack = 2·slack
/// - distribution: new_ε - new_slack = 2(ε - slack) - ℰ(0) ≥ series(ℰ')  ✓
/// - termination:  new_slack · 2^(depth-1) = slack · 2^depth ≥ 1            ✓
pub fn bounded_geo_dist(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(depth): Ghost<nat>,
    Ghost(eps): Ghost<real>,
    Ghost(slack): Ghost<real>,
) -> (ret: (BigNum, Tracked<ErrorCreditResource>))
    requires
        forall |i: nat| #[trigger] seq_at(e, i) >= 0real,
        eps > 0real,
        slack > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        geo_series_bounded_by(e, eps - slack),
        slack * pow(2real, depth) >= 1real,
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0.view()) }),
    decreases depth,
{
    proof {
        // Base case: depth == 0 ⟹ eps ≥ 1 ⟹ contradiction
        if depth == 0nat {
            assert(pow(2real, 0nat) == 1real);
            assert(partial_sum(geo_summands(e), 0nat) == 0real); // trigger series bound
            ec_contradict(&input_credit);
        }

        // Establish eps >= e(0) from geometric series bound at n=1
        assert(seq_at(e, 0nat) >= 0real);
        assert(pow(0.5real, 0nat) == 1real);
        assert(geo_summands(e)(0nat) == pow(0.5real, 0nat) * e(0nat));
        assert(partial_sum(geo_summands(e), 0nat) == 0real);
        assert(partial_sum(geo_summands(e), 1nat) ==
            partial_sum(geo_summands(e), 0nat) + geo_summands(e)(0nat));
        // Now: partial_sum(..., 1) = 0 + 1*e(0) = e(0)
        // And: eps - slack >= partial_sum(..., 1) from geo_series_bounded_by
        assert(eps - slack >= e(0nat)) by(nonlinear_arith)
            requires
                eps - slack >= partial_sum(geo_summands(e), 1nat),
                partial_sum(geo_summands(e), 1nat) ==
                    partial_sum(geo_summands(e), 0nat) + geo_summands(e)(0nat),
                partial_sum(geo_summands(e), 0nat) == 0real,
                geo_summands(e)(0nat) == pow(0.5real, 0nat) * e(0nat),
                pow(0.5real, 0nat) == 1real;
        lemma_geo_dist_average(e, eps);
    }

    let ghost credit_alloc = geo_dist_credit_alloc(e, eps);

    let (val, Tracked(outcome_credit)) = rand_1_u64(
        Tracked(input_credit),
        Ghost(credit_alloc),
    );

    if val == 0 {
        let ret = bignum_zero();
        (ret, Tracked(outcome_credit))
    } else {
        let ghost new_eps = 2real * eps - e(0nat);
        let ghost new_slack = 2real * slack;

        proof {
            // Non-negativity of shift_e(e)
            assert forall |i: nat| #[trigger] seq_at(shift_e(e), i) >= 0real by {
                assert(seq_at(e, i + 1) >= 0real);
            };

            // Re-establish eps - slack >= e(0) in this branch
            assert(seq_at(e, 0nat) >= 0real);
            assert(pow(0.5real, 0nat) == 1real);
            assert(geo_summands(e)(0nat) == pow(0.5real, 0nat) * e(0nat));
            assert(partial_sum(geo_summands(e), 0nat) == 0real);
            assert(partial_sum(geo_summands(e), 1nat) ==
                partial_sum(geo_summands(e), 0nat) + geo_summands(e)(0nat));
            assert(eps - slack >= e(0nat)) by(nonlinear_arith)
                requires
                    eps - slack >= partial_sum(geo_summands(e), 1nat),
                    partial_sum(geo_summands(e), 1nat) ==
                        partial_sum(geo_summands(e), 0nat) + geo_summands(e)(0nat),
                    partial_sum(geo_summands(e), 0nat) == 0real,
                    geo_summands(e)(0nat) == pow(0.5real, 0nat) * e(0nat),
                    pow(0.5real, 0nat) == 1real;
            // new_eps > 0: from eps >= e(0) + slack and slack > 0
            assert(new_eps > 0real) by(nonlinear_arith)
                requires
                    new_eps == 2real * eps - e(0nat),
                    eps - slack >= e(0nat),
                    slack > 0real,
                    e(0nat) >= 0real;

            // Distribution bound for shift_e
            lemma_shift_bound(e, eps, slack);

            // Termination: new_slack * pow(2, depth-1) ≥ 1
            real_assoc_mult(slack, 2real, pow(2real, (depth - 1) as nat));
            assert(new_slack * pow(2real, (depth - 1) as nat) == slack * pow(2real, depth));
        }

        let (rest, output_credit) = bounded_geo_dist(
            Ghost(shift_e(e)),
            Tracked(outcome_credit),
            Ghost((depth - 1) as nat),
            Ghost(new_eps),
            Ghost(new_slack),
        );

        let result = bignum_succ(rest);
        (result, output_credit)
    }
}

/// Unbounded geometric distribution sampler with distribution credit.
///
///   ε ≥ Σ_{i=0}^∞ (1/2)^i * ℰ(i)
///   ------------------------------------
///   [{ ↯(ε) }] geo() [{ v. ↯(ℰ(v)) }]
///
/// Internally allocates a thin-air credit for termination; caller only provides
/// the distribution credit ε that bounds the geometric series.
pub fn unbounded_geo_dist(
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(dist_bound): Ghost<real>,
) -> (ret: (BigNum, Tracked<ErrorCreditResource>))
    requires
        forall |i: nat| #[trigger] seq_at(e, i) >= 0real,
        dist_bound >= 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: dist_bound }),
        geo_series_bounded_by(e, dist_bound),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0.view()) }),
{
    let Tracked(slack_credit) = thin_air();

    let ghost slack: real;
    let ghost depth: nat;

    proof {
        slack = choose |v: real| v > 0real &&
            (ErrorCreditCarrier::Value { car: v } =~= slack_credit.view());
        pure_fact_with_base(slack, 2real);
        depth = choose |k: nat| slack * pow(2real, k) >= 1real;
    }

    let ghost eps = dist_bound + slack;
    let tracked combined: ErrorCreditResource;
    proof {
        combined = join_credits(input_credit, slack_credit, dist_bound, slack);
    }

    bounded_geo_dist(
        Ghost(e),
        Tracked(combined),
        Ghost(depth),
        Ghost(eps),
        Ghost(slack),
    )
}

/// Average of geo_dist_credit_alloc is exactly eps:
///   (ℰ(0) + (2ε - ℰ(0))) / 2 = ε
proof fn lemma_geo_dist_average(e: spec_fn(nat) -> real, eps: real)
    requires
        eps > 0real,
        eps >= e(0nat),
    ensures
        eps >= (geo_dist_credit_alloc(e, eps)(0real)
              + geo_dist_credit_alloc(e, eps)(1real)) / 2real,
{}

#[verifier::nonlinear]
proof fn real_assoc_mult(a: real, b: real, c: real)
    ensures a * (b * c) == (a * b) * c,
{}

} // verus!
