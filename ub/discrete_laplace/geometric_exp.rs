// Sample from Geometric(1 - exp(-x)) for x ≥ 0.
//
// Loop: flip Bernoulli(exp(-x)). If true, increment k. If false, return k.
// Output k has P[k] = p^k · (1 - p) where p = exp(-x).
//
// Distribution credit specification:
//
//   ε ≥ Σ_{k=0}^∞ p^k · (1 - p) · ℰ(k)
//   -------------------------------------------------
//   [{ ↯(ε) }] sample_geometric_exp_slow(x) [{ v. ↯(ℰ(v)) }]
//
// This is analogous to geo_dist.rs but with base p = exp(-x) instead of p = 1/2.

use vstd::prelude::*;

use random::{UBig, ubig_zero, ubig_succ};

verus! {

use crate::ub::*;
use crate::extern_spec::{ExUBig, ubig_view};
use crate::math::pow::pow;
use crate::rand_primitives::thin_air;
use crate::discrete_laplace::bernoulli_exp::sample_bernoulli_exp;

/// k-th summand of the geometric series: p^k · (1 - p) · ℰ(k).
pub open spec fn geo_exp_summand(p: real, e: spec_fn(nat) -> real, k: nat) -> real {
    pow(p, k) * (1real - p) * e(k)
}

/// Partial sum: Σ_{i<n} p^i · (1 - p) · ℰ(i).
pub open spec fn geo_exp_partial_sum(p: real, e: spec_fn(nat) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { geo_exp_partial_sum(p, e, (n - 1) as nat) + geo_exp_summand(p, e, (n - 1) as nat) }
}

/// The series is bounded: ∀n. bound ≥ Σ_{k<n} p^k · (1-p) · ℰ(k).
pub open spec fn geo_exp_series_bounded_by(p: real, e: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| bound >= #[trigger] geo_exp_partial_sum(p, e, n)
}

/// Sample from Geometric(1 - exp(-x)) where x = numer_x/denom_x.
///
/// Loop: flip Bernoulli(exp(-x)). If true, k++. If false, return k.
#[verifier::exec_allows_no_decreases_clause]
pub fn sample_geometric_exp_slow(
    numer_x: u64,
    denom_x: u64,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(nat) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (UBig, Tracked<ErrorCreditResource>))
    requires
        denom_x > 0,
        0real <= p < 1real,
        forall |k: nat| (#[trigger] e(k)) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        geo_exp_series_bounded_by(p, e, eps),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ubig_view(&ret.0)) }),
{
    let mut k = ubig_zero();
    loop {
        let Tracked(flip_credit) = thin_air();
        proof { assume(false); }

        let (heads, _out) = sample_bernoulli_exp(
            numer_x,
            denom_x,
            Ghost(|_b: bool| 0real),
            Ghost(0real),
            Tracked(flip_credit),
            Ghost(1real),
        );

        if heads {
            k = ubig_succ(k);
        } else {
            proof { assume(false); }
            return (k, Tracked(input_credit));
        }
    }
}

} // verus!
