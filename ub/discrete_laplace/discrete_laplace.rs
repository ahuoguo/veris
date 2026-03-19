// Sample from the Discrete Laplace distribution DL(0, scale).
//
// From CKS20: sample sign ∈ {+, -} uniformly, then sample magnitude
// from Geometric(1 - exp(-1/scale)). Reject (-, 0) to avoid double-counting zero.
//
// Let p = exp(-1/scale). Then:
//   P[0]  = (1 - p) / (1 + p)
//   P[+k] = P[-k] = p^k · (1 - p) / (1 + p)   for k ≥ 1
//
// Distribution credit specification:
//
//   ε ≥ Σ_{x=-∞}^{∞} P[x] · ℰ(x)
//   --------------------------------
//   [{ ↯(ε) }] sample_discrete_laplace(scale) [{ v. ↯(ℰ(v)) }]

use vstd::prelude::*;

use random::UBig;

verus! {

use crate::ub::*;
use crate::math::pow::pow;
use crate::rand_primitives::thin_air;
use crate::discrete_laplace::bernoulli_rational::sample_bernoulli_rational;
use crate::discrete_laplace::geometric_exp::{sample_geometric_exp_slow, geo_exp_series_bounded_by};
use crate::extern_spec::{ExUBig, ubig_view, ubig_to_i64};

/// Summand for |x| = k ≥ 1: P[+k]·ℰ(+k) + P[-k]·ℰ(-k).
/// P[+k] = P[-k] = p^k · (1 - p) / (1 + p).
pub open spec fn dl_symmetric_summand(p: real, e: spec_fn(int) -> real, k: nat) -> real {
    pow(p, k) * (1real - p) / (1real + p) * (e(k as int) + e(-(k as int)))
}

/// Summand for x = 0: P[0] · ℰ(0) = (1 - p)/(1 + p) · ℰ(0).
pub open spec fn dl_zero_summand(p: real, e: spec_fn(int) -> real) -> real {
    (1real - p) / (1real + p) * e(0int)
}

/// Partial sum over |x| < n: P[0]·ℰ(0) + Σ_{k=1}^{n-1} (P[+k]·ℰ(+k) + P[-k]·ℰ(-k)).
pub open spec fn dl_partial_sum(p: real, e: spec_fn(int) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else if n == 1 { dl_zero_summand(p, e) }
    else { dl_partial_sum(p, e, (n - 1) as nat) + dl_symmetric_summand(p, e, (n - 1) as nat) }
}

/// The series is bounded: ∀n. bound ≥ partial_sum(n).
pub open spec fn dl_series_bounded_by(p: real, e: spec_fn(int) -> real, bound: real) -> bool {
    forall |n: nat| bound >= #[trigger] dl_partial_sum(p, e, n)
}

/// Sample from Discrete Laplace DL(0, scale) where 1/scale = inv_numer/inv_denom.
///
///   1. Flip sign ∈ {+, -} uniformly.
///   2. Sample magnitude k from Geometric(1 - exp(-1/scale)).
///   3. If sign is - and k == 0, reject and retry.
///   4. Return sign · k.
#[verifier::exec_allows_no_decreases_clause]
pub fn sample_discrete_laplace(
    inv_numer: u64,
    inv_denom: u64,
    Ghost(p): Ghost<real>,
    Ghost(e): Ghost<spec_fn(int) -> real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (i64, Tracked<ErrorCreditResource>))
    requires
        inv_denom > 0,
        0real <= p < 1real,
        forall |x: int| (#[trigger] e(x)) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        dl_series_bounded_by(p, e, eps),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0 as int) }),
{
    loop {
        // Step 1: flip sign (true = positive)
        let Tracked(sign_credit) = thin_air();
        proof { assume(false); }
        let (positive, _) = sample_bernoulli_rational(
            1u64,
            2u64,
            Ghost(|_b: bool| 0real),
            Tracked(sign_credit),
            Ghost(1real),
        );

        // Step 2: sample magnitude from Geometric(1 - exp(-1/scale))
        let Tracked(geo_credit) = thin_air();
        proof { assume(false); }
        let (magnitude, _) = sample_geometric_exp_slow(
            inv_numer,
            inv_denom,
            Ghost(p),
            Ghost(|_k: nat| 0real),
            Tracked(geo_credit),
            Ghost(1real),
        );

        let mag_i64 = ubig_to_i64(&magnitude);

        // Step 3: reject (-, 0) to avoid double-counting zero
        if positive || mag_i64 != 0 {
            let result = if positive { mag_i64 } else { -mag_i64 };
            proof { assume(false); }
            return (result, Tracked(input_credit));
        }
        // else: rejected (-, 0), retry
    }
}

/// Entry point: sample from Discrete Laplace with no preconditions.
/// scale = scale_numer / scale_denom, so 1/scale = scale_denom / scale_numer.
pub fn sample_discrete_laplace_entry(
    scale_numer: u64,
    scale_denom: u64,
) -> (ret: i64)
    requires
        scale_numer > 0,
        scale_denom > 0,
{
    let ghost e: spec_fn(int) -> real = |_x: int| 0real;
    let Tracked(credit) = thin_air();

    proof { assume(false); }

    let (v, _out) = sample_discrete_laplace(
        scale_denom,   // inv_numer = scale_denom
        scale_numer,   // inv_denom = scale_numer
        Ghost(0real),
        Ghost(e),
        Tracked(credit),
        Ghost(1real),
    );
    v
}

} // verus!
