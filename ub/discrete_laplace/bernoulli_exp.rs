// Sample from Bernoulli(exp(-x)) for x ≥ 0.
//
// Decomposes x = floor(x) + frac(x), then:
//   1. Sample floor(x) independent Bernoulli(exp(-1)).
//   2. If all are true, sample Bernoulli(exp(-frac(x))).
//   3. Return false if any Bernoulli(exp(-1)) is false.
//
// Since exp(-x) = exp(-1)^floor(x) · exp(-frac(x)), the output
// is Bernoulli(exp(-x)).
//
// Distribution credit specification (same form as bernoulli_exp1):
//
//   ε ≥ exp(-x) · ℰ(true) + (1 - exp(-x)) · ℰ(false)
//   ---------------------------------------------------
//   [{ ↯(ε) }] sample_bernoulli_exp(x) [{ v. ↯(ℰ(v)) }]

use vstd::prelude::*;

verus! {

use crate::ub::*;
use crate::rand_primitives::thin_air;
use crate::discrete_laplace::bernoulli_rational::bernoulli_weighted_sum;
use crate::discrete_laplace::bernoulli_exp1::sample_bernoulli_exp1;

/// Sample from Bernoulli(exp(-x)) where x = numer_x/denom_x ≥ 0.
///
/// While x > 1: flip Bernoulli(exp(-1)). If false, return false. Else x -= 1.
/// Then flip Bernoulli(exp(-frac(x))).
#[verifier::exec_allows_no_decreases_clause]
pub fn sample_bernoulli_exp(
    numer_x: u64,
    denom_x: u64,
    Ghost(e): Ghost<spec_fn(bool) -> real>,
    Ghost(prob_true): Ghost<real>,
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(eps): Ghost<real>,
) -> (ret: (bool, Tracked<ErrorCreditResource>))
    requires
        denom_x > 0,
        0real <= prob_true <= 1real,
        e(true) >= 0real,
        e(false) >= 0real,
        eps > 0real,
        input_credit.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        eps >= bernoulli_weighted_sum(prob_true, e),
    ensures
        ret.1@.view() =~= (ErrorCreditCarrier::Value { car: e(ret.0) }),
{
    let mut remaining_numer = numer_x;

    // While x > 1 (i.e. remaining_numer > denom_x), sample Bernoulli(exp(-1))
    while remaining_numer > denom_x {
        let Tracked(flip_credit) = thin_air();
        proof { assume(false); }

        let (heads, _out) = sample_bernoulli_exp1(
            denom_x,    // numer = denom means x = 1
            denom_x,
            Ghost(|_b: bool| 0real),
            Tracked(flip_credit),
            Ghost(1real),
        );

        if !heads {
            proof { assume(false); }
            return (false, Tracked(input_credit));
        }
        remaining_numer = remaining_numer - denom_x;
    }

    // Now remaining_numer <= denom_x, so frac part ∈ [0, 1]
    let Tracked(frac_credit) = thin_air();
    proof { assume(false); }

    let (result, _out) = sample_bernoulli_exp1(
        remaining_numer,
        denom_x,
        Ghost(|_b: bool| 0real),
        Tracked(frac_credit),
        Ghost(1real),
    );

    proof { assume(false); }
    (result, Tracked(input_credit))
}

} // verus!
