use vstd::calc_macro::*;
use vstd::pcm::*;
use vstd::prelude::*;

verus! {

use crate::ub::*;
use crate::pure_fact::pow;

/// Recursive sum of credit_alloc over [0, n)
/// credit_alloc(i) is the error credit allocated to outcome i
/// Defining this using `fold_left` was not that pleasant to work with
pub open spec fn sum_credit(credit_alloc: spec_fn(real) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { sum_credit(credit_alloc, (n - 1) as nat) + credit_alloc((n - 1) as real) }
}

/// Average of credit_alloc over [0, bound)
/// This is the expected error credit when sampling uniformly from [0, bound)
pub open spec fn average(bound: u64, credit_alloc: spec_fn(real) -> real) -> real {
    sum_credit(credit_alloc, bound as nat) / bound as real
}

//// Wrappers
#[verus::trusted]
#[verifier::external_body]
pub fn rand_u64(
    bound: u64,
    Tracked(e1): Tracked<ErrorCreditResource>,
    Ghost(e2): Ghost<spec_fn(real) -> real>,
) -> (ret: (
    // TODO: can't have return value like this: ((n, e2): (u64, Tracked<ErrorCreditResource>))
    u64,
    Tracked<ErrorCreditResource>,
))
    requires
      // ε₁ ≥ 𝔼(ℰ₂)
      bound > 0,  // bound is the finite support
      exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= e1.view()) && eps >= average(bound, e2),
    ensures
      // Result is in range [0, bound)
      ret.0 < bound,
      // owns ↯(ℰ₂(n))
      (ErrorCreditCarrier::Value { car: e2(ret.0 as real) }) =~= ret.1.view().view(),
{
    let val: u64 = random::rand_u64(bound);
    (val, Tracked::assume_new())
}

// REVIEW:
// In Eris, you can only invoke a thin air rule if your postcondition is a WP or is wrapped in some modality
// you can't not invoke thin air rule in any lemma (this might(?) be unsound)
#[verus::trusted]
#[verifier::external_body]
pub fn thin_air() -> (ret: Tracked<ErrorCreditResource>)
    ensures
        // owns ↯(ε) for ε > 0
        exists |eps: real| eps > 0.0 && (ErrorCreditCarrier::Value { car: eps } =~= ret.view().view()),
{
    Tracked::assume_new()
}

pub open spec fn flip_credit_alloc(x: real) -> real {
    if x == 1real {
        0real
    } else {
        1real
    }
}

/// A wrapper around `rand_u64(2)` for coin flip scenarios.
/// Simplifies the average calculation to (credit_alloc(0) + credit_alloc(1)) / 2.
pub fn rand_1_u64(
    Tracked(input_credit): Tracked<ErrorCreditResource>,
    Ghost(credit_alloc): Ghost<spec_fn(real) -> real>,
) -> (ret: (
    u64,
    Tracked<ErrorCreditResource>,
))
    requires
        exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= input_credit.view()) &&
            eps >= (credit_alloc(0real) + credit_alloc(1real)) / 2real,
    ensures
        ret.0 == 0 || ret.0 == 1,
        (ErrorCreditCarrier::Value { car: credit_alloc(ret.0 as real) }) =~= ret.1.view().view(),
{
    // Prove that average(2, credit_alloc) == (credit_alloc(0) + credit_alloc(1)) / 2
    // by unfolding sum_credit using asserts
    assert(average(2u64, credit_alloc) == (credit_alloc(0real) + credit_alloc(1real)) / 2real) by {
        // assert(sum_credit(credit_alloc, 2) == sum_credit(credit_alloc, 1) + credit_alloc(1real));
        assert(sum_credit(credit_alloc, 1) == sum_credit(credit_alloc, 0) + credit_alloc(0real)); // OBSERVE
        // assert(sum_credit(credit_alloc, 0) == 0real);
    };
    let (val, output_credit) = rand_u64(2u64, Tracked(input_credit), Ghost(credit_alloc));
    (val, output_credit)
}

pub fn flip(Tracked(input_credit): Tracked<ErrorCreditResource>) -> (ret: u64)
    requires
        (ErrorCreditCarrier::Value { car: 0.5real }) == input_credit.view(),
    ensures
        ret == 1,
{
    assert(flip_credit_alloc(0real) + flip_credit_alloc(1real) == 1real);
    let (val, Tracked(outcome_credit)) = rand_1_u64(Tracked(input_credit), Ghost(|x: real| flip_credit_alloc(x)));

    proof {
        if (val != 1) {
            ec_contradict(&outcome_credit);
        }
    }
    assert(val == 1);
    val
}

} // verus!
