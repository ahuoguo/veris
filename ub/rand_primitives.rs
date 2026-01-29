use vstd::calc_macro::*;
use vstd::pcm::*;
use vstd::prelude::*;

verus! {

use crate::ub::*;
use crate::pure_fact::{gt_1, pow};

pub open spec fn average(bound: u64, e2: spec_fn(real) -> real) -> real {
    let inputs: Seq<int> = Seq::new(bound as nat, |i: int| i);
    let nom = inputs.fold_left(0real, |acc: real, x| acc + e2(x as real));
    let denom = bound as real;
    nom / denom
}

//// Wrappers
#[verus::trusted]
#[verifier::external_body]
pub fn rand_u64(
    bound: u64,
    Tracked(e1): Tracked<ErrorCreditResource>,
    Ghost(e2): Ghost<spec_fn(real) -> real>,
) -> (ret: (
    u64,
    Tracked<ErrorCreditResource>,
))
// TODO: can't have return value like this: ((n, e2): (u64, Tracked<ErrorCreditResource>))
    requires
      // Σ ℰ2(i) / bound = ε1
      bound > 0,
    //   (ErrorCreditCarrier::Value { car: average(bound, e2) }) =~= e1.view(),
      exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= e1.view()) &&
          eps >= average(bound, e2),
    ensures
      // Result is in range [0, bound)
      ret.0 < bound,
      // owns ↯(ℰ2(n))
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

pub open spec fn flip_e2(x: real) -> real {
    if x == 1real {
        0real
    } else {
        1real
    }
}

// TODO: this is bad since this consumes the token, `.explode is better`...
pub proof fn ec_contradict(tracked e: ErrorCreditResource)
    requires
        exists |car: real| {
            &&& car >= 1real 
            &&& e.view() =~= (ErrorCreditCarrier::Value { car })
        }
    ensures
        false,
{
    let car = choose|v: real| e.view() == (ErrorCreditCarrier::Value { car: v });
    e.explode(car);
    e.valid();
    assert(!e.view().valid());
}

// a wrapper around `rand 1` will be very helpful for the rejection sampler example
// so you don't need to deal with `average`
pub fn rand_1_u64(
    Tracked(e1): Tracked<ErrorCreditResource>,
    Ghost(e2): Ghost<spec_fn(real) -> real>,
) -> (ret: (
    u64,
    Tracked<ErrorCreditResource>,
))
    requires
        // Specification: ℰ2(0) + ℰ2(1) = ε1 * 2
        exists |eps: real| (ErrorCreditCarrier::Value { car: eps } =~= e1.view()) &&
            eps >= (e2(0real) + e2(1real)) / 2real,
        // (ErrorCreditCarrier::Value { car: ((e2(0real) + e2(1real)) / 2real) }) =~= e1.view(),
    ensures
        // Result is either 0 or 1
        ret.0 == 0 || ret.0 == 1,
        (ErrorCreditCarrier::Value { car: e2(ret.0 as real) }) =~= ret.1.view().view(),
{
    // TODO: is there a more automatic way to unfold this fold_left?
    // if I have a fold_left that computes a sum in reals, what's the easiest way to prove its value?
    // Prove that average(2u64, e2) equals the precondition expression
    assert(Seq::new(2 as nat, |i: int| i) =~= seq![0int, 1int]);
    assert(average(2u64, e2) == (e2(0real) + e2(1real)) / 2real) by {
        calc! {
            (==)
            seq![0int, 1int].fold_left(0real, |acc: real, x| acc + e2(x as real)); {
                assert(seq![0int, 1int].drop_last() =~= seq![0int]);
            }
            seq![0int].fold_left(0real, |acc: real, x| acc + e2(x as real)) + e2(1int as real); {
                assert(seq![0int].drop_last() =~= seq![]);
            }
            (seq![].fold_left(0real, |acc: real, x: int| acc + e2(x as real)) + e2(0int as real)) + e2(1int as real);
        }
    };
    let (val, e2_tracked) = rand_u64(2u64, Tracked(e1), Ghost(e2));
    (val, e2_tracked)
}

pub fn flip(Tracked(e1): Tracked<ErrorCreditResource>) -> (ret: u64)
    requires
        (ErrorCreditCarrier::Value { car: 0.5real }) == e1.view(),
    ensures
        ret == 1,
{
    assert(flip_e2(0real) + flip_e2(1real) == 1real);
    let (val, Tracked(e2)) = rand_1_u64(Tracked(e1), Ghost(|x: real| flip_e2(x)));

    // TODO: some how you can't put `proof {...}` in `assert by`
    // and `assert by {...}` is not considered as a proof block
    proof {
        if (val != 1) {
            // owns ↯(ℰ(1)) -> contradiction
            ec_contradict(e2);
        }
    }
    assert(val == 1);
    val
}

pub fn geo() -> (ret: u64)
{
    let Tracked(a) = thin_air();
    // This is a super hacky (but official) way to depend on ghost values...
    let ghost mut hi;
    let ghost mut epsilon;

    // ∀ ε > 0, r >1, ∃ k, ε * r ^ k >= 1
    // the decreasing part is k
    proof {
        if a.view().value() =~= None { } // OBSERVE
    }
    assert(exists |v: real| a.view().value() == Some(v));
    proof {
        epsilon = choose|i: real| a.view().value() == Some(i);
        pure_fact(epsilon);
        assert(gt_1(2real)); // OBSERVE
        assert(exists |k : nat| epsilon * pow(2real, k) >= 1real);
        hi = choose|i: nat| epsilon * pow(2real, i) >= 1real;
        assert(epsilon * pow(2real, hi) >= 1real);
    }
    assert(epsilon * pow(2real, hi) >= 1real);
    geo_aux(Tracked(a), Ghost(hi)) // ε
}

pub fn geo_aux(Tracked(a): Tracked<ErrorCreditResource>, Ghost(k): Ghost<nat>) -> (ret: u64)
    requires
        exists |eps: real| {
            &&& eps > 0.0 
            &&& (ErrorCreditCarrier::Value { car: eps } =~= a.view())
            &&& eps * pow(2real, k) >= 1real
        }
    ensures
        ret >= 1,
    decreases
        k
{
    let ghost mut eps : real;
    let ghost mut eps1 : real;

    assert(exists |v: real| a.view().value() == Some(v));
    proof {
        eps = choose|i: real| a.view().value() == Some(i);
        if k == 0nat {
            assert(eps * pow(2real, k) >= 1real);
            assert(eps >= 1real);
            // ~~TODO: not sure how to make verus types happy~~ SOLVED!
            // I basically want to do a case split and use the resource correspondingly...
            // TODO: is there a better lemma to wrap around this?
            a.explode(eps);
            a.valid();
            assert(!a.view().valid());
            assert(false);
        }
        assert(k != 0nat);
    }
    let (val, Tracked(e2)) = rand_1_u64(Tracked(a), Ghost(|x: real| flip_eps(x, eps)));

    if val == 0 {
        1
    } else {
        assert(flip_eps(val as real, eps) == 2real * eps);
        proof{
            calc! {
                (==)
                (2real*eps) * pow(2real, (k - 1) as nat); {
                }
                (eps * 2real) * pow(2real, (k - 1) as nat); {
                    real_assoc_mult(eps, 2real, pow(2real, (k - 1) as nat));
                }
                eps * (2real * pow(2real, (k - 1) as nat)); {
                }
                eps * pow(2real, k);
            };
        }
        assert( (2real*eps) * pow(2real, (k - 1) as nat) >= 1real);
        let v = geo_aux(Tracked(e2), Ghost((k-1) as nat ));
        // TODO: will arithmetic overflow if `+1`, maybe we should not name this as geometric...
        // assume(false);
        v
    }
}

proof fn pure_fact(epsilon: real)
    requires
        epsilon > 0real,
    ensures
        forall |r: real| #[trigger]gt_1(r) ==> 
            exists |k : nat| epsilon * #[trigger]pow(r, k) >= 1real,
{
    crate::pure_fact::pure_fact(epsilon);
}

#[verifier::nonlinear]
proof fn real_assoc_mult(a: real, b: real, c: real)
    ensures
        a * (b * c) == (a * b) * c,
{
}

spec fn flip_eps(x: real, eps: real) -> real {
    if x == 0real {
        0real
    } else {
        2real * eps
    }
}


} // verus!

// `fn main` is outside of `verus!`, so it is not checked
fn main() {
    println!("Geometric Distribution Test");
    for _ in 0..100 {
        println!("{}", geo());
    }
}