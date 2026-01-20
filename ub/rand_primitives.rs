use vstd::calc_macro::*;
use vstd::pcm::*;
use vstd::prelude::*;

verus! {

// TODO: is there a better way to import ub module?
mod ub;
use crate::ub::*;

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

pub proof fn ec_contradict(tracked e: ErrorCreditResource)
    requires
        e.view() =~= (ErrorCreditCarrier::Value { car: 1 as real }),
    ensures
        false,
{
    e.explode(1real);
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

// pub open spec fn flip_dummy(x: real, a: real) -> real {
//     if x == 1real {
//         a
//     } else {
//         a
//     }
// }

pub open spec fn pow(x:real, k: nat) -> real 
    decreases k
{
    if k == 0 {
        1real
    } else {
        x * pow(x, (k - 1) as nat)
    }
}

pub open spec fn gt_1 (r: real) -> bool
{
    r > 1real
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
        assume(forall |r: real| #[trigger]gt_1(r) ==> exists |k : nat| epsilon * #[trigger]pow(r, k) >= 1real ); // TODO: pure fact, hopefully this is easy to discharge...
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
    assert(exists |v: real| a.view().value() == Some(v));
    proof {
        eps = choose|i: real| a.view().value() == Some(i);
    }
    let (val, Tracked(e2)) = rand_1_u64(Tracked(a), Ghost(|x: real| flip_eps(x, eps)));

    if val == 0 {
        1
    } else {
        proof {
            if k == 0nat {
                // then invariant doesn't hold...
                assume(false);
            }
        }
        assume(exists |eps: real| {
            &&& eps > 0.0 
            &&& (ErrorCreditCarrier::Value { car: eps } =~= e2.view())
            &&& eps * pow(2real, (k-1) as nat) >= 1real
        });
        let v = geo_aux(Tracked(e2), Ghost((k-1) as nat ));
        // TODO: will arithmetic overflow if `+1`, maybe we should not name this as geometric...
        v
    }
}

spec fn flip_eps(x: real, eps: real) -> real {
    if x == 0real {
        0real
    } else {
        eps
    }
}

// ∀ ε > 0, [ ↯(ε) ] rejection_sampler() [ v. v = 1 ]

// In Eris, you can only invoke a thin air rule if your postcondition is a WP or is wrapped in some modality
// you can't not invoke thin air rule in any lemma (this might(?) be unsound)

} // verus!
// TODO: main here is not checked...
fn main() {
    for _ in 0..10 {
        let a = flip(vstd::prelude::Tracked::assume_new());
        println!("{}", a);
    }

}