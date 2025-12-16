use vstd::prelude::*;
use vstd::pcm::*;
use vstd::calc_macro::*;

verus! {
// TODO: figure out the right way to import
// use crate::ub::*;
mod ub;
use crate::ub::*;

// TODO: the types here are a bit messy
pub open spec fn average(bound: u64, e2: spec_fn(int) -> int) -> real
{
  let inputs:Seq<int> = Seq::new(bound as nat, |i:int| i);
  let nom = inputs.fold_left(0int, |acc: int, x| acc + e2(x)) as real;
  let denom = bound as real;
  nom / denom
}

//// Wrappers

#[verus::trusted]
#[verifier::external_body]
pub fn rand_u64(bound: u64,
                Tracked(e1): Tracked<ErrorCreditResource>,
                Ghost(e2): Ghost<spec_fn(int) -> int>)
          -> (ret : (u64, Tracked<ErrorCreditResource>))
  // TODO: can't have return value like this: ((n, e2): (u64, Tracked<ErrorCreditResource>))
  requires
    // Σ ℰ2(i) / bound = ε1
    (ErrorCreditCarrier::Value{car: average(bound, e2)}) =~= e1.view()
  ensures
    // owns ↯(ℰ(n))
    // TODO: this `.view().view()` looks pretty ugly, is there a way to improve?
    (ErrorCreditCarrier::Value{car: e2(ret.0 as int) as real}) =~= ret.1.view().view()
{
  let val: u64 = random::rand_u64(bound);
  (val, Tracked::assume_new())
}

// TODO: temporary hack for parsing error... (see zulip)
pub open spec fn flip_e2(a:bool) -> (spec_fn(int) -> int) {
  |a:int| if a == 1 { 0 } else { 1 }
}

proof fn ec_contradict(tracked e: ErrorCreditResource)
  requires
    e.view() =~= (ErrorCreditCarrier::Value{car: 1 as real})
  ensures
    false
  {
    e.explode(1real);
    e.valid();
    assert(!e.view().valid());
  }

pub fn flip(Tracked(e1): Tracked<ErrorCreditResource>) -> (ret: u64)
  requires
    (ErrorCreditCarrier::Value{car: 0.5real}) == e1.view()
{
  assert(average(2u64, flip_e2(true)) == 0.5real) by {
    assert(Seq::new(2 as nat, |i:int| i) =~= seq![0, 1]);
    // TODO: is there a more automatic way to unfold this fold_left?
    calc! {
      (==)
      seq![0, 1].fold_left(0int, |acc: int, x| acc + flip_e2(true)(x)); {
        assert(seq![0int, 1].drop_last() =~= seq![0]);
      }
      seq![0].fold_left(0int, |acc: int, x| acc + flip_e2(true)(x)) + flip_e2(true)(1);
      {
        assert(seq![0int].drop_last() =~= seq![]);
      }
      (seq![].fold_left(0int, |acc: int, x| acc + flip_e2(true)(x)) + flip_e2(true)(0)) + flip_e2(true)(1);
    }
    assert(seq![0, 1].fold_left(0int, |acc: int, x| acc + flip_e2(true)(x)) == 1int);
    assert(1real / 2real == 0.5real);
  };
  // Need to wrap with ghost becuase argument must be exec mode
  // https://verus-lang.github.io/verus/guide/reference-var-modes.html#using-tracked-and-ghost-variables-from-an-exec-function
  let (val, Tracked(e2)) = rand_u64(2u64, Tracked(e1), Ghost(flip_e2(true)));

  // TODO: some how you can't put `proof {...}` in `assert by`
  // and `assert by {...}` is not considered as a proof block
  proof {
    if(val != 1) {
      assert(flip_e2(true)(val as int) == 1);
      ec_contradict(e2);
    }
  }
  assert(val == 1);
  val
}
}

// TODO: main here is not checked...
fn main() {
  for _ in 0..10 {
    let a = flip(vstd::prelude::Tracked::assume_new());
    println!("{}", a);
  }
}