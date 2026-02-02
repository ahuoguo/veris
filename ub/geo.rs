use vstd::prelude::*;
use vstd::calc_macro::*;
use vstd::pcm::*;

verus! {
  use crate::ub::*;
  use crate::rand_primitives::{rand_1_u64, thin_air, ec_contradict};
  use crate::pure_fact::{gt_1, pow};

  pub fn geo() -> (ret: u64)
  {
      let Tracked(e) = thin_air();
      // This is a super hacky (but official) way to depend on ghost values...
      let ghost mut hi;
      let ghost mut epsilon;

      // ∀ ε > 0, r >1, ∃ k, ε * r ^ k >= 1
      // the decreasing part is k
      proof {
          if e.view().value() =~= None { } // OBSERVE
      }
      assert(exists |v: real| e.view().value() == Some(v));
      proof {
          epsilon = choose|i: real| e.view().value() == Some(i);
          crate::pure_fact::pure_fact(epsilon);
          assert(gt_1(2real)); // OBSERVE
          assert(exists |k : nat| epsilon * pow(2real, k) >= 1real);
          hi = choose|i: nat| epsilon * pow(2real, i) >= 1real;
          assert(epsilon * pow(2real, hi) >= 1real);
      } 
      assert(epsilon * pow(2real, hi) >= 1real);
      geo_aux(Tracked(e), Ghost(hi)) // ε
  }

  pub fn geo_aux(Tracked(e): Tracked<ErrorCreditResource>, Ghost(k): Ghost<nat>) -> (ret: u64)
      requires
          exists |eps: real| {
              &&& eps > 0.0 
              &&& (ErrorCreditCarrier::Value { car: eps } =~= e.view())
              &&& eps * pow(2real, k) >= 1real
          }
      ensures
          ret >= 0,
      decreases
          k
  {
      let ghost mut eps : real;
      let ghost mut eps1 : real;

      assert(exists |v: real| e.view().value() == Some(v));
      proof {
          eps = choose|i: real| e.view().value() == Some(i);
          if k == 0nat {
              assert(eps * pow(2real, k) >= 1real);
              assert(eps >= 1real);
              ec_contradict(&e);
              assert(false);
          }
          assert(k != 0nat);
      }
      let (val, Tracked(e1)) = rand_1_u64(Tracked(e), Ghost(|x: real| flip_eps(x, eps)));
      if val == 0 {
          0
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
          let v = geo_aux(Tracked(e1), Ghost((k-1) as nat ));
          v.wrapping_add(1u64)
      }
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
}

