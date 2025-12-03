// Now, this file is more like a demonstration that why encoding as rational numbers is slow

use vstd::pcm::*;
use vstd::prelude::*;

verus! {

// wrapper around ec, namely `↯`
// A error credit represents a resource with a non zero value
// ideally the carrier should be nonnegreal
// https://logsem.github.io/clutch/clutch.base_logic.error_credits.html
// ideally the carrier should be nonnegreal, but Verus doesn't have real theory
// we now model it as a rational number as the division between two integers

// TODO: how to we quotient out the equivalence
pub enum ErrorCreditCarrier {
    Value { nom: nat, denom: nat },
    Empty,
    Invalid,
}

// you can always get 0 error credit
impl ErrorCreditCarrier {
    pub closed spec fn zero() -> Self {
        ErrorCreditCarrier::Value { nom: 0, denom: 1 }
    }
}

impl PCM for ErrorCreditCarrier {
    closed spec fn valid(self) -> bool {
        match self {
            ErrorCreditCarrier::Value { nom, denom } => denom > 0 && nom <= denom,
            ErrorCreditCarrier::Empty => true,
            ErrorCreditCarrier::Invalid => false,
        }
    }

    // addition of rational numbers
    closed spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (
                ErrorCreditCarrier::Value { nom: n1, denom: d1 },
                ErrorCreditCarrier::Value { nom: n2, denom: d2 },
            ) => { ErrorCreditCarrier::Value { nom: n1 * d2 + n2 * d1, denom: d1 * d2 } },
            (ErrorCreditCarrier::Empty, ec) | (ec, ErrorCreditCarrier::Empty) => ec,
            _ => ErrorCreditCarrier::Invalid,
        }
    }

    closed spec fn unit() -> Self {
        ErrorCreditCarrier::Empty
    }

    proof fn closed_under_incl(a: Self, b: Self) by(nonlinear_arith)
    {
      match (a, b) {
          (
              ErrorCreditCarrier::Value { nom: n1, denom: d1 },
              ErrorCreditCarrier::Value { nom: n2, denom: d2 },
          ) => {
            // WH n1 * d2 + n2 * d1 <= d1 * d2
            // WTS n2 <= d2
            assert(n1 * d2 + n2 * d1 <= d1 * d2 ==> n2 <= d2);

          },
          (ErrorCreditCarrier::Empty, _) => {},
          _ => {}
      }
    }

    proof fn commutative(a: Self, b: Self) by(nonlinear_arith) 
    {
    }

    proof fn associative(a: Self, b: Self, c: Self) by(nonlinear_arith)  {
      match (a, b, c) {
          (
              ErrorCreditCarrier::Value { nom: n1, denom: d1 },
              ErrorCreditCarrier::Value { nom: n2, denom: d2 },
              ErrorCreditCarrier::Value { nom: n3, denom: d3 },
          ) => {
              assert(n1*d2*d3 + n2*d1*d3 + n3*d1*d2 == n1*d2*d3 + n2*d1*d3 + n3*d2*d1);
              assert((d1 * d2) * d3 == d1 * (d2 * d3));
          },
          _ => {}
      }
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

// impl PartialEq for ErrorCreditCarrier {
//     fn eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             (
//                 ErrorCreditCarrier::Value { nom: n1, denom: d1 },
//                 ErrorCreditCarrier::Value { nom: n2, denom: d2 },
//             ) => n1 * d2 == n2 * d1,
//             (ErrorCreditCarrier::Empty, ErrorCreditCarrier::Empty) => true,
//             (ErrorCreditCarrier::Invalid, ErrorCreditCarrier::Invalid) => true,
//             _ => false,
//         }
//     }
// }

// want to prove 2/4 == 1/2
#[verifier::auto_ext_equal()]
proof fn error_credit_eq(a: ErrorCreditCarrier, b: ErrorCreditCarrier)
    requires
      a == (ErrorCreditCarrier::Value { nom: 2, denom: 4 }) &&
      b == (ErrorCreditCarrier::Value { nom: 1, denom: 2 }),
    ensures
        a == b,
{
    assert(2 * 2 == 1 * 4);
}


// #[verifier(external_body)]
// exec fn flip(tracked ec: Tracked<ErrorCreditCarrier>) -> (res: bool)
//     ensures
//       res == true
// {
//   fill_bytes()
} // verus!
// the key difference is normally in `frac`, you will have a `new`
// methods to let you
// exmaple of { ↯(0.5) } flip() { v. v = 1 }
/**
 ```rust
  fn flip (tracked ec: Tracked(ErrorCredits(0.5))) -> (res: bool)
    ensures
      res == true
  {
  }
```
 */
// I think what we want is to extend assert with an error credit...
// v = flip()
// assert (0.5) (v == 1);
fn main() {}
