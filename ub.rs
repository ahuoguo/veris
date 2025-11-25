use vstd::prelude::*;
use vstd::pcm::*;

verus! {

// wrapper around ec, namely `↯`
// A error credit represents a resource with a non zero value
// ideally the carrier should be nonnegreal
// https://logsem.github.io/clutch/clutch.base_logic.error_credits.html
// TODO: not sure how to get real, but in `frac.rs` they have a
// compile-constant `TOTAL`
pub enum ErrorCreditCarrier<const TOTAL: u64> {
    Value { n: int },
    Empty,
    Invalid,
}

// you can always get 0 error credit
impl<const TOTAL: u64> ErrorCreditCarrier<TOTAL> {
    pub closed spec fn zero() -> Self {
        ErrorCreditCarrier::Value { n: 0 }
    }
}

impl<const TOTAL: u64> PCM for ErrorCreditCarrier<TOTAL> {
    closed spec fn valid(self) -> bool {
        match self {
            ErrorCreditCarrier::Value { n } => 0 <= n <= TOTAL as int,
            ErrorCreditCarrier::Empty => true,
            ErrorCreditCarrier::Invalid => false,
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (ErrorCreditCarrier::Invalid, _) | (_, ErrorCreditCarrier::Invalid) => {
                ErrorCreditCarrier::Invalid
            }
            (ErrorCreditCarrier::Value { n: n1 }, ErrorCreditCarrier::Value { n: n2 }) => {
              if n1 < 0 || n2 < 0 {
                  ErrorCreditCarrier::Invalid
              } else {
                  let sum = n1 + n2;
                  ErrorCreditCarrier::Value { n: sum }
              }
            },
            (ErrorCreditCarrier::Empty, other) | (other, ErrorCreditCarrier::Empty) => other,
        }
    }

    closed spec fn unit() -> Self {
        ErrorCreditCarrier::Empty
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

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
fn main() {}
