use vstd::pcm::*;
use vstd::prelude::*;

verus! {

// wrapper around ec, namely `↯`
// A error credit represents a resource with a non zero value
// https://logsem.github.io/clutch/clutch.base_logic.error_credits.html
pub enum ErrorCreditCarrier {
    Value { car: real },
    Empty,
    Invalid,
}

impl ErrorCreditCarrier {
    pub closed spec fn zero() -> Self {
        ErrorCreditCarrier::Value { car: 0real }
    }

    pub open spec fn value(self) -> Option<real> {
        match self {
            ErrorCreditCarrier::Value { car } => Some(car),
            _ => None,
        }
    }
}

impl PCM for ErrorCreditCarrier {
    closed spec fn valid(self) -> bool {
        match self {
            ErrorCreditCarrier::Value { car } => 0real <= car < 1real,
            ErrorCreditCarrier::Empty => true,
            ErrorCreditCarrier::Invalid => false,
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (ErrorCreditCarrier::Value { car: c1 }, ErrorCreditCarrier::Value { car: c2 }) => {
                // REVIEW: we have to bake in the `nonnegreal` part in the op
                // I guess verus doesn't have a good way to express subset types like Dafny...
                if c1 < 0real || c2 < 0real {
                    ErrorCreditCarrier::Invalid
                } else {
                    ErrorCreditCarrier::Value { car: c1 + c2 }
                }

            },
            (ErrorCreditCarrier::Empty, ec) | (ec, ErrorCreditCarrier::Empty) => ec,
            _ => ErrorCreditCarrier::Invalid,
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

pub struct ErrorCreditResource {
    r: Resource<ErrorCreditCarrier>,
}

impl ErrorCreditResource {
    pub closed spec fn view(self) -> ErrorCreditCarrier {
        self.r.value()
    }

    pub proof fn explode(tracked &self, c: real)
        requires
            self.view() =~= (ErrorCreditCarrier::Value { car: c }),
            c >= 1real,
        ensures
            !self.view().valid(),
    {
    }

    pub proof fn valid(tracked &self)
        ensures
            self.view().valid(),
    {
        self.r.validate();
    }
}

} // verus!

fn main() {}
