use vstd::pcm::*;
use vstd::prelude::*;

verus! {

// Ghost name for the single global error-credit resource location.
pub uninterp spec fn EC_GLOBAL_LOC() -> int;

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
    // All error credits live at the single global location.
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.r.loc() == EC_GLOBAL_LOC()
    }

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

pub proof fn ec_contradict(tracked e: &ErrorCreditResource)
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

/// Combine two error credits into one with summed value.
pub proof fn join_credits(
    tracked c1: ErrorCreditResource,
    tracked c2: ErrorCreditResource,
    v1: real,
    v2: real,
) -> (tracked out: ErrorCreditResource)
    requires
        c1.view() =~= (ErrorCreditCarrier::Value { car: v1 }),
        c2.view() =~= (ErrorCreditCarrier::Value { car: v2 }),
        v1 >= 0real,
        v2 >= 0real,
    ensures
        out.view() =~= (ErrorCreditCarrier::Value { car: v1 + v2 }),
{
    use_type_invariant(&c1);
    use_type_invariant(&c2);
    let tracked joined = c1.r.join(c2.r);
    ErrorCreditResource { r: joined }
}


} // verus!

fn main() {}
