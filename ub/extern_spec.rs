// External type specifications and assumed specifications for third-party libraries.
//
// All external_type_specification, assume_specification, and external_body
// wrappers for types/functions from bignum crate

use vstd::prelude::*;

use random::{UBig, ubig_zero, ubig_succ, ubig_pred, ubig_is_zero, ubig_add, ubig_mul, ubig_mul_u64, ubig_from_u64, ubig_is_odd};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUBig(UBig);

/// Ghost interpretation of a UBig as a nat.
pub uninterp spec fn ubig_view(n: &UBig) -> nat;

pub assume_specification[ random::ubig_zero ]() -> (ret: UBig)
    ensures ubig_view(&ret) == 0nat;

pub assume_specification[ random::ubig_succ ](n: UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(&n) + 1;

pub assume_specification[ <UBig as Clone>::clone ](n: &UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(n);

pub assume_specification[ random::ubig_pred ](n: UBig) -> (ret: UBig)
    requires ubig_view(&n) > 0,
    ensures ubig_view(&ret) == ubig_view(&n) - 1;

pub assume_specification[ random::ubig_is_zero ](n: &UBig) -> (ret: bool)
    ensures ret == (ubig_view(n) == 0);

pub assume_specification[ random::ubig_add ](a: UBig, b: UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(&a) + ubig_view(&b);

pub assume_specification[ random::ubig_mul ](a: UBig, b: UBig) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(&a) * ubig_view(&b);

pub assume_specification[ random::ubig_mul_u64 ](a: &UBig, b: u64) -> (ret: UBig)
    ensures ubig_view(&ret) == ubig_view(a) * b as nat;

pub assume_specification[ random::ubig_from_u64 ](n: u64) -> (ret: UBig)
    ensures ubig_view(&ret) == n as nat;

pub assume_specification[ random::ubig_is_odd ](n: &UBig) -> (ret: bool)
    ensures ret == (ubig_view(n) % 2 == 1);

#[verifier::external_body]
pub fn ubig_lt(a: &UBig, b: &UBig) -> (ret: bool)
    ensures ret == (ubig_view(a) < ubig_view(b)),
{
    a < b
}

#[verifier::external_body]
pub fn ubig_to_i64(n: &UBig) -> (ret: i64)
{
    let v: u64 = n.try_into().unwrap();
    v as i64
}

} // verus!
