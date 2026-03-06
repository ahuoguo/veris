pub fn rand_u64(bound: u64) -> u64 {
  // TODO: unwarp is probably very bad
  // TODO: where to do the bounds check
  opendp::traits::samplers::sample_uniform_uint_below(bound).unwrap()
}

pub use dashu::integer::UBig;

pub fn ubig_zero() -> UBig {
    UBig::ZERO
}

pub fn ubig_one() -> UBig {
    UBig::ONE
}

pub fn ubig_succ(n: UBig) -> UBig {
    n + UBig::ONE
}

pub fn ubig_add(a: UBig, b: UBig) -> UBig {
    a + b
}