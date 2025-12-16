pub fn rand_u64(bound: u64) -> u64 {
  // TODO: unwarp is probably very bad
  // TODO: where to do the bounds check
  opendp::traits::samplers::sample_uniform_uint_below(bound).unwrap()
}