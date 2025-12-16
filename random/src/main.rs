// import commonly used items from the prelude:
use opendp::traits::samplers::sample_uniform_uint_below;

fn main() {
    // generate a random boolean 10 times
    for _ in 0..10 {
        let res: Result<u32, opendp::error::Error> = sample_uniform_uint_below(2u32);
        match res {
            Ok(val) => println!("Random boolean: {}", val),
            Err(e) => println!("Error generating random boolean: {:?}", e),
        }
    }
}

// verus!{

// // following
// //// Wrappers
// #[verus::trusted]
// #[verifier::external_body]
// /// Sample an integer uniformly from `[0, upper)`
// fn rand_u64() -> u64 {
//   use opendp::traits::samplers::sample_uniform_uint_below;
//   // TODO: unwarp is probably very bad
//   sample_uniform_uint_below(1u64 << 64).unwrap()
// }

// }
