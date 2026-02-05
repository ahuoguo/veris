// Library file to build all ub modules together

pub mod ub;
pub mod rand_primitives;
pub mod pure_fact;
pub mod geo;
pub mod ho_rej_samp;

// `fn main` is outside of `verus!`, so it is not checked
fn main() {
    println!("Geometric Distribution Test");
    for _ in 0..100 {
        println!("{}", geo::geometric());
    }

    println!("Rejection Sampler Test");
    println!("{}", ho_rej_samp::example_rejection_sampler());
}
