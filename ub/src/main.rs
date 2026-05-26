// Runtime smoke tests for the verified samplers. Lives outside the lib
// crate (and outside `verus!`) so it isn't part of verification.

use ub::{discrete_laplace, geo, geo_dist, ho_rej_samp};

fn main() {
    println!("Geometric Distribution Test");
    for _ in 0..100 {
        println!("{}", geo::geometric());
    }

    println!("Geometric Distribution (UBig) Test");
    for _ in 0..100 {
        let v = geo_dist::geo_dist_sample();
        println!("{}", v);
    }

    println!("Discrete Laplace (scale=4) Test");
    let mut res = Vec::new();
    for _ in 0..100 {
        let v = discrete_laplace::discrete_laplace::sample_discrete_laplace_entry(1, 4);
        res.push(v);
    }
    println!("{:?}", res);

    println!("Rejection Sampler Test");
    println!("{}", ho_rej_samp::example_rejection_sampler());
}
