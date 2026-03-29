// Library file to build all ub modules together

pub mod ub;
pub mod rand_primitives;
pub mod extern_spec;
pub mod math;
pub mod geo;
pub mod geo_dist;
pub mod ho_rej_samp;
pub mod discrete_laplace;
pub mod random_walk;

// `fn main` is outside of `verus!`, so it is not checked
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

