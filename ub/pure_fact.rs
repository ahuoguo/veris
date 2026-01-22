use vstd::prelude::*;

verus! {

pub open spec fn gt_1 (r: real) -> bool
{
    r > 1real
}

pub open spec fn pow(x:real, k: nat) -> real 
    decreases k
{
    if k == 0 {
        1real
    } else {
        x * pow(x, (k - 1) as nat)
    }
}

// Helper: product of values >= 1 is >= 1
#[verifier::nonlinear]
proof fn lemma_mul_ge_one(a: real, b: real)
    requires
        a >= 1real,
        b >= 1real,
    ensures
        a * b >= 1real,
{
}

// Helper: pow(r, k) >= 1 when r >= 1
proof fn lemma_pow_ge_one(r: real, k: nat)
    requires
        r >= 1real,
    ensures
        pow(r, k) >= 1real,
    decreases k
{
    if k == 0 {
    } else {
        lemma_pow_ge_one(r, (k - 1) as nat);
        lemma_mul_ge_one(r, pow(r, (k - 1) as nat));
    }
}

// Division properties
#[verifier::nonlinear]
proof fn lemma_div_pos(x: real)
    requires
        x > 0real,
    ensures
        1real / x > 0real,
{
}

#[verifier::nonlinear]
proof fn lemma_mul_div_cancel(x: real)
    requires
        x > 0real,
    ensures
        x * (1real / x) == 1real,
{
}

#[verifier::nonlinear]
proof fn lemma_div_nonneg(x: real, y: real)
    requires
        x >= 0real,
        y > 0real,
    ensures
        x / y >= 0real,
{
}

// Spec function for trigger
pub open spec fn nat_to_real(n: nat) -> real {
    n as real
}

// Bernoulli's inequality: (1 + δ)^k ≥ 1 + k*δ for δ > 0
// This gives us: pow(r, k) ≥ 1 + k*(r-1) for r > 1
proof fn lemma_bernoulli(r: real, k: nat)
    requires
        r > 1real,
    ensures
        pow(r, k) >= 1real + nat_to_real(k) * (r - 1real),
    decreases k
{
    let delta = r - 1real;
    if k == 0 {
        assert(pow(r, 0nat) == 1real);
        assert(nat_to_real(0nat) == 0real);
        assert(1real + 0real * delta == 1real);
    } else {
        let prev = (k - 1) as nat;
        lemma_bernoulli(r, prev);
        // IH: pow(r, prev) >= 1 + prev*delta
        // Goal: pow(r, k) = r * pow(r, prev) >= 1 + k*delta

        // r * pow(r, prev) >= r * (1 + prev*delta)   [by IH and r > 0]
        //                   = r + r*prev*delta
        //                   = (1 + delta) + (1 + delta)*prev*delta
        //                   = 1 + delta + prev*delta + prev*delta²
        //                   = 1 + (1 + prev)*delta + prev*delta²
        //                   = 1 + k*delta + prev*delta²
        //                   >= 1 + k*delta   [since prev*delta² >= 0]

        lemma_pow_ge_one(r, prev);
        lemma_bernoulli_step(r, prev, delta);
    }
}

// Helper for Bernoulli inductive step
#[verifier::nonlinear]
proof fn lemma_bernoulli_step(r: real, prev: nat, delta: real)
    requires
        r > 1real,
        delta == r - 1real,
        delta > 0real,
        pow(r, prev) >= 1real + nat_to_real(prev) * delta,
    ensures
        r * pow(r, prev) >= 1real + nat_to_real(prev + 1) * delta,
{
    // r * pow(r, prev) >= r * (1 + prev*delta)
    //                   = r + r*prev*delta
    // Need to show: r + r*prev*delta >= 1 + (prev+1)*delta
    //             = r + r*prev*delta >= 1 + prev*delta + delta
    //             = r - 1 - delta + r*prev*delta - prev*delta >= 0
    //             = delta - delta + (r-1)*prev*delta >= 0
    //             = delta*prev*delta >= 0
    // Which is true since delta > 0 and prev >= 0
}

proof fn archimedean_nat(x: real)
    requires
        x >= 0real,
    ensures
        exists |n: nat| #[trigger] nat_to_real(n) >= x,
{
    let a: nat = x.floor() as nat;
    assert(x < nat_to_real(a + 1));   
}

// Archimedean property for powers: powers of r > 1 grow without bound
// Proven using Bernoulli's inequality
proof fn archimedean_pow(r: real, target: real)
    requires
        r > 1real,
        target > 0real,
    ensures
        exists |k: nat| #[trigger] pow(r, k) >= target,
{
    let delta = r - 1real;

    if target <= 1real {
        // k = 0 works: pow(r, 0) = 1 >= target
        assert(pow(r, 0nat) == 1real);
        assert(pow(r, 0nat) >= target);
    } else {
        // Need k such that pow(r, k) >= target
        // By Bernoulli: pow(r, k) >= 1 + k*delta
        // So it suffices to find k such that 1 + k*delta >= target
        // i.e., k*delta >= target - 1
        // i.e., k >= (target - 1)/delta

        // By Archimedean property for naturals, such k exists
        lemma_div_pos(delta);
        let bound = (target - 1real) / delta;
        lemma_div_nonneg(target - 1real, delta);
        archimedean_nat(bound);
        let k = choose |k: nat| #[trigger] nat_to_real(k) >= bound;

        // Now show pow(r, k) >= target
        lemma_bernoulli(r, k);
        // pow(r, k) >= 1 + k*delta >= 1 + bound*delta = 1 + (target-1) = target
        lemma_archimedean_final(r, k, target, delta, bound);
    }
}

#[verifier::nonlinear]
proof fn lemma_archimedean_final(r: real, k: nat, target: real, delta: real, bound: real)
    requires
        r > 1real,
        delta == r - 1real,
        delta > 0real,
        target > 1real,
        bound == (target - 1real) / delta,
        nat_to_real(k) >= bound,
        pow(r, k) >= 1real + nat_to_real(k) * delta,
    ensures
        pow(r, k) >= target,
{
    // k >= bound = (target - 1)/delta
    // So k*delta >= target - 1
    // So 1 + k*delta >= target
    // And pow(r, k) >= 1 + k*delta >= target
}

// Helper: if a >= b and c > 0, then c * a >= c * b
#[verifier::nonlinear]
proof fn lemma_mul_mono(a: real, b: real, c: real)
    requires
        a >= b,
        c > 0real,
    ensures
        c * a >= c * b,
{
}

pub proof fn pure_fact(epsilon: real)
    requires
        epsilon > 0real,
    ensures
        forall |r: real| #[trigger]gt_1(r) ==>
            exists |k : nat| epsilon * #[trigger]pow(r, k) >= 1real,
{
    assert forall |r: real| #[trigger]gt_1(r) implies
        exists |k : nat| epsilon * #[trigger]pow(r, k) >= 1real
    by {
        // For any r > 1 and epsilon > 0, there exists k such that epsilon * r^k >= 1
        // By Archimedean property, there exists k such that r^k >= 1/epsilon
        lemma_div_pos(epsilon);
        archimedean_pow(r, 1real / epsilon);
        let k = choose |k: nat| #[trigger] pow(r, k) >= 1real / epsilon;
        // Since pow(r, k) >= 1/epsilon and epsilon > 0, we have epsilon * pow(r, k) >= 1
        lemma_mul_mono(pow(r, k), 1real / epsilon, epsilon);
        lemma_mul_div_cancel(epsilon);
    }
}

}

fn main() {}


