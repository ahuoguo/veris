// TODO: i might split this to 2 files... to move the instantiation out of the generic code

// Higher Order Rejection Sampler
// https://logsem.github.io/clutch/clutch.eris.examples.approximate_samplers.approx_higherorder_rejection_sampler.html
//
// A sampling scheme is parameterized by:
// - `sampler`: A sampling function that generates candidate values
// - `checker`: A predicate that determines if a sample should be accepted
// - `εfactor`: Error amplification factor
//
// Spec (from Clutch):
//   Given ↯ε, after sampler() returns v, either:
//   - checker(v) = true and Θ(v) holds
//   - OR we have ↯ε' where ε ≤ ε' * εfactor

use vstd::prelude::*;
use vstd::calc_macro::*;
use crate::ub::*;
use crate::rand_primitives::{rand_u64, rand_1_u64, thin_air, average, sum_credit};
use crate::pure_fact::{pow, pure_fact_with_base};

verus! {


/// Outcome of a sampling step in a sampling scheme.
///
/// After calling sample(), we get a value and one of:
/// - `Accepted`: checker will return true, postcondition Θ holds
/// - `Rejected`: we have amplified error credit, checker returns false
pub enum SampleOutcome {
    Accepted,
    Rejected(Tracked<ErrorCreditResource>),
}

/// A sampling scheme packages a sampler and checker with their specifications.
///
/// The key spec (matching Clutch's `sampling_scheme_spec`):
/// ```
/// Given ↯ε, after sampler() returns v:
///   Either: checker(v) = true ∧ Θ(v)
///   Or:     ↯ε' where ε ≤ ε' * self.amp()
/// ```

pub trait SamplingScheme {
    // TODO: do we really need a separate postcondition spec?
    // in the threshold example they are the same...
    /// The postcondition Θ that holds when a sample is accepted
    spec fn postcond(&self) -> spec_fn(u64) -> bool;

    /// The checker specification (what values are accepted)
    spec fn check_spec(&self) -> spec_fn(u64) -> bool;

    /// Amplification factor: on reject, ε becomes amp * ε
    spec fn amp(&self) -> real;

    /// Validity predicate - scheme-specific requirements for error credit accounting
    spec fn valid(&self) -> bool;

    /// Sample a value with error credit accounting
    ///
    /// Returns (v, outcome) where:
    /// - If outcome is Accepted: check_spec(v) is true and postcond(v) holds
    /// - If outcome is Rejected: check_spec(v) is false and we have amp*ε credit
    fn sample(
        &self,
        Tracked(e): Tracked<ErrorCreditResource>,
        Ghost(eps): Ghost<real>,
    ) -> (ret: (u64, SampleOutcome))
        requires
            self.valid(),
            eps > 0real,
            e.view() =~= (ErrorCreditCarrier::Value { car: eps }),
        ensures
            match ret.1 {
                SampleOutcome::Accepted => {
                    &&& (self.check_spec())(ret.0)
                    &&& (self.postcond())(ret.0)
                }
                SampleOutcome::Rejected(ref amplified_credit) => {
                    &&& !(self.check_spec())(ret.0)
                    &&& amplified_credit@.view() =~= (ErrorCreditCarrier::Value { car: self.amp() * eps })
                }
            };

    /// Execute the checker (for use in the rejection loop)
    fn check(&self, v: u64) -> (ret: bool)
        ensures ret == (self.check_spec())(v);
}

// ============================================================================
// Higher-Order Rejection Sampler
// ============================================================================

/// Bounded rejection sampler over any sampling scheme
///
/// Loops until sample() returns an accepted value.
/// Uses error credit invariant: eps * amp^depth >= 1
pub fn bounded_rejection_sampler<S: SamplingScheme>(
    scheme: &S,
    Tracked(e): Tracked<ErrorCreditResource>,
    Ghost(depth): Ghost<nat>,
) -> (ret: u64)
    requires
        scheme.amp() > 1real,
        scheme.valid(),
        exists |eps: real| {
            &&& eps > 0real
            &&& e.view() =~= (ErrorCreditCarrier::Value { car: eps })
            &&& eps * pow(scheme.amp(), depth) >= 1real
        },
    ensures
        (scheme.check_spec())(ret),
        (scheme.postcond())(ret),
    decreases depth,
{
    let ghost amp = scheme.amp();
    let ghost eps: real;

    proof {
        eps = choose |v: real| {
            &&& v > 0real
            &&& e.view() =~= (ErrorCreditCarrier::Value { car: v })
            &&& v * pow(amp, depth) >= 1real
        };

        // Base case: depth == 0 implies eps >= 1, contradiction
        if depth == 0nat {
            assert(pow(amp, 0nat) == 1real);
            assert(eps >= 1real);
            ec_contradict(&e);
        }
    }

    let (val, outcome) = scheme.sample(Tracked(e), Ghost(eps));

    match outcome {
        SampleOutcome::Accepted => {
            val
        }
        SampleOutcome::Rejected(e1_tracked) => {
            let ghost new_eps = amp * eps;

            proof {
                // e1 has amp * eps credit
                assert(e1_tracked@.view() =~= (ErrorCreditCarrier::Value { car: new_eps }));

                // Show new_eps > 0
                lemma_pos_mult(amp, eps);

                // Show: new_eps * amp^(depth-1) >= 1
                calc! {
                    (==)
                    new_eps * pow(amp, (depth - 1) as nat); {}
                    (amp * eps) * pow(amp, (depth - 1) as nat); {
                        real_assoc_mult(eps, amp, pow(amp, (depth - 1) as nat));
                    }
                    eps * (amp * pow(amp, (depth - 1) as nat)); {}
                    eps * pow(amp, depth);
                }
                assert(new_eps * pow(amp, (depth - 1) as nat) >= 1real);
            }

            bounded_rejection_sampler(scheme, e1_tracked, Ghost((depth - 1) as nat))
        }
    }
}

/// Unbounded rejection sampler
pub fn rejection_sampler<S: SamplingScheme>(
    scheme: &S,
) -> (ret: u64)
    requires
        scheme.amp() > 1real,
        scheme.valid(),
    ensures
        (scheme.check_spec())(ret),
        (scheme.postcond())(ret),
{
    // OBSERVE: the thin_air credit is created here
    // TODO: maybe we should take a thin_air credit as input instead?
    let Tracked(e) = thin_air();
    let ghost amp = scheme.amp();

    let ghost hi: nat;
    let ghost epsilon: real;

    proof {
        if e.view().value() =~= None { }
    }
    assert(exists |v: real| e.view().value() == Some(v));

    proof {
        epsilon = choose |i: real| e.view().value() == Some(i);
        crate::pure_fact::pure_fact_with_base(epsilon, amp);
        assert(exists |k: nat| epsilon * pow(amp, k) >= 1real);
        hi = choose |k: nat| epsilon * pow(amp, k) >= 1real;
    }

    bounded_rejection_sampler(scheme, Tracked(e), Ghost(hi))
}

// ============================================================================
// Helper lemmas
// ============================================================================

#[verifier::nonlinear]
proof fn real_assoc_mult(a: real, b: real, c: real)
    ensures
        a * (b * c) == (a * b) * c,
{
}

#[verifier::nonlinear]
proof fn lemma_pos_mult(a: real, b: real)
    requires
        a > 0real,
        b > 0real,
    ensures
        a * b > 0real,
{
}

/// Lemma: a/b > 1 when a > b > 0
#[verifier::nonlinear]
proof fn lemma_div_gt_1(a: real, b: real)
    requires
        a > b,
        b > 0real,
    ensures
        a / b > 1real,
{
}

// ============================================================================
// Lemmas for average bound
// ============================================================================

/// Credit allocation for uniform threshold sampling.
/// - For outcomes i < threshold: credit = 0 (accepted, no amplification needed)
/// - For outcomes i >= threshold: credit = amp * eps where amp = bound / (bound - threshold)
pub open spec fn threshold_credit_alloc(bound: u64, threshold: u64, eps: real) -> spec_fn(real) -> real {
    |i: real| if i < threshold as real { 0real } else { (bound as real / (bound - threshold) as real) * eps }
}

/// Lemma: sum_credit(threshold_credit_alloc, n) for n <= threshold is 0,
///        and for n > threshold equals (n - threshold) * amp * eps
proof fn lemma_sum_threshold(bound: u64, threshold: u64, eps: real, n: nat)
    requires
        bound > 0,
        threshold < bound,
        n <= bound,
    ensures
        n <= threshold ==> sum_credit(threshold_credit_alloc(bound, threshold, eps), n) == 0real,
        n > threshold ==> sum_credit(threshold_credit_alloc(bound, threshold, eps), n) ==
            (n - threshold) as real * (bound as real / (bound - threshold) as real) * eps,
    decreases n,
{
    let credit_alloc = threshold_credit_alloc(bound, threshold, eps);
    let amp = bound as real / (bound - threshold) as real;

    if n == 0 {
        // Base case: sum of empty range is 0
    } else {
        lemma_sum_threshold(bound, threshold, eps, (n - 1) as nat);
        let prev_sum = sum_credit(credit_alloc, (n - 1) as nat);
        let curr_credit = credit_alloc((n - 1) as real);

        if n <= threshold {
            // n-1 < threshold, so credit_alloc(n-1) = 0
            assert(((n - 1) as real) < threshold as real);
            assert(curr_credit == 0real);
            // prev_sum == 0 by IH (since n-1 <= threshold)
        } else if (n - 1) as nat <= threshold as nat {
            // Transition case: n > threshold but n-1 <= threshold
            // So n-1 == threshold, meaning n == threshold + 1
            // credit_alloc(n-1) = credit_alloc(threshold) = amp * eps (since threshold >= threshold)
            assert(!(((n - 1) as real) < threshold as real));
            assert(curr_credit == amp * eps);
            // prev_sum == 0 by IH (since n-1 <= threshold)
            assert(prev_sum == 0real);
            // sum = 0 + amp * eps = 1 * amp * eps = (n - threshold) * amp * eps
            assert((n - threshold) as nat == 1nat);
            assert((n - threshold) as real == 1real);
            assert(sum_credit(credit_alloc, n) == amp * eps);
            assert((n - threshold) as real * amp * eps == amp * eps) by(nonlinear_arith)
                requires (n - threshold) as real == 1real;
            assert(sum_credit(credit_alloc, n) == (n - threshold) as real * amp * eps);
        } else {
            // Both in rejected region: n > threshold and n-1 > threshold
            assert(!(((n - 1) as real) < threshold as real));
            assert(curr_credit == amp * eps);
            // prev_sum == (n-1-threshold) * amp * eps by IH
            // sum = prev_sum + amp * eps = (n-threshold) * amp * eps
            assert(sum_credit(credit_alloc, n) == (n - threshold) as real * amp * eps) by(nonlinear_arith)
                requires
                    prev_sum == ((n - 1) as nat - threshold as nat) as real * amp * eps,
                    curr_credit == amp * eps,
                    sum_credit(credit_alloc, n) == prev_sum + curr_credit,
                    n > threshold,
            ;
        }
    }
}

/// Lemma: eps >= average(bound, threshold_credit_alloc)
///
/// Proof: sum = (bound - threshold) * amp * eps = bound * eps, so average = eps
proof fn lemma_average_bound(bound: u64, threshold: u64, eps: real)
    requires
        bound > 0,
        threshold < bound,
        eps > 0real,
    ensures
        eps >= average(bound, threshold_credit_alloc(bound, threshold, eps)),
{
    let credit_alloc = threshold_credit_alloc(bound, threshold, eps);
    let amp = bound as real / (bound - threshold) as real;

    lemma_sum_threshold(bound, threshold, eps, bound as nat);
    // sum_credit = (bound - threshold) * amp * eps

    // (bound - threshold) * amp * eps = (bound - threshold) * (bound / (bound - threshold)) * eps = bound * eps
    // average = sum / bound = (bound * eps) / bound = eps
    assert(average(bound, credit_alloc) == eps) by(nonlinear_arith)
        requires
            sum_credit(credit_alloc, bound as nat) == (bound - threshold) as real * amp * eps,
            amp == bound as real / (bound - threshold) as real,
            bound > threshold,
            bound > 0,
    ;
}

// ============================================================================
// Concrete Implementation: Uniform + Threshold
// ============================================================================

/// A sampling scheme with uniform sampling and threshold checking.
/// - Samples uniformly from [0, bound)
/// - Accepts values < threshold
/// - Postcondition: v < threshold
pub struct UniformThresholdScheme {
    pub bound: u64,
    pub threshold: u64,
}

impl SamplingScheme for UniformThresholdScheme {
    open spec fn postcond(&self) -> spec_fn(u64) -> bool {
        |v: u64| v < self.threshold
    }

    open spec fn check_spec(&self) -> spec_fn(u64) -> bool {
        |v: u64| v < self.threshold
    }

    /// Amplification factor = bound / (bound - threshold)
    open spec fn amp(&self) -> real {
        self.bound as real / (self.bound - self.threshold) as real
    }

    /// Valid requires:
    /// - threshold < bound (for amp to be defined and > 1)
    open spec fn valid(&self) -> bool {
        self.threshold < self.bound
    }

    fn sample(
        &self,
        Tracked(input_credit): Tracked<ErrorCreditResource>,
        Ghost(eps): Ghost<real>,
    ) -> (ret: (u64, SampleOutcome))
        ensures
            match ret.1 {
                SampleOutcome::Accepted => {
                    &&& (self.check_spec())(ret.0)
                    &&& (self.postcond())(ret.0)
                }
                SampleOutcome::Rejected(ref amplified_credit) => {
                    &&& !(self.check_spec())(ret.0)
                    &&& amplified_credit@.view() =~= (ErrorCreditCarrier::Value { car: self.amp() * eps })
                }
            },
    {
        let ghost credit_alloc = threshold_credit_alloc(self.bound, self.threshold, eps);

        proof {
            // valid() ensures threshold < bound, which gives us preconditions for lemma_average_bound
            lemma_average_bound(self.bound, self.threshold, eps);
        }

        let (val, Tracked(outcome_credit)) = rand_u64(self.bound, Tracked(input_credit), Ghost(credit_alloc));

        if val < self.threshold {
            proof {
                assert(credit_alloc(val as real) == 0real);
            }
            (val, SampleOutcome::Accepted)
        } else {
            (val, SampleOutcome::Rejected(Tracked(outcome_credit)))
        }
    }

    fn check(&self, v: u64) -> (ret: bool)
        ensures ret == (self.check_spec())(v),
    {
        v < self.threshold
    }
}

/// Example: Sample from [0, 8) but only accept < 5
/// Rejection rate = 3/8, so amp = 8/3
pub fn example_rejection_sampler() -> (ret: u64)
    ensures ret < 5,
{
    let scheme = UniformThresholdScheme { bound: 8, threshold: 5 };
    proof {
        assert(scheme.valid());
        lemma_div_gt_1(8real, 3real);
        assert(scheme.amp() > 1real);
    }
    rejection_sampler(&scheme)
}

} // verus!
