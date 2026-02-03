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
use crate::rand_primitives::{rand_u64, rand_1_u64, thin_air, ec_contradict, average};
use crate::pure_fact::{gt_1, pow, pure_fact_with_base};

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

/// The e2 function for threshold checking
/// Amplification factor = bound / (bound - threshold)
/// This ensures average(bound, e2) == eps exactly
pub open spec fn threshold_e2(bound: u64, threshold: u64, eps: real) -> spec_fn(real) -> real {
    |i: real| if i < threshold as real { 0real } else { (bound as real / (bound - threshold) as real) * eps }
}

/// Recursive spec for sum of e2 over [0, n)
pub open spec fn sum_e2(e2: spec_fn(real) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { sum_e2(e2, (n - 1) as nat) + e2((n - 1) as real) }
}

/// Lemma: fold_left equals sum_e2
proof fn lemma_fold_left_sum(e2: spec_fn(real) -> real, n: nat)
    ensures
        Seq::new(n, |i: int| i).fold_left(0real, |acc: real, x: int| acc + e2(x as real)) == sum_e2(e2, n),
    decreases n,
{
    let s = Seq::new(n, |i: int| i);
    if n == 0 {
        assert(s =~= Seq::<int>::empty());
    } else {
        let s_prev = Seq::new((n - 1) as nat, |i: int| i);
        assert(s.drop_last() =~= s_prev);
        assert(s.last() == (n - 1) as int);
        lemma_fold_left_sum(e2, (n - 1) as nat);
    }
}

/// Trigger helper for e2
spec fn e2_at(e2: spec_fn(real) -> real, i: nat) -> real {
    e2(i as real)
}

/// Lemma: sum of zeros is zero
proof fn lemma_sum_zeros(e2: spec_fn(real) -> real, n: nat)
    requires
        forall |i: nat| i < n ==> #[trigger] e2_at(e2, i) == 0real,
    ensures
        sum_e2(e2, n) == 0real,
    decreases n,
{
    if n > 0 {
        lemma_sum_zeros(e2, (n - 1) as nat);
        let ghost idx: nat = (n - 1) as nat;
        assert(idx < n);
        assert(e2_at(e2, idx) == 0real);
        assert(e2(idx as real) == 0real);
    }
}

/// Lemma: sum of constants
proof fn lemma_sum_constants(e2: spec_fn(real) -> real, start: nat, count: nat, c: real)
    requires
        forall |i: nat| start <= i < start + count ==> #[trigger] e2_at(e2, i) == c,
    ensures
        sum_e2(e2, start + count) - sum_e2(e2, start) == count as real * c,
    decreases count,
{
    if count == 0 {
        assert(sum_e2(e2, start + 0) - sum_e2(e2, start) == 0real);
    } else {
        let ghost idx: nat = (start + count - 1) as nat;
        assert(start <= idx < start + count);
        // Instantiate the forall
        assert(e2_at(e2, idx) == c);
        assert(e2(idx as real) == c);

        lemma_sum_constants(e2, start, (count - 1) as nat, c);
        // IH: sum_e2(e2, start + count - 1) - sum_e2(e2, start) == (count - 1) * c

        // By definition of sum_e2:
        // sum_e2(e2, start + count) = sum_e2(e2, start + count - 1) + e2((start + count - 1) as real)
        assert(sum_e2(e2, (start + count) as nat) == sum_e2(e2, (start + count - 1) as nat) + e2((start + count - 1) as real));

        // Therefore:
        // sum_e2(e2, start + count) - sum_e2(e2, start)
        //   = sum_e2(e2, start + count - 1) + e2(start + count - 1) - sum_e2(e2, start)
        //   = (count - 1) * c + c
        //   = count * c
        assert(sum_e2(e2, start + count) - sum_e2(e2, start) == count as real * c) by(nonlinear_arith)
            requires
                sum_e2(e2, (start + count - 1) as nat) - sum_e2(e2, start) == (count - 1) as real * c,
                sum_e2(e2, (start + count) as nat) == sum_e2(e2, (start + count - 1) as nat) + c,
        ;
    }
}

/// Lemma: sum of threshold_e2
/// Sum = 0 * threshold + amp * eps * (bound - threshold) = bound * eps
proof fn lemma_sum_threshold_e2(bound: u64, threshold: u64, eps: real)
    requires
        bound > 0,
        threshold < bound,
    ensures
        sum_e2(threshold_e2(bound, threshold, eps), bound as nat) == bound as real * eps,
{
    let e2 = threshold_e2(bound, threshold, eps);
    let amp = bound as real / (bound - threshold) as real;

    // Sum over [0, threshold) is 0
    assert forall |i: nat| i < threshold as nat implies #[trigger] e2_at(e2, i) == 0real by {
        assert((i as real) < threshold as real);
    }
    lemma_sum_zeros(e2, threshold as nat);
    assert(sum_e2(e2, threshold as nat) == 0real);

    // Sum over [threshold, bound) is (bound - threshold) * amp * eps
    assert forall |i: nat| threshold as nat <= i < bound as nat implies #[trigger] e2_at(e2, i) == amp * eps by {
        assert(!((i as real) < threshold as real));
    }
    let ghost c = amp * eps;
    lemma_sum_constants(e2, threshold as nat, (bound - threshold) as nat, c);
    // From lemma_sum_constants:
    // sum_e2(e2, threshold + (bound - threshold)) - sum_e2(e2, threshold) == (bound - threshold) * c
    let ghost diff = sum_e2(e2, threshold as nat + (bound - threshold) as nat) - sum_e2(e2, threshold as nat);
    assert(diff == (bound - threshold) as real * c);

    // threshold + (bound - threshold) == bound
    assert((threshold as nat + (bound - threshold) as nat) == bound as nat);

    // So: sum_e2(e2, bound) - sum_e2(e2, threshold) == (bound - threshold) * c
    // which equals sum_e2(e2, threshold) + (bound - threshold) * c

    // (bound - threshold) * c = (bound - threshold) * amp * eps = bound * eps
    assert((bound - threshold) as real * c == bound as real * eps) by(nonlinear_arith)
        requires
            c == amp * eps,
            amp == bound as real / (bound - threshold) as real,
            bound > threshold,
            bound > 0,
    ;

    // sum_e2(e2, threshold) == 0, so:
    // sum_e2(e2, bound) == 0 + bound * eps == bound * eps
}

/// Lemma: eps >= average(bound, threshold_e2)
///
/// Proof sketch:
/// - e2(i) = 0 if i < threshold, else (bound/(bound-threshold)) * eps
/// - Sum = (bound/(bound-threshold)) * eps * (bound - threshold) = eps * bound
/// - Average = eps * bound / bound = eps
/// - So eps >= average holds with equality!
proof fn lemma_average_bound(bound: u64, threshold: u64, eps: real)
    requires
        bound > 0,
        threshold < bound,
        eps > 0real,
    ensures
        eps >= average(bound, threshold_e2(bound, threshold, eps)),
{
    let e2 = threshold_e2(bound, threshold, eps);

    // Show fold_left equals sum_e2
    lemma_fold_left_sum(e2, bound as nat);

    // Show sum_e2 equals bound * eps
    lemma_sum_threshold_e2(bound, threshold, eps);

    // average = sum / bound = (bound * eps) / bound = eps
    assert(average(bound, e2) == eps) by(nonlinear_arith)
        requires
            sum_e2(e2, bound as nat) == bound as real * eps,
            Seq::new(bound as nat, |i: int| i).fold_left(0real, |acc: real, x: int| acc + e2(x as real)) == sum_e2(e2, bound as nat),
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
        Tracked(e): Tracked<ErrorCreditResource>,
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
        // Define error function: 0 if accepted, amp*eps if rejected
        // where amp = bound / (bound - threshold)
        let ghost e2 = threshold_e2(self.bound, self.threshold, eps);

        proof {
            // valid() ensures threshold < bound, which gives us preconditions for lemma_average_bound
            lemma_average_bound(self.bound, self.threshold, eps);
        }

        let (val, Tracked(e1)) = rand_u64(self.bound, Tracked(e), Ghost(e2));

        if val < self.threshold {
            proof {
                assert(e2(val as real) == 0real);
            }
            (val, SampleOutcome::Accepted)
        } else {
            (val, SampleOutcome::Rejected(Tracked(e1)))
        }
    }

    fn check(&self, v: u64) -> (ret: bool)
        ensures ret == (self.check_spec())(v),
    {
        v < self.threshold
    }
}

// ============================================================================
// Example
// ============================================================================

/// Example: Sample from [0, 8) but only accept < 5
/// Rejection rate = 3/8, so amp = 8/3
pub fn example_rejection_sampler() -> (ret: u64)
    ensures ret < 5,
{
    let scheme = UniformThresholdScheme { bound: 8, threshold: 5 };
    proof {
        // valid: threshold < bound (5 < 8 ✓)
        assert(scheme.valid());

        // amp = 8/(8-5) = 8/3 > 1
        lemma_div_gt_1(8real, 3real);
        assert(scheme.amp() > 1real);
    }
    rejection_sampler(&scheme)
}

} // verus!
