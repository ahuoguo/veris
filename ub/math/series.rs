/// Real Analysis: Limits, Sequences, and Series
///
/// Partly follows the structure of Dafny-VMC's Math/Analysis library:
///   https://github.com/dafny-lang/Dafny-VMC/tree/main/src/Math/Analysis

use vstd::prelude::*;

verus! {

use crate::math::pow::pow;

// ============================================================================
// Real arithmetic helpers
// ============================================================================

pub open spec fn abs(x: real) -> real {
    if x >= 0real { x } else { -x }
}

pub open spec fn dist(x: real, y: real) -> real {
    abs(x - y)
}

// ============================================================================
// Sequences: nat → real
// ============================================================================

// TODO: do you need this?
/// Trigger helper for sequence evaluation
pub open spec fn seq_at(s: spec_fn(nat) -> real, n: nat) -> real {
    s(n)
}

/// Monotone non-decreasing: s(n) ≤ s(n+1) for all n
pub open spec fn is_nondecreasing(s: spec_fn(nat) -> real) -> bool {
    forall |n: nat| #[trigger] seq_at(s, n) <= seq_at(s, n + 1)
}

/// Bounded above: s(n) ≤ bound for all n
pub open spec fn is_bounded_above(s: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| #[trigger] seq_at(s, n) <= bound
}

/// Pointwise ordering: s1(n) ≤ s2(n) for all n
pub open spec fn seq_leq(s1: spec_fn(nat) -> real, s2: spec_fn(nat) -> real) -> bool {
    forall |n: nat| #[trigger] seq_at(s1, n) <= seq_at(s2, n)
}

// ============================================================================
// Limits (ε-N definition)
//
// ∀ ε > 0. ∃ N. ∀ n ≥ N. |s(n) - L| < ε
// ============================================================================

/// All terms from index start onward are within eps of limit
pub open spec fn suffix_is_close(s: spec_fn(nat) -> real, limit: real, eps: real, start: nat) -> bool {
    forall |n: nat| n >= start ==> dist(#[trigger] seq_at(s, n), limit) < eps
}

/// There exists a suffix within eps of limit
pub open spec fn exists_close_suffix(s: spec_fn(nat) -> real, limit: real, eps: real) -> bool {
    exists |start: nat| suffix_is_close(s, limit, eps, start)
}

/// ε-N convergence: s converges to limit
pub open spec fn converges_to(s: spec_fn(nat) -> real, limit: real) -> bool {
    forall |epsilon: real| epsilon > 0real ==> #[trigger] exists_close_suffix(s, limit, epsilon)
}

/// s converges to some limit
pub open spec fn converges(s: spec_fn(nat) -> real) -> bool {
    exists |limit: real| converges_to(s, limit)
}

// ============================================================================
// Partial sums and series
// ============================================================================

/// Partial sum: s(0) + s(1) + ... + s(n-1)
pub open spec fn partial_sum(s: spec_fn(nat) -> real, n: nat) -> real
    decreases n,
{
    if n == 0 { 0real }
    else { partial_sum(s, (n - 1) as nat) + s((n - 1) as nat) }
}

/// Named wrapper for the sequence of partial sums (avoids lambdas in triggers)
/// x[i] = s(0) + s(1) + ... + s(i-1)
pub open spec fn partial_sum_seq(s: spec_fn(nat) -> real) -> spec_fn(nat) -> real {
    |n: nat| partial_sum(s, n)
}

/// Series s sums to sum: the partial sums converge to sum
pub open spec fn sums_to(s: spec_fn(nat) -> real, sum: real) -> bool {
    converges_to(partial_sum_seq(s), sum)
}

/// Series s is summable (partial sums converge)
pub open spec fn is_summable(s: spec_fn(nat) -> real) -> bool {
    exists |sum: real| sums_to(s, sum)
}

/// All partial sums bounded above (sufficient for convergence with non-negative terms)
pub open spec fn partial_sums_bounded_by(s: spec_fn(nat) -> real, bound: real) -> bool {
    forall |n: nat| bound >= #[trigger] partial_sum(s, n)
}

// ============================================================================
// Geometric series: Σ_{i=0}^∞ (1/2)^(i+1) * e(i)
//
// The weight (1/2)^(i+1) matches the geometric distribution PMF:
// outcome i has probability (1/2)^(i+1) (i tails then 1 heads).
// ============================================================================

/// The weighted summands: (1/2)^(i+1) * e(i)
pub open spec fn geo_summands(e: spec_fn(nat) -> real) -> spec_fn(nat) -> real {
    |i: nat| pow(0.5real, i + 1) * e(i)
}

/// Partial sum of the geometric series: Σ_{i=0}^{n-1} (1/2)^(i+1) * e(i)
pub open spec fn geo_partial_sum(e: spec_fn(nat) -> real, n: nat) -> real {
    partial_sum(geo_summands(e), n)
}

/// ε ≥ Σ_{i=0}^∞ (1/2)^(i+1) * ℰ(i)
///
/// Encoded as: bound is an upper bound for ALL finite partial sums.
pub open spec fn geo_series_bounded_by(e: spec_fn(nat) -> real, bound: real) -> bool {
    partial_sums_bounded_by(geo_summands(e), bound)
}

/// Shifted sequence: e'(i) = e(i + 1)
pub open spec fn shift_e(e: spec_fn(nat) -> real) -> spec_fn(nat) -> real {
    |i: nat| e(i + 1)
}

// ============================================================================
// Arithmetic helper lemmas
// ============================================================================

#[verifier::nonlinear]
proof fn lemma_abs_triangle(a: real, b: real)
    ensures abs(a + b) <= abs(a) + abs(b),
{}

pub proof fn lemma_triangle_inequality(x: real, y: real, z: real)
    ensures dist(x, z) <= dist(x, y) + dist(y, z),
{
    lemma_abs_triangle(x - y, y - z);
}

#[verifier::nonlinear]
pub proof fn lemma_dist_pos(x: real, y: real)
    requires x != y,
    ensures dist(x, y) > 0real,
{}

#[verifier::nonlinear]
pub proof fn lemma_dist_symmetric(x: real, y: real)
    ensures dist(x, y) == dist(y, x),
{}

#[verifier::nonlinear]
pub proof fn lemma_pow_nonneg(x: real, n: nat)
    requires x >= 0real,
    ensures pow(x, n) >= 0real,
    decreases n,
{
    if n > 0 {
        lemma_pow_nonneg(x, (n - 1) as nat);
    }
}

// ============================================================================
// Convergence lemmas
// ============================================================================

/// Limit uniqueness: a sequence cannot converge to two different values
pub proof fn lemma_limit_unique(s: spec_fn(nat) -> real, limit1: real, limit2: real)
    requires
        converges_to(s, limit1),
        converges_to(s, limit2),
    ensures
        limit1 == limit2,
{
    if limit1 != limit2 {
        lemma_dist_pos(limit1, limit2);
        let d = dist(limit1, limit2);
        let half_d = d / 2real;
        assert(half_d > 0real) by(nonlinear_arith)
            requires d > 0real, half_d == d / 2real;

        // Instantiate convergence at ε = d/2
        assert(exists_close_suffix(s, limit1, half_d));
        assert(exists_close_suffix(s, limit2, half_d));
        let n1: nat = choose |start: nat| suffix_is_close(s, limit1, half_d, start);
        let n2: nat = choose |start: nat| suffix_is_close(s, limit2, half_d, start);
        let n: nat = if n1 >= n2 { n1 } else { n2 };

        // Both distances < d/2
        assert(dist(seq_at(s, n), limit1) < half_d);
        assert(dist(seq_at(s, n), limit2) < half_d);

        // Triangle inequality + symmetry give contradiction
        lemma_triangle_inequality(limit1, s(n), limit2);
        lemma_dist_symmetric(limit1, s(n));

        assert(false) by(nonlinear_arith)
            requires
                d > 0real,
                half_d == d / 2real,
                d <= dist(limit1, s(n)) + dist(s(n), limit2),
                dist(limit1, s(n)) == dist(s(n), limit1),
                dist(s(n), limit1) < half_d,
                dist(s(n), limit2) < half_d,
        ;
    }
}

/// Monotone convergence: a bounded non-decreasing sequence converges
/// (Requires completeness of reals — axiomatized)
#[verifier::external_body]
pub proof fn lemma_monotone_convergence(s: spec_fn(nat) -> real, bound: real)
    requires
        is_nondecreasing(s),
        is_bounded_above(s, bound),
    ensures
        converges(s),
{
}

/// Partial sums of non-negative terms are non-decreasing
pub proof fn lemma_partial_sums_nondecreasing(s: spec_fn(nat) -> real)
    requires
        forall |n: nat| #[trigger] seq_at(s, n) >= 0real,
    ensures
        is_nondecreasing(partial_sum_seq(s)),
{
    assert forall |m: nat|
        #[trigger] seq_at(partial_sum_seq(s), m)
            <= seq_at(partial_sum_seq(s), m + 1)
    by {
        assert(seq_at(s, m) >= 0real);
    };
}

/// Bounded non-negative series is summable
pub proof fn lemma_bounded_series_summable(s: spec_fn(nat) -> real, bound: real)
    requires
        forall |n: nat| #[trigger] seq_at(s, n) >= 0real,
        partial_sums_bounded_by(s, bound),
    ensures
        is_summable(s),
{
    lemma_partial_sums_nondecreasing(s);

    assert forall |m: nat|
        #[trigger] seq_at(partial_sum_seq(s), m) <= bound
    by {
        assert(bound >= partial_sum(s, m));
    };

    lemma_monotone_convergence(partial_sum_seq(s), bound);

    let limit: real = choose |limit: real| converges_to(partial_sum_seq(s), limit);
    assert(sums_to(s, limit));
}

// ============================================================================
// Geometric series lemmas
// ============================================================================

/// First-step decomposition of the geometric partial sum:
///   geo_partial_sum(e, n+1) = 0.5·e(0) + 0.5·geo_partial_sum(shift_e(e), n)
proof fn lemma_series_first_step(e: spec_fn(nat) -> real, n: nat)
    ensures
        geo_partial_sum(e, n + 1) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), n),
    decreases n,
{
    if n == 0 {
        assert(pow(0.5real, 0nat) == 1real);
        assert(geo_partial_sum(e, 1nat) == 0.5real * e(0nat)) by(nonlinear_arith)
            requires
                geo_partial_sum(e, 1nat) == geo_partial_sum(e, 0nat) + geo_summands(e)(0nat),
                geo_partial_sum(e, 0nat) == 0real,
                geo_summands(e)(0nat) == pow(0.5real, 0nat + 1) * e(0nat),
                pow(0.5real, 1nat) == 0.5real * pow(0.5real, 0nat),
                pow(0.5real, 0nat) == 1real;
    } else {
        lemma_series_first_step(e, (n - 1) as nat);
        assert(pow(0.5real, n + 1) == 0.5real * pow(0.5real, n));
        assert(geo_partial_sum(e, n + 1) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), n))
            by(nonlinear_arith)
            requires
                geo_partial_sum(e, n) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), (n - 1) as nat),
                geo_partial_sum(e, n + 1) == geo_partial_sum(e, n) + geo_summands(e)(n),
                geo_partial_sum(shift_e(e), n) == geo_partial_sum(shift_e(e), (n - 1) as nat) + geo_summands(shift_e(e))((n - 1) as nat),
                geo_summands(e)(n) == pow(0.5real, n + 1) * e(n),
                geo_summands(shift_e(e))((n - 1) as nat) == pow(0.5real, n) * e(n),
                pow(0.5real, n + 1) == 0.5real * pow(0.5real, n),
        ;
    }
}

/// Distribution bound transfers through recursion:
///   geo_series_bounded_by(e, eps - slack)
///   ⟹ geo_series_bounded_by(shift_e(e), (2eps - e(0)) - 2·slack)
///
/// Proof:
/// S1 = (1/2)e_0 + (1/4)e_1  + ...
/// S2 = (1/2)e_1 + (1/4)e_2  + ...
/// S1 = (1/2)e_0 + (1/2) S2
/// so if S1 ≤ eps - slack and e_0 ≥ 0, then S2 ≤ 2eps - e_0 - 2slack
pub proof fn lemma_shift_bound(e: spec_fn(nat) -> real, eps: real, slack: real)
    requires
        forall |i: nat| (#[trigger] e(i)) >= 0real,
        geo_series_bounded_by(e, eps - slack),
    ensures
        geo_series_bounded_by(
            shift_e(e),
            (2real * eps - e(0nat)) - 2real * slack,
        ),
{
    assert forall |n: nat| ((2real * eps - e(0nat)) - 2real * slack)
        >= #[trigger] partial_sum(geo_summands(shift_e(e)), n) by
    {
        lemma_series_first_step(e, n);
        assert(eps - slack >= partial_sum(geo_summands(e), n + 1));
        assert(((2real * eps - e(0nat)) - 2real * slack) >= partial_sum(geo_summands(shift_e(e)), n))
            by(nonlinear_arith) requires
                geo_partial_sum(e, n + 1) == 0.5real * e(0nat) + 0.5real * geo_partial_sum(shift_e(e), n),
                eps - slack >= geo_partial_sum(e, n + 1),
                e(0nat) >= 0real,
                geo_partial_sum(shift_e(e), n) == partial_sum(geo_summands(shift_e(e)), n);
    };
}

/// Bounded geometric series is summable (converges via monotone convergence)
pub proof fn lemma_geo_series_summable(e: spec_fn(nat) -> real, bound: real)
    requires
        forall |i: nat| #[trigger] seq_at(e, i) >= 0real,
        geo_series_bounded_by(e, bound),
    ensures
        is_summable(geo_summands(e)),
{
    // geo_summands have non-negative terms
    assert forall |n: nat| #[trigger] seq_at(geo_summands(e), n) >= 0real by {
        assert(seq_at(e, n) >= 0real);
        lemma_pow_nonneg(0.5real, n + 1);
        assert(geo_summands(e)(n) >= 0real) by(nonlinear_arith)
            requires pow(0.5real, n + 1) >= 0real, e(n) >= 0real;
    };

    lemma_bounded_series_summable(geo_summands(e), bound);
}

} // verus!
