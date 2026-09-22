/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Ideal.CutFamily
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity

/-!
# The Bézout potential of iterated retained cut families of affine primes

Let `k` be a field, `σ` a finite type and `Ps` a finite family of prime ideals of
`MvPolynomial σ k`. Write `H(Q)` for `affineHilbertPolynomial Q`. If every polynomial in `cuts` has
total degree at most `b`, the potential `∑ Q, affineDegree Q * b ^ natDegree H(Q)` over the
iterated retained cut family `Ideal.iteratedRetainedCutFamily Ps s cuts` is at most the same sum
over `Ps`.

This is the abstract weight bound `Ideal.sum_iteratedRetainedCutFamily_le` applied to the weight
`affineDegree Q * b ^ natDegree H(Q)`. Its step hypothesis is the one-cut potential bound
`MvPolynomial.sum_affineDegree_mul_pow_retainedMinimalPrimes_le`, which comes from purity of
principal cuts and the Bézout bound. When `1 ≤ b`, the potential of each member dominates its affine
degree, so the affine degrees of the final members sum to at most the initial potential.

## Main statements

* `MvPolynomial.sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le`: the potential does not
  increase.
* `MvPolynomial.sum_affineDegree_iteratedRetainedCutFamily_le`: the total affine degree of the
  final family is at most the initial potential.
* `MvPolynomial.sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le` and
  `MvPolynomial.sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le`: starting
  from the components of a hypersurface `g = 0` with `totalDegree g ≤ v`, the potential is at most
  `v * b ^ (Nat.card σ - 1)` before and after the cuts.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/CutFamily/Iteration.lean`, namespace `AffineHilbert`.

* `sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le` is
  `sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le`. The source hypotheses
  `∀ P ∈ Ps, s ∉ P` and `1 ≤ b` are dropped; primality of `Ps` and the degree bound remain.
* `sum_retainedCutFamily_affineDegree_mul_pow_le` is the case `cuts = [f]`.
* `iteratedRetainedCutFamily_singleton_spec` was the conjunction, for `Ps = {P}`, of the potential
  bound, `Ideal.isPrime_of_mem_iteratedRetainedCutFamily`,
  `Ideal.notMem_of_mem_iteratedRetainedCutFamily`,
  `Ideal.exists_le_of_mem_iteratedRetainedCutFamily` and
  `MvPolynomial.exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus`; it is derived in the
  acceptance tests rather than restated.
* `sum_affineDegree_iteratedRetainedCutFamily_le` is new.

From `ArkLib/ToMathlib/AlgebraicGeometry/CutFamily/Hypersurface.lean`:

* The definitions `hypersurfacePrimeFamily g s` and `hypersurfaceCutFamily g s cuts` are not
  introduced; they are `(Ideal.span {g}).retainedMinimalPrimes s` and
  `Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts`.
* `hypersurfacePrimeFamily_potential_le` is
  `sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le`, with the same hypotheses.
* `hypersurfaceCutFamily_potential_le` is
  `sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le`; the hypothesis `1 ≤ b`
  is dropped.
* `hypersurfacePrimeFamily_prime_open`, `hypersurfaceCutFamily_spec` and
  `hypersurfaceCutFamily_covers` are conjunctions of `Ideal.mem_retainedMinimalPrimes`,
  `Ideal.isPrime_of_mem_iteratedRetainedCutFamily`,
  `Ideal.notMem_of_mem_iteratedRetainedCutFamily`,
  `Ideal.exists_le_of_mem_iteratedRetainedCutFamily`,
  `MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus` and
  `MvPolynomial.exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus`; they are derived in the
  acceptance tests. `hypersurfacePrimeFamily_dimension` is
  `natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton` in
  `ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity`, for every minimal prime of
  `span {g}`; `hypersurfaceCutFamily_dimension_le` is
  `natDegree_affineHilbertPolynomial_le_of_mem` in
  `ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial`, for every ideal containing
  `g`. The
  incidence theorem `hypersurfaceCutFamily_incidence_off_excluded` is
  `MvPolynomial.card_le_of_agreement_off_excluded_of_hypersurface` in
  `ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {k σ : Type*} [Field k] [Finite σ]

/-- The Bézout potential does not increase along an iterated retained cut family. Let every
member of `Ps` be prime and every element of `cuts` have total degree at most `b`. Then the sum of
`affineDegree Q * b ^ natDegree H(Q)` over the iterated family is at most the same sum over `Ps`.

Primality of `Ps` is needed for the first cut: purity of principal cuts fails for non-prime
ideals (see `MvPolynomial.sum_affineDegree_mul_pow_retainedMinimalPrimes_le`). The degree bound is
needed because the Bézout bound for one cut is linear in the degree of the cutting polynomial. No
hypothesis on `s` or on `b` is needed. -/
theorem sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le
    {Ps : Finset (Ideal (MvPolynomial σ k))} (hprime : ∀ P ∈ Ps, P.IsPrime)
    (s : MvPolynomial σ k) {b : ℕ} {cuts : List (MvPolynomial σ k)}
    (hdeg : ∀ f ∈ cuts, f.totalDegree ≤ b) :
    ∑ Q ∈ Ideal.iteratedRetainedCutFamily Ps s cuts,
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      ∑ P ∈ Ps, affineDegree P * (b : ℚ) ^ (affineHilbertPolynomial P).natDegree :=
  Ideal.sum_iteratedRetainedCutFamily_le
    (fun Q ↦ affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree)
    (fun Q ↦ mul_nonneg (affineDegree_nonneg Q) (by positivity)) hprime s cuts
    fun P hP f hf ↦ by
      have := hP
      exact sum_affineDegree_mul_pow_retainedMinimalPrimes_le s (hdeg f hf)

/-- If `1 ≤ b`, the affine degrees of the members of an iterated retained cut family of primes by
polynomials of total degree at most `b` sum to at most the initial potential
`∑ P ∈ Ps, affineDegree P * b ^ natDegree H(P)`.

Each term `affineDegree Q` is at most `affineDegree Q * b ^ natDegree H(Q)` when `1 ≤ b`. The
hypothesis `1 ≤ b` is needed: for `b = 0`, no cuts, and `Ps = {⊥}` in one variable, the left side
is `affineDegree ⊥ = 1` and the right side is `1 * 0 ^ 1 = 0`. -/
theorem sum_affineDegree_iteratedRetainedCutFamily_le
    {Ps : Finset (Ideal (MvPolynomial σ k))} (hprime : ∀ P ∈ Ps, P.IsPrime)
    (s : MvPolynomial σ k) {b : ℕ} (hb : 1 ≤ b) {cuts : List (MvPolynomial σ k)}
    (hdeg : ∀ f ∈ cuts, f.totalDegree ≤ b) :
    ∑ Q ∈ Ideal.iteratedRetainedCutFamily Ps s cuts, affineDegree Q ≤
      ∑ P ∈ Ps, affineDegree P * (b : ℚ) ^ (affineHilbertPolynomial P).natDegree :=
  (Finset.sum_le_sum fun Q _ ↦ le_mul_of_one_le_right (affineDegree_nonneg Q)
    (one_le_pow₀ (by exact_mod_cast hb))).trans
    (sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le hprime s hdeg)

/-- Let `g ≠ 0` with `totalDegree g ≤ v`. Every minimal prime of `span {g}` has natural degree
`Nat.card σ - 1`, so for every `b` the potential of the components retained by `s` is

  `∑ Q, affineDegree Q * b ^ natDegree H(Q) ≤ v * b ^ (Nat.card σ - 1)`.

The affine degrees sum to at most `v` by the Bézout bound
`principalCut_sum_affineDegree_retainedMinimalPrimes_le` applied to `P = ⊥`. The hypothesis
`g ≠ 0` is needed: for `g = 0`, `v = 0`, `s = 1` and `b = 1`, the only component is `⊥`, and the
left side is `1` while the right side is `0`. -/
theorem sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le
    {g : MvPolynomial σ k} (hg : g ≠ 0) (s : MvPolynomial σ k) {v : ℕ} (hv : g.totalDegree ≤ v)
    (b : ℕ) :
    ∑ Q ∈ (Ideal.span {g}).retainedMinimalPrimes s,
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      v * (b : ℚ) ^ (Nat.card σ - 1) := by
  have hsum : ∑ Q ∈ (Ideal.span {g}).retainedMinimalPrimes s, affineDegree Q ≤ v := by
    simpa only [bot_sup_eq, affineDegree_bot, mul_one] using
      principalCut_sum_affineDegree_retainedMinimalPrimes_le (P := ⊥) s
        (by rwa [Ideal.mem_bot]) hv
  calc ∑ Q ∈ (Ideal.span {g}).retainedMinimalPrimes s,
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree
      = (∑ Q ∈ (Ideal.span {g}).retainedMinimalPrimes s, affineDegree Q) *
          (b : ℚ) ^ (Nat.card σ - 1) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun Q hQ ↦ ?_
        have := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hg
          (Ideal.mem_retainedMinimalPrimes.mp hQ).1
        rw [show (affineHilbertPolynomial Q).natDegree = Nat.card σ - 1 by omega]
    _ ≤ v * (b : ℚ) ^ (Nat.card σ - 1) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)

/-- Let `g ≠ 0` with `totalDegree g ≤ v`, and let every polynomial in `cuts` have total degree at
most `b`. Starting from the components of `g = 0` retained by `s` and cutting by `cuts`, the
final potential satisfies

  `∑ Q, affineDegree Q * b ^ natDegree H(Q) ≤ v * b ^ (Nat.card σ - 1)`.

This chains `sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le` with
`sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le`. -/
theorem sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le
    {g : MvPolynomial σ k} (hg : g ≠ 0) (s : MvPolynomial σ k) {v b : ℕ}
    (hv : g.totalDegree ≤ v) {cuts : List (MvPolynomial σ k)}
    (hdeg : ∀ f ∈ cuts, f.totalDegree ≤ b) :
    ∑ Q ∈ Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts,
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      v * (b : ℚ) ^ (Nat.card σ - 1) :=
  (sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le
    (fun _ hP ↦ (Ideal.mem_retainedMinimalPrimes.mp hP).1.isPrime) s hdeg).trans
    (sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le hg s hv b)

end MvPolynomial
