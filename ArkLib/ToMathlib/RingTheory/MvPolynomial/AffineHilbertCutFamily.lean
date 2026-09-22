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

end MvPolynomial
