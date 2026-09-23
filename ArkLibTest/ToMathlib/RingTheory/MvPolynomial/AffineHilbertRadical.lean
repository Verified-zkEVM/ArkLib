/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertRadical

/-!
# Acceptance tests for the affine Hilbert polynomial of a radical

In one variable, `I = (X₀ ^ 2)` and `J = (X₀)` satisfy `J ^ 2 = I ≤ J`. The examples compute the
Hilbert function bound `H(I, N) ≤ 2 * H(J, N)` at `N = 2`, where it is an equality `2 = 2 * 1`,
and show that the natural degrees agree while the affine degrees `2` and `1` differ, so only the
natural degree is preserved. They show that the inclusion `I ≤ J` is needed for equality of
natural degrees, and derive the floor-division identity, the standard-exponent step for `degLex`
with `0 < t`, the Hilbert function bound with `Fintype.card σ`, and the radical statement.
-/

open MvPolynomial Polynomial
open scoped MonomialOrder

namespace AffineHilbertRadicalTest

/-- The ideal `(X₀ ^ 2)` in one variable. -/
noncomputable abbrev spanXSq : Ideal (MvPolynomial (Fin 1) ℚ) := Ideal.span {X 0 ^ 2}

/-- The ideal `(X₀)` in one variable. -/
noncomputable abbrev spanX : Ideal (MvPolynomial (Fin 1) ℚ) := Ideal.span {X 0}

theorem spanX_sq : spanX ^ 2 = spanXSq := Ideal.span_singleton_pow _ 2

theorem spanXSq_le_spanX : spanXSq ≤ spanX :=
  Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ two_ne_zero)

/-- The bound `H(I, N) ≤ 2 ^ 1 * H(J, N)` of `affineHilbertFunction_le_pow_mul_of_pow_le` is
attained at `N = 2`: `H(I, 2) = 2` counts `1, X₀` and `H(J, 2) = 1` counts `1`. -/
example :
    affineHilbertFunction spanXSq 2 = 2 ^ Nat.card (Fin 1) * affineHilbertFunction spanX 2 := by
  have hI := affineHilbertFunction_span_singleton
    (pow_ne_zero 2 (X_ne_zero (0 : Fin 1)) : (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) ≠ 0)
    (N := 2) (by rw [totalDegree_X_pow])
  have hJ := affineHilbertFunction_span_singleton
    (X_ne_zero (0 : Fin 1) : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0)
    (N := 2) (by rw [totalDegree_X]; norm_num)
  rw [totalDegree_X_pow, Nat.card_eq_fintype_card, Fintype.card_fin] at hI
  rw [totalDegree_X, Nat.card_eq_fintype_card, Fintype.card_fin] at hJ
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num [Nat.choose] at hI hJ
  have hI' : affineHilbertFunction spanXSq 2 = 2 := by exact_mod_cast hI
  have hJ' : affineHilbertFunction spanX 2 = 1 := by exact_mod_cast hJ
  rw [hI', hJ']
  norm_num

/-- `(X₀ ^ 2)` and `(X₀)` have affine Hilbert polynomials of the same natural degree, but
different affine degrees `2` and `1`: the leading coefficient is not preserved. -/
example : (affineHilbertPolynomial spanX).natDegree = (affineHilbertPolynomial spanXSq).natDegree ∧
    affineDegree spanXSq = 2 ∧ affineDegree spanX = 1 := by
  refine ⟨natDegree_affineHilbertPolynomial_eq_of_pow_le_of_le spanX_sq.le spanXSq_le_spanX, ?_,
    ?_⟩
  · rw [affineDegree_span_singleton (pow_ne_zero 2 (X_ne_zero 0)), totalDegree_X_pow]
    norm_num
  · rw [affineDegree_span_singleton (X_ne_zero 0), totalDegree_X]
    norm_num

/-- The inclusion `I ≤ J` is needed for equality of natural degrees: `J = (X₀)` in two variables
satisfies `J ^ 1 ≤ ⊤`, but `⊤` has natural degree `0` and `J` has natural degree `1`. -/
example : (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) ^ 1 ≤ ⊤ ∧
    (affineHilbertPolynomial (⊤ : Ideal (MvPolynomial (Fin 2) ℚ))).natDegree ≠
      (affineHilbertPolynomial (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)})).natDegree := by
  refine ⟨le_top, ?_⟩
  have hne : Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ≠ ⊤ := fun h ↦ by
    have h1 := congrArg affineDegree h
    rw [affineDegree_top, affineDegree_span_singleton (X_ne_zero 0), totalDegree_X] at h1
    norm_num at h1
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one (X_ne_zero 0) hne
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  rw [affineHilbertPolynomial_top, natDegree_zero]
  omega

/-- Floor division is coordinatewise natural division. -/
example {σ : Type*} (t : ℕ) (e : σ →₀ ℕ) (i : σ) : (e ⌊/⌋ t) i = e i / t := rfl

/-- The standard-exponent step for `degLex`, with the extra hypothesis `0 < t`. -/
example {F σ : Type*} [Field F] [LinearOrder σ] [WellFoundedGT σ] {I J : Ideal (MvPolynomial σ F)}
    {t : ℕ} (_ht : 0 < t) (hpow : J ^ t ≤ I) {e : σ →₀ ℕ}
    (he : e ∈ MonomialOrder.degLex.standardExponents I) :
    e ⌊/⌋ t ∈ MonomialOrder.degLex.standardExponents J :=
  MonomialOrder.degLex.floorDiv_mem_standardExponents hpow he

/-- The Hilbert function bound with `Fintype.card σ` and the extra hypothesis `0 < t`. -/
example {F σ : Type*} [Field F] [Fintype σ] {I J : Ideal (MvPolynomial σ F)} {t : ℕ}
    (_ht : 0 < t) (hpow : J ^ t ≤ I) (N : ℕ) :
    affineHilbertFunction I N ≤ affineHilbertFunction J N * t ^ Fintype.card σ := by
  rw [mul_comm, ← Nat.card_eq_fintype_card]
  exact affineHilbertFunction_le_pow_mul_of_pow_le hpow N

/-- The radical has an affine Hilbert polynomial of the same natural degree. -/
example {F σ : Type*} [Field F] [Finite σ] (I : Ideal (MvPolynomial σ F)) :
    (affineHilbertPolynomial I.radical).natDegree = (affineHilbertPolynomial I).natDegree :=
  natDegree_affineHilbertPolynomial_radical I

end AffineHilbertRadicalTest
