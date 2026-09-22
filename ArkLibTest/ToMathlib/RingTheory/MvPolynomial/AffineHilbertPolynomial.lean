/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial

/-!
# Acceptance tests for the affine Hilbert polynomial

The examples compute the affine Hilbert polynomial of the zero ideal in two variables, of the unit
ideal, and of the line `X₀ = 0` in two variables (natural degree `1`) and the point `X₀ = 0` in one
variable (natural degree `0`, hence a finite-dimensional quotient). They show that the regularity
hypothesis of the principal-cut degree drop is needed: for `I = (X₀²)` and `f = X₀` in one
variable the coefficient bound reads `1 ≤ 0`. They also derive uniqueness from an eventual
agreement, the prime-ideal principal cut with the disjunct `= 0`, and the comparison with the
extra hypothesis that the larger ideal is proper, from the general statements.
-/

open MvPolynomial Polynomial Filter

namespace AffineHilbertPolynomialTest

/-- The variable `X₀` is not a unit: evaluating a relation `a * X₀ = 1` at the origin gives
`0 = 1`. -/
theorem not_isUnit_X_zero {n : ℕ} : ¬IsUnit (X 0 : MvPolynomial (Fin (n + 1)) ℚ) := by
  rintro ⟨u, hu⟩
  have h := congrArg (MvPolynomial.eval (0 : Fin (n + 1) → ℚ)) u.inv_mul
  rw [hu] at h
  simp at h

theorem span_X_zero_ne_top {n : ℕ} :
    Ideal.span {(X 0 : MvPolynomial (Fin (n + 1)) ℚ)} ≠ ⊤ :=
  fun h ↦ not_isUnit_X_zero (Ideal.span_singleton_eq_top.mp h)

/-- A polynomial that eventually agrees with the affine Hilbert function is the affine Hilbert
polynomial. -/
example {k σ : Type*} [Field k] [Finite σ] (I : Ideal (MvPolynomial σ k)) {P : ℚ[X]}
    (hP : ∃ N₀ : ℕ, ∀ N ≥ N₀, P.eval (N : ℚ) = (affineHilbertFunction I N : ℚ)) :
    P = affineHilbertPolynomial I :=
  let ⟨_, h⟩ := hP
  eq_affineHilbertPolynomial_of_eval_eq h

/-- The principal-cut degree drop for a prime ideal, with the disjunct that the polynomial of the
cut is `0`. -/
example {k σ : Type*} [Field k] [Finite σ] {I : Ideal (MvPolynomial σ k)} (hI : I.IsPrime)
    {f : MvPolynomial σ k} (hfI : f ∉ I) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    affineHilbertPolynomial (I ⊔ Ideal.span {f}) = 0 ∨
      (affineHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤
          (affineHilbertPolynomial I).natDegree - 1 ∧
        (affineHilbertPolynomial (I ⊔ Ideal.span {f})).coeff
            ((affineHilbertPolynomial I).natDegree - 1) ≤
          (b : ℚ) * (affineHilbertPolynomial I).natDegree *
            (affineHilbertPolynomial I).leadingCoeff :=
  Or.inr (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime hI hfI hfdeg)

/-- The comparison along an inclusion, with the extra hypothesis that the larger ideal is proper. -/
example {k σ : Type*} [Field k] [Finite σ] {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J)
    (_hJ : J ≠ ⊤) :
    (affineHilbertPolynomial J).natDegree ≤ (affineHilbertPolynomial I).natDegree ∧
      ((affineHilbertPolynomial J).natDegree = (affineHilbertPolynomial I).natDegree →
        (affineHilbertPolynomial J).leadingCoeff ≤ (affineHilbertPolynomial I).leadingCoeff) :=
  ⟨natDegree_affineHilbertPolynomial_le_of_le hIJ,
    leadingCoeff_affineHilbertPolynomial_le_of_le hIJ⟩

/-- In two variables the zero ideal has affine Hilbert polynomial of natural degree `2`, and its
value at `1` is the number `3` of monomials `1, X₀, X₁`. -/
example : (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))).natDegree = 2 ∧
    (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))).eval 1 = 3 := by
  refine ⟨by simp, ?_⟩
  rw [affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin,
    show (1 : ℚ) = ((1 : ℕ) : ℚ) by norm_num,
    preHilbertPoly_eq_choose_add_sub ℚ 2 (Nat.zero_le _)]
  norm_num [Nat.choose]

/-- The unit ideal has the zero affine Hilbert polynomial. -/
example : affineHilbertPolynomial (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) = 0 := by
  simp

/-- The line `X₀ = 0` in two variables has affine Hilbert polynomial of natural degree `1`. -/
example : (affineHilbertPolynomial
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)})).natDegree = 1 := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one (X_ne_zero 0)
    (span_X_zero_ne_top (n := 1))
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- The point `X₀ = 0` in one variable has affine Hilbert polynomial of natural degree `0`, so its
coordinate ring is finite-dimensional. -/
example : Module.Finite ℚ
    (MvPolynomial (Fin 1) ℚ ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one (X_ne_zero 0)
    (span_X_zero_ne_top (n := 0))
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact natDegree_affineHilbertPolynomial_eq_zero_iff.mp (by omega)

/-- The affine Hilbert polynomial of `span {f}` for nonzero `f` of total degree `d` in one
variable is `preHilbertPoly ℚ 1 0` minus its shift by `d`: its natural degree is `0`, and its
constant coefficient is `d`. -/
theorem affineHilbertPolynomial_span_singleton_fin_one {f : MvPolynomial (Fin 1) ℚ}
    (hf : f ≠ 0) (hd : 0 < f.totalDegree) :
    (affineHilbertPolynomial (Ideal.span {f})).natDegree = 0 ∧
      (affineHilbertPolynomial (Ideal.span {f})).coeff 0 = f.totalDegree := by
  have hP : (preHilbertPoly ℚ 1 0).natDegree = 1 := natDegree_preHilbertPoly ℚ 1 0
  have hlc : (preHilbertPoly ℚ 1 0).leadingCoeff = 1 := by
    rw [leadingCoeff_preHilbertPoly]
    simp
  rw [affineHilbertPolynomial_span_singleton hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h := natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (Nat.cast_ne_zero.mpr hd.ne') (by rw [hP]; exact Nat.one_pos)
  rw [hP, Nat.sub_self] at h
  refine ⟨h.1, ?_⟩
  have hc := coeff_natDegree (p := backwardDifference (f.totalDegree : ℚ) (preHilbertPoly ℚ 1 0))
  rw [h.1, h.2, hlc] at hc
  rw [hc]
  simp

/-- The ideal `(X₀²)` in one variable. -/
noncomputable abbrev spanXSq : Ideal (MvPolynomial (Fin 1) ℚ) := Ideal.span {X 0 ^ 2}

/-- The regularity hypothesis of the principal-cut degree drop is needed. In one variable take
`I = (X₀²)`, `f = X₀` and `b = 1`; the class of `X₀` is a zero divisor modulo `X₀²`. The affine
Hilbert polynomial of `I` is the constant `2`, of natural degree `0`, and that of
`I ⊔ span {X₀} = span {X₀}` is the constant `1`. The coefficient bound would read `1 ≤ 0`. -/
example :
    ¬(affineHilbertPolynomial (spanXSq ⊔ Ideal.span {X 0})).coeff
        ((affineHilbertPolynomial spanXSq).natDegree - 1) ≤
      (1 : ℚ) * (affineHilbertPolynomial spanXSq).natDegree *
        (affineHilbertPolynomial spanXSq).leadingCoeff := by
  have hsup : spanXSq ⊔ Ideal.span {X 0} = Ideal.span {X 0} :=
    sup_eq_right.mpr (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ two_ne_zero))
  have hX2 := affineHilbertPolynomial_span_singleton_fin_one
    (pow_ne_zero 2 (X_ne_zero (0 : Fin 1) : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0))
    (by rw [totalDegree_X_pow]; norm_num)
  have hX := affineHilbertPolynomial_span_singleton_fin_one
    (X_ne_zero (0 : Fin 1) : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0) (by rw [totalDegree_X]; norm_num)
  rw [hsup, hX2.1, hX.2, totalDegree_X]
  norm_num

end AffineHilbertPolynomialTest
