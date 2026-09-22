/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbert

/-!
# Acceptance tests for the affine Hilbert function

The examples compute the affine Hilbert function at degree zero for proper and unit ideals, show
that the principal-cut inequality fails without its hypothesis `b ≤ N`, and derive the prime-ideal
form of the inequality from the regular-element form.
-/

open MvPolynomial

namespace AffineHilbertTest

/-- The variable `X₀` is not a unit: evaluating a relation `a * X₀ = 1` at the origin gives
`0 = 1`. -/
theorem not_isUnit_X_zero : ¬IsUnit (X 0 : MvPolynomial (Fin 1) ℚ) := by
  rintro ⟨u, hu⟩
  have h := congrArg (eval (0 : Fin 1 → ℚ)) u.inv_mul
  rw [hu] at h
  simp at h

/-- The unit ideal has quotient zero, so its Hilbert function vanishes identically. -/
example (N : ℕ) : affineHilbertFunction (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) N = 0 := by
  simp

/-- A proper ideal has Hilbert function `1` at degree zero: only the constants survive. -/
example : affineHilbertFunction (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) 0 = 1 := by
  classical
  simp [affineHilbertFunction_zero, not_isUnit_X_zero]

/-- The hypothesis `b ≤ N` of the principal-cut inequality is needed. Take `I = ⊥` in one
variable, `f = X₀`, `b = 1` and `N = 0`. The element `X₀` is regular modulo `⊥` and has total
degree `1`, but the left side is `1 + 1` (natural subtraction gives `N - b = 0`) while the right
side is `1`. -/
example :
    IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (X 0)) ∧
      (X 0 : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1 ∧
      ¬(affineHilbertFunction ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ⊔ Ideal.span {X 0}) 0 +
          affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 - 1) ≤
        affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0) := by
  classical
  refine ⟨IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ?_, by simp, ?_⟩
  · rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact X_ne_zero 0
  · simp [affineHilbertFunction_zero, not_isUnit_X_zero]

/-- The principal-cut inequality for a prime ideal `I` and `f ∉ I`, derived from the
regular-element form. -/
example {σ : Type*} [Finite σ] {I : Ideal (MvPolynomial σ ℚ)} (hI : I.IsPrime)
    {f : MvPolynomial σ ℚ} (hfI : f ∉ I) {b N : ℕ} (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    affineHilbertFunction (I ⊔ Ideal.span {f}) N + affineHilbertFunction I (N - b) ≤
      affineHilbertFunction I N := by
  have := hI
  exact principalCut_affineHilbertFunction_add_le
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hfI)) hfdeg hbN

/-- Inside its range the principal cut applies to `I = ⊥`, `f = X₀`: at degree `N = 1` the cut
ideal `(X₀)` contributes at most `H(⊥, 1) - H(⊥, 0)`. -/
example :
    affineHilbertFunction ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ⊔ Ideal.span {X 0}) 1 +
        affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0 ≤
      affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 := by
  simpa using principalCut_affineHilbertFunction_add_le_of_isPrime (σ := Fin 1) (k := ℚ)
    (b := 1) (N := 1) Ideal.isPrime_bot (f := X 0)
    (by rw [Ideal.mem_bot]; exact X_ne_zero 0) (by simp) le_rfl

/-- A finite-dimensional quotient has eventually constant Hilbert function equal to its
dimension. -/
example {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ ℚ))
    [Module.Finite ℚ (MvPolynomial σ ℚ ⧸ I)] :
    ∃ N₀, ∀ N ≥ N₀, affineHilbertFunction I N = Module.finrank ℚ (MvPolynomial σ ℚ ⧸ I) :=
  exists_affineHilbertFunction_eq_finrank I

/-- Multiplicativity of the filtration: the class of `3 * X₀ * X₁` lies in the piece of degree
`2`, built from scalars in degree `0` and variables in degree `1`. -/
example (I : Ideal (MvPolynomial (Fin 2) ℚ)) :
    algebraMap ℚ _ 3 * Ideal.Quotient.mk I (X 0) * Ideal.Quotient.mk I (X 1) ∈
      quotientDegreeLE I 2 := by
  have h01 := mul_mem_quotientDegreeLE (algebraMap_mem_quotientDegreeLE I 3 0)
    (mk_X_mem_quotientDegreeLE I 0)
  have h := mul_mem_quotientDegreeLE h01 (mk_X_mem_quotientDegreeLE I 1)
  simpa using h

end AffineHilbertTest
