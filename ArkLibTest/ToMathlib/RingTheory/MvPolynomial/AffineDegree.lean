/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree

/-!
# Acceptance tests for the affine degree

The examples compute the affine degree of the polynomial ring, the unit ideal, a hypersurface
`X₀ ^ 3 = 0` in two variables, and a nonzero constant. Combining the hypersurface formula with the
finite-dimensional formula computes `finrank ℚ (ℚ[X₀] ⧸ (X₀ ^ 2)) = 2`. They show that `f ≠ 0` is
needed in `affineDegree_span_singleton` and that the equal-degree hypothesis is needed in
`affineDegree_le_of_le`, and derive the source-shaped statements.
-/

open MvPolynomial Polynomial

namespace AffineDegreeTest

/-- The polynomial ring in two variables has affine degree `1`. -/
example : affineDegree (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) = 1 := affineDegree_bot

/-- The unit ideal has affine degree `0`. -/
example : affineDegree (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) = 0 := affineDegree_top

/-- The hypersurface `X₀ ^ 3 = 0` in two variables has affine degree `3`. -/
example : affineDegree (Ideal.span {(X 0 ^ 3 : MvPolynomial (Fin 2) ℚ)}) = 3 := by
  rw [affineDegree_span_singleton (pow_ne_zero 3 (X_ne_zero 0)), totalDegree_X_pow]
  norm_num

/-- A nonzero constant generates the unit ideal, and both sides of `affineDegree_span_singleton`
are `0`; no properness hypothesis is needed. -/
example : affineDegree (Ideal.span {(C 2 : MvPolynomial (Fin 2) ℚ)}) = 0 := by
  rw [affineDegree_span_singleton (by simp), totalDegree_C, Nat.cast_zero]

/-- The hypothesis `f ≠ 0` of `affineDegree_span_singleton` is needed: `span {0} = ⊥` has affine
degree `1`, while `totalDegree 0 = 0`. -/
example : affineDegree (Ideal.span {(0 : MvPolynomial (Fin 2) ℚ)}) ≠
    ((0 : MvPolynomial (Fin 2) ℚ).totalDegree : ℚ) := by
  rw [Ideal.span_singleton_eq_bot.mpr rfl, affineDegree_bot, totalDegree_zero]
  norm_num

/-- The ideal `(X₀ ^ 2)` in one variable. -/
noncomputable abbrev spanXSq : Ideal (MvPolynomial (Fin 1) ℚ) := Ideal.span {X 0 ^ 2}

theorem affineDegree_spanXSq : affineDegree spanXSq = 2 := by
  rw [affineDegree_span_singleton (pow_ne_zero 2 (X_ne_zero 0)), totalDegree_X_pow]
  norm_num

/-- In one variable the affine Hilbert polynomial of `span {X₀ ^ 2}` has natural degree `0`. -/
theorem natDegree_affineHilbertPolynomial_spanXSq :
    (affineHilbertPolynomial spanXSq).natDegree = 0 := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (pow_ne_zero 2 (X_ne_zero (0 : Fin 1)) : (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) ≠ 0)
    fun h ↦ by
      have h1 := congrArg affineDegree h
      rw [affineDegree_top, affineDegree_spanXSq] at h1
      norm_num at h1
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact Nat.add_right_cancel (m := 1) h

/-- The hypersurface and finite-dimensional formulas together compute
`finrank ℚ (ℚ[X₀] ⧸ (X₀ ^ 2)) = 2`. -/
example : Module.finrank ℚ (MvPolynomial (Fin 1) ℚ ⧸ spanXSq) = 2 := by
  have := natDegree_affineHilbertPolynomial_eq_zero_iff.mp natDegree_affineHilbertPolynomial_spanXSq
  have h := affineDegree_eq_finrank spanXSq
  rw [affineDegree_spanXSq] at h
  exact_mod_cast h.symm

/-- The equal-degree hypothesis of `affineDegree_le_of_le` is needed: `⊥ ≤ span {X₀ ^ 2}` in one
variable, but the affine degrees are `1` and `2`. -/
example : (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ≤ spanXSq ∧
    ¬affineDegree spanXSq ≤ affineDegree (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by
  rw [affineDegree_spanXSq, affineDegree_bot]
  exact ⟨bot_le, by norm_num⟩

/-- The source statement of positivity. -/
example {F σ : Type*} [Field F] [Finite σ] {I : Ideal (MvPolynomial σ F)} (hI : I ≠ ⊤) :
    0 < affineDegree I :=
  affineDegree_pos hI

/-- The source statement for hypersurfaces, which assumed the ideal proper. -/
example {F σ : Type*} [Field F] [Finite σ] {f : MvPolynomial σ F} (hf : f ≠ 0)
    (_hproper : Ideal.span ({f} : Set (MvPolynomial σ F)) ≠ ⊤) :
    affineDegree (Ideal.span {f}) = (f.totalDegree : ℚ) :=
  affineDegree_span_singleton hf

end AffineDegreeTest
