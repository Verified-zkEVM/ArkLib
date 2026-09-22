/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.UnivariateSpecialization
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Acceptance tests for univariate specialization and zeros along one coordinate

* The specialization of `X₀ * X₁` in `X₁` at `x = (3, 5)` evaluates to `3 * 2 = 6` at `2`; the
  value `x 1 = 5` is ignored.
* The parabola `X₁ ^ 2 - X₀` over `ZMod 3` has at most `2 * 3 = 6` zeros at which `2 X₁ ≠ 0`,
  and the zeros `(1, 1)` and `(1, 2)` lie on one line parallel to the `X₁` axis, which is the
  degree bound `2` for that line.
* Over `ZMod 4`, the polynomial `2 X` has the two zeros `0` and `2` with nonzero derivative, more
  than `degreeOf = 1`: the domain hypothesis of the counting theorem cannot be dropped.
-/

namespace MvPolynomial

noncomputable section

/-- The specialization ignores the `X₁` coordinate of the assignment and evaluates `X₀` at `3`. -/
example :
    (univariateSpecialization (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) 1 ![3, 5]).eval 2 = 6 := by
  rw [eval_univariateSpecialization]
  norm_num [Function.update]

/-- The parabola `X₁ ^ 2 - X₀` over `ZMod 3`. -/
private abbrev parabola : MvPolynomial (Fin 2) (ZMod 3) :=
  X 1 ^ 2 - X 0

private theorem degreeOf_parabola_le : parabola.degreeOf 1 ≤ 2 := by
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · simp
  · simp [degreeOf_X]

/-- Zeros of the parabola in `(ZMod 3)²` with `2 X₁ ≠ 0`: at most `2 * 3`, the count computed by
the theorem from `degreeOf 1 = 2` and the three choices of `X₀`. -/
example (T : Finset (Fin 2 → ZMod 3))
    (hT : ∀ x ∈ T, eval x parabola = 0 ∧ eval x (pderiv 1 parabola) ≠ 0) :
    T.card ≤ 6 := by
  have h := card_le_degreeOf_mul_prod_of_eval_pderiv_ne_zero (fun _ ↦ Finset.univ) 1 parabola T
    fun x hx ↦ ⟨by simp, hT x hx⟩
  have hprod : ∏ j ∈ (Finset.univ : Finset (Fin 2)).erase 1,
      (Finset.univ : Finset (ZMod 3)).card = 3 := by decide
  rw [hprod] at h
  have := degreeOf_parabola_le
  omega

/-- The two zeros `(1, 1)` and `(1, 2)` of the parabola share their `X₀` coordinate and have
`2 X₁ ≠ 0`; the specialization `X₁ ^ 2 - 1` on that line has degree `2`, so the bound is
attained on this line. -/
example :
    eval ![1, 1] parabola = 0 ∧ eval ![1, 2] parabola = 0 ∧
      eval ![1, 1] (pderiv 1 parabola) ≠ 0 ∧ eval ![1, 2] (pderiv 1 parabola) ≠ 0 := by
  simp only [parabola, map_sub, map_pow, eval_X, Derivation.leibniz_pow, pderiv_X,
    Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, mul_one,
    sub_zero, nsmul_eq_mul, map_mul, map_natCast]
  decide

/-- Over `ZMod 4`, the degree-one polynomial `2 X` has two zeros with nonzero derivative, so the
bound `degreeOf * ∏ = 1` fails and the domain hypothesis is needed. -/
example :
    ∃ T : Finset (Unit → ZMod 4),
      (∀ x ∈ T, eval x (C 2 * X () : MvPolynomial Unit (ZMod 4)) = 0 ∧
        eval x (pderiv () (C 2 * X () : MvPolynomial Unit (ZMod 4))) ≠ 0) ∧
      (C 2 * X () : MvPolynomial Unit (ZMod 4)).degreeOf () *
          ∏ _j ∈ (Finset.univ : Finset Unit).erase (), (Finset.univ : Finset (ZMod 4)).card <
        T.card := by
  refine ⟨{fun _ ↦ 0, fun _ ↦ 2}, fun x hx ↦ ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      simp only [map_mul, eval_C, eval_X, Derivation.leibniz, pderiv_C, pderiv_X_self, smul_eq_mul,
        mul_one, mul_zero, add_zero] <;> decide
  · have : Fact (1 < 4) := ⟨by norm_num⟩
    have hdeg : (C 2 * X () : MvPolynomial Unit (ZMod 4)).degreeOf () ≤ 1 :=
      (degreeOf_C_mul_le _ _ _).trans_eq (degreeOf_X_self ())
    have hcard : ({fun _ ↦ 0, fun _ ↦ 2} : Finset (Unit → ZMod 4)).card = 2 := by decide
    rw [hcard, Finset.univ_unique, Finset.erase_singleton, Finset.prod_empty, mul_one]
    omega

end

end MvPolynomial
