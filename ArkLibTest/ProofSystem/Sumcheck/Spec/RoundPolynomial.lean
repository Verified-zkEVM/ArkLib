/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import ArkLib.ProofSystem.Sumcheck.Spec.RoundPolynomial
import Mathlib.FieldTheory.Finite.Basic

/-! # Polynomial and selected-coordinate degree controls for honest sumcheck rounds -/

namespace Sumcheck.Spec.SingleRound.RoundPolynomialTest

open MvPolynomial

noncomputable section

/-- The polynomial does not depend on coordinate one, despite its global degree cap three. -/
def polynomial : OracleStatement ℤ 2 3 () := ⟨X 0, by
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  simp only [degreeOf_X]
  split <;> omega⟩

/-- A singleton domain is sufficient for this last-round control. -/
def domain : Fin 1 ↪ ℤ := ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- A previously fixed coordinate yields a constant polynomial in the final round. -/
theorem last_round_constant :
    (projectedRoundPolynomial ℤ 2 3 domain 1 (fun _ ↦ 5) polynomial).val =
      Polynomial.C 5 := by
  rw [projectedRoundPolynomial_eq_sum_eval₂]
  have h (s : Fin 1 → Polynomial ℤ) :
      Fin.insertNth (α := fun _ : Fin 2 ↦ Polynomial ℤ) 1 Polynomial.X s 0 = s 0 := by
    rw [Fin.insertNth_apply_below (by decide)]
    rfl
  simp [polynomial, roundSuffix, h, Fin.append, Fin.addCases]

/-- The coordinate bound is zero, sharper than the global cap three. -/
theorem last_round_degree_zero :
    (projectedRoundPolynomial ℤ 2 3 domain 1 (fun _ ↦ 5) polynomial).val.natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [polynomial, degreeOf_X] using
    projectedRoundPolynomial_natDegree_le (n := 1) (deg := 3) domain
      (1 : Fin 2) (fun _ ↦ 5) polynomial

/-- Direct polynomial substitution retains a square even over the two-element field. -/
theorem finite_field_square :
    Polynomial.map (MvPolynomial.eval (Fin.elim0 : Fin 0 → ZMod 2))
      (finSuccEquivNth (ZMod 2) 0 ((X 0 : MvPolynomial (Fin 1) (ZMod 2)) ^ 2)) =
      Polynomial.X ^ 2 := by
  rw [map_finSuccEquivNth_eq_eval₂_insertNth]
  simp

/-- Equal value tables over the two-element field do not identify these polynomials. -/
theorem square_ne_linear : (Polynomial.X : Polynomial (ZMod 2)) ^ 2 ≠ Polynomial.X := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) ↦ p.coeff 2) h
  norm_num [Polynomial.coeff_X] at hc

/-- The distinct square and linear polynomials nevertheless agree at every field element. -/
theorem square_eval_eq_linear (r : ZMod 2) :
    Polynomial.eval r (Polynomial.X ^ 2) = Polynomial.eval r Polynomial.X := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using ZMod.pow_card r

/-- Reversing coordinates binds the original linear variable first, not the squared one. -/
theorem reversed_coordinate :
    Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (5 : ℤ)))
      (finSuccEquivNth ℤ (0 : Fin 2)
        (rename Fin.rev (X 0 ^ 2 + C 3 * X 1))) =
      Polynomial.C 25 + Polynomial.C 3 * Polynomial.X := by
  rw [map_finSuccEquivNth_eq_eval₂_insertNth]
  norm_num [MvPolynomial.eval₂_rename, Fin.rev, Fin.insertNth, Fin.succAboveCases]

/-- The substitution identity also accepts a trivial semiring. -/
theorem trivial_semiring_substitution (p : MvPolynomial (Fin 1) (ZMod 1)) :
    Polynomial.map (MvPolynomial.eval (Fin.elim0 : Fin 0 → ZMod 1))
      (finSuccEquivNth (ZMod 1) 0 p) =
      MvPolynomial.eval₂ Polynomial.C
        (Fin.insertNth 0 Polynomial.X (fun i : Fin 0 ↦ Polynomial.C (Fin.elim0 i))) p :=
  map_finSuccEquivNth_eq_eval₂_insertNth 0 Fin.elim0 p

end
end Sumcheck.Spec.SingleRound.RoundPolynomialTest
