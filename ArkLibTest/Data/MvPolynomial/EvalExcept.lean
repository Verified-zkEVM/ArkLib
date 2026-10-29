/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors, Elias Judin
-/
import ArkLib.Data.MvPolynomial.EvalExcept
import Mathlib.FieldTheory.Finite.Basic

/-! # Coordinate-line restriction controls

These ordinary-import clients retain the finite-field, coordinate-order, and trivial-semiring
controls from PR #1128, and exercise empty tails and heterogeneous domain sums.
-/

namespace MvPolynomial.EvalExceptTest

open MvPolynomial Finset

noncomputable section

/-- Restriction fixes the only variable on which the source depends. -/
example : (X 0 : MvPolynomial (Fin 2) ℤ).evalExcept 1 (fun _ => 5) = Polynomial.C 5 := by
  simp [evalExcept, map_finSuccEquivNth_eq_eval₂_insertNth,
    Fin.insertNth, Fin.succAboveCases]

/-- The selected coordinate has degree zero despite a nonconstant source. -/
example : (evalExcept (1 : Fin 2) (fun _ : Fin 1 => (5 : ℤ)) (X 0)).natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [degreeOf_X] using natDegree_evalExcept_le
    (1 : Fin 2) (fun _ : Fin 1 => (5 : ℤ)) (X 0)

/-- Direct substitution retains a square over the two-element field. -/
example :
    ((X 0 : MvPolynomial (Fin 1) (ZMod 2)) ^ 2).evalExcept 0 Fin.elim0 =
      Polynomial.X ^ 2 := by
  rw [evalExcept_eq_eval₂_insertNth]
  simp

/-- Equal value tables over a finite field do not identify polynomials. -/
example : (Polynomial.X : Polynomial (ZMod 2)) ^ 2 ≠ Polynomial.X := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 2) h
  norm_num [Polynomial.coeff_X] at hc

example (r : ZMod 2) :
    Polynomial.eval r (Polynomial.X ^ 2) = Polynomial.eval r Polynomial.X := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using ZMod.pow_card r

/-- Reversing coordinates selects the original linear variable. -/
example :
    (rename Fin.rev (X 0 ^ 2 + C 3 * X 1) : MvPolynomial (Fin 2) ℤ).evalExcept
      0 (fun _ => 5) =
      Polynomial.C 25 + Polynomial.C 3 * Polynomial.X := by
  rw [evalExcept_eq_eval₂_insertNth]
  norm_num [MvPolynomial.eval₂_rename, Fin.rev, Fin.insertNth, Fin.succAboveCases]

/-- The substitution identity needs no nontriviality assumption. -/
example (p : MvPolynomial (Fin 1) (ZMod 1)) :
    Polynomial.map (MvPolynomial.eval (Fin.elim0 : Fin 0 → ZMod 1))
      (finSuccEquivNth (ZMod 1) 0 p) =
      MvPolynomial.eval₂ Polynomial.C
        (Fin.insertNth 0 Polynomial.X (fun i : Fin 0 => Polynomial.C (Fin.elim0 i))) p :=
  map_finSuccEquivNth_eq_eval₂_insertNth 0 Fin.elim0 p

/-- A three-point suffix domain produces the residual polynomial `3 X² + 9`. -/
example :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin 1 => ({2, 3, 4} : Finset ℤ)),
      (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) ℤ).evalExcept 0 x) =
        Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 9 := by
  simp only [evalExcept, map_finSuccEquivNth_eq_eval₂_insertNth]
  rw [Fin.sum_piFinset_cons]
  norm_num
  ring

/-- Different domains on the two coordinates recover the concrete previous sum `21`. -/
example :
    ∑ a ∈ ({0, 1} : Finset ℤ),
      (∑ x ∈ Fintype.piFinset (fun _ : Fin 1 => ({2, 3, 4} : Finset ℤ)),
        (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) ℤ).evalExcept 0 x).eval a = 21 := by
  calc
    _ = ∑ x ∈ Fintype.piFinset ![({0, 1} : Finset ℤ), {2, 3, 4}],
        (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) ℤ).eval x := by
      simp only [Polynomial.eval_finsetSum]
      exact sum_eval_evalExcept_zero ![({0, 1} : Finset ℤ), {2, 3, 4}] _
    _ = 21 := by
      rw [Fin.sum_piFinset_cons]
      simp_rw [Fin.sum_piFinset_cons]
      norm_num

end
end MvPolynomial.EvalExceptTest
