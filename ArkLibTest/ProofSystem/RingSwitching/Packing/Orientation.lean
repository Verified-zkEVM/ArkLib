/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import CompPoly.Fields.Binary.Tower.Concrete.Basis
/-!
# Ring-switching coordinate orientation

Over `GF(4)/GF(2)`, packing `t(X₀, X₁) = X₀` gives the constant generator.
The honest folded element is `1 ⊗ Z₁`. Its columns recover the original evaluation,
while its rows give the target for batching against the packed polynomial. The final
equality scalar must agree with evaluation of the actual batched multiplier.
-/

open Module RingSwitching MvPolynomial
open Sumcheck.Structured
open ConcreteBinaryTower
open scoped TensorProduct
noncomputable section

namespace ArkLibTest.RingSwitchingOrientation
private abbrev K := ConcreteBTField 0
private abbrev L := ConcreteBTField 1
local instance : Algebra K L := ConcreteBTFieldAlgebra (h_le := by decide)
private def beta : Basis (Fin 1 → Fin 2) K L :=
  (basisSucc 0).reindex (Equiv.funUnique (Fin 1) (Fin 2)).symm
private def p : RingSwitchingProfile K L 1 := binaryTowerProfile 1 K L beta
private def t : MultilinearPoly K 2 :=
  ⟨X 0, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    simp only [degreeOf_X]
    split <;> omega
  ⟩
private def tp : MultilinearPoly L 1 := packMLE 1 L K 2 1 rfl beta t
private def r : Fin 2 → L := fun _ => 0
private def shat : p.A := embedded_MLP_eval 1 L K p 2 1 rfl tp r
private theorem beta_zero : beta (fun _ => 0) = 1 := by
  simp [beta, Basis.reindex_apply, basisSucc]
private theorem beta_one : beta (fun _ => 1) = Z 1 := by
  simp [beta, Basis.reindex_apply, basisSucc]
private theorem honest_input_claim : (0 : L) = t.val.aeval r := by simp [t, r]

private theorem sum_one_bit {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 2) → M) :
    ∑ x, f x = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp f]
  simp only [Fin.sum_univ_two]
  apply congrArg₂ (· + ·) <;> apply congrArg f <;> funext i <;> fin_cases i <;> rfl
private theorem tp_constant : tp.val = C (Z 1) := by
  simp only [tp, packMLE, t, eval_X, Basis.equivFun_symm_apply]
  simp only [show (0 : Fin 2).val < 1 by decide, dite_true]
  simp only [sum_one_bit, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    zero_smul, one_smul, zero_add, beta_one]
  symm
  apply eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
  · intro i; simp
  · intro x; simp

private theorem shat_eq : shat = (1 : L) ⊗ₜ[K] Z 1 := by
  change (eval _) (MvPolynomial.map _ tp.val) = _
  rw [tp_constant, map_C, eval_C]
  rfl

private theorem bit_zero_ne_one :
    (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ : Fin 1 => (1 : Fin 2)) := by decide

private theorem column_zero : p.decomposeColumns shat (fun _ => 0) = 0 := by
  rw [shat_eq]
  change decompose_tensor_algebra_columns (L := L) (K := K) beta
    ((1 : L) ⊗ₜ[K] Z 1) (fun _ => 0) = _
  rw [decompose_tensor_algebra_columns_tmul, ← beta_one, Basis.repr_self]
  simp [bit_zero_ne_one]

private theorem column_one : p.decomposeColumns shat (fun _ => 1) = 1 := by
  rw [shat_eq]
  change decompose_tensor_algebra_columns (L := L) (K := K) beta
    ((1 : L) ⊗ₜ[K] Z 1) (fun _ => 1) = _
  rw [decompose_tensor_algebra_columns_tmul, ← beta_one, Basis.repr_self]
  simp

private theorem row_zero (y : L) : p.decomposeRows ((1 : L) ⊗ₜ[K] y) (fun _ => 0) = y := by
  change decompose_tensor_algebra_rows (L := L) (K := K) beta _ _ = _
  rw [decompose_tensor_algebra_rows_tmul, ← beta_zero, Basis.repr_self]
  simp

private theorem row_one (y : L) : p.decomposeRows ((1 : L) ⊗ₜ[K] y) (fun _ => 1) = 0 := by
  change decompose_tensor_algebra_rows (L := L) (K := K) beta _ _ = _
  rw [decompose_tensor_algebra_rows_tmul, ← beta_zero, Basis.repr_self]
  simp [Ne.symm bit_zero_ne_one]

-- The accepted statement is the actual evaluation of the small-field polynomial.
example : (0 : L) = t.val.aeval r := honest_input_claim

example : performCheckOriginalEvaluation 1 L K p 2 1 rfl 0 r shat = true := by
  simp [performCheckOriginalEvaluation, eqWeightedCoordSum, sum_one_bit,
    column_zero, column_one, r, eqTilde]

-- A false claimed value for the same honest folded element is rejected.
example : performCheckOriginalEvaluation 1 L K p 2 1 rfl 1 r shat = false := by
  simp [performCheckOriginalEvaluation, eqWeightedCoordSum, sum_one_bit,
    column_zero, column_one, r, eqTilde]

private theorem batched_target : compute_s0 1 L K p shat (fun _ => 0) = Z 1 := by
  rw [shat_eq]
  simp [compute_s0, eqWeightedCoordSum, sum_one_bit, row_zero, row_one, eqTilde]

private theorem multiplier_zero :
    compute_A_func 1 L K p 1 (fun _ => 0) (fun _ => 0) (fun _ => 0) = 1 := by
  have hb : beta.repr (1 : L) (fun _ => 0) = 1 := by
    rw [← beta_zero, Basis.repr_self]
    simp
  simp [compute_A_func, eqTilde, sum_one_bit, p, hb]

private theorem multiplier_one :
    compute_A_func 1 L K p 1 (fun _ => 0) (fun _ => 0) (fun _ => 1) = 0 := by
  simp [compute_A_func, eqTilde]

-- Batching agrees with the sumcheck summand built from the actual multiplier and packing.
example : compute_s0 1 L K p shat (fun _ => 0) =
    ∑ w : Fin 1 → Fin 2,
      compute_A_func 1 L K p 1 (fun _ => 0) (fun _ => 0) w *
        tp.val.eval (fun i => (w i : L)) := by
  rw [batched_target, sum_one_bit, multiplier_zero, multiplier_one, tp_constant]
  simp

private theorem multiplier_polynomial :
    (compute_A_MLE 1 L K p 1 (fun _ => 0) (fun _ => 0)).val = 1 - X 0 := by
  symm
  apply eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
  · intro i
    exact (degreeOf_sub_le _ _ _).trans (by fin_cases i; simp)
  · intro w
    have hw : w = (fun _ => 0) ∨ w = (fun _ => 1) := by
      have h := (w 0).isLt
      interval_cases hval : (w 0).val
      · left; funext i; fin_cases i; exact Fin.ext hval
      · right; funext i; fin_cases i; exact Fin.ext hval
    rcases hw with rfl | rfl
    · simp [multiplier_zero]
    · simp [multiplier_one]

private theorem final_tensor :
    compute_final_eq_tensor 1 L K p 2 1 rfl r (fun _ => Z 1) =
      (1 : L) ⊗ₜ[K] (1 - Z 1) := by
  unfold compute_final_eq_tensor
  rw [eqTilde_eq_prod]
  simp only [Fin.prod_univ_one, r, map_zero, zero_mul, sub_zero, one_mul]
  change (1 : L ⊗[K] L) - (1 ⊗ₜ[K] Z 1) = _
  rw [TensorProduct.tmul_sub]
  rfl

-- The non-Boolean final challenge detects transposing the two coordinate systems.
example : compute_final_eq_value 1 L K p 2 1 rfl r (fun _ => Z 1) (fun _ => 0) =
    (compute_A_MLE 1 L K p 1 (fun _ => 0) (fun _ => 0)).val.eval (fun _ => Z 1) := by
  unfold compute_final_eq_value
  rw [final_tensor, multiplier_polynomial]
  simp [eqWeightedCoordSum, sum_one_bit, row_zero, row_one, eqTilde]

end ArkLibTest.RingSwitchingOrientation
