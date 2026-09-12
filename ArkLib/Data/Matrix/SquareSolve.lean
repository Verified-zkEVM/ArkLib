/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Matrix.NonzeroKernelSemantics
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Square-system solution through executed elimination

Homogenize `M x = b` with one extra coordinate, execute the nonzero-kernel machine, and divide
by that coordinate. For an injective square matrix it cannot be zero. This adapter avoids
executing the permutation formula for a determinant or Cramer's rule.
-/

@[expose] public section

namespace Matrix.SquareSolve

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- The extra first column homogenizes the right-hand side. -/
def augmented (M : Matrix (Fin n) (Fin n) F) (b : Fin n → F) :
    Matrix (Fin n) (Fin (n + 1)) F :=
  fun i => Fin.cases (-b i) (M i)

/-- Actual homogeneous rows consumed by the existing elimination machine. -/
def rows (M : Matrix (Fin n) (Fin n) F) (b : Fin n → F) :
    List (PivotSelectionMachine.Row F) :=
  List.ofFn fun i => (List.ofFn (augmented M b i), 0)

/-- Execute elimination and dehomogenize its nonzero kernel vector; a zero homogenizing
coordinate or an unfinished machine state is an explicit failure. -/
def solve? (M : Matrix (Fin n) (Fin n) F) (b : Fin n → F) : Option (Fin n → F) :=
  let input := rows M b
  match (NonzeroKernelMachine.runFuel (n + 1)
      (NonzeroKernelMachine.budget input.length (n + 1)) (.check input input)).1 with
  | .done _ coefficients =>
      let t := coefficients.getD 0 0
      if t = 0 then none
      else some (fun i => coefficients.getD i.succ.val 0 / t)
  | _ => none

omit [DecidableEq F] in
/-- Homogeneous matrix equations express the original right-hand side times the extra coordinate. -/
theorem augmented_mulVec (M : Matrix (Fin n) (Fin n) F) (b : Fin n → F)
    (z : Fin (n + 1) → F) :
    augmented M b *ᵥ z = 0 ↔ M *ᵥ (fun i => z i.succ) = z 0 • b := by
  simp only [funext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    augmented, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, Pi.smul_apply,
    smul_eq_mul]
  apply forall_congr'
  intro i
  simp only [neg_mul, neg_add_eq_sub, sub_eq_zero, mul_comm]

/-- An injective square system always returns a solution through the actual kernel machine. -/
theorem solve?_success_of_injective (M : Matrix (Fin n) (Fin n) F) (b : Fin n → F)
    (hinj : Function.Injective M.mulVec) :
    ∃ x, solve? M b = some x ∧ M *ᵥ x = b := by
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp
    (show Function.Injective M.mulVecLin from hinj)) b
  let witness : ℕ → F := fun i => if h : i < n + 1 then
    Fin.cases 1 x ⟨i, h⟩ else 0
  have hrect : ForwardEchelonMachine.Rectangular (n + 1) (rows M b) := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simp
  have hhom : ∀ row ∈ rows M b, row.2 = 0 := by
    simp [rows]
  have hw : PivotSelectionMachine.Satisfies (rows M b) witness := by
    rw [rows, PivotSelectionMachine.satisfies_ofFn]
    change augmented M b *ᵥ (fun i => witness i.val) = 0
    rw [augmented_mulVec]
    simpa [witness] using hx
  obtain ⟨chosen, coefficients, cost, hrun, hlen, hchosen, hone, hsat, _⟩ :=
    NonzeroKernelMachine.evaluation_runFuel (n + 1) (rows M b) hrect hhom
      ⟨witness, hw, 0, by omega, by simp [witness]⟩
  have heq : M *ᵥ (fun i => coefficients.getD i.succ.val 0) =
      coefficients.getD 0 0 • b := by
    exact (augmented_mulVec M b _).mp
      ((PivotSelectionMachine.satisfies_ofFn (augmented M b) 0 _).mp hsat)
  have ht : coefficients.getD 0 0 ≠ 0 := by
    intro ht
    have hzero : (fun i : Fin n => coefficients.getD i.succ.val 0) = 0 := by
      apply hinj
      rw [ht, zero_smul] at heq
      simpa only [Matrix.mulVec_zero] using heq
    have hall (j : Fin (n + 1)) : coefficients.getD j.val 0 = 0 := by
      refine Fin.cases ht (fun i => congrFun hzero i) j
    exact one_ne_zero (hone.symm.trans (hall ⟨chosen, hchosen⟩))
  refine ⟨fun i => coefficients.getD i.succ.val 0 / coefficients.getD 0 0, ?_, ?_⟩
  · unfold solve?
    dsimp only
    rw [hrun]
    dsimp only
    rw [if_neg ht]
  · have hscaled := Matrix.mulVec_smul M (coefficients.getD 0 0)⁻¹
      (fun i => coefficients.getD i.succ.val 0)
    rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul] at hscaled
    simpa only [Pi.smul_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hscaled

end Matrix.SquareSolve
