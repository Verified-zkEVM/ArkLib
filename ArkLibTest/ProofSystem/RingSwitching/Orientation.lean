/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic
/-!
# Tensor-factor orientation regressions

The actual honest packing and folded message of the prefix variable must pass the production
scalar check. The formerly used opposite coordinates reject that same nonzero packed witness.
-/
open MvPolynomial Module RingSwitching
namespace RingSwitching.OrientationTest
noncomputable section
abbrev W := Fin 1 → Fin 2
abbrev L := W → ZMod 3
abbrev basis : Basis W (ZMod 3) L := Pi.basisFun _ _
abbrev prof := binaryTowerProfile 1 (ZMod 3) L basis
abbrev y : L := basis (fun _ => 1)
lemma coordSum_zero (c : W → L) : eqWeightedCoordSum 1 L c (fun _ => 0) = c (fun _ => 0) := by
  have hcast (u : W) : (fun i : Fin 1 => if u i == 1 then (1 : L) else 0) =
      (u : Fin 1 → L) := by
    funext i
    generalize u i = a
    fin_cases a <;> rfl
  unfold eqWeightedCoordSum
  simp_rw [hcast]
  rw [← MLE_eval]
  exact MLE_eval_zeroOne (R := L) (fun _ => 0) c
lemma cols : prof.decomposeColumns (prof.φ₁ y) = fun _ => y := by
  have h := prof.decomposeColumns_mul 1 y
  simpa [Pi.basisFun_repr] using h
lemma wrong_column_check : decide (0 = eqWeightedCoordSum 1 L
    (prof.decomposeColumns (prof.φ₁ y)) (fun _ => 0)) = false := by
  rw [cols, coordSum_zero]
  simp only [decide_eq_false_iff_not]
  intro h
  have hy := congrFun h (fun _ => 1)
  simp [y, basis, Pi.basisFun_apply] at hy
lemma correct_input_check :
    performCheckOriginalEvaluation 1 L (ZMod 3) prof 2 1 rfl
    0 (fun _ => 0) (prof.φ₁ y) = true := by
  have hrows : prof.decomposeRows (prof.φ₁ y) =
      fun u => algebraMap (ZMod 3) L (basis.repr y u) := by
    have h := prof.decomposeRows_mul 1 y
    simpa using h
  change decide (0 = eqWeightedCoordSum 1 L (prof.decomposeRows (prof.φ₁ y))
    (fun _ => 0)) = true
  rw [hrows, coordSum_zero]
  have hne : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1) := by decide
  simp [y, hne]

def sourcePoly : Sumcheck.Structured.MultilinearPoly (ZMod 3) 2 :=
  ⟨MLE (fun v : Fin 2 → Fin 2 => (v 0 : ZMod 3)), MLE_mem_restrictDegree _⟩
def packedPoly : Sumcheck.Structured.MultilinearPoly L 1 :=
  ⟨MLE (fun _ : Fin 1 → Fin 2 => y), MLE_mem_restrictDegree _⟩
lemma honest_packing : packMLE 1 L (ZMod 3) 2 1 rfl basis sourcePoly = packedPoly := by
  apply Subtype.ext
  dsimp only [packMLE, packedPoly]
  congr 1
  funext w
  simp only [sourcePoly, MLE_eval_zeroOne, Pi.basisFun_equivFun]
  change (fun v : W => (v 0 : ZMod 3)) = y
  funext v
  simp only [Fin.isValue, Pi.basisFun_apply, Pi.single_apply]
  split
  · rename_i h
    simp [h]
  · rename_i h
    have hv : v 0 = 0 := by
      by_contra hc
      have hv1 : v 0 = 1 := by omega
      apply h
      funext i
      fin_cases i
      exact hv1
    simp [hv]

lemma honest_folded_message : embedded_MLP_eval 1 L (ZMod 3) prof 2 1 rfl
    (packMLE 1 L (ZMod 3) 2 1 rfl basis sourcePoly) (fun _ => 0) = prof.φ₁ y := by
  rw [honest_packing]
  have hp : packedPoly.val = C y := by
    apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp packedPoly.property)
      (by simp)
    intro w
    simp [packedPoly, MLE_eval_zeroOne]
  simp [embedded_MLP_eval, componentWise_embed_MLE, embedCoeffs, hp]

lemma actual_honest_check : performCheckOriginalEvaluation 1 L (ZMod 3) prof 2 1 rfl
    0 (fun _ => 0) (embedded_MLP_eval 1 L (ZMod 3) prof 2 1 rfl
      (packMLE 1 L (ZMod 3) 2 1 rfl basis sourcePoly) (fun _ => 0)) = true := by
  rw [honest_folded_message]
  exact correct_input_check

lemma actual_batched_target : compute_s0 1 L (ZMod 3) prof (prof.φ₁ y) 0 = y := by
  unfold compute_s0
  rw [cols]
  exact coordSum_zero (fun _ => y)

lemma actual_final_multiplier :
    compute_final_eq_value 1 L (ZMod 3) prof 2 1 rfl 0 (fun _ => y) 0 = 1 - y := by
  have ht : compute_final_eq_tensor 1 L (ZMod 3) prof 2 1 rfl 0 (fun _ => y) =
      prof.φ₁ (1 - y) := by
    simp [compute_final_eq_tensor, eqTilde]
  have hc : prof.decomposeColumns (prof.φ₁ (1 - y)) = fun _ => 1 - y := by
    simpa [Pi.basisFun_repr] using prof.decomposeColumns_mul 1 (1 - y)
  change eqWeightedCoordSum 1 L
    (prof.decomposeColumns (compute_final_eq_tensor 1 L (ZMod 3) prof 2 1 rfl 0
      (fun _ => y))) 0 = 1 - y
  rw [ht]
  exact (congrArg (fun c => eqWeightedCoordSum 1 L c 0) hc).trans (coordSum_zero _)

-- The concrete nonzero folded message comes from a satisfiable production source relation.
def sourceOracles : AbstractOStmtIn L 1 where
  ιₛᵢ := Empty
  OStmtIn := Empty.elim
  Oₛᵢ := fun i => nomatch i
  initialCompatibility := fun p => p.1 = packedPoly

lemma sourcePoly_eq_X : sourcePoly.val = X 0 := by
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq (R := ZMod 3) sourcePoly.val (X 0)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp sourcePoly.property)
    (by intro i; fin_cases i <;> simp [degreeOf_X])
  intro v
  simp [sourcePoly, MLE_eval_zeroOne]

lemma honest_input_relation :
    BatchingPhase.batchingInputRelationProp 1 L (ZMod 3) prof 2 1 rfl sourceOracles
      ⟨0, 0⟩ (fun i => nomatch i) ⟨sourcePoly, packedPoly⟩ := by
  refine ⟨honest_packing.symm, ?_, rfl⟩
  simp [sourcePoly_eq_X]

end
end RingSwitching.OrientationTest
