/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Algebra.Grouped
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-! # Acceptance checks for grouped scalar reconstruction and clearing -/

open Logup MvPolynomial

namespace Logup.GroupedTest

/-- A generic executable caller consumes scalar answers already bound by the source program. -/
def reconstructCaller {R : Type*} [CommRing R] {T K n : ℕ}
    (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R) (lambda : Fin K → R)
    (x : Fin n → R) (value weight : Fin T → R) (helper : Fin K → R) : R :=
  reconstruct groups alpha z lambda x value weight helper

/-- The cover deliberately differs from consecutive order. -/
def asymmetricGroups : Vector (List (Fin 3)) 2 := #v[[0, 2], [1]]

def asymmetricCaller {R : Type*} [CommRing R] : R :=
  reconstructCaller asymmetricGroups 7 ![5, 7] ![2, 5] ![2, 3] ![2, 3, 5] ![1, 4, 2]
    ![3, -1]

-- Group pairs are (12,10) and (4,4); residuals 18,-8 batch to -4; the kernel is 462.
example : (asymmetricCaller : ℤ) = -1846 := by decide
example : (asymmetricCaller : ZMod 17) = 7 := by decide

example : asymmetricGroups.toList.flatten.Perm (List.finRange 3) := by decide

example : groupFraction [0, 1] (5 : ℤ) (fun _ : Fin 2 ↦ 5)
    (fun i ↦ if i = 0 then 3 else 7) = ⟨0, 0⟩ := by decide

example : groupResidual [0, 1] (5 : ℤ) (fun _ : Fin 2 ↦ 5)
    (fun i ↦ if i = 0 then 3 else 7) 11 = 0 := by decide

example : groupResidual [0] (5 : ℤ) (fun _ : Fin 1 ↦ 5) (fun _ ↦ 3) 11 = -3 := by decide

example : reconstructCaller (#v[] : Vector (List (Fin 0)) 0) (0 : ℤ)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 = 0 := by decide

/-- An empty block has pair (0,1), so its residual is its helper. -/
example : reconstructCaller (#v[[]] : Vector (List (Fin 0)) 1) (0 : ℤ)
    Fin.elim0 (fun _ ↦ 2) Fin.elim0 Fin.elim0 Fin.elim0 (fun _ ↦ 5) = 15 := by decide

def oneGroup : Vector (List (Fin 1)) 1 := #v[[0]]

/-- This circuit is cubic: value, weight and helper equal x; alpha and z are zero. -/
def cubicCaller (x : ZMod 17) : ZMod 17 :=
  reconstructCaller (n := 1) oneGroup 0 (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ x)
    (fun _ ↦ x) (fun _ ↦ x) (fun _ ↦ x)

example : cubicCaller 2 = 8 := by decide

theorem cubic_polynomial :
    batchedPolynomial oneGroup (0 : ℚ) (fun _ ↦ 0) (fun _ ↦ 1)
      (fun _ ↦ X (0 : Fin 1)) (fun _ ↦ X 0) (fun _ ↦ X 0) = X 0 ^ 3 := by
  simpa [batchedPolynomial, residualPolynomial, groupResidual, groupFraction,
    oneGroup, eqPolynomial, singleEqPolynomial] using
    (show (X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) +
      (1 - X 0) * (X 0 * (-X 0) - X 0) = X 0 ^ 3 by ring)

/-- The individual-degree bound ell+2 is attained already by one singleton group. -/
example : degreeOf (0 : Fin 1) (batchedPolynomial oneGroup (0 : ℚ) (fun _ ↦ 0)
    (fun _ ↦ 1) (fun _ ↦ X (0 : Fin 1)) (fun _ ↦ X 0) (fun _ ↦ X 0)) = 3 := by
  rw [cubic_polynomial]
  simp

example : batchedPolynomial oneGroup (0 : ℚ) (fun _ ↦ 0) (fun _ ↦ 1)
    (fun _ ↦ X (0 : Fin 1)) (fun _ ↦ X 0) (fun _ ↦ X 0) ∈
      restrictDegree (Fin 1) ℚ 3 := by
  have hx : (X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ∈ restrictDegree (Fin 1) ℚ 1 := by
    rw [mem_restrictDegree_iff_degreeOf_le]
    exact fun j ↦ degreeOf_X_le j 0
  apply batchedPolynomial_mem_restrictDegree oneGroup 0 (fun _ ↦ 0) (fun _ ↦ 1)
    (fun _ ↦ X 0) (fun _ ↦ X 0) (fun _ ↦ X 0) 1
  · intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    decide
  · exact fun _ ↦ hx
  · exact fun _ ↦ hx
  · exact fun _ ↦ hx

/-- The bounded view used by the native oracle family agrees for every helper realization. -/
example {R : Type*} [CommRing R] {T K n : ℕ}
    (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R) (lambda : Fin K → R)
    (ell : ℕ) (hgroups : ∀ k : Fin K, groups[k.val].length ≤ ell)
    (value weight : Fin T → restrictDegree (Fin n) R 1)
    (helper : Fin K → restrictDegree (Fin n) R 1) (x : Fin n → R) :
    eval x (boundedBatchedPolynomial groups alpha z lambda ell hgroups value weight helper).val =
      reconstruct groups alpha z lambda x (fun i ↦ eval x (value i).val)
        (fun i ↦ eval x (weight i).val) (fun k ↦ eval x (helper k).val) :=
  eval_batchedPolynomial groups alpha z lambda (fun i ↦ (value i).val)
    (fun i ↦ (weight i).val) (fun k ↦ (helper k).val) x

/-- A concrete clearing implication over an infinite field, at a pole. -/
example : Polynomial.eval (5 : ℚ) (PartialFractions.clearedNumerator
    ((Finset.univ : Finset Unit).product (Finset.univ : Finset (Fin 2)))
    (fun _ ↦ 5) (fun _ ↦ 1)) = 0 := by
  apply eval_clearedNumerator_eq_zero_of_groupResidual_eq_zero
    (#v[[0, 1]] : Vector (List (Fin 2)) 1) 5 Finset.univ
    (fun _ _ ↦ 5) (fun _ _ ↦ 1) (fun _ _ ↦ 0)
  · decide
  · intro row _ k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simp [groupResidual, groupFraction]
  · simp

#eval (asymmetricCaller : ℤ)
#eval (asymmetricCaller : ZMod 17)
#eval cubicCaller 2

-- A long group exercises the actual map/fold caller without a kernel reduction proof.
#eval let p := groupFraction (List.finRange 100000) (1 : ℤ) (fun _ ↦ 0) (fun _ ↦ 0)
  (p.numerator, p.denominator)

open Lean Elab Command

run_cmd do
  for name in #[``Logup.groupFraction, ``Logup.groupResidual, ``Logup.reconstruct,
      ``reconstructCaller, ``asymmetricCaller, ``cubicCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Logup.groupFraction, ``Logup.groupResidual, ``Logup.reconstruct,
      ``Logup.map_groupFraction, ``Logup.map_groupResidual, ``Logup.residualPolynomial,
      ``Logup.batchedPolynomial, ``Logup.eval_residualPolynomial, ``Logup.eval_batchedPolynomial,
      ``Logup.degreeOf_groupFraction_le, ``Logup.degreeOf_residualPolynomial_le,
      ``Logup.degreeOf_batchedPolynomial_le, ``Logup.batchedPolynomial_mem_restrictDegree,
      ``Logup.boundedBatchedPolynomial, ``Logup.sum_eval_batchedPolynomial,
      ``Logup.groupFraction_numerator_eq_helper_sum_mul_denominator,
      ``Logup.fold_rows_numerator_eq_zero,
      ``Logup.eval_clearedNumerator_eq_zero_of_groupResidual_eq_zero] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end Logup.GroupedTest
