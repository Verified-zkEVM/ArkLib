/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import ArkLib.ToMathlib.LinearAlgebra.LagrangeLine
import ArkLib.ToMathlib.LinearAlgebra.LineInjectivity
import ArkLib.ToMathlib.LinearAlgebra.TriangularInjective
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Acceptance tests for linear algebra bounds and interpolation
-/

open Module Polynomial Finset Lagrange

/-- The second axis lies in the kernel of the first projection, bounding its rank by one. -/
example : finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) ≤ 1 := by
  have h := LinearMap.finrank_range_le_sub_of_injective_ker (LinearMap.fst ℚ ℚ ℚ)
    ((LinearMap.inr ℚ ℚ ℚ).codRestrict (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ))
      fun x => by simp)
    (fun _ _ hxy => congrArg Prod.snd (Subtype.ext_iff.mp hxy))
  simpa using h

/-- The coordinates on the range preserve the projection's kernel and cover its coordinate space. -/
example : LinearMap.ker (LinearMap.fst ℚ ℚ ℚ).rangeCoordinates =
      LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) ∧
    Function.Surjective (LinearMap.fst ℚ ℚ ℚ).rangeCoordinates :=
  ⟨LinearMap.ker_rangeCoordinates _, LinearMap.rangeCoordinates_surjective _⟩

/-- The first projection kills a nonzero vector because its rank is below the source dimension. -/
example : ∃ v : ℚ × ℚ, v ≠ 0 ∧ LinearMap.fst ℚ ℚ ℚ v = 0 := by
  apply LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt
  rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, finrank_top, finrank_self,
    finrank_prod, finrank_self]
  norm_num

/-- Two identity components have product rank bounded by the sum of their ranks. -/
example : finrank ℚ (LinearMap.range
      (LinearMap.pi fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) ≤
    ∑ _ : Fin 2, finrank ℚ (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) :=
  LinearMap.finrank_range_pi_le_sum (fun _ : Fin 2 => LinearMap.id)

/-- Two coordinate functionals on `ℚ³` have a common nonzero kernel vector. -/
example : ∃ v : Fin 3 → ℚ, v ≠ 0 ∧ ∀ i : Fin 2,
    LinearMap.proj (R := ℚ) (φ := fun _ => ℚ) i.castSucc v = 0 := by
  refine LinearMap.exists_ne_zero_of_sum_finrank_range_lt _ ?_
  calc ∑ i : Fin 2, finrank ℚ (LinearMap.range
        (LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i.castSucc))
      ≤ ∑ _i : Fin 2, 1 := Finset.sum_le_sum fun i _ =>
        (Submodule.finrank_le _).trans_eq (finrank_self ℚ)
    _ < finrank ℚ (Fin 3 → ℚ) := by simp

namespace LagrangeLineTest

/-- The concrete interpolation nodes `0, 1` over `ℚ`. -/
def v : Fin 2 → ℚ := ![0, 1]

lemma v_injOn : Set.InjOn v (univ : Finset (Fin 2)) := by
  intro i _ j _ h
  fin_cases i <;> fin_cases j <;> simp_all [v]

/-- Mapping this interpolant to `ℝ` commutes with interpolation. -/
example : (interpolate univ v ![1, 2]).map (Rat.castHom ℝ) =
    interpolate univ (Rat.castHom ℝ ∘ v) (Rat.castHom ℝ ∘ ![1, 2]) :=
  map_interpolate _ _ _ _

/-- The line `1 + 2X` is reconstructed from its values at the two rational nodes. -/
example : (C 1 + C 2 * X : ℝ[X]) =
    (C 1 + X : ℚ[X]).map (Rat.castHom ℝ) + C 1 * (X : ℚ[X]).map (Rat.castHom ℝ) := by
  have hline : interpolate univ v ![1, 2] = C 1 + X := by
    symm
    apply eq_interpolate_of_eval_eq _ v_injOn
    · rw [card_univ, Fintype.card_fin]
      compute_degree!
    · intro i _
      fin_cases i <;> norm_num [v]
  have hX : interpolate univ v ![0, 1] = X := by
    symm
    apply eq_interpolate_of_eval_eq _ v_injOn
    · rw [card_univ, Fintype.card_fin]
      compute_degree!
    · intro i _
      fin_cases i <;> simp [v]
  rw [← hline, ← hX]
  apply eq_map_interpolate_add_C_mul_of_eval_eq _ v_injOn
  · rw [card_univ, Fintype.card_fin]
    compute_degree!
  · intro i _
    fin_cases i <;> norm_num [v]

end LagrangeLineTest

namespace LineInjectivityTest

/-- Two distinct lines over `ℚ` meet at the single parameter `2`. -/
example : {z : ℚ | (1 : ℚ) + z • (2 : ℚ) = 3 + z • 1} = {2} := by
  have hsub := subsingleton_setOf_add_smul_eq_add_smul (K := ℚ) (a := (1 : ℚ)) (b := 2)
    (c := 3) (d := 1) (by simp)
  exact hsub.eq_singleton_of_mem (by norm_num)

/-- A concrete finite family of rational lines has a parameter outside the forbidden set. -/
example : ∃ z ∉ ({0, 1, -1} : Set ℚ), Set.InjOn (fun p : ℚ × ℚ ↦ p.1 + z • p.2)
    ({(0, 0), (0, 1), (1, 0), (1, 1)} : Set (ℚ × ℚ)) :=
  Set.Finite.exists_notMem_injOn_add_smul (by simp) Prod.fst Prod.snd
    (fun _ _ _ _ h ↦ h) (by simp)

end LineInjectivityTest

/-- A two-block lower-triangular sum with injective diagonal blocks is injective. -/
example : Function.Injective
    (∑ i : Fin 2, (![LinearMap.pi ![LinearMap.id, LinearMap.id],
        LinearMap.pi ![0, LinearMap.id]] i).comp
      (LinearMap.proj i : (Fin 2 → ℚ) →ₗ[ℚ] ℚ) :
        (Fin 2 → ℚ) →ₗ[ℚ] Fin 2 → ℚ) := by
  refine LinearMap.injective_sum_comp_proj_of_triangular _ (fun i => LinearMap.proj i)
    (fun i j hij x => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> intro x y h <;> simpa using h
