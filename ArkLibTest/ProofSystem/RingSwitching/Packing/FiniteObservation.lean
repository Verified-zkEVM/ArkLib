/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.FiniteObservation
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic

/-! # Finite observations over unequal-rank algebras with zero divisors -/

namespace RingSwitching.Packing.FiniteObservationTest

noncomputable section

/-- Packing rank two and opening rank three over the ring `ZMod 6`. -/
abbrev data : PackingData (ZMod 6) where
  P := Fin 2 → ZMod 6
  E := Fin 3 → ZMod 6
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Pi.basisFun _ _
  openBasis := Pi.basisFun _ _

def weights : Fin 2 → data.E := ![![1, 2, 3], ![4, 5, 0]]
def values : Fin 2 → data.P := ![![1, 2], ![3, 4]]

/-- This fixture has nonzero zero divisors. -/
theorem zero_divisors : (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by
  decide

set_option backward.isDefEq.respectTransparency false in
/-- Direct arithmetic gives an asymmetric nonzero observed family. -/
theorem observed_values : data.observe weights values = ![![1, 5, 3], ![0, 0, 0]] := by
  ext i u
  fin_cases i <;> fin_cases u <;>
    norm_num [PackingData.observe, data, weights, values,
      Pi.basisFun_repr (R := ZMod 6), Fin.sum_univ_succ, Algebra.smul_def, Pi.mul_apply,
      Pi.add_apply, Pi.algebraMap_apply] <;> decide

set_option backward.isDefEq.respectTransparency false in
/-- The same table has three packed slices. -/
theorem slice_values : data.coordinateSlices weights values = ![![1, 0], ![5, 0], ![3, 0]] := by
  ext u i
  fin_cases u <;> fin_cases i <;>
    norm_num [PackingData.coordinateSlices, data, weights, values,
      Pi.basisFun_repr (R := ZMod 6), Fin.sum_univ_succ, Algebra.smul_def, Pi.mul_apply,
      Pi.add_apply, Pi.algebraMap_apply] <;> decide

/-- The shared production theorem transposes the independently computed fixture. -/
theorem transpose :
    data.transpose ![![1, 5, 3], ![0, 0, 0]] = ![![1, 0], ![5, 0], ![3, 0]] := by
  rw [← observed_values, ← slice_values]
  exact data.transpose_observe weights values

/-- Shared readback recovers the independently computed opening-valued family. -/
theorem readback :
    data.transpose.symm ![![1, 0], ![5, 0], ![3, 0]] = ![![1, 5, 3], ![0, 0, 0]] := by
  rw [← observed_values, ← slice_values]
  exact data.readback_coordinateSlices weights values

/-- An empty observation set has zero family and slices. -/
theorem empty_observation :
    data.observe (fun i : Fin 0 => i.elim0) (fun i => i.elim0) = 0 ∧
      data.coordinateSlices (fun i : Fin 0 => i.elim0) (fun i => i.elim0) = 0 := by
  constructor <;> funext i <;> simp [PackingData.observe, PackingData.coordinateSlices]

/-- The inverse theorem also applies to the empty observation set. -/
theorem empty_readback : data.transpose.symm (0 : data.ιE → data.P) = 0 := by
  rw [← empty_observation.2, data.readback_coordinateSlices]
  exact empty_observation.1

/-- The deterministic base-opening specialization still permits packing rank two. -/
abbrev baseData : PackingData (ZMod 6) where
  P := Fin 2 → ZMod 6
  E := ZMod 6
  ιP := Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Module.Basis.singleton Unit _

set_option backward.isDefEq.respectTransparency false in
/-- A singleton weighted observation evaluates each packing coordinate. -/
theorem singleton_readback :
    baseData.transpose.symm (fun _ => ![0, 2]) = ![0, 2] := by
  have h := baseData.readback_coordinateSlices (fun _ : Unit => (2 : ZMod 6))
    (fun _ => ![3, 4])
  have hs : baseData.coordinateSlices (fun _ : Unit => (2 : ZMod 6))
      (fun _ => ![3, 4]) = fun _ => ![0, 2] := by
    ext u i
    fin_cases i <;> norm_num [PackingData.coordinateSlices, baseData,
      Module.Basis.singleton_repr, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply] <;> decide
  have ho : baseData.observe (fun _ : Unit => (2 : ZMod 6))
      (fun _ => ![3, 4]) = ![0, 2] := by
    ext i
    fin_cases i <;>
      norm_num [PackingData.observe, baseData, Pi.basisFun_repr (R := ZMod 6)] <;> decide
  rw [hs, ho] at h
  exact h

end

end RingSwitching.Packing.FiniteObservationTest
