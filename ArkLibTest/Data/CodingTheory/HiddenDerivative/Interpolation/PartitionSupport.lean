/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.CurveCertificate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting

open ReedSolomon.HiddenDerivative
open Polynomial PolynomialDifferential

private def twoCenters : Fin 2 ↪ ℚ where
  toFun i := i.val
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private noncomputable def zeroReceived : Fin 2 → ℚ[X] := fun _ ↦ 0

example : Nonempty (SymbolicReceivedCurve.CurveCertificate ℚ 2 2 0 1 0 0 twoCenters
    zeroReceived) := by
  simpa using exists_partitionSupport_curve_certificate
    (D := 1) (d := 0) (m := 1) (W := 0) (n := 2) (A := 2) (k := 2) (ℓ := 0) (ν := 1)
    (L := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    twoCenters zeroReceived (by intro i; simp [zeroReceived])
    (by
      intro u hu
      have h : u none + 1 * totalJetDegree u < 2 := by
        exact_mod_cast hu.2
      omega)
    (by
      have hcard : (partitionSupportExponents 1 0 0 (2 : ℝ) (by norm_num)).card =
          partitionSourceCount 1 0 0 2 := by
        simpa using
          (card_partitionSupportExponents (D := 1) (d := 0) (W := 0) (by norm_num) 2)
      rw [hcard]
      norm_num [partitionSourceCount, localDerivativeCoordinateBudget, contactThreshold,
        weightedHigherJetCount, Finset.natWeightedSimplex, Finset.sum_range_succ])
