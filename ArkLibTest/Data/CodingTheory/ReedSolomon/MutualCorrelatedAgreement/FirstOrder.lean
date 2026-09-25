/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.CurveAgreement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

/-!
# First-order curve agreement acceptance tests

Concrete rational examples exercise base-field and extension-field exceptional-set bounds
for first-order power-batched curves.

## Main statements

* The height-slot bound has a nonvacuous base-field instance at the tight exponent.
* Height-slot and finite-certificate bounds have nonvacuous extension-field instances.

## References

* [DKT26]
-/

open Polynomial Finset PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative

noncomputable section

private def curveDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def curveValues : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 0

private theorem curveHeightSurplus :
    firstOrderCurveShiftedRowSlotBound 1 1 2 1 1 1 0 1 <
      firstOrderCurveShiftedHeightSlotCount 1 1 2 1 1 0 1 := by
  norm_num [firstOrderCurveShiftedRowSlotBound, firstOrderGradedRankBound,
    firstOrderGradedSourceCount, firstOrderCurveShiftedHeightSlotCount,
    Finset.sum_range_succ]

private theorem algebraicClosureInfinite : Infinite (AlgebraicClosure ℚ) := by
  exact Infinite.of_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective

local instance : Infinite (AlgebraicClosure ℚ) := algebraicClosureInfinite
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- The base-field height theorem remains nonvacuous at the tight exponent. -/
example : ∃ z : ℚ, ∃ P : ℚ[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet curveDomain (powerBatchedWord curveValues z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues (RingHom.id ℚ) 1 z P := by
  classical
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
      (F := ℚ) (E := AlgebraicClosure ℚ) (D := 1) (A := 1) (m := 2) (M := 1)
      (μ := 1) (k := 1) (h := 1) (n := 1) (K := 2) (L := 1) (ell := 0)
      curveDomain curveValues (algebraMap ℚ (AlgebraicClosure ℚ))
      (by norm_num) (by norm_num) (by norm_num) curveHeightSurplus
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨z, 0, by simp, ?_, ?_⟩
  · have hset : polynomialAgreementSet curveDomain (powerBatchedWord curveValues z)
        (0 : ℚ[X]) = Finset.univ := by
      ext i
      simp [polynomialAgreementSet, powerBatchedWord, curveValues]
    rw [hset]
    simp
  · apply hgood z hz 0 (by simp)
    simp [polynomialAgreementSet, powerBatchedWord, curveValues]

/-- The extension-field height theorem gives a challenge with exact power agreement. -/
example : ∃ z : AlgebraicClosure ℚ, ∃ P : (AlgebraicClosure ℚ)[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet
      (curveDomain.trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
      (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
        (curveValues t i)) z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z P := by
  classical
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  let extensionDomain := curveDomain.trans ⟨iota, iota.injective⟩
  let extensionValues : Fin 1 → Fin 1 → AlgebraicClosure ℚ :=
    fun t i ↦ iota (curveValues t i)
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
      (F := ℚ) (E := AlgebraicClosure ℚ) (D := 1) (A := 1) (m := 2) (M := 1)
      (μ := 1) (k := 1) (h := 1) (n := 1) (K := 2) (L := 1) (ell := 0)
      curveDomain curveValues iota
      (by norm_num) (by norm_num) (by norm_num) curveHeightSurplus
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  have hset : polynomialAgreementSet extensionDomain (powerBatchedWord extensionValues z)
      (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, extensionValues, curveValues,
      extensionDomain, curveDomain]
  have hagree : 1 ≤ (polynomialAgreementSet extensionDomain
      (powerBatchedWord extensionValues z) (0 : (AlgebraicClosure ℚ)[X])).card := by
    rw [hset]
    simp
  refine ⟨z, 0, by simp, hagree, ?_⟩
  have h := hgood z hz 0 (by simp) hagree
  convert h using 1

/-- A finite curve certificate also gives a nonvacuous extension-field conclusion. -/
example : ∃ z : AlgebraicClosure ℚ, ∃ P : (AlgebraicClosure ℚ)[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet
      (curveDomain.trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
      (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
        (curveValues t i)) z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z P := by
  classical
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  let extensionDomain := curveDomain.trans ⟨iota, iota.injective⟩
  let extensionValues : Fin 1 → Fin 1 → AlgebraicClosure ℚ :=
    fun t i ↦ iota (curveValues t i)
  obtain ⟨cert⟩ :=
    exists_finite_firstOrder_curve_certificate_of_heightSlotCount
      (D := 1) (A := 1) (m := 2) (M := 1) (μ := 1) (k := 1) (h := 1) (n := 1)
      0 (by norm_num) (by norm_num) (by norm_num) curveDomain
      (fun i ↦ powerBatchedCoordinate (fun t ↦ curveValues t i))
      (by intro i; norm_num [powerBatchedCoordinate, curveValues]) curveHeightSurplus
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
      (D := 1) (A := 1) (m := 2) (M := 1) (μ := 1) (k := 1) (h := 1) (n := 1)
      (K := 2) (L := 1) (ell := 0) curveDomain curveValues iota _ cert
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  have hset : polynomialAgreementSet extensionDomain (powerBatchedWord extensionValues z)
      (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, extensionValues, curveValues,
      extensionDomain, curveDomain]
  have hagree : 1 ≤ (polynomialAgreementSet extensionDomain
      (powerBatchedWord extensionValues z) (0 : (AlgebraicClosure ℚ)[X])).card := by
    rw [hset]
    simp
  refine ⟨z, 0, by simp, hagree, ?_⟩
  have h := hgood z hz 0 (by simp) hagree
  convert h using 1

end
