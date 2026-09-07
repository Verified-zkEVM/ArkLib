/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ConcreteCurveBounds
import ArkLibExamples.ReedSolomon.ProveKitInterpolation
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FirstOrderCurve

/-!
# Concrete polynomial-curve agreement bounds

This module instantiates the first-order polynomial-curve theorem for every LambdaVM
curve row and for the two published ProveKit profiles. Each conclusion constructs an actual
base-field exceptional set and gives exact power agreement outside it.

## Reading the statements

Fix an evaluation-domain embedding and a tuple of received words. The theorem chooses one
exceptional set before the scalar challenge and before any close candidate polynomial.
Outside that set, every candidate of degree below `k` agreeing in at least `A` positions is
an exact power combination of constituent messages. Its entire agreement set is the common
agreement set of those messages with the received tuple. This is stronger than recovering a
correlated tuple on some chosen subset of `A` positions.

`CurveCertificate.exists_exceptional_exact_powerAgreement` is the reusable specialization step.
Its inputs are the executable interpolation-height certificate, an admissible split, a rational
envelope inequality, and the characteristic condition. The named application theorems discharge
all the numerical inputs. The final exceptional-cardinality bound is a conclusion, not a premise.

## Proof route

The finite first-order curve theorem constructs a primitive interpolation equation, follows its
separant chain, and counts the geometric exceptional fibers using the separate first-derivative
cap. It then descends the exact agreement conclusion to the base field. The algebraically closed
extension in these statements is a proof device; both the exceptional set and recovered messages
live over `F`. The certified-budget modules choose an algebraic closure automatically and connect
these counts to the canonical finite fields and local error arithmetic.
-/

open Polynomial
open ReedSolomon
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ConcreteCurveMCA

open CurveProfile ConcreteCurves ConcreteCurveBounds CurveCertificate

noncomputable section

set_option maxRecDepth 4096

universe u

/-- Every LambdaVM curve row has an actual base-field exceptional set within its recorded
budget. -/
theorem lambdaVM_exists_exceptional_exact_powerAgreement
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (i : Fin 35) (domain : Fin (lambdaVM i).n ↪ F)
    (values : Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max ((lambdaVM i).k - 1) (lambdaVM i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F, (exceptional.card : ℚ) ≤ lambdaVMBudget i ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (lambdaVM i).k →
        (lambdaVM i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (lambdaVM i).k z P := by
  apply CurveCertificate.exists_exceptional_exact_powerAgreement
    (F := F) (E := E) (p := lambdaVM i) (lambdaVM_verified i)
    (lambdaVMSplit i) (lambdaVMBudget i) (lambdaVM_split_admissible i)
  · fin_cases i <;> decide
  · exact lambdaVM_envelope_le i
  · exact iota
  · exact hchar

/-- The published BN254 exceptional budget bounds the sharp curve envelope. -/
theorem bn254_curve_envelope_le :
    firstOrderCurveBound 1048576 262144 262144 262197 492831 688 168 1 867623
        (τ := 524285) (η := firstOrderCurveDirectRatio 1048576 262144 492831) ≤
      ProveKit.bn254.exceptionalCount := by
  decide +kernel

/-- The revised cubic-Goldilocks exceptional budget bounds the sharp curve envelope. -/
theorem goldilocksCubic113_curve_envelope_le :
    firstOrderCurveBound 1048576 262144 262144 268399 508263 30 7 1 339
        (τ := 524285) (η := firstOrderCurveDirectRatio 1048576 262144 508263) ≤
      ProveKit.goldilocksCubic113.exceptionalCount := by
  decide +kernel

/-- Height 867623 passes the actual degree-one polynomial-curve coefficient test. -/
theorem bn254_curve_interpolation_height :
    firstOrderCurveShiftedRowSlotBound 262143 492831 384 168 688 1048576 1 867623 <
      firstOrderCurveShiftedHeightSlotCount 262143 492831 384 168 688 1 867623 :=
  ProveKit.bn254_interpolation_height

/-- Height 339 passes the revised degree-one polynomial-curve coefficient test. -/
theorem goldilocksCubic113_curve_interpolation_height :
    firstOrderCurveShiftedRowSlotBound 262143 508263 16 7 30 1048576 1 339 <
      firstOrderCurveShiftedHeightSlotCount 262143 508263 16 7 30 1 339 := by
  simpa [LineProfile.D, LineProfile.shiftedRowSlots, LineProfile.shiftedHeightSlots,
    ProveKit.goldilocksCubic113Profile] using
      ProveKit.goldilocksCubic113_verified.2.2.2.1

/-- The published BN254 profile's exact exceptional count is derived from the sharp
polynomial-curve theorem. -/
theorem bn254_exists_exceptional_exact_powerAgreement
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin 1048576 ↪ F) (values : Fin 2 → Fin 1048576 → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ProveKit.bn254.exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 262144 →
        492831 ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) 262144 z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := 262143) (A := 492831) (m := 384) (M := 168) (mu := 688)
      (k := 262144) (h := 867623) (n := 1048576) (K := 262144)
      (L := 262197) (ell := 1) domain values iota
      (by norm_num) (by norm_num) (by norm_num) bn254_curve_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa using hchar)
  exact ⟨exceptional, hcard.trans bn254_curve_envelope_le, hgood⟩

/-- The published cubic-Goldilocks profile's exact exceptional count is derived from the sharp
polynomial-curve theorem. -/
theorem goldilocksCubic113_exists_exceptional_exact_powerAgreement
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin 1048576 ↪ F) (values : Fin 2 → Fin 1048576 → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ProveKit.goldilocksCubic113.exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 262144 →
        508263 ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) 262144 z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := 262143) (A := 508263) (m := 16) (M := 7) (mu := 30)
      (k := 262144) (h := 339) (n := 1048576) (K := 262144)
      (L := 268399) (ell := 1) domain values iota
      (by norm_num) (by norm_num) (by norm_num)
      goldilocksCubic113_curve_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa using hchar)
  exact ⟨exceptional, hcard.trans goldilocksCubic113_curve_envelope_le, hgood⟩

end

end ArkLibExamples.ReedSolomon.ConcreteCurveMCA
