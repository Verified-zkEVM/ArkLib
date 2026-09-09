/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrderCurve
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
/-!
# Appendix polynomial-curve agreement bounds

This module certifies the two published 512-word BN254 profiles separately from the main
concrete-profile table.

## Reading the statements

For an arbitrary evaluation-domain embedding and 512 received words, each theorem constructs
one base-field exceptional set before the challenge and candidate polynomial are chosen.
Outside that set, every sufficiently agreeing degree-bounded candidate has exact power
agreement with all 512 words. The displayed integers are proved cardinality ceilings, rather
than hypotheses supplied to the semantic theorem.

The `11 / 50` row uses the published interpolation witness verbatim. For the `439 / 2000` row,
the published internal witness has multiplicity 3072 and total-jet cap 5504. Its direct finite
sum is expensive for the kernel to reduce. The proof below instead checks a smaller witness
with multiplicity 384 and total-jet cap 717. This gives a strictly stronger envelope bound and
therefore proves the same published agreement and exceptional-count conclusion.

## Proof route

The finite height inequalities supply actual polynomial-curve interpolation certificates.
`exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight` then constructs the
exceptional set, performs the dimension-sensitive geometric count at the tight Taylor exponent,
and descends exact agreement from an algebraically closed extension to the base field. No final
exceptional-count or agreement conclusion is assumed.
-/

open Polynomial
open ReedSolomon
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.AppendixCurveMCA

noncomputable section

set_option maxRecDepth 4096

universe u

/-- The 512-word BN254 profile at gap `11 / 50` has the published exceptional ceiling. -/
theorem bn254_gap22_curve_envelope_le :
    firstOrderCurveBound 1048576 262144 262144 262197 492831 688 168 511 973916154
      (2 * 262144 - 3) (firstOrderCurveDirectRatio 1048576 262144 492831) ≤
      575805257522140069855911588994 := by
  decide +kernel

/-- A smaller witness for the 512-word BN254 row at gap `439 / 2000` is already below the
published exceptional ceiling. -/
theorem bn254_gap2195_curve_envelope_le :
    firstOrderCurveBound 1048576 262144 262144 262246 492307 717 168 511 263537005
      (2 * 262144 - 3) (firstOrderCurveDirectRatio 1048576 262144 492307) ≤
      2350054974909344148634572067848032 := by
  decide +kernel

/-- The gap-`11 / 50` height passes the actual polynomial-curve coefficient test. -/
theorem bn254_gap22_curve_interpolation_height :
    firstOrderCurveShiftedRowSlotBound 262143 492831 384 168 688 1048576 511 973916154 <
      firstOrderCurveShiftedHeightSlotCount 262143 492831 384 168 688 511 973916154 := by
  decide +kernel

/-- A smaller support gives a stronger certificate at gap `439 / 2000` than the published
ceiling. -/
theorem bn254_gap2195_curve_interpolation_height :
    firstOrderCurveShiftedRowSlotBound 262143 492307 384 168 717 1048576 511 263537005 <
      firstOrderCurveShiftedHeightSlotCount 262143 492307 384 168 717 511 263537005 := by
  decide +kernel

/-- The published 512-word BN254 profile at gap `11 / 50` constructs an actual exceptional
set with its recorded cardinality ceiling. -/
theorem bn254_gap22_exists_exceptional_exact_powerAgreement
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin 1048576 ↪ F) (values : Fin 512 → Fin 1048576 → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ 575805257522140069855911588994 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 262144 →
        492831 ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) 262144 z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := 262143) (A := 492831) (m := 384) (M := 168) (mu := 688)
      (k := 262144) (h := 973916154) (n := 1048576) (K := 262144)
      (L := 262197) (ell := 511) domain values iota
      (by norm_num) (by norm_num) (by norm_num) bn254_gap22_curve_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa using hchar)
  exact ⟨exceptional, hcard.trans bn254_gap22_curve_envelope_le, hgood⟩

/-- The published 512-word BN254 profile at gap `439 / 2000` constructs an actual exceptional
set with its recorded cardinality ceiling. -/
theorem bn254_gap2195_exists_exceptional_exact_powerAgreement
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin 1048576 ↪ F) (values : Fin 512 → Fin 1048576 → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ 2350054974909344148634572067848032 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 262144 →
        492307 ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) 262144 z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := 262143) (A := 492307) (m := 384) (M := 168) (mu := 717)
      (k := 262144) (h := 263537005) (n := 1048576) (K := 262144)
      (L := 262246) (ell := 511) domain values iota
      (by norm_num) (by norm_num) (by norm_num) bn254_gap2195_curve_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simpa using hchar)
  exact ⟨exceptional, hcard.trans bn254_gap2195_curve_envelope_le, hgood⟩

end

end ArkLibExamples.ReedSolomon.AppendixCurveMCA
