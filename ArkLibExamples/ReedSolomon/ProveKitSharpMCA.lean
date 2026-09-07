/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AffineAgreementBounds
import ArkLibExamples.ReedSolomon.ConcreteCurveMCA
import ArkLibExamples.ReedSolomon.Fields

/-!
# Sharp affine MCA endpoints for the ProveKit profiles

The concrete polynomial-curve construction gives an exceptional set for every pair of received
scalar words. At batching degree one, exact power agreement is exact line agreement. This module
uses that bridge, row-wise interleaving invariance, and the affine-space reduction to obtain MCA
bounds for the actual width-eight ProveKit codes.

The BN254 theorem covers the accepted original 109-query row, with agreement threshold `492831`
and radius `555745 / 1048576`. The cubic-Goldilocks theorem covers its published row, with
agreement threshold `508263` and radius `540313 / 1048576`. Their exceptional budgets are the
sharp counts recorded in `ProveKit.bn254.exceptionalCount` and
`ProveKit.goldilocksCubic113.exceptionalCount`.

The canonical corollaries instantiate CompPoly's BN254 scalar field and Mathlib's degree-three
Goldilocks field. They quantify over every positive affine dimension and every family of received
width-eight words through `mcaError`; the only remaining input is the evaluation-domain embedding.

These are coding-theoretic MCA statements. Query sampling, proof-of-work grinding, transcript
generation, commitments, and composition with other protocol error terms are outside their scope.
-/

open Code CoreDefinitions LinearCode Polynomial
open ReedSolomon ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open ConcreteFields

noncomputable section

/-- Relative decoding radius of the accepted original 109-query BN254 row. -/
def sharpBN254OriginalRadius : NNReal := 555745 / 1048576

/-- Relative decoding radius of the published cubic-Goldilocks row. -/
def sharpGoldilocksCubic113Radius : NNReal := 540313 / 1048576

@[simp] theorem sharpBN254OriginalRadius_coe :
    (sharpBN254OriginalRadius : ℝ) = 555745 / 1048576 := by
  norm_num [sharpBN254OriginalRadius]

@[simp] theorem sharpGoldilocksCubic113Radius_coe :
    (sharpGoldilocksCubic113Radius : ℝ) = 540313 / 1048576 := by
  norm_num [sharpGoldilocksCubic113Radius]

universe u

/-- The sharp BN254 certificate over an algebraically closed extension. One exceptional set is
chosen before the extension-field challenge and candidate polynomial; the recovered correlated
pair has base-field coefficients and the complete agreement sets are equal. -/
theorem bn254_exists_exceptional_exact_correlatedPair_sharp
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ bn254.exceptionalCount ∧
      (exceptional.card : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < 262144 →
        492831 ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota 262144 z P := by
  have hchar' : ringChar F = 0 ∨ max (262144 - 1) 688 < ringChar F :=
    hchar.imp_right fun hpos ↦
      (max_le_max (by norm_num : 262144 - 1 ≤ 1048576) le_rfl).trans_lt hpos
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := 262143) (A := 492831) (m := 384) (M := 168) (mu := 688)
      (k := 262144) (h := 867623) (n := 1048576) (K := 262144)
      (L := 262197) (ell := 1) domain ![f, g] iota
      (by norm_num) (by norm_num) (by norm_num)
      ConcreteCurveMCA.bn254_curve_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hchar'
  have hcardSharp : (exceptional.card : ℚ) ≤ bn254.exceptionalCount :=
    hcard.trans ConcreteCurveMCA.bn254_curve_envelope_le
  refine ⟨exceptional, hcardSharp, ?_, ?_⟩
  · calc
      (exceptional.card : ℚ) / bn254.fieldSize ≤
          bn254.exceptionalCount / bn254.fieldSize := by
            exact div_le_div_of_nonneg_right hcardSharp (by positivity)
      _ ≤ (1 : ℚ) / 2 ^ 128 := by norm_num [bn254]
  · intro z hz P hP hA
    apply exactCorrelatedPair_of_powerAgreement_one domain ![f, g] iota z P
    apply hgood z hz P hP
    have hreceived : powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
        (fun i ↦ iota (f i) + z * iota (g i)) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    rw [hreceived]
    exact hA

/-- The preceding sharp extension-field theorem at the pinned BN254 scalar characteristic. -/
theorem bn254_scalar_exists_exceptional_exact_correlatedPair_sharp
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) (iota : F →+* E)
    (hscalar : ringChar F = bn254.fieldSize) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ bn254.exceptionalCount ∧
      (exceptional.card : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < 262144 →
        492831 ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota 262144 z P := by
  apply bn254_exists_exceptional_exact_correlatedPair_sharp domain f g iota
  right
  rw [hscalar]
  norm_num [bn254]

/-- The sharp BN254 curve certificate supplies the scalar exact-line interface. -/
theorem bn254_sharp_lineAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    LineExactAgreementBound domain 262144 492831
      bn254.exceptionalCount := by
  apply lineExactAgreementBound_of_powerAgreement_one domain
    (bn254.exceptionalCount : ℚ)
  intro values
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ConcreteCurveMCA.bn254_exists_exceptional_exact_powerAgreement
      (E := AlgebraicClosure F) domain values
      (algebraMap F (AlgebraicClosure F)) hchar
  exact ⟨exceptional, by simpa only [bn254] using hcard, hgood⟩

/-- The sharp cubic-Goldilocks curve certificate supplies the scalar exact-line interface. -/
theorem goldilocksCubic113_sharp_lineAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    LineExactAgreementBound domain 262144 508263
      goldilocksCubic113.exceptionalCount := by
  apply lineExactAgreementBound_of_powerAgreement_one domain
    (goldilocksCubic113.exceptionalCount : ℚ)
  intro values
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ConcreteCurveMCA.goldilocksCubic113_exists_exceptional_exact_powerAgreement
      (E := AlgebraicClosure F) domain values
      (algebraMap F (AlgebraicClosure F))
      hchar
  exact ⟨exceptional, by simpa only [goldilocksCubic113] using hcard, hgood⟩

open Classical in
/-- The sharp original BN254 certificate gives the count-level affine MCA bound. -/
theorem bn254_original109_widthEight_affine_mcaError_le_count
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((bn254.exceptionalCount : ℝ) /
        ((Fintype.card F : ℝ) - 1)) := by
  exact ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 492831) (bn254.exceptionalCount : ℝ)
      (bn254_sharp_lineAgreement domain hchar)
      sharpBN254OriginalRadius (by norm_num [bn254]) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpBN254OriginalRadius])
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpBN254OriginalRadius])
      (by rw [sharpBN254OriginalRadius_coe]; norm_num [bn254])

open Classical in
/-- The sharp original BN254 count-level bound is below the local 128-bit target. -/
theorem bn254_original109_widthEight_affine_mcaError_le_sharp
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hcard : Fintype.card F = bn254.fieldSize) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := bn254_original109_widthEight_affine_mcaError_le_count domain hchar hs
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [bn254]))

open Classical in
/-- The sharp cubic-Goldilocks certificate gives the count-level affine MCA bound. -/
theorem goldilocksCubic113_widthEight_affine_mcaError_le_count
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) ≤
      ENNReal.ofReal ((goldilocksCubic113.exceptionalCount : ℝ) /
        ((Fintype.card F : ℝ) - 1)) := by
  exact ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 508263) (goldilocksCubic113.exceptionalCount : ℝ)
      (goldilocksCubic113_sharp_lineAgreement domain hchar)
      sharpGoldilocksCubic113Radius (by norm_num [goldilocksCubic113]) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpGoldilocksCubic113Radius])
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpGoldilocksCubic113Radius])
      (by rw [sharpGoldilocksCubic113Radius_coe]; norm_num [goldilocksCubic113])

open Classical in
/-- The cubic-Goldilocks count-level bound is below the local 128-bit target. -/
theorem goldilocksCubic113_widthEight_affine_mcaError_le_sharp
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hcard : Fintype.card F = goldilocksCubic113.fieldSize) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := goldilocksCubic113_widthEight_affine_mcaError_le_count domain hchar hs
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [goldilocksCubic113]))

open Classical in
/-- The canonical BN254 scalar field retains the exact count-level affine MCA bound. -/
theorem bn254Scalar_original109_widthEight_affine_mcaError_le_count
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1)) := by
  have hmca := bn254_original109_widthEight_affine_mcaError_le_count domain (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize]) hs
  rw [bn254Scalar_card] at hmca
  simpa [BN254.scalarFieldSize, bn254] using hmca

open Classical in
/-- The accepted original BN254 theorem on the canonical scalar field. -/
theorem bn254Scalar_original109_widthEight_affine_mcaError_le_sharp
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  apply bn254_original109_widthEight_affine_mcaError_le_sharp domain
  · right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize, bn254]
  · rw [bn254Scalar_card]
    norm_num [BN254.scalarFieldSize, bn254]
  · exact hs

open Classical in
/-- The canonical cubic Goldilocks field retains the exact count-level affine MCA bound. -/
theorem goldilocksCubic113_concrete_widthEight_affine_mcaError_le_count
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) ≤
      ENNReal.ofReal ((goldilocksCubic113.exceptionalCount : ℝ) /
        (goldilocksCubic113.fieldSize - 1)) := by
  have hmca := goldilocksCubic113_widthEight_affine_mcaError_le_count domain (by
    right
    rw [goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize]) hs
  rw [goldilocksCubic_card] at hmca
  simpa [Goldilocks.fieldSize, goldilocksCubic113] using hmca

open Classical in
/-- The published cubic-Goldilocks theorem on the canonical degree-three field. -/
theorem goldilocksCubic113_concrete_widthEight_affine_mcaError_le_sharp
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  apply goldilocksCubic113_widthEight_affine_mcaError_le_sharp domain
  · right
    rw [goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize, goldilocksCubic113]
  · rw [goldilocksCubic_card]
    norm_num [Goldilocks.fieldSize, goldilocksCubic113]
  · exact hs

end

end ArkLibExamples.ReedSolomon.ProveKit
