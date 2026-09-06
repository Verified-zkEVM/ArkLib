/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitAffine
import ArkLibExamples.ReedSolomon.ProveKitSharpLists
import ArkLibExamples.ReedSolomon.ProveKitSharpMCA

/-!
# Certified local ProveKit coding budgets

This module joins the semantic MCA and list-decoding theorems to the closed arithmetic for the
accepted ProveKit rows. It first transports the published sharp scalar list caps through the
rational-function packing of width-eight rows. It then packages, for the canonical challenge
fields, the affine MCA bound, the interleaved list bound, and the corresponding local slot,
query, and payload calculations.

The original BN254 package uses 109 queries and the published bounds
`E = 1126820196482631879700641773`, `L = 147000408479737`. The retuned BN254 package uses 108
queries and the independently derived bounds `E = 93006457356522169112176655917`,
`L = 1011109123693944`. The cubic Goldilocks package uses the revised 113-query row and bounds
`E = 14436064712520704240`, `L = 8279136487`.

## Reading this file alongside the paper

Section 6.3 (ProveKit: fewer WHIR openings) and Table 2 of the main paper use `E` for
exceptional challenges and `Λ` for close candidates. Here these are `exceptionalCount` and
`listSize`. Start with `GoldilocksCubic113CertifiedLocalBudget` or
`BN254Retuned108CertifiedLocalBudget`, then read the constructor theorem immediately below.
A `structure ... : Prop` lists the claims to prove; the theorem ending in `where` proves every
field by naming its supporting theorem. Thus the package itself is a conclusion.

In these statements, `domain : Fin 1048576 ↪ F` means any choice of distinct evaluation points.
The code dimension is 262144, so its messages have degree strictly below 262144.
`^⋈ (Fin 8)` packs eight codewords into each received row. `Lambda` is the worst-case number of
close codewords over all received words; `mcaError` supplies the corresponding uniform affine
agreement guarantee. `ENNReal.ofReal` and the casts to `ℚ`, `ℝ`, or `ℕ∞` change the number type,
not the numerical bound. `s` counts affine directions, and `hs : 1 ≤ s` excludes dimension zero.

The affine term uses the exact denominator `q - 1`; the list term uses `q`.
Each arithmetic field names a separate affected check. In particular, bounding the displayed
MCA-plus-list sum by `2^-128` does not sum it with the OOD, query, and opening slots.
The paper's expected authentication savings are proved in `ProveKitExpectedPayload`;
`payloadLowerBounds` below gives the conservative byte inequalities.

No exceptional or list bound is an input to the package theorems. The MCA bounds quantify over
all received affine families through `mcaError`, and the `Code.Lambda` bounds quantify over all
received width-eight words. The numerical fields reproduce the local error and raw-payload model;
they do not compose a whole protocol or model transcript and commitment behavior.
-/

open Polynomial Code CoreDefinitions LinearCode
open ReedSolomon ReedSolomon.ListDecoding ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open ConcreteFields
open ArkLib.FiniteFieldBudget

noncomputable section

/-- The sharp BN254 MCA endpoint and the original 109-query list endpoint use the same radius. -/
theorem sharpBN254OriginalRadius_eq_original109Radius :
    sharpBN254OriginalRadius = original109Radius := by
  rfl

/-- Capacity gap whose threshold is the published cubic-Goldilocks agreement count. -/
def goldilocksCubic113Gap : ℝ := 246119 / 1048576

/-- The cubic-Goldilocks gap gives threshold `508263` and the radius used by the sharp MCA
endpoint. -/
theorem goldilocksCubic113_gap_spec :
    agreementThreshold goldilocksCubic113Gap 1048576 262144 = 508263 ∧
      capacityRadius goldilocksCubic113Gap 1048576 262144 = sharpGoldilocksCubic113Radius := by
  constructor
  · norm_num [agreementThreshold, goldilocksCubic113Gap]
  · rw [sharpGoldilocksCubic113Radius_coe]
    norm_num [capacityRadius, goldilocksCubic113Gap]

open Classical in
/-- Rational-function packing preserves the published sharp BN254 list cap at width eight. -/
theorem bn254_original109_widthEight_lambda_le_sharp
    {F : Type*} [Field F] (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → F)))
        (original109Radius : ℝ) ≤ (bn254.listSize : ℕ∞) := by
  have hpacked :=
    ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
      original109Gap (by norm_num [original109Gap]) (by norm_num) domain
        (L := bn254.listSize) (t := 8) (by
          intro received S hS
          have hcharRat : ringChar (RatFunc F) = 0 ∨
              max 1048576 688 < ringChar (RatFunc F) := by
            simpa [ReedSolomon.ringChar_ratFunc] using hchar
          have hS' : ∀ P ∈ S,
              IsAgreementSolution
                (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
                received 262144 492831 P := by
            intro P hP
            have hs := hS P hP
            rw [show agreementThreshold original109Gap 1048576 262144 = 492831 by
              exact original109_gap_spec.1] at hs
            simpa [IsAgreementSolution, polynomialAgreementSet] using hs
          have hb := bn254_finite_list_bound_sharp
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
              received hcharRat S hS'
          exact_mod_cast hb)
  rw [original109_gap_spec.2] at hpacked
  exact hpacked

open Classical in
/-- Rational-function packing preserves the published cubic-Goldilocks list cap at width eight. -/
theorem goldilocksCubic113_widthEight_lambda_le_sharp
    {F : Type*} [Field F] (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 30 < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → F)))
        (sharpGoldilocksCubic113Radius : ℝ) ≤ (goldilocksCubic113.listSize : ℕ∞) := by
  have hpacked :=
    ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
      goldilocksCubic113Gap (by norm_num [goldilocksCubic113Gap]) (by norm_num) domain
        (L := goldilocksCubic113.listSize) (t := 8) (by
          intro received S hS
          have hcharRat : ringChar (RatFunc F) = 0 ∨
              max 1048576 30 < ringChar (RatFunc F) := by
            simpa [ReedSolomon.ringChar_ratFunc] using hchar
          have hS' : ∀ P ∈ S,
              IsAgreementSolution
                (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
                received 262144 508263 P := by
            intro P hP
            have hs := hS P hP
            rw [show agreementThreshold goldilocksCubic113Gap 1048576 262144 = 508263 by
              exact goldilocksCubic113_gap_spec.1] at hs
            simpa [IsAgreementSolution, polynomialAgreementSet] using hs
          have hb := goldilocksCubic113_finite_list_bound_sharp
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
              received hcharRat S hS'
          exact_mod_cast hb)
  rw [goldilocksCubic113_gap_spec.2] at hpacked
  exact hpacked

/-! ## Closed arithmetic packages -/

/-- The original row's affine MCA loss and list term fit together in one local slot. The MCA
denominator is `q - 1`, as required by the affine-space reduction. -/
theorem bn254_original_affineMCA_list_slot_le :
    (bn254.exceptionalCount : ℚ) / (bn254.fieldSize - 1) +
        (2 * bn254.listSize : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 := by
  norm_num [bn254]

/-- The cubic row's affine MCA loss and list term fit together in one local slot. -/
theorem goldilocksCubic113_affineMCA_list_slot_le :
    (goldilocksCubic113.exceptionalCount : ℚ) / (goldilocksCubic113.fieldSize - 1) +
        (2 * goldilocksCubic113.listSize : ℚ) / goldilocksCubic113.fieldSize ≤
      (1 : ℚ) / 2 ^ 128 := by
  norm_num [goldilocksCubic113]

/-- The accepted retuned row also uses the affine denominator in its combined local slot. -/
theorem bn254_retuned108_affineMCA_list_slot_le :
    (retunedExceptionalCount : ℚ) / (bn254.fieldSize - 1) +
        (2 * retunedListSize : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 := by
  norm_num [bn254, retunedExceptionalCount, retunedListSize]

open Classical in
/-- The retuned canonical BN254 endpoint before weakening its count-level MCA term. -/
theorem bn254Scalar_retuned108_widthEight_affine_mcaError_le_count
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((retunedExceptionalCount : ℝ) / (bn254.fieldSize - 1)) := by
  have hmca := ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 491867) (retunedExceptionalCount : ℝ)
      (retuned_lineAgreement domain (by
        right
        rw [bn254Scalar_ringChar]
        norm_num [BN254.scalarFieldSize]))
      retuned108Radius (by norm_num) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num [retuned108Radius])
      (by rw [← NNReal.coe_lt_coe]; norm_num [retuned108Radius])
      (by rw [retuned108Radius_coe]; norm_num)
  rw [bn254Scalar_card] at hmca
  simpa [BN254.scalarFieldSize, bn254] using hmca

open Classical in
/-- The original semantic MCA error plus its list term meets the shared local target. -/
theorem bn254Scalar_original109_mcaError_add_list_le
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) +
        ENNReal.ofReal ((2 * bn254.listSize : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  calc
    _ ≤ ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1)) +
          ENNReal.ofReal ((2 * bn254.listSize : ℝ) / bn254.fieldSize) :=
      add_le_add
        (bn254Scalar_original109_widthEight_affine_mcaError_le_count domain hs) le_rfl
    _ = ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1) +
          (2 * bn254.listSize : ℝ) / bn254.fieldSize) := by
      rw [ENNReal.ofReal_add (by norm_num [bn254]) (by norm_num [bn254])]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) :=
      ENNReal.ofReal_le_ofReal (by norm_num [bn254])

open Classical in
/-- The cubic-Goldilocks semantic MCA error plus its list term meets the shared local target. -/
theorem goldilocksCubic113_mcaError_add_list_le
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) +
        ENNReal.ofReal ((2 * goldilocksCubic113.listSize : ℝ) /
          goldilocksCubic113.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  calc
    _ ≤ ENNReal.ofReal ((goldilocksCubic113.exceptionalCount : ℝ) /
          (goldilocksCubic113.fieldSize - 1)) +
        ENNReal.ofReal ((2 * goldilocksCubic113.listSize : ℝ) /
          goldilocksCubic113.fieldSize) :=
      add_le_add
        (goldilocksCubic113_concrete_widthEight_affine_mcaError_le_count domain hs) le_rfl
    _ = ENNReal.ofReal ((goldilocksCubic113.exceptionalCount : ℝ) /
          (goldilocksCubic113.fieldSize - 1) +
        (2 * goldilocksCubic113.listSize : ℝ) / goldilocksCubic113.fieldSize) := by
      rw [ENNReal.ofReal_add (by norm_num [goldilocksCubic113])
        (by norm_num [goldilocksCubic113])]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) :=
      ENNReal.ofReal_le_ofReal (by norm_num [goldilocksCubic113])

open Classical in
/-- The retuned semantic MCA error plus its list term meets the shared local target. -/
theorem bn254Scalar_retuned108_mcaError_add_list_le
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) +
        ENNReal.ofReal ((2 * retunedListSize : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  calc
    _ ≤ ENNReal.ofReal ((retunedExceptionalCount : ℝ) / (bn254.fieldSize - 1)) +
          ENNReal.ofReal ((2 * retunedListSize : ℝ) / bn254.fieldSize) :=
      add_le_add
        (bn254Scalar_retuned108_widthEight_affine_mcaError_le_count domain hs) le_rfl
    _ = ENNReal.ofReal ((retunedExceptionalCount : ℝ) / (bn254.fieldSize - 1) +
          (2 * retunedListSize : ℝ) / bn254.fieldSize) := by
      rw [ENNReal.ofReal_add
        (by norm_num [bn254, retunedExceptionalCount])
        (by norm_num [bn254, retunedListSize])]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) :=
      ENNReal.ofReal_le_ofReal
        (by norm_num [bn254, retunedExceptionalCount, retunedListSize])

/-- All closed local arithmetic attached to the accepted original BN254 row. -/
structure BN254OriginalArithmetic : Prop where
  -- Pairwise candidate collisions at the initial out-of-domain sample(s).
  initialOodSlot :
    bn254.listSize * (bn254.listSize - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
      2 * bn254.fieldSize
  listSlot : 2 * bn254.listSize * 2 ^ 128 ≤ bn254.fieldSize
  affineMCAAndListSlot :
    (bn254.exceptionalCount : ℚ) / (bn254.fieldSize - 1) +
        (2 * bn254.listSize : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128
  openingSlot : 2 * (1 + bn254.queries) * 160 * 2 ^ 128 ≤ bn254.fieldSize
  -- The exact query/grinding inequality; the stored hash threshold is inclusive.
  querySelection :
    (bn254.powThreshold + 1) * bn254.agreementNumerator ^ bn254.queries * 2 ^ 128 ≤
        2 ^ 64 * bn254.n ^ bn254.queries ∧
      2 ^ 64 * bn254.n ^ (bn254.queries - 1) <
        (bn254.powThreshold + 1) *
          bn254.agreementNumerator ^ (bn254.queries - 1) * 2 ^ 128
  payloadLowerBounds :
    (bn254.nominalQueries - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 4032 ∧
      (bn254.zeroSlackQueryReference - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 2240

/-- All closed local arithmetic attached to the published cubic-Goldilocks row. -/
structure GoldilocksCubic113Arithmetic : Prop where
  -- Pairwise candidate collisions at the initial out-of-domain sample(s).
  initialOodSlot :
    goldilocksCubic113.listSize * (goldilocksCubic113.listSize - 1) *
          (goldilocksCubic113.vectorSize - 1) ^ 2 * 2 ^ 128 ≤
      2 * goldilocksCubic113.fieldSize ^ 2
  listSlot : 2 * goldilocksCubic113.listSize * 2 ^ 128 ≤ goldilocksCubic113.fieldSize
  affineMCAAndListSlot :
    (goldilocksCubic113.exceptionalCount : ℚ) / (goldilocksCubic113.fieldSize - 1) +
        (2 * goldilocksCubic113.listSize : ℚ) / goldilocksCubic113.fieldSize ≤
      (1 : ℚ) / 2 ^ 128
  openingSlot :
    2 * (1 + goldilocksCubic113.queries) * 160 * 2 ^ 128 ≤ goldilocksCubic113.fieldSize
  -- The exact query/grinding inequality; the stored hash threshold is inclusive.
  querySelection :
    (goldilocksCubic113.powThreshold + 1) *
          goldilocksCubic113.agreementNumerator ^ goldilocksCubic113.queries * 2 ^ 128 ≤
        2 ^ 64 * goldilocksCubic113.n ^ goldilocksCubic113.queries ∧
      2 ^ 64 * goldilocksCubic113.n ^ (goldilocksCubic113.queries - 1) <
        (goldilocksCubic113.powThreshold + 1) *
          goldilocksCubic113.agreementNumerator ^ (goldilocksCubic113.queries - 1) * 2 ^ 128
  payloadLowerBounds :
    (goldilocksCubic113.nominalQueries - goldilocksCubic113.queries) *
          (goldilocksCubic113.interleavingWidth * goldilocksCubic113.fieldBytes - 32) -
        (goldilocksCubic113.initialOodSamples - 1) * goldilocksCubic113.extensionBytes = 424 ∧
      (goldilocksCubic113.zeroSlackQueryReference - goldilocksCubic113.queries) *
          (goldilocksCubic113.interleavingWidth * goldilocksCubic113.fieldBytes - 32) -
        (goldilocksCubic113.initialOodSamples - 1) * goldilocksCubic113.extensionBytes = 168

/-- Closed local arithmetic for the accepted retuned 108-query BN254 option. -/
structure BN254Retuned108Arithmetic : Prop where
  -- Pairwise candidate collisions at the initial out-of-domain sample(s).
  initialOodSlot :
    (retunedListSize : ℕ) * (retunedListSize - 1) * (2097152 - 1) * 2 ^ 128 ≤
      2 * bn254.fieldSize
  affineMCAAndListSlot :
    (retunedExceptionalCount : ℚ) / (bn254.fieldSize - 1) +
        (2 * retunedListSize : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128
  openingSlot : (2 * (1 + 108) * 160 : ℕ) * 2 ^ 128 ≤ bn254.fieldSize
  -- The exact query/grinding inequality; the stored hash threshold is inclusive.
  querySelection :
    QueryMeetsTarget (2 ^ 64) 17350852076870155 491867 1048576 108 128
  -- Why 109 remains an alternative: 108 needs 8.2--8.3% more expected grinding.
  grindingWork :
    (1082 : ℚ) / 1000 <
        (bn254.powThreshold + 1 : ℚ) / (17350852076870155 + 1) ∧
      (bn254.powThreshold + 1 : ℚ) / (17350852076870155 + 1) < (1083 : ℚ) / 1000
  extraPayloadLowerBound :
    (127 - 108 : ℕ) * (8 * 32 - 32) = (127 - 109) * (8 * 32 - 32) + 224

/-- The original BN254 closed arithmetic has no supplied count premise. -/
theorem bn254OriginalArithmetic : BN254OriginalArithmetic where
  -- Pairwise candidate collisions at the initial out-of-domain sample(s).
  initialOodSlot := bn254_changed_slots_meet_target.1
  listSlot := bn254_changed_slots_meet_target.2.2.1
  affineMCAAndListSlot := bn254_original_affineMCA_list_slot_le
  openingSlot := bn254_changed_slots_meet_target.2.2.2.2
  -- The exact query/grinding inequality; the stored hash threshold is inclusive.
  querySelection := bn254_query_selection
  payloadLowerBounds := bn254_payload_lower_bounds

/-- The cubic-Goldilocks closed arithmetic has no supplied count premise. -/
theorem goldilocksCubic113Arithmetic : GoldilocksCubic113Arithmetic where
  -- Pairwise candidate collisions at the initial out-of-domain sample(s).
  initialOodSlot := goldilocksCubic113_changed_slots_meet_target.1
  listSlot := goldilocksCubic113_changed_slots_meet_target.2.2.1
  affineMCAAndListSlot := goldilocksCubic113_affineMCA_list_slot_le
  openingSlot := goldilocksCubic113_changed_slots_meet_target.2.2.2.2
  -- The exact query/grinding inequality; the stored hash threshold is inclusive.
  querySelection := goldilocksCubic113_query_selection
  payloadLowerBounds := goldilocksCubic113_payload_lower_bounds

/-- The accepted retuned BN254 closed arithmetic has no supplied count premise. -/
theorem bn254Retuned108Arithmetic : BN254Retuned108Arithmetic where
  -- Pairwise candidate collisions at the initial out-of-domain sample(s).
  initialOodSlot := retuned_count_slots.2.1
  affineMCAAndListSlot := bn254_retuned108_affineMCA_list_slot_le
  openingSlot := retuned_count_slots.2.2
  -- The exact query/grinding inequality; the stored hash threshold is inclusive.
  querySelection := retuned_query108
  -- Why 109 remains an alternative: 108 needs 8.2--8.3% more expected grinding.
  grindingWork := retuned_grinding_work
  extraPayloadLowerBound := retuned_extra_payload_lower_bound

/-! ## Canonical-field bundles -/

/-- Semantic coding bounds and local arithmetic for the accepted original BN254 row. -/
structure BN254OriginalCertifiedLocalBudget {s : ℕ}
    (domain : Fin 1048576 ↪ BN254Scalar) : Prop where
  -- All received affine families: the exceptional-count bound becomes E / (q - 1).
  affineMCA :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1))
  -- The combined changed algebraic slot, including the two list-dependent terms.
  affineMCAAndList :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) +
        ENNReal.ofReal ((2 * bn254.listSize : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128)
  -- For every received width-eight word, at most L codewords lie within this radius.
  interleavedList :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → BN254Scalar)))
        (original109Radius : ℝ) ≤ (bn254.listSize : ℕ∞)
  -- The remaining named query/OOD/opening/payload checks are proved as part of the package.
  arithmetic : BN254OriginalArithmetic

/-- Semantic coding bounds and local arithmetic for the published cubic-Goldilocks row. -/
structure GoldilocksCubic113CertifiedLocalBudget {s : ℕ}
    (domain : Fin 1048576 ↪ GoldilocksCubic) : Prop where
  -- All received affine families: the exceptional-count bound becomes E / (q - 1).
  affineMCA :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) ≤
      ENNReal.ofReal ((goldilocksCubic113.exceptionalCount : ℝ) /
        (goldilocksCubic113.fieldSize - 1))
  -- The combined changed algebraic slot, including the two list-dependent terms.
  affineMCAAndList :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubic113Radius : ℝ) +
        ENNReal.ofReal ((2 * goldilocksCubic113.listSize : ℝ) /
          goldilocksCubic113.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128)
  -- For every received width-eight word, at most L codewords lie within this radius.
  interleavedList :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → GoldilocksCubic)))
        (sharpGoldilocksCubic113Radius : ℝ) ≤ (goldilocksCubic113.listSize : ℕ∞)
  -- The remaining named query/OOD/opening/payload checks are proved as part of the package.
  arithmetic : GoldilocksCubic113Arithmetic

/-- Semantic coding bounds and local arithmetic for the accepted retuned 108-query BN254 row. -/
structure BN254Retuned108CertifiedLocalBudget {s : ℕ}
    (domain : Fin 1048576 ↪ BN254Scalar) : Prop where
  -- All received affine families: the exceptional-count bound becomes E / (q - 1).
  affineMCA :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((retunedExceptionalCount : ℝ) / (bn254.fieldSize - 1))
  -- The combined changed algebraic slot, including the two list-dependent terms.
  affineMCAAndList :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) +
        ENNReal.ofReal ((2 * retunedListSize : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128)
  -- For every received width-eight word, at most L codewords lie within this radius.
  interleavedList :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → BN254Scalar)))
        (retuned108Radius : ℝ) ≤ (retunedListSize : ℕ∞)
  -- The remaining named query/OOD/opening/payload checks are proved as part of the package.
  arithmetic : BN254Retuned108Arithmetic

open Classical in
/-- Construct the complete local original-BN254 package from the evaluation domain alone. -/
theorem bn254Scalar_original109_certifiedLocalBudget
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    BN254OriginalCertifiedLocalBudget (s := s) domain where
  -- Each assignment supplies a proof of the matching field above, starting with actual MCA.
  affineMCA := bn254Scalar_original109_widthEight_affine_mcaError_le_count domain hs
  affineMCAAndList := bn254Scalar_original109_mcaError_add_list_le domain hs
  interleavedList := bn254_original109_widthEight_lambda_le_sharp domain (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize])
  arithmetic := bn254OriginalArithmetic

open Classical in
/-- Construct the complete local cubic-Goldilocks package from the evaluation domain alone. -/
theorem goldilocksCubic113_certifiedLocalBudget
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    GoldilocksCubic113CertifiedLocalBudget (s := s) domain where
  -- Each assignment supplies a proof of the matching field above, starting with actual MCA.
  affineMCA := goldilocksCubic113_concrete_widthEight_affine_mcaError_le_count domain hs
  affineMCAAndList := goldilocksCubic113_mcaError_add_list_le domain hs
  interleavedList := goldilocksCubic113_widthEight_lambda_le_sharp domain (by
    right
    rw [goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize])
  arithmetic := goldilocksCubic113Arithmetic

open Classical in
/-- Construct the complete local retuned-BN254 package from the evaluation domain alone. -/
theorem bn254Scalar_retuned108_certifiedLocalBudget
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    BN254Retuned108CertifiedLocalBudget (s := s) domain where
  -- Each assignment supplies a proof of the matching field above, starting with actual MCA.
  affineMCA := bn254Scalar_retuned108_widthEight_affine_mcaError_le_count domain hs
  affineMCAAndList := bn254Scalar_retuned108_mcaError_add_list_le domain hs
  interleavedList := retuned108_widthEight_lambda_le domain (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize])
  arithmetic := bn254Retuned108Arithmetic

end

end ArkLibExamples.ReedSolomon.ProveKit
