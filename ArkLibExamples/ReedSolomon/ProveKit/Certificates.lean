/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.CurveCertificate
import ArkLibExamples.ReedSolomon.ProveKit.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile

/-!
# Refined first-order curve certificates for ProveKit

This module asks Lean to recompute the finite derivative-weighted supports, shifted heights, and
refined exceptional-count envelopes for every frozen row supported by the current generic curve
constructor.  The quantified theorems construct actual exceptional sets for arbitrary received
words; `E` is therefore a proved output rather than an assumed budget.

The finite curve constructor uses the direct weighted-degree consequence of the capped support,
including the endpoint `D = 1`.  Thus the three terminal `k=2` rows use the same frozen
`D = k-1` support as the other rows; no interpolation parameter or protocol parameter changes at
the endpoint.

The cap-sensitive curve refinement proves the E envelopes below. The derivative-sensitive
finite-list theorem proves the corresponding L ceilings from the same profiles.
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open _root_.ReedSolomon.CurveProfile _root_.ReedSolomon.CurveCertificate

noncomputable section

set_option maxRecDepth 4096

universe u

/-- All six rows in each Passport outer witness. -/
def passportOuterProfiles : Fin 6 → LineProfile := ![
  { n := 262144, k := 65536, agreement := 123208, multiplicity := 384,
    firstDerivativeCap := 168, totalJetCap := 688, batchingDegree := 1,
    supportDimension := 2264148617900, localRank := 8635900,
    columnY₀Weight := 483817790739660, height := 736047,
    heightSlots := 1666038244117319540 },
  { n := 131072, k := 8192, agreement := 29020, multiplicity := 48,
    firstDerivativeCap := 30, totalJetCap := 170, batchingDegree := 1,
    supportDimension := 3082501430, localRank := 23500,
    columnY₀Weight := 159352270730, height := 50274, heightSlots := 154813407122520 },
  { n := 65536, k := 1024, agreement := 6906, multiplicity := 40,
    firstDerivativeCap := 34, totalJetCap := 310, batchingDegree := 1,
    supportDimension := 1152690770, localRank := 17570,
    columnY₀Weight := 97151864530, height := 68717, heightSlots := 79113452468330 },
  { n := 32768, k := 128, agreement := 1782, multiplicity := 12,
    firstDerivativeCap := 12, totalJetCap := 168, batchingDegree := 1,
    supportDimension := 21923954, localRank := 637,
    columnY₀Weight := 1180950290, height := 1067, heightSlots := 22233832582 },
  { n := 16384, k := 16, agreement := 463, multiplicity := 8,
    firstDerivativeCap := 4, totalJetCap := 246, batchingDegree := 1,
    supportDimension := 2261415, localRank := 130,
    columnY₀Weight := 183988885, height := 1368, heightSlots := 2911888250 },
  { n := 8192, k := 2, agreement := 85, multiplicity := 4,
    firstDerivativeCap := 4, totalJetCap := 339, batchingDegree := 1,
    supportDimension := 289830, localRank := 35,
    columnY₀Weight := 32746300, height := 10454, heightSlots := 2997426350 }
]

def passportOuterSplits : Fin 6 → ℕ := ![65566, 8257, 1046, 201, 42, 5]

/-- All four profiles inside each Passport zero-knowledge proof. -/
def passportInternalProfiles : Fin 4 → LineProfile := ![
  { n := 4096, k := 1024, agreement := 1933, multiplicity := 96,
    firstDerivativeCap := 42, totalJetCap := 174, batchingDegree := 1,
    supportDimension := 571856054, localRank := 139105,
    columnY₀Weight := 30642993766, height := 6809, heightSlots := 3863696733974 },
  { n := 2048, k := 128, agreement := 453, multiplicity := 68,
    firstDerivativeCap := 34, totalJetCap := 241, batchingDegree := 1,
    supportDimension := 113922375, localRank := 55335,
    columnY₀Weight := 8565482205, height := 10622, heightSlots := 1201631907420 },
  { n := 1024, k := 16, agreement := 107, multiplicity := 16,
    firstDerivativeCap := 16, totalJetCap := 114, batchingDegree := 1,
    supportDimension := 1466947, localRank := 1428,
    columnY₀Weight := 51860693, height := 9703, heightSlots := 14183392995 },
  { n := 512, k := 2, agreement := 19, multiplicity := 12,
    firstDerivativeCap := 12, totalJetCap := 227, batchingDegree := 1,
    supportDimension := 339014, localRank := 637,
    columnY₀Weight := 25598976, height := 1919, heightSlots := 625307904 }
]

def passportInternalSplits : Fin 4 → ℕ := ![1028, 129, 16, 2]

/-- All four profiles in each cubic-Goldilocks lookup witness. -/
def goldilocksWitnessProfiles : Fin 4 → LineProfile := ![
  passportInternalProfiles 0,
  { n := 2048, k := 128, agreement := 453, multiplicity := 38,
    firstDerivativeCap := 23, totalJetCap := 133, batchingDegree := 1,
    supportDimension := 23738140, localRank := 11590,
    columnY₀Weight := 979761820, height := 394257, heightSlots := 9357971838300 },
  passportInternalProfiles 2,
  passportInternalProfiles 3
]

def goldilocksWitnessSplits : Fin 4 → ℕ := ![1028, 128, 16, 2]

/-- Initial curve profile of the independent cubic-Goldilocks blinding proof. -/
def goldilocksBlindProfile : LineProfile :=
  { n := 32, k := 8, agreement := 14, multiplicity := 64,
    firstDerivativeCap := 28, totalJetCap := 116, batchingDegree := 1,
    supportDimension := 1364160, localRank := 42050,
    columnY₀Weight := 51445884, height := 1405, heightSlots := 1866563076 }

def goldilocksBlindSplit : ℕ := 8

/-- The interpolation fields of a certificate row agree with the corresponding frozen protocol
row.  Computed support and height data are checked separately by `CurveVerification`. -/
def ProfileMatchesRound (p : LineProfile) (r : CodeRound) : Prop :=
  p.n = r.n ∧ p.k = r.k ∧ p.agreement = r.agreement ∧
    p.multiplicity = r.multiplicity ∧ p.firstDerivativeCap = r.derivativeCap ∧
    p.totalJetCap = r.jetDegree ∧ p.batchingDegree = 1

theorem passportOuterProfiles_match (i : Fin 6) :
    ProfileMatchesRound (passportOuterProfiles i) (passportOuterWitness.row i) := by
  fin_cases i <;> simp [ProfileMatchesRound, passportOuterProfiles, passportOuterWitness,
    codeRound]

theorem passportInternalProfiles_match (i : Fin 4) :
    ProfileMatchesRound (passportInternalProfiles i) (passportInternalZk.row i) := by
  fin_cases i <;> simp [ProfileMatchesRound, passportInternalProfiles, passportInternalZk,
    codeRound]

theorem goldilocksWitnessProfiles_match (i : Fin 4) :
    ProfileMatchesRound (goldilocksWitnessProfiles i) (goldilocksLookupWitness.row i) := by
  fin_cases i <;> simp [ProfileMatchesRound, goldilocksWitnessProfiles,
    passportInternalProfiles, goldilocksLookupWitness, codeRound]

theorem goldilocksBlindProfile_match :
    ProfileMatchesRound goldilocksBlindProfile (goldilocksLookupBlind.row 0) := by
  simp [ProfileMatchesRound, goldilocksBlindProfile, goldilocksLookupBlind, codeRound]

set_option maxHeartbeats 2000000 in
-- Kernel reduction of the six complete support tables requires an elevated local limit.
theorem passportOuterProfiles_verified (i : Fin 6) :
    (passportOuterProfiles i).CurveVerification := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel reduction of the four complete support tables requires an elevated local limit.
theorem passportInternalProfiles_verified (i : Fin 4) :
    (passportInternalProfiles i).CurveVerification := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel reduction of the lookup support tables requires an elevated local limit.
theorem goldilocksWitnessProfiles_verified (i : Fin 4) :
    (goldilocksWitnessProfiles i).CurveVerification := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel reduction of the blinding support table requires an elevated local limit.
theorem goldilocksBlindProfile_verified : goldilocksBlindProfile.CurveVerification := by
  decide +kernel

theorem passportOuterSplits_admissible (i : Fin 6) :
    (passportOuterProfiles i).k ≤ passportOuterSplits i ∧
      passportOuterSplits i ≤ (passportOuterProfiles i).agreement ∧
      (passportOuterProfiles i).agreement ≤ (passportOuterProfiles i).n := by
  fin_cases i <;> decide

theorem passportInternalSplits_admissible (i : Fin 4) :
    (passportInternalProfiles i).k ≤ passportInternalSplits i ∧
      passportInternalSplits i ≤ (passportInternalProfiles i).agreement ∧
      (passportInternalProfiles i).agreement ≤ (passportInternalProfiles i).n := by
  fin_cases i <;> decide

theorem goldilocksWitnessSplits_admissible (i : Fin 4) :
    (goldilocksWitnessProfiles i).k ≤ goldilocksWitnessSplits i ∧
      goldilocksWitnessSplits i ≤ (goldilocksWitnessProfiles i).agreement ∧
      (goldilocksWitnessProfiles i).agreement ≤ (goldilocksWitnessProfiles i).n := by
  fin_cases i <;> decide

theorem goldilocksBlindSplit_admissible :
    goldilocksBlindProfile.k ≤ goldilocksBlindSplit ∧
      goldilocksBlindSplit ≤ goldilocksBlindProfile.agreement ∧
      goldilocksBlindProfile.agreement ≤ goldilocksBlindProfile.n := by
  decide

/-- The refined curve expression proves every Passport outer E ceiling. -/
theorem passportOuter_envelopes_le (i : Fin 6) :
    _root_.ReedSolomon.CurveCertificate.envelope
      (passportOuterProfiles i) (passportOuterSplits i) ≤
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The refined curve expression proves every internal-zk E ceiling. -/
theorem passportInternal_envelopes_le (i : Fin 4) :
    _root_.ReedSolomon.CurveCertificate.envelope
      (passportInternalProfiles i) (passportInternalSplits i) ≤
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The refined curve expression proves every lookup-witness E ceiling. -/
theorem goldilocksWitness_envelopes_le (i : Fin 4) :
    _root_.ReedSolomon.CurveCertificate.envelope
      (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i) ≤
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The refined curve expression proves the lookup blinding E ceiling. -/
theorem goldilocksBlind_envelope_le :
    _root_.ReedSolomon.CurveCertificate.envelope
      goldilocksBlindProfile goldilocksBlindSplit ≤
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

theorem passportOuter_listEnvelopes_le (i : Fin 6) :
    tightListEnvelope (passportOuterProfiles i) ≤
      (passportOuterWitness.row ⟨i.val, by omega⟩).listSize := by
  fin_cases i <;> norm_num [tightListEnvelope, firstOrderTightListWeight,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.fixedFiberDerivativeImageDegree, passportOuterProfiles, passportOuterWitness,
    codeRound]

theorem passportInternal_listEnvelopes_le (i : Fin 4) :
    tightListEnvelope (passportInternalProfiles i) ≤
      (passportInternalZk.row ⟨i.val, by omega⟩).listSize := by
  fin_cases i <;> norm_num [tightListEnvelope, firstOrderTightListWeight,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.fixedFiberDerivativeImageDegree, passportInternalProfiles, passportInternalZk,
    codeRound]

theorem goldilocksWitness_listEnvelopes_le (i : Fin 4) :
    tightListEnvelope (goldilocksWitnessProfiles i) ≤
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).listSize := by
  fin_cases i
  · norm_num [tightListEnvelope, firstOrderTightListWeight, firstOrderCurveFiberStageOne,
      firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
      AffineHilbert.fixedFiberDerivativeImageDegree, goldilocksWitnessProfiles,
      passportInternalProfiles, goldilocksLookupWitness, codeRound]
  · norm_num [tightListEnvelope, firstOrderTightListWeight, firstOrderCurveFiberStageOne,
      firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
      AffineHilbert.fixedFiberDerivativeImageDegree, goldilocksWitnessProfiles,
      goldilocksLookupWitness, codeRound]
  · change tightListEnvelope (passportInternalProfiles 2) ≤
      (passportInternalZk.row 2).listSize
    exact passportInternal_listEnvelopes_le 2
  · change tightListEnvelope (passportInternalProfiles 3) ≤
      (passportInternalZk.row 3).listSize
    exact passportInternal_listEnvelopes_le 3

theorem goldilocksBlind_listEnvelope_le :
    tightListEnvelope goldilocksBlindProfile ≤ (goldilocksLookupBlind.row 0).listSize := by
  norm_num [tightListEnvelope, firstOrderTightListWeight, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.fixedFiberDerivativeImageDegree, goldilocksBlindProfile, goldilocksLookupBlind,
    codeRound]

theorem passportOuter_finiteListBound
    (i : Fin 6) {F : Type u} [Field F]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (received : Fin (passportOuterProfiles i).n → F)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (passportOuterProfiles i).k
      (passportOuterProfiles i).agreement P) :
    (S.card : ℚ) ≤ (passportOuterWitness.row ⟨i.val, by omega⟩).listSize := by
  apply (finiteListBound_of_profile (passportOuterProfiles_verified i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    domain received hchar S hS).trans
  exact passportOuter_listEnvelopes_le i

theorem passportInternal_finiteListBound
    (i : Fin 4) {F : Type u} [Field F]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (received : Fin (passportInternalProfiles i).n → F)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (passportInternalProfiles i).k
      (passportInternalProfiles i).agreement P) :
    (S.card : ℚ) ≤ (passportInternalZk.row ⟨i.val, by omega⟩).listSize := by
  apply (finiteListBound_of_profile (passportInternalProfiles_verified i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    domain received hchar S hS).trans
  exact passportInternal_listEnvelopes_le i

theorem goldilocksWitness_finiteListBound
    (i : Fin 4) {F : Type u} [Field F]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (received : Fin (goldilocksWitnessProfiles i).n → F)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (goldilocksWitnessProfiles i).k
      (goldilocksWitnessProfiles i).agreement P) :
    (S.card : ℚ) ≤ (goldilocksLookupWitness.row ⟨i.val, by omega⟩).listSize := by
  apply (finiteListBound_of_profile (goldilocksWitnessProfiles_verified i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    domain received hchar S hS).trans
  exact goldilocksWitness_listEnvelopes_le i

theorem goldilocksBlind_finiteListBound
    {F : Type u} [Field F]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (received : Fin goldilocksBlindProfile.n → F)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received goldilocksBlindProfile.k
      goldilocksBlindProfile.agreement P) :
    (S.card : ℚ) ≤ (goldilocksLookupBlind.row 0).listSize := by
  apply (finiteListBound_of_profile goldilocksBlindProfile_verified (by decide) (by decide)
    (by decide) (by decide) domain received hchar S hS).trans
  exact goldilocksBlind_listEnvelope_le

open Classical in
/-- Each supported Passport outer row constructs an actual exceptional set, uniformly over its
received pair and candidate polynomial. -/
theorem passportOuter_exists_exceptional
    (i : Fin 6) {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (values : Fin ((passportOuterProfiles i).batchingDegree + 1) →
      Fin (passportOuterProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
          (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportOuterProfiles i).k →
        (passportOuterProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportOuterProfiles i).k z P := by
  exact _root_.ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement
    (F := F) (E := E) (p := passportOuterProfiles i)
    (passportOuterProfiles_verified i) (passportOuterSplits i)
    (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (passportOuterSplits_admissible i) (by fin_cases i <;> decide)
    (passportOuter_envelopes_le i) domain values iota hchar

open Classical in
/-- Each supported Passport internal row constructs its advertised actual exceptional set. -/
theorem passportInternal_exists_exceptional
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (values : Fin ((passportInternalProfiles i).batchingDegree + 1) →
      Fin (passportInternalProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
          (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportInternalProfiles i).k →
        (passportInternalProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportInternalProfiles i).k z P := by
  exact _root_.ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement
    (F := F) (E := E) (p := passportInternalProfiles i)
    (passportInternalProfiles_verified i) (passportInternalSplits i)
    (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount
    (passportInternalSplits_admissible i) (by fin_cases i <;> decide)
    (passportInternal_envelopes_le i) domain values iota hchar

open Classical in
/-- Each supported lookup-witness row constructs its advertised actual exceptional set. -/
theorem goldilocksWitness_exists_exceptional
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (values : Fin ((goldilocksWitnessProfiles i).batchingDegree + 1) →
      Fin (goldilocksWitnessProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
          (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (goldilocksWitnessProfiles i).k →
        (goldilocksWitnessProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (goldilocksWitnessProfiles i).k z P := by
  exact _root_.ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement
    (F := F) (E := E) (p := goldilocksWitnessProfiles i)
    (goldilocksWitnessProfiles_verified i) (goldilocksWitnessSplits i)
    (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (goldilocksWitnessSplits_admissible i) (by fin_cases i <;> decide)
    (goldilocksWitness_envelopes_le i) domain values iota hchar

open Classical in
/-- The lookup blinding profile constructs its advertised actual exceptional set. -/
theorem goldilocksBlind_exists_exceptional
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (values : Fin 2 → Fin goldilocksBlindProfile.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ (goldilocksLookupBlind.row 0).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < goldilocksBlindProfile.k →
        goldilocksBlindProfile.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          goldilocksBlindProfile.k z P := by
  exact _root_.ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement
    (F := F) (E := E) (p := goldilocksBlindProfile) goldilocksBlindProfile_verified
    goldilocksBlindSplit (goldilocksLookupBlind.row 0).exceptionalCount
    goldilocksBlindSplit_admissible (by decide) goldilocksBlind_envelope_le
    domain values iota hchar

/-- Every Passport outer row supplies the full-set scalar line-agreement interface with its
derived exceptional-count ceiling. -/
theorem passportOuter_lineExactAgreement
    (i : Fin 6) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).totalJetCap < ringChar F) :
    LineExactAgreementBound domain (passportOuterProfiles i).k
      (passportOuterProfiles i).agreement
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;>
    apply lineExactAgreementBound_of_powerAgreement_one domain <;>
    intro values <;>
    exact passportOuter_exists_exceptional _ domain values
      (algebraMap F (AlgebraicClosure F)) hchar

/-- Every Passport internal row supplies its full-set scalar line-agreement interface. -/
theorem passportInternal_lineExactAgreement
    (i : Fin 4) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).totalJetCap < ringChar F) :
    LineExactAgreementBound domain (passportInternalProfiles i).k
      (passportInternalProfiles i).agreement
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;>
    apply lineExactAgreementBound_of_powerAgreement_one domain <;>
    intro values <;>
    exact passportInternal_exists_exceptional _ domain values
      (algebraMap F (AlgebraicClosure F)) hchar

/-- Every cubic-Goldilocks witness row supplies its full-set scalar line-agreement interface. -/
theorem goldilocksWitness_lineExactAgreement
    (i : Fin 4) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).totalJetCap < ringChar F) :
    LineExactAgreementBound domain (goldilocksWitnessProfiles i).k
      (goldilocksWitnessProfiles i).agreement
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;>
    apply lineExactAgreementBound_of_powerAgreement_one domain <;>
    intro values <;>
    exact goldilocksWitness_exists_exceptional _ domain values
      (algebraMap F (AlgebraicClosure F)) hchar

/-- The cubic-Goldilocks blinding row supplies its scalar line-agreement interface. -/
theorem goldilocksBlind_lineExactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.totalJetCap < ringChar F) :
    LineExactAgreementBound domain goldilocksBlindProfile.k goldilocksBlindProfile.agreement
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  apply lineExactAgreementBound_of_powerAgreement_one domain
  intro values
  exact goldilocksBlind_exists_exceptional domain values
    (algebraMap F (AlgebraicClosure F)) hchar

end

end ArkLibExamples.ReedSolomon.ProveKit
