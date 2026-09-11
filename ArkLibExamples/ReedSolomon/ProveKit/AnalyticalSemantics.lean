/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.Analytical
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp

/-!
# Semantic certificates for the analytical ProveKit rows

This module connects the distinct MCA and scalar-list supports used by the two further
analytical ProveKit improvements to the retained squarefree semantic theorems. Each result is
local to one invocation selected by `copy`; no transcript-wide union or independence claim is
made here. The measured schedules in `Parameters.lean` remain unchanged.
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.AnalyticalSemantics

open ConcreteFields _root_.ReedSolomon.CurveCertificate
open _root_.ReedSolomon.CurveProfile

noncomputable section

set_option maxRecDepth 32768

local instance : DecidableEq BN254Scalar := Classical.decEq _
local instance : DecidableEq GoldilocksCubic := Classical.decEq _

/-- Passport fifth-row interpolation profile for its analytical MCA event. -/
def passportOuterMcaProfile : LineProfile where
  n := 16384
  k := 16
  agreement := 394
  multiplicity := 60
  firstDerivativeCap := 60
  totalJetCap := 1568
  batchingDegree := 1
  supportDimension := 1097099030
  localRank := 66185
  columnY₀Weight := 565822223150
  height := 43116
  heightSlots := 46737796653360

/-- Passport fifth-row interpolation profile for its independent analytical list event. -/
def passportOuterListProfile : LineProfile where
  n := 16384
  k := 16
  agreement := 394
  multiplicity := 56
  firstDerivativeCap := 53
  totalJetCap := 1391
  batchingDegree := 1
  supportDimension := 845055981
  localRank := 51562
  columnY₀Weight := 404744123511
  height := 1483758
  heightSlots := 1253454673189068

/-- Goldilocks first-row interpolation profile for its analytical MCA event. -/
def goldilocksLookupMcaProfile : LineProfile where
  n := 4096
  k := 1024
  agreement := 1933
  multiplicity := 96
  firstDerivativeCap := 42
  totalJetCap := 174
  batchingDegree := 1
  supportDimension := 571856054
  localRank := 139105
  columnY₀Weight := 30642993766
  height := 6809
  heightSlots := 3863696733974

/-- Goldilocks first-row interpolation profile for its independent analytical list event. -/
def goldilocksLookupListProfile : LineProfile where
  n := 4096
  k := 1024
  agreement := 1933
  multiplicity := 63
  firstDerivativeCap := 28
  totalJetCap := 118
  batchingDegree := 1
  supportDimension := 166303690
  localRank := 40600
  columnY₀Weight := 5841095610
  height := 441221
  heightSlots := 73371005613570

/-- The profile fields are exactly the fifth analytical Passport row and its two supports. -/
theorem passportOuterProfiles_match :
    passportOuterMcaProfile.n = (passportOuterAnalytical.row 4).n ∧
      passportOuterMcaProfile.k = (passportOuterAnalytical.row 4).k ∧
      passportOuterMcaProfile.agreement = (passportOuterAnalytical.row 4).agreement ∧
      { multiplicity := passportOuterMcaProfile.multiplicity,
        derivativeCap := passportOuterMcaProfile.firstDerivativeCap,
        jetDegree := passportOuterMcaProfile.totalJetCap } =
        passportOuterAnalyticalMcaSupport 4 ∧
      { multiplicity := passportOuterListProfile.multiplicity,
        derivativeCap := passportOuterListProfile.firstDerivativeCap,
        jetDegree := passportOuterListProfile.totalJetCap } =
        passportOuterAnalyticalListSupport 4 := by
  decide

/-- The profile fields are exactly the first analytical Goldilocks row and its two supports. -/
theorem goldilocksLookupProfiles_match :
    goldilocksLookupMcaProfile.n = (goldilocksLookupAnalytical.row 0).n ∧
      goldilocksLookupMcaProfile.k = (goldilocksLookupAnalytical.row 0).k ∧
      goldilocksLookupMcaProfile.agreement =
        (goldilocksLookupAnalytical.row 0).agreement ∧
      { multiplicity := goldilocksLookupMcaProfile.multiplicity,
        derivativeCap := goldilocksLookupMcaProfile.firstDerivativeCap,
        jetDegree := goldilocksLookupMcaProfile.totalJetCap } =
        goldilocksLookupAnalyticalMcaSupport 0 ∧
      { multiplicity := goldilocksLookupListProfile.multiplicity,
        derivativeCap := goldilocksLookupListProfile.firstDerivativeCap,
        jetDegree := goldilocksLookupListProfile.totalJetCap } =
        goldilocksLookupAnalyticalListSupport 0 := by
  decide

set_option maxHeartbeats 2000000 in
-- Kernel evaluation checks the complete Passport MCA support table.
theorem passportOuterMcaProfile_verified : passportOuterMcaProfile.CurveVerification := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel evaluation checks the complete Passport list support table.
theorem passportOuterListProfile_verified : passportOuterListProfile.CurveVerification := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel evaluation checks the complete Goldilocks MCA support table.
theorem goldilocksLookupMcaProfile_verified :
    goldilocksLookupMcaProfile.CurveVerification := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Kernel evaluation checks the complete Goldilocks list support table.
theorem goldilocksLookupListProfile_verified :
    goldilocksLookupListProfile.CurveVerification := by
  decide +kernel

theorem passportOuterMcaSplit_admissible :
    passportOuterMcaProfile.k ≤ 19 ∧ 19 ≤ passportOuterMcaProfile.agreement ∧
      passportOuterMcaProfile.agreement ≤ passportOuterMcaProfile.n := by
  decide

theorem goldilocksLookupMcaSplit_admissible :
    goldilocksLookupMcaProfile.k ≤ 1028 ∧
      1028 ≤ goldilocksLookupMcaProfile.agreement ∧
      goldilocksLookupMcaProfile.agreement ≤ goldilocksLookupMcaProfile.n := by
  decide

/-- The squarefree semantic envelope fits the analytical Passport exceptional count. -/
theorem passportOuterMca_envelope_le :
    squarefreeSharpCurveEnvelope passportOuterMcaProfile 19 ≤ 40320140359804306 := by
  decide +kernel

/-- The independent squarefree list envelope fits the analytical Passport list count. -/
theorem passportOuterList_envelope_le :
    squarefreeListEnvelope passportOuterListProfile ≤ 180429296 := by
  norm_num [squarefreeListEnvelope, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.fixedFiberDerivativeImageDegree, passportOuterListProfile,
    FirstOrder.Squarefree.ordinaryDegreeEnvelope]

/-- The squarefree semantic envelope fits the analytical Goldilocks exceptional count. -/
theorem goldilocksLookupMca_envelope_le :
    squarefreeSharpCurveEnvelope goldilocksLookupMcaProfile 1028 ≤
      12566666451549204 := by
  decide +kernel

/-- The independent squarefree list envelope fits the analytical Goldilocks list count. -/
theorem goldilocksLookupList_envelope_le :
    squarefreeListEnvelope goldilocksLookupListProfile ≤ 39721253 := by
  norm_num [squarefreeListEnvelope, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.fixedFiberDerivativeImageDegree, goldilocksLookupListProfile,
    FirstOrder.Squarefree.ordinaryDegreeEnvelope]

theorem passportOuterMca_characteristic :
    ringChar BN254Scalar = 0 ∨
      max (passportOuterMcaProfile.k - 1) passportOuterMcaProfile.firstDerivativeCap <
        ringChar BN254Scalar := by
  right
  rw [bn254Scalar_ringChar]
  norm_num [passportOuterMcaProfile, BN254.scalarFieldSize]

theorem passportOuterList_characteristic :
    ringChar BN254Scalar = 0 ∨
      max (passportOuterListProfile.k - 1) passportOuterListProfile.firstDerivativeCap <
        ringChar BN254Scalar := by
  right
  rw [bn254Scalar_ringChar]
  norm_num [passportOuterListProfile, BN254.scalarFieldSize]

theorem goldilocksLookupMca_characteristic :
    ringChar GoldilocksCubic = 0 ∨
      max (goldilocksLookupMcaProfile.k - 1) goldilocksLookupMcaProfile.firstDerivativeCap <
        ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  norm_num [goldilocksLookupMcaProfile, Goldilocks.fieldSize]

theorem goldilocksLookupList_characteristic :
    ringChar GoldilocksCubic = 0 ∨
      max (goldilocksLookupListProfile.k - 1)
          goldilocksLookupListProfile.firstDerivativeCap < ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  norm_num [goldilocksLookupListProfile, Goldilocks.fieldSize]

/-- Scalar list semantics for the fifth analytical Passport row. -/
theorem passportOuter_finiteList
    (_copy : Fin 2)
    (domain : Fin passportOuterListProfile.n ↪ BN254Scalar)
    (received : Fin passportOuterListProfile.n → BN254Scalar)
    (S : Finset BN254Scalar[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received passportOuterListProfile.k
      passportOuterListProfile.agreement P) :
    (S.card : ℝ) ≤ 180429296 := by
  apply (finiteSquarefreeListBound_of_profile passportOuterListProfile_verified rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) domain received
    passportOuterList_characteristic S hS).trans
  exact passportOuterList_envelope_le

/-- Scalar list semantics for the first analytical Goldilocks row. -/
theorem goldilocksLookup_finiteList
    (_copy : Fin 2)
    (domain : Fin goldilocksLookupListProfile.n ↪ GoldilocksCubic)
    (received : Fin goldilocksLookupListProfile.n → GoldilocksCubic)
    (S : Finset GoldilocksCubic[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received goldilocksLookupListProfile.k
      goldilocksLookupListProfile.agreement P) :
    (S.card : ℝ) ≤ 39721253 := by
  apply (finiteSquarefreeListBound_of_profile goldilocksLookupListProfile_verified rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) domain received
    goldilocksLookupList_characteristic S hS).trans
  exact goldilocksLookupList_envelope_le

/-- The complete close-polynomial set for the fifth analytical Passport row is finite and obeys
the advertised list bound. -/
theorem passportOuter_completeList
    (copy : Fin 2)
    (domain : Fin passportOuterListProfile.n ↪ BN254Scalar)
    (received : Fin passportOuterListProfile.n → BN254Scalar) :
    (closePolynomialSet domain received passportOuterListProfile.k
        passportOuterListProfile.agreement).Finite ∧
      ((closePolynomialSet domain received passportOuterListProfile.k
        passportOuterListProfile.agreement).ncard : ℝ) ≤ 180429296 := by
  classical
  let T := closePolynomialSet domain received passportOuterListProfile.k
    passportOuterListProfile.agreement
  have hfinite : T.Finite := closePolynomialSet_finite domain received (by decide)
  have hcard := passportOuter_finiteList copy domain received hfinite.toFinset (by
    intro P hP
    simpa [T, closePolynomialSet, IsAgreementSolution, polynomialAgreementSet] using
      (hfinite.mem_toFinset.mp hP))
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hcard

/-- The complete close-polynomial set for the first analytical Goldilocks row is finite and
obeys the advertised list bound. -/
theorem goldilocksLookup_completeList
    (copy : Fin 2)
    (domain : Fin goldilocksLookupListProfile.n ↪ GoldilocksCubic)
    (received : Fin goldilocksLookupListProfile.n → GoldilocksCubic) :
    (closePolynomialSet domain received goldilocksLookupListProfile.k
        goldilocksLookupListProfile.agreement).Finite ∧
      ((closePolynomialSet domain received goldilocksLookupListProfile.k
        goldilocksLookupListProfile.agreement).ncard : ℝ) ≤ 39721253 := by
  classical
  let T := closePolynomialSet domain received goldilocksLookupListProfile.k
    goldilocksLookupListProfile.agreement
  have hfinite : T.Finite := closePolynomialSet_finite domain received (by decide)
  have hcard := goldilocksLookup_finiteList copy domain received hfinite.toFinset (by
    intro P hP
    simpa [T, closePolynomialSet, IsAgreementSolution, polynomialAgreementSet] using
      (hfinite.mem_toFinset.mp hP))
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hcard

open Classical in
/-- Exact full-agreement recovery for the fifth analytical Passport-row MCA event. -/
theorem passportOuter_exists_exceptional
    (_copy : Fin 2)
    (domain : Fin passportOuterMcaProfile.n ↪ BN254Scalar)
    (values : Fin (passportOuterMcaProfile.batchingDegree + 1) →
      Fin passportOuterMcaProfile.n → BN254Scalar) :
    ∃ exceptional : Finset BN254Scalar,
      (exceptional.card : ℚ) ≤ 40320140359804306 ∧
      ∀ z ∉ exceptional, ∀ P : BN254Scalar[X], P.degree < passportOuterMcaProfile.k →
        passportOuterMcaProfile.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id BN254Scalar)
          passportOuterMcaProfile.k z P := by
  exact exists_exceptional_exact_powerAgreement_squarefree_sharp_le
    passportOuterMcaProfile_verified 19 40320140359804306
    passportOuterMcaSplit_admissible (by decide) (by decide) (by decide) (by decide)
    passportOuterMca_envelope_le domain values
    (algebraMap BN254Scalar (AlgebraicClosure BN254Scalar))
    passportOuterMca_characteristic

open Classical in
/-- Exact full-agreement recovery for the first analytical Goldilocks-row MCA event. -/
theorem goldilocksLookup_exists_exceptional
    (_copy : Fin 2)
    (domain : Fin goldilocksLookupMcaProfile.n ↪ GoldilocksCubic)
    (values : Fin (goldilocksLookupMcaProfile.batchingDegree + 1) →
      Fin goldilocksLookupMcaProfile.n → GoldilocksCubic) :
    ∃ exceptional : Finset GoldilocksCubic,
      (exceptional.card : ℚ) ≤ 12566666451549204 ∧
      ∀ z ∉ exceptional, ∀ P : GoldilocksCubic[X],
        P.degree < goldilocksLookupMcaProfile.k →
        goldilocksLookupMcaProfile.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic)
          goldilocksLookupMcaProfile.k z P := by
  exact exists_exceptional_exact_powerAgreement_squarefree_sharp_le
    goldilocksLookupMcaProfile_verified 1028 12566666451549204
    goldilocksLookupMcaSplit_admissible (by decide) (by decide) (by decide) (by decide)
    goldilocksLookupMca_envelope_le domain values
    (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
    goldilocksLookupMca_characteristic

end

end ArkLibExamples.ReedSolomon.ProveKit.AnalyticalSemantics
