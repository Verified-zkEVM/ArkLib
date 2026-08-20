/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SecurityGames
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RevisedHybridGame
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SAmbientLazySampling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Section5Nonempty
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ConcreteHybrids
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HybridClaimInterfaces

/-!
# Revised proof of CO25 Lemma 5.1

`SecurityGames` contains the executable games and numerical definitions.  This module is the
proof layer for their Section 5 hybrid chain.  Keeping that dependency direction lets the
stateful first-bad proof import the revised game executor without an import cycle, and lets this
module consume the resulting exact Lemma 5.8 endpoints.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction.OracleDistribution

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : CodecCore pSpec U]
  [Section5Nonempty pSpec]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [VCVCompatible U]
  [VCVCompatible Salt] in
/-- The query-budget half of the revised Lemma 5.1 endpoint.  The paper charges only the
standard challenge-oracle calls introduced by the D2S bridge; ambient-oracle and unit-sampling
calls are deliberately outside this predicate.  A memo hit still reissues its corresponding
standard query, so the charge is exactly controlled by the prover's forward-permutation budget. -/
theorem d2sAlgoRevised_challengeQueryBound
    [Fintype U]
    [∀ i, Fintype (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Challenge i)]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    IsD2SAlgoChallengeQueryBound
      (ProverTransform.d2sAlgoRevised (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      maliciousProver tₕ tₚ tₚᵢ := by
  classical
  have hForward : OracleComp.IsQueryBoundP maliciousProver
      (ProverTransform.isD2SOuterForwardPermPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚ := by
    refine (OracleComp.isQueryBoundP_congr_pred
      (p := isLemma5_1PermQuery (oSpec := oSpec) (StmtIn := StmtIn) (U := U))
      (p' := ProverTransform.isD2SOuterForwardPermPoint
        (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) ?_).mp hBound.2.1
    rintro (_ | (_ | (_ | _))) <;> rfl
  have hChallenge :=
    ProverTransform.d2sAlgoRevised_isQueryBoundP_challenge_of_forward
      (T_H := T_H) (T_P := T_P) (Salt := Salt) maliciousProver tₚ hForward
  refine (OracleComp.isQueryBoundP_congr_pred
    (p := ProverTransform.isD2SOuterChallengePoint
      (oSpec := oSpec) (U := U)
      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
    (p' := isD2SAlgoChallengePoint (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (Salt := Salt)) ?_).mp ?_
  · rintro (_ | (_ | _)) <;> rfl
  · simpa only [θStar] using hChallenge

/-! ## Main lemma interface

The two declarations below retain the public Section 6 interface.  They deliberately refer to the
concrete transforms rather than an opaque witness, so downstream soundness reductions preserve
their endpoints by defeq.
-/

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
theorem lemma_5_1_inner
    [DecidableEq ι]
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ) :
      ∀ (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ),
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
      tvDist
        (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver
          (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
        (hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver
          (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
        ≤ (ηStar U tₕ tₚ tₚᵢ
          (DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ))
          (εcodec := codec.decodingBias) : ℝ)
      ∧ IsD2SAlgoChallengeQueryBound
          (ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
            (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          maliciousProver tₕ tₚ tₚᵢ := by
  intro maliciousProver hBound
  refine ⟨?_, d2sAlgoRevised_challengeQueryBound
    (T_H := T_H) (T_P := T_P) (Salt := Salt) maliciousProver tₕ tₚ tₚᵢ hBound⟩
  let T := tₕ + tₚ + tₚᵢ
  let nV := DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)
  have h01 :
      tvDist
          (Statement.Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver)
          (Statement.Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver) ≤
        Statement.badEventBound U (T + 1 + nV) := by
    simpa only [Statement.Claim521, Statement.HybridTVDist, T, nV] using
      (claim_5_21 (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver tₕ tₚ tₚᵢ) hBound
  have h12 :
      tvDist
          (Statement.Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver)
          (Statement.Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver) = 0 := by
    simpa only [Statement.Claim522, Statement.HybridTVDist] using
      claim_5_22 (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver
  have h24 :
      tvDist
          (Statement.Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver)
          (Statement.Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver) ≤
        Statement.etaStarCodecTerm (tₚ : ℝ)
          (iSup fun i => (codec.decodingBias i : ℝ))
          (∑ i, (codec.decodingBias i : ℝ)) + Statement.Dcap U T nV := by
    simpa only [Statement.Claim524, Statement.HybridTVDist, T, nV] using
      (claim_5_24 (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver tₕ tₚ tₚᵢ) hBound
  have hTriangle :
      tvDist
          (Statement.Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver)
          (Statement.Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver) ≤
        Statement.badEventBound U (T + 1 + nV) +
          (0 + (Statement.etaStarCodecTerm (tₚ : ℝ)
            (iSup fun i => (codec.decodingBias i : ℝ))
            (∑ i, (codec.decodingBias i : ℝ)) + Statement.Dcap U T nV)) := by
    calc
      _ ≤ tvDist
          (Statement.Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver)
          (Statement.Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver) +
          tvDist
            (Statement.Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
              oSpecImpl V maliciousProver)
            (Statement.Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P)
              oSpecImpl V maliciousProver) := tvDist_triangle _ _ _
      _ ≤ tvDist
          (Statement.Hyb0 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver)
          (Statement.Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
            oSpecImpl V maliciousProver) +
          (tvDist
            (Statement.Hyb1 (Salt := Salt) (T_H := T_H) (T_P := T_P)
              oSpecImpl V maliciousProver)
            (Statement.Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P)
              oSpecImpl V maliciousProver) +
            tvDist
              (Statement.Hyb2 (Salt := Salt) (T_H := T_H) (T_P := T_P)
                oSpecImpl V maliciousProver)
              (Statement.Hyb4 (Salt := Salt) (T_H := T_H) (T_P := T_P)
                oSpecImpl V maliciousProver)) := by
          gcongr
          exact tvDist_triangle _ _ _
      _ ≤ Statement.badEventBound U (T + 1 + nV) +
          (0 + (Statement.etaStarCodecTerm (tₚ : ℝ)
            (iSup fun i => (codec.decodingBias i : ℝ))
            (∑ i, (codec.decodingBias i : ℝ)) + Statement.Dcap U T nV)) := by
          rw [h12]
          gcongr
  have hArithmetic :
      Statement.badEventBound U (T + 1 + nV) +
          (0 + (Statement.etaStarCodecTerm (tₚ : ℝ)
            (iSup fun i => (codec.decodingBias i : ℝ))
            (∑ i, (codec.decodingBias i : ℝ)) + Statement.Dcap U T nV)) =
        (ηStar U tₕ tₚ tₚᵢ nV (εcodec := codec.decodingBias) : ℝ) := by
    dsimp [T, Statement.badEventBound, Statement.capacitySize, Statement.etaStarCodecTerm,
      Statement.Dcap, ηStar, θStar]
    push_cast
    ring
  simpa only [Statement.Hyb0, Statement.Hyb4, Statement.HybridTVDist] using
    hTriangle.trans_eq hArithmetic

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedSectionVars false in
theorem lemma_5_1
    [DecidableEq ι]
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (tₕ tₚ tₚᵢ : ℕ) :
    ∃ (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (d2sTraceTransform : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (duplexSpongeChallengeOracle StmtIn U)),
      ∀ (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ),
      IsLemma5_1QueryBound maliciousProver tₕ tₚ tₚᵢ →
      tvDist
        (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sTraceTransform)
        (hyb4Absorbing (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform)
        ≤ (ηStar U tₕ tₚ tₚᵢ
          (DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ))
          (εcodec := codec.decodingBias) : ℝ)
      ∧ IsD2SAlgoChallengeQueryBound d2sAlgoTransform maliciousProver tₕ tₚ tₚᵢ :=
  ⟨ProverTransform.d2sAlgoRevised (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
    d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
    lemma_5_1_inner (T_H := T_H) (T_P := T_P) oSpecImpl V tₕ tₚ tₚᵢ⟩

end DuplexSpongeFS.KeyLemma
