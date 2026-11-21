/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Construction
public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.RandomOracle

/-!
# Completeness proofs for the canonical Fiat–Shamir application

The protocol interface and canonical byte serialization preserve the compatibility compiler's
completeness error exactly.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U σ : Type}

/-- The typed protocol compiler and compatibility compiler have the same completeness event. -/
theorem InteractiveProtocol.compileFiatShamir_completeness_iff [VCVCompatible Salt]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec)
      (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (ε : ℝ≥0) :
    (P.toReduction.compileFiatShamir sampleSalt).completeness init impl relation acceptRejectRel ε ↔
      (P.compileFiatShamir sampleSalt).completeness init impl relation ε := by
  simp only [Reduction.completeness, NonInteractiveArgument.completeness, OptionT.prEvent_eq_run]
  apply forall_congr'
  intro stmt
  apply forall_congr'
  intro wit
  apply imp_congr_right
  intro _
  rw [CanonicalFS.compileFiatShamir_run_option]
  simp only [liftComp_eq_liftM, QueryImpl.simulateQ_addLift_liftM_left]
  simp [InteractiveProtocol.toReduction,
    InteractiveProver.toReductionProver, InteractiveVerifier.toReductionVerifier,
    NonInteractiveArgument.run, InteractiveProtocol.compileFiatShamir,
    InteractiveProver.compileFiatShamir, InteractiveVerifier.compileFiatShamir,
    acceptRejectRel, OptionT.lift, MessagesUpTo.toMessages]

/-- The typed basic Fiat–Shamir argument preserves arbitrary interactive completeness error. -/
theorem CanonicalFS.compileFiatShamir_application_completeness [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Salt) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec Salt)
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (Statement × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement) (Salt := Salt) impl)
      relation ε := by
  apply (P.compileFiatShamir_completeness_iff sampleSalt _ _ relation ε).mp
  exact CanonicalFS.completeness_randomOracle impl P.toReduction sampleSalt
    relation acceptRejectRel ε ((P.toReduction_completeness_iff _ _ _ _).mpr h)

/-- Canonical byte serialization adds no completeness error to basic Fiat–Shamir. -/
theorem CanonicalFS.compileFiatShamirBytes_completeness [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamirBytes saltLength serializer sampleSalt).completeness
      (pure ((),
        (∅ : (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement)
        (Salt := Vector U saltLength) impl) relation ε := by
  rw [InteractiveProtocol.compileFiatShamirBytes, NonInteractiveArgument.serialize_completeness_iff]
  exact CanonicalFS.compileFiatShamir_application_completeness P impl sampleSalt relation ε h
