/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.General
import ArkLibTest.OracleReduction.HistoricalTypeCheck

/-! Historical signatures from commit 88e079f0a5b871088e5cc53a0b6047f459fc0323.
Only the historical averaged predicate is renamed to its current explicit name.
Proofs use the current public theorem; full elaborated types and binder modes are checked.
-/

@[expose] public section

namespace RingSwitching.FullRingSwitching

noncomputable section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Module

variable (κ : ℕ) [NeZero κ]

variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]

variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]

variable [Algebra K L]

variable (P : RingSwitchingProfile K L κ)

variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

variable (h_l : ℓ = ℓ' + κ)

variable (mlIOPCS : MLIOPCS L ℓ')

open scoped NNReal

open Sumcheck.Structured

section SecurityProperties

variable {σ : Type} (init : ProbComp σ)
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem batchingCore_perfectCompleteness_historicalType [Finite L] [Finite K]
    [IsDomain K] [NoZeroDivisors L] (hCoord : CoordinateLaws P) :
    (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
      (pSpec := pSpecLargeFieldReduction κ L K P ℓ') (relIn :=
      BatchingPhase.strictBatchingInputRelation κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn)
      (relOut := mlIOPCS.toStrictRelInput) (init := init) (impl := impl) :=
  by historical_exact batchingCore_perfectCompleteness

assert_historical_type batchingCore_perfectCompleteness
  batchingCore_perfectCompleteness_historicalType

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem fullOracleReduction_perfectCompleteness_historicalType [Finite L]
    [Finite K] [IsDomain K] [NoZeroDivisors L] (hCoord : CoordinateLaws P) :
    OracleProof.perfectCompleteness (oracleProof :=
      fullOracleReduction κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS) (relation :=
      BatchingPhase.strictBatchingInputRelation κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn)
      (init := init) (impl := impl) :=
  by historical_exact fullOracleReduction_perfectCompleteness

assert_historical_type fullOracleReduction_perfectCompleteness
  fullOracleReduction_perfectCompleteness_historicalType

omit [Fintype K] [DecidableEq K] in
theorem fullOracleVerifier_rbrKnowledgeSoundness_historicalType
    [Finite K] [IsDomain K] [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) (hUnique : mlIOPCS.toAbstractOStmtIn.Functional) :
    OracleProof.rbrKnowledgeSoundnessAveraged
      (verifier := fullOracleVerifier κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (init := init) (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  historical_exact fullOracleVerifier_rbrKnowledgeSoundness

assert_historical_type fullOracleVerifier_rbrKnowledgeSoundness
  fullOracleVerifier_rbrKnowledgeSoundness_historicalType

end SecurityProperties

end

end RingSwitching.FullRingSwitching
