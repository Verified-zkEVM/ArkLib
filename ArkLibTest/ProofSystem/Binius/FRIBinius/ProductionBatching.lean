/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLibTest.ProofSystem.Binius.ConcreteCommitment
import ArkLib.ProofSystem.Binius.FRIBinius.General

/-!
# Tensor FRI-Binius batching over a concrete rank-four field

The existing tensor message and vector challenge reach the interleaved-core relation,
with the honest production codeword oracle and a nonconstant packed witness. These clients
exercise the tensor batching phase; they do not assert security of the later FRI or query phases.
-/

noncomputable section

namespace Binius.FRIBinius.ProductionBatchingTest

open OracleSpec OracleComp ProtocolSpec MvPolynomial Sumcheck.Structured RingSwitching
open Binius.ConcreteCommitment
open scoped NNReal

abbrev L := PackedField
abbrev K := ZMod 2
local instance : Fintype L := Fintype.ofFinite L
local instance : DecidableEq L := Classical.decEq L
local instance : SampleableType L := SampleableType.ofFintype L
local instance : Fact (Nat.Prime (ringChar K)) :=
  ⟨by simpa only [ZMod.ringChar_zmod_n] using Nat.prime_two⟩
local instance : Fact (Fintype.card K = 2) := ⟨ZMod.card 2⟩
local instance : Fact (1 ∣ 2) := ⟨one_dvd 2⟩

abbrev profile := FullFRIBinius.biniusProfile 2 L K binaryBasis
abbrev packed := coordinate 0

def source : MultilinearPoly K 4 := unpackMLE 2 L K 4 2 rfl profile.basis packed

def oracle : InitialOracles := honestOracle packed

def witness : BatchingWitIn L K 4 2 := ⟨source, packed⟩

def input (r : Fin 4 → L) : BatchingStmtIn L 4 := ⟨r, aeval r source.val⟩

def message (r : Fin 4 → L) : profile.A := embedded_MLP_eval 2 L K profile 4 2 rfl packed r

abbrev spec := pSpecBatching 2 L K profile
abbrev V := BatchingPhase.oracleVerifier 2 L K profile 4 2 rfl commitment

/-- The source and packed witness agree by the production pack/unpack maps. -/
theorem source_packs : packMLE 2 L K 4 2 rfl profile.basis source = packed :=
  packMLE_unpackMLE rfl profile.basis packed

/-- The batching input relation is inhabited using the production honest codeword oracle. -/
theorem source_related (r : Fin 4 → L) :
    ((input r, oracle), witness) ∈
      BatchingPhase.batchingInputRelation 2 L K profile 4 2 rfl commitment :=
  ⟨source_packs.symm, rfl, honestOracle_compatible packed⟩

/-- The tensor's column family is the shared transpose of its row family. -/
theorem tensor_coordinates (r : Fin 4 → L) :
    (Packing.sameAlgebra profile.basis).transpose (profile.decomposeRows (message r)) =
      profile.decomposeColumns (message r) := profile.transpose_rows _

/-- Every vector challenge gives the exact initial sumcheck relation consumed by the FRI core. -/
theorem core_input_related (r : Fin 4 → L) (c : Fin 2 → L) :
    ((BatchingPhase.nextStatement 2 L K profile 4 2 (input r) (message r) c, oracle),
      BatchingPhase.nextWitness 2 L K profile 4 2 rfl (input r) (message r) c packed) ∈
      sumcheckRoundRelation 2 L K profile 4 2 rfl commitment 0 :=
  BatchingPhase.honest_relOut 2 L K profile 4 2 rfl commitment (source_related r) c

/-- The batching verifier forwards the same oracle and structured statement. -/
theorem accepts (r : Fin 4 → L) (c : Fin 2 → L) :
    V.toVerifier.verify (input r, oracle) (FullTranscript.mk2 (message r) c) =
      pure (BatchingPhase.nextStatement 2 L K profile 4 2 (input r) (message r) c, oracle) := by
  rw [BatchingPhase.oracleVerifier_verify]
  have hc := BatchingPhase.honest_check 2 L K profile 4 2 rfl commitment (source_related r)
  change performCheckOriginalEvaluation 2 L K profile 4 2 rfl
    (input r).original_claim (input r).t_eval_point (message r) = true at hc
  simp only [FullTranscript.messages, FullTranscript.challenges, FullTranscript.mk2]
  rw [hc]
  rfl

def falseInput (r : Fin 4 → L) : BatchingStmtIn L 4 :=
  ⟨r, aeval r source.val + 1⟩

/-- Raising the scalar claim by one fails the row-coordinate guard. -/
theorem false_guard (r : Fin 4 → L) :
    performCheckOriginalEvaluation 2 L K profile 4 2 rfl
      (falseInput r).original_claim r (message r) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := original_claim_of_check profile rfl source r (falseInput r).original_claim
    (message r) (by rw [source_packs]; rfl) h
  change aeval r source.val + 1 = aeval r source.val at he
  have : (1 : L) = 0 := add_left_cancel (he.trans (add_zero _).symm)
  exact one_ne_zero this

/-- The batching verifier aborts the false input for every batching vector. -/
theorem rejects (r : Fin 4 → L) (c : Fin 2 → L) :
    V.toVerifier.verify (falseInput r, oracle) (FullTranscript.mk2 (message r) c) = failure := by
  rw [BatchingPhase.oracleVerifier_verify]
  simp only [FullTranscript.messages, FullTranscript.mk2]
  erw [false_guard r]
  rfl

private theorem rate : 2 + 1 < 2 ^ 2 := by decide

abbrev coreSpec := BinaryBasefold.pSpecCoreInteraction K binaryBasis
  (ϑ := 1) (h_ℓ_add_R_rate := show 2 + 1 < 2 ^ 2 by decide)

local instance : ∀ i, OracleInterface ((spec ++ₚ coreSpec).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := spec) (pSpec₂ := coreSpec)

/-- The production batching-plus-FRI verifier cannot continue after that rejection. -/
theorem core_rejects (r : Fin 4 → L) (c : Fin 2 → L)
    (tr : FullTranscript (BinaryBasefold.pSpecCoreInteraction K binaryBasis
      (ϑ := 1) (h_ℓ_add_R_rate := show 2 + 1 < 2 ^ 2 by decide))) :
    (FullFRIBinius.batchingCoreVerifier 2 L K binaryBasis 4 2 1 1 rate rfl).toVerifier.verify
      (falseInput r, oracle) (FullTranscript.mk2 (message r) c ++ₜ tr) = failure := by
  unfold FullFRIBinius.batchingCoreVerifier
  erw [OracleVerifier.append_toVerifier]
  change (V.toVerifier.verify (falseInput r, oracle)
    (FullTranscript.mk2 (message r) c ++ₜ tr).fst >>= fun out => _) = _
  rw [FullTranscript.append_fst, rejects]
  simp

/-- The batching head is complete for every oracle state. -/
theorem complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (BatchingPhase.batchingOracleReduction 2 L K profile 4 2 rfl commitment).perfectCompleteness
      init impl (BatchingPhase.batchingInputRelation 2 L K profile 4 2 rfl commitment)
      (sumcheckRoundRelation 2 L K profile 4 2 rfl commitment 0) :=
  FullFRIBinius.batchingReduction_perfectCompleteness
    2 L K binaryBasis 4 2 1 1 (by decide) rfl

/-- Production security uses binding and its exact extractor and knowledge state. -/
theorem worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (BatchingPhase.batchingInputRelation 2 L K profile 4 2 rfl commitment)
      (sumcheckRoundRelation 2 L K profile 4 2 rfl commitment 0) V.toVerifier
      (BatchingPhase.batchingWitMid L K 4 2)
      (BatchingPhase.batchingRbrExtractor 2 L K profile 4 2 rfl commitment)
      (BatchingPhase.batchingKnowledgeStateFunction 2 L K profile 4 2 rfl commitment)
      (BatchingPhase.batchingRBRKnowledgeError 2 L K profile) :=
  FullFRIBinius.batchingVerifier_rbrKnowledgeSoundnessWorstCaseWith
    2 L K binaryBasis 4 2 1 1 (by decide) rfl

/-- The single vector challenge has the error bound two-sixteenths. -/
theorem error_value :
    BatchingPhase.batchingRBRKnowledgeError 2 L K profile ⟨1, rfl⟩ = (2 / 16 : ℝ≥0) := by
  simp only [BatchingPhase.batchingRBRKnowledgeError, field_card]
  norm_num

end Binius.FRIBinius.ProductionBatchingTest

end
