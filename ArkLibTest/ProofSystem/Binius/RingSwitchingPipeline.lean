/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.Binius.RingSwitchingCommitment
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.FullFamilyOpening

/-!
# Actual GF16 Binius commitment through the complete ring-switch head and tail

The live retained-dimension-two, rank-four fixture uses its production codeword oracle and
unique-distance compatibility relation. The complete checked family phase and product-sumcheck
tail reach the same commitment's evaluation relation. This does not instantiate or prove the
later interleaved FRI opening protocol.
-/

noncomputable section

namespace Binius.RingSwitchingPipelineTests

open MvPolynomial OracleSpec OracleComp ProtocolSpec
open RingSwitching.Packing ConcreteCommitment RingSwitchingCommitmentTests

local instance : Fintype PackedField := Fintype.ofFinite PackedField
local instance : DecidableEq PackedField := Classical.decEq PackedField
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨by simpa only [ZMod.ringChar_zmod_n] using Nat.prime_two⟩
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩
local instance : Fact (1 ∣ 2) := ⟨one_dvd 2⟩

/-- The actual nonconstant source and actual codeword oracle satisfy the pipeline's input. -/
theorem source_related : ((input, oracle), family) ∈ FullFamily.relIn data 2 pc :=
  input_related

/-- The endpoint retains the production compatibility relation on the same oracle and polynomial. -/
theorem actual_opening_related (r : Fin 2 → PackedField) :
    (((r, aeval r (coordinate 0).val), oracle), coordinate 0) ∈ pc.evalRel :=
  ⟨rfl, honestOracle_compatible (coordinate 0)⟩

/-- Full checked ring switching is state-uniformly complete against the actual Binius commitment. -/
theorem complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (FullFamilyOpening.reduction data 2 batch pc).perfectCompleteness init impl
      (FullFamily.relIn data 2 pc) pc.evalRel :=
  FullFamilyOpening.perfectCompleteness data 2 batch pc init impl

/-- The complete production pipeline uses actual binding and the exposed append extractor/state. -/
theorem worstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (FullFamily.relIn data 2 pc) pc.evalRel
      (FullFamilyOpening.verifier data 2 batch pc).toVerifier
      (FullFamilyOpening.Witness data 2) (FullFamilyOpening.extractor data 2 batch pc)
      (FullFamilyOpening.knowledgeStateFunction data 2 batch pc init impl)
      (FullFamilyOpening.rbrError data 2 batch) :=
  FullFamilyOpening.rbrKnowledgeSoundnessWorstCaseWith data 2 batch pc
    (FRIBinius.binaryBasefoldPackedCommitment_functional
      2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide)) Function.injective_id init impl

/-- A false original family aborts the complete verifier, regardless of all later tail messages. -/
theorem false_family_rejected (c : PackedField)
    (tail : FullTranscript (FullFamilyTail.pSpec (C := PackedField) 2)) :
    (FullFamilyOpening.verifier data 2 batch pc).toVerifier.run (falseInput, oracle)
      (FullTranscript.mk2 slices c ++ₜ tail) = failure := by
  erw [FullFamilyOpening.verifier_toVerifier, Verifier.append_run]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd, Verifier.run]
  rw [verifier_reject]
  rfl

end Binius.RingSwitchingPipelineTests

end
