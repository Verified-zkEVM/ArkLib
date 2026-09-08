/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.ScalarOpening
import ArkLibTest.ProofSystem.RingSwitching.Packing.ScalarFamily

/-!
# The original-scalar pipeline reaches the same packed opening

The existing nonconstant source, rank-one packing, rank-two product opening algebra and ZMod5
batching instantiate the complete scalar/family/sumcheck pipeline. Every phase retains the
same commitment. A false scalar claim is rejected independently of every later tail message.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.ScalarOpening

open MvPolynomial OracleSpec OracleComp ProtocolSpec
open RingSwitching.Packing.Tests.ScalarFamily

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The original nonconstant source is a witness of the complete pipeline's input. -/
theorem original_source : ((stmt, ost), source) ∈ ScalarHead.relIn data 1 layout pc :=
  source_related

/-- The packed polynomial has its true opening on this very same commitment oracle. -/
theorem opening (r : Fin 1 → ZMod 5) :
    (((r, aeval r (data.packedMLE (layout.components source)).val), ost),
      data.packedMLE (layout.components source)) ∈ pc.evalRel :=
  pc.evalRel_honest _ r

/-- Perfect completeness is for the complete oracle reduction at every initial state. -/
theorem complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitching.Packing.ScalarOpening.reduction data 1 layout bat pc).perfectCompleteness
      init impl (ScalarHead.relIn data 1 layout pc) pc.evalRel :=
  RingSwitching.Packing.ScalarOpening.perfectCompleteness data 1 layout bat pc init impl

/-- Both the batching and scalar-round errors use the appended extractor and KSF. -/
theorem worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (ScalarHead.relIn data 1 layout pc) pc.evalRel
      (RingSwitching.Packing.ScalarOpening.verifier data 1 layout bat pc).toVerifier
      (RingSwitching.Packing.ScalarOpening.Witness data 1 layout)
      (RingSwitching.Packing.ScalarOpening.extractor data 1 layout bat pc)
      (RingSwitching.Packing.ScalarOpening.knowledgeStateFunction data 1 layout bat pc init impl)
      (RingSwitching.Packing.ScalarOpening.rbrError data 1 bat) :=
  RingSwitching.Packing.ScalarOpening.rbrKnowledgeSoundnessWorstCaseWith data 1 layout bat pc
    pc.commitsTo_functional Function.injective_id init impl

/-- Failure of the original scalar check survives the entire tail at every transcript. -/
theorem false_scalar_rejected (c : ZMod 5)
    (tail : FullTranscript (FullFamilyTail.pSpec (C := ZMod 5) 1)) :
    (RingSwitching.Packing.ScalarOpening.verifier data 1 layout bat pc).toVerifier.run
      (falseStmt, ost) (tr c ++ₜ tail) = failure := by
  erw [RingSwitching.Packing.ScalarOpening.verifier_toVerifier, Verifier.append_run]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  rw [RingSwitching.Packing.Tests.ScalarFamily.false_scalar_rejected]
  rfl

end RingSwitching.Packing.Tests.ScalarOpening

end
