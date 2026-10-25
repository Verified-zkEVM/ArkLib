/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.ReachableImplications
public import ArkLib.OracleReduction.Security.Stateless
public import ArkLib.OracleReduction.Security.Acceptance

/-!
# RBR-to-standard implications with stateless ambient handlers

The singleton-state interpretation connects the fresh-initial-state terminal obligation to the
actual verifier continuation. The accumulated error is exactly the sum of the averaged RBR errors.

## Proof organization and literature

The transition/error-accumulation argument follows Claim 31.1.7 and Construction 31.1.8 of
[Chiesa and Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024].
Their RBR notion supplies a whole-transcript extractor; ArkLib instead supplies local
witness-indexed extraction steps. `BackwardExtraction` composes those steps backwards and
shows that failed extraction forces a bad challenge. `PrefixProbability` bounds the union
of these events under the actual prefix distributions, without assuming lossless continuations.
Thus this is an adaptation of the argument, not a literal port of the book's RBR definition.

The general state-retaining proofs live in `ReachableImplications`; this module specializes
them using `Stateless` to connect the terminal condition to the verifier continuation. Neither a
guarded verifier nor an acceptance-only output relation is required. The restriction is on
the ambient handler, not on the verifier's syntactic form.

## References

* [Chiesa, A. and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]

/-! ## Averaged RBR soundness -/

/-- RBR soundness implies standard soundness for any stateless ambient handler, with the same
input/output languages and the sum of the per-challenge errors. -/
theorem rbrSoundness_implies_soundness
    (impl : QueryImpl oSpec ProbComp) (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrSoundness (pure PUnit.unit) impl.statelessLift langIn langOut ε) :
    verifier.soundness (pure PUnit.unit) impl.statelessLift langIn langOut (∑ i, ε i) := by
  obtain ⟨sF, hSF⟩ := h
  apply rbrSoundness_implies_soundness_of_reachable
    (pure PUnit.unit) impl.statelessLift langIn langOut verifier sF ε
  · intro Wi Wo wi p stmt hstmt i
    exact hSF stmt hstmt Wi Wo wi p i
  · intro Wi Wo wi p stmt _ result _ stmtOut hout hrel
    exact sF.stateless_terminal stmt result.1.1 stmtOut
      (by simpa only [QueryImpl.simulateQ_statelessLift_run'] using hout) hrel

/-! ## Backward extraction and averaged RBR knowledge soundness -/

/-- The explicit backward extractor turns averaged RBR knowledge soundness into standard
knowledge soundness for a stateless handler. Relations and the additive error are unchanged. -/
theorem rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction (pure PUnit.unit) impl.statelessLift
      relIn relOut extractor)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundnessWith (pure PUnit.unit) impl.statelessLift
      relIn relOut WitMid extractor kSF ε) :
    verifier.knowledgeSoundnessWith (pure PUnit.unit) impl.statelessLift relIn relOut
      extractor.toStraightline (∑ i, ε i) := by
  apply rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith_of_reachable
    (pure PUnit.unit) impl.statelessLift relIn relOut verifier WitMid extractor kSF ε h
  intro stmt wi p result _ stmtOut hout hrel
  exact kSF.stateless_terminal stmt result.1.1 result.1.2.2 stmtOut
    (by simpa only [QueryImpl.simulateQ_statelessLift_run'] using hout) hrel

/-! ## Worst-case extractor-preserving bridge -/


/-- The explicit worst-case extractor is preserved through both implication bridges. -/
theorem rbrKnowledgeSoundnessWorstCaseWith_implies_knowledgeSoundnessWith
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction (pure PUnit.unit) impl.statelessLift
      relIn relOut extractor)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundnessWorstCaseWith (pure PUnit.unit) impl.statelessLift
      relIn relOut WitMid extractor kSF ε) :
    verifier.knowledgeSoundnessWith (pure PUnit.unit) impl.statelessLift relIn relOut
      extractor.toStraightline (∑ i, ε i) :=
  rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith impl relIn relOut verifier
    WitMid extractor kSF ε (rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
      _ _ h)

/-! ## Existential and worst-case corollaries -/

/-- Existential RBR knowledge soundness supplies the backward straightline extractor.
The stateless handler may have a nonempty specification and randomized responses. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundness (pure PUnit.unit) impl.statelessLift relIn relOut ε) :
    verifier.knowledgeSoundness (pure PUnit.unit) impl.statelessLift relIn relOut (∑ i, ε i) := by
  obtain ⟨WitMid, extractor, kSF, h⟩ := h
  exact knowledgeSoundness_of_with _ _
    (rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith impl relIn relOut verifier
      WitMid extractor kSF ε h)

/-- Worst-case RBR soundness also implies standard soundness, through the averaged bridge. -/
theorem rbrSoundnessWorstCase_implies_soundness
    (impl : QueryImpl oSpec ProbComp) (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrSoundnessWorstCase (pure PUnit.unit) impl.statelessLift langIn langOut ε) :
    verifier.soundness (pure PUnit.unit) impl.statelessLift langIn langOut (∑ i, ε i) :=
  rbrSoundness_implies_soundness impl langIn langOut verifier ε
    (rbrSoundnessWorstCase_implies_rbrSoundness _ _ h)

/-- Worst-case RBR knowledge soundness implies standard knowledge soundness at the same sum. -/
theorem rbrKnowledgeSoundnessWorstCase_implies_knowledgeSoundness
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundnessWorstCase (pure PUnit.unit) impl.statelessLift
      relIn relOut ε) :
    verifier.knowledgeSoundness (pure PUnit.unit) impl.statelessLift relIn relOut (∑ i, ε i) :=
  rbrKnowledgeSoundness_implies_knowledgeSoundness impl relIn relOut verifier ε
    (rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness _ _ h)

end Verifier

/-! ## Oracle-verifier wrappers -/

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {ιIn ιOut : Type} {OStmtIn : ιIn → Type} {OStmtOut : ιOut → Type}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]

/-- Oracle-verifier form of the stateless RBR-to-standard soundness implication. -/
theorem rbrSoundness_implies_soundness
    (impl : QueryImpl oSpec ProbComp)
    (langIn : Set (StmtIn × ∀ i, OStmtIn i)) (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrSoundness (pure PUnit.unit) impl.statelessLift langIn langOut ε) :
    verifier.soundness (pure PUnit.unit) impl.statelessLift langIn langOut (∑ i, ε i) :=
  Verifier.rbrSoundness_implies_soundness impl langIn langOut verifier.toVerifier ε h

/-- Oracle-verifier form retaining the specific backward straightline extractor. -/
theorem rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec (StmtIn × ∀ i, OStmtIn i)
      WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction (pure PUnit.unit) impl.statelessLift
      relIn relOut extractor)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundnessWith (pure PUnit.unit) impl.statelessLift
      relIn relOut WitMid extractor kSF ε) :
    verifier.knowledgeSoundnessWith (pure PUnit.unit) impl.statelessLift relIn relOut
      extractor.toStraightline (∑ i, ε i) :=
  Verifier.rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith impl relIn relOut
    verifier.toVerifier WitMid extractor kSF ε h

/-- Oracle-verifier form preserves the exact relation pair and summed RBR knowledge error. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundness (pure PUnit.unit) impl.statelessLift relIn relOut ε) :
    verifier.knowledgeSoundness (pure PUnit.unit) impl.statelessLift relIn relOut (∑ i, ε i) :=
  Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness impl relIn relOut
    verifier.toVerifier ε h

/-- Oracle-verifier worst-case RBR knowledge soundness gives the same standard error sum. -/
theorem rbrKnowledgeSoundnessWorstCase_implies_knowledgeSoundness
    (impl : QueryImpl oSpec ProbComp)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.toVerifier.rbrKnowledgeSoundnessWorstCase (pure PUnit.unit) impl.statelessLift
      relIn relOut ε) :
    verifier.knowledgeSoundness (pure PUnit.unit) impl.statelessLift relIn relOut (∑ i, ε i) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_knowledgeSoundness impl relIn relOut
    verifier.toVerifier ε h

end OracleVerifier
