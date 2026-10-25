/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.PrefixProbability
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

`Stateless` connects the terminal condition to the actual verifier continuation. Neither a
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
  intro WitIn WitOut witIn prover stmtIn hstmt
  let handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp := impl + challengeQueryImpl
  let event : FullTranscript pSpec → Prop :=
    Transcript.HasBadRound (sF.badChallenge stmtIn) (.last n)
  have htrace : Pr{let result ← (simulateQ handler
      (prover.runToRound (.last n) stmtIn witIn))}[event result.1] ≤ ∑ i, (ε i : ENNReal) := by
    apply prover.hasBadRound_probability_le_sum
    · intro m hdir tr hbad
      exact Direction.noConfusion (hdir.symm.trans hbad.1)
    · intro i
      have hi := hSF stmtIn hstmt WitIn WitOut witIn prover i
      simpa only [pure_bind, QueryImpl.statelessLift_addLift,
        QueryImpl.simulateQ_statelessLift_run', StateFunction.badChallenge,
        Transcript.init_concat, i.2, true_and] using hi
  have hfull := (prover.run_transcript_probability_le handler stmtIn witIn event).trans htrace
  change Pr{let result ← (OptionT.mk (do
    (simulateQ (impl.statelessLift.addLift challengeQueryImpl : QueryImpl _
      (StateT PUnit ProbComp)) ((Reduction.mk prover verifier).run stmtIn witIn).run).run'
        (← pure PUnit.unit)))}[result.2 ∈ langOut] ≤ _
  simp only [QueryImpl.statelessLift_addLift,
    QueryImpl.simulateQ_statelessLift_run', OptionT.prEvent_eq_run, OptionT.run_mk]
  rw [Reduction.run_run_eq_bind, simulateQ_bind]
  refine le_trans ?_ (by exact_mod_cast hfull)
  apply prEvent_bind_le_prEvent_of_support
  intro result _ hfalse
  simp only [bind_pure_comp, simulateQ_map, prEvent_map,
    QueryImpl.simulateQ_add_liftComp_left]
  apply prEvent_eq_zero_of_forall_mem_support
  intro out hout
  cases out with
  | none => simp
  | some stmtOut =>
    intro hmem
    apply hfalse
    exact sF.hasBadRound_of_not_mem stmtIn hstmt (.last n) result.1
      (sF.stateless_terminal stmtIn result.1 stmtOut hout hmem)

/-! ## Backward extraction and averaged RBR knowledge soundness -/

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem backward_game_eq_map
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmtIn : StmtIn) (witIn : WitIn) :
    (do
      let ⟨⟨⟨transcript, _, witOut⟩, stmtOut⟩, proveLog, verifyLog⟩ ←
        reduction.runWithLog stmtIn witIn
      let extractedWitIn ← liftM
        (extractor.toStraightline stmtIn witOut transcript proveLog.fst verifyLog).run
      pure (stmtIn, extractedWitIn, stmtOut, witOut)) =
    (fun ⟨⟨transcript, _, witOut⟩, stmtOut⟩ => (stmtIn,
      some (extractor.extractPrefix stmtIn (.last n) transcript
        (extractor.extractOut stmtIn transcript witOut)),
      stmtOut, witOut)) <$> reduction.run stmtIn witIn := by
  simp only [Extractor.RoundByRound.toStraightline_run, liftM_pure, bind_pure_comp]
  rw [← Reduction.runWithLog_discard_logs_eq_run]
  simp only [Functor.map_map]
  rfl

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
  intro stmtIn witIn prover
  let handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp := impl + challengeQueryImpl
  let event : FullTranscript pSpec → Prop :=
    Transcript.HasBadRound (kSF.badChallenge stmtIn) (.last n)
  have htrace : Pr{let result ← (simulateQ handler
      (prover.runToRound (.last n) stmtIn witIn))}[event result.1] ≤ ∑ i, (ε i : ENNReal) := by
    apply prover.hasBadRound_probability_le_sum
    · intro m hdir tr hbad
      exact Direction.noConfusion (hdir.symm.trans hbad.1)
    · intro i
      have hi := h stmtIn witIn prover i
      simp only [pure_bind, QueryImpl.statelessLift_addLift,
        QueryImpl.simulateQ_statelessLift_run'] at hi
      let logged := do
        let ⟨⟨tr, _⟩, log⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
        let challenge ← liftComp (pSpec.getChallenge i) _
        pure (tr, challenge, log)
      have hmap : (fun ⟨transcript, challenge, _⟩ => (transcript, challenge)) <$> logged = (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          pure (transcript, challenge)) := by
        rw [← Prover.runWithLogToRound_discard_log_eq_runToRound]
        simp only [logged, map_bind, map_pure, bind_map_left]
      rw [← hmap, simulateQ_map, prEvent_map]
      simpa only [KnowledgeStateFunction.badChallenge, Transcript.init_concat, i.2, true_and]
        using hi
  have hfull := (prover.run_transcript_probability_le handler stmtIn witIn event).trans htrace
  change Pr{let ⟨stmtIn, extractedWitIn, stmtOut, witOut⟩ ← (OptionT.mk (do
    (simulateQ (impl.statelessLift.addLift challengeQueryImpl : QueryImpl _
      (StateT PUnit ProbComp)) (do
        let ⟨⟨⟨transcript, _, witOut⟩, stmtOut⟩, proveLog, verifyLog⟩ ←
          (Reduction.mk prover verifier).runWithLog stmtIn witIn
        let extractedWitIn ← liftM
          (extractor.toStraightline stmtIn witOut transcript proveLog.fst verifyLog).run
        pure (stmtIn, extractedWitIn, stmtOut, witOut)).run).run' (← pure PUnit.unit)))}[
      (∀ witIn ∈ extractedWitIn, (stmtIn, witIn) ∉ relIn) ∧ (stmtOut, witOut) ∈ relOut] ≤ _
  rw [backward_game_eq_map, OptionT.run_map]
  simp only [QueryImpl.statelessLift_addLift, OptionT.prEvent_eq_run, OptionT.run_mk]
  rw [QueryImpl.simulateQ_statelessLift_run', simulateQ_map, prEvent_map]
  rw [Reduction.run_run_eq_bind, simulateQ_bind]
  refine le_trans ?_ (by exact_mod_cast hfull)
  apply prEvent_bind_le_prEvent_of_support
  rintro ⟨transcript, _, witOut⟩ _ hfalse
  simp only [bind_pure_comp, simulateQ_map, prEvent_map,
    QueryImpl.simulateQ_add_liftComp_left]
  apply prEvent_eq_zero_of_forall_mem_support
  intro out hout
  cases out with
  | none => simp
  | some stmtOut =>
    intro hbad
    apply hfalse
    apply kSF.hasBadRound_of_extractPrefix_invalid stmtIn (.last n) transcript
      (extractor.extractOut stmtIn transcript witOut)
    · exact kSF.stateless_terminal stmtIn transcript witOut stmtOut hout hbad.2
    · exact hbad.1 _ rfl

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
