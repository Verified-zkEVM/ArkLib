/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.PrefixProbability
public import ArkLib.OracleReduction.Security.Acceptance
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient

/-!
# RBR implications with reachable-state terminal conditions

The terminal obligation concerns only states and transcripts reachable after the prover's
full run, including its output computation. It does not require a singleton state space or
an all-states condition. This follows the state-retaining approach of Calgooon's ArkLib PR
#1245 and its review discussion, extending it to witness-aware backward extraction.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut σ : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]

/-- Erasing the final state does not change an event on the returned value. -/
theorem prEvent_run'_init {α : Type} (init : ProbComp σ) (comp : StateT σ ProbComp α)
    (event : α → Prop) :
    Pr{let result ← (do comp.run' (← init))}[event result] =
      Pr{let result ← (do comp.run (← init))}[event result.1] := by
  simp only [StateT.run'_eq, ← map_bind, prEvent_map]

/-- Soundness follows from the same RBR state when its terminal clause holds on reachable runs.
The premise retains the actual post-prover oracle state, rather than restarting from `init`. -/
theorem rbrSoundness_implies_soundness_of_reachable
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (sF : verifier.StateFunction init impl langIn langOut)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hrbr : ∀ (WitIn WitOut : Type) (witIn : WitIn)
      (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) stmtIn,
      stmtIn ∉ langIn → ∀ i : pSpec.ChallengeIdx,
      Pr{let result ← (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) (do
          let result ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          pure (result.1, challenge))).run' (← init))}[
        ¬ sF i.1.castSucc stmtIn result.1 ∧
          sF i.1.succ stmtIn (result.1.concat result.2)] ≤ ε i)
    (hfull : ∀ (WitIn WitOut : Type) (witIn : WitIn)
      (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) stmtIn,
      stmtIn ∉ langIn → ∀ result ∈ support (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (prover.run stmtIn witIn)).run (← init)),
      ∀ stmtOut,
      some stmtOut ∈ support ((simulateQ impl (verifier.run stmtIn result.1.1).run).run'
        result.2) → stmtOut ∈ langOut → sF (.last n) stmtIn result.1.1) :
    verifier.soundness init impl langIn langOut (∑ i, ε i) := by
  intro WitIn WitOut witIn prover stmtIn hstmt
  let handler := (impl.addLift challengeQueryImpl :
    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
  let event := Transcript.HasBadRound (sF.badChallenge stmtIn) (.last n)
  have htrace : Pr{let result ← (do
      (simulateQ handler (prover.runToRound (.last n) stmtIn witIn)).run (← init))}[
      event result.1.1] ≤ ∑ i, (ε i : ENNReal) := by
    apply prover.hasBadRound_probability_le_sum
    · intro m hdir tr hbad
      exact Direction.noConfusion (hdir.symm.trans hbad.1)
    · intro i
      have hi := hrbr WitIn WitOut witIn prover stmtIn hstmt i
      rw [prEvent_run'_init] at hi
      simpa only [StateFunction.badChallenge, Transcript.init_concat, i.2, true_and] using hi
  have hbound := (prover.run_transcript_probability_le handler init stmtIn witIn
    event).trans htrace
  change Pr{let result ← OptionT.mk (do
    (simulateQ handler ((Reduction.mk prover verifier).run stmtIn witIn).run).run'
      (← init))}[result.2 ∈ langOut] ≤ _
  rw [OptionT.prEvent_eq_run, OptionT.run_mk, prEvent_run'_init]
  rw [Reduction.run_run_eq_bind, simulateQ_bind]
  simp only [StateT.run_bind, ← bind_assoc]
  refine le_trans ?_ (by exact_mod_cast hbound)
  apply prEvent_bind_le_prEvent_of_support
  intro result hresult hfalse
  simp only [handler, bind_pure_comp, simulateQ_map, StateT.run_map, prEvent_map,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left]
  apply prEvent_eq_zero_of_forall_mem_support
  rintro ⟨out, os⟩ hout
  cases out with
  | none => simp
  | some stmtOut =>
    intro hmem
    apply hfalse
    apply sF.hasBadRound_of_not_mem stmtIn hstmt (.last n) result.1.1
    apply hfull WitIn WitOut witIn prover stmtIn hstmt result hresult stmtOut _ hmem
    rw [StateT.run'_eq, support_map]
    exact ⟨(some stmtOut, os), hout, rfl⟩

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

/-- Backward extraction gives standard KS when the terminal knowledge state is valid at
reachable post-prover states. No singleton-state or losslessness assumption is required. -/
theorem rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith_of_reachable
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid extractor kSF ε)
    (hfull : ∀ stmtIn witIn (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec),
      ∀ result ∈ support (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (prover.run stmtIn witIn)).run (← init)),
      ∀ stmtOut,
      some stmtOut ∈ support ((simulateQ impl (verifier.run stmtIn result.1.1).run).run'
        result.2) → (stmtOut, result.1.2.2) ∈ relOut →
      kSF (.last n) stmtIn result.1.1
        (extractor.extractOut stmtIn result.1.1 result.1.2.2)) :
    verifier.knowledgeSoundnessWith init impl relIn relOut extractor.toStraightline
      (∑ i, ε i) := by
  intro stmtIn witIn prover
  let handler := (impl.addLift challengeQueryImpl :
    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
  let event := Transcript.HasBadRound (kSF.badChallenge stmtIn) (.last n)
  have htrace : Pr{let result ← (do
      (simulateQ handler (prover.runToRound (.last n) stmtIn witIn)).run (← init))}[
      event result.1.1] ≤ ∑ i, (ε i : ENNReal) := by
    apply prover.hasBadRound_probability_le_sum
    · intro m hdir tr hbad
      exact Direction.noConfusion (hdir.symm.trans hbad.1)
    · intro i
      have hi := h stmtIn witIn prover i
      rw [prEvent_run'_init] at hi
      let logged := do
        let ⟨⟨tr, _⟩, log⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
        let challenge ← liftComp (pSpec.getChallenge i) _
        pure (tr, challenge, log)
      have hmap : (fun ⟨tr, challenge, _⟩ => (tr, challenge)) <$> logged = (do
          let result ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          pure (result.1, challenge)) := by
        rw [← Prover.runWithLogToRound_discard_log_eq_runToRound]
        simp only [logged, map_bind, map_pure, bind_map_left]
      rw [← hmap]
      simp only [simulateQ_map, StateT.run_map, ← map_bind, prEvent_map]
      simpa only [KnowledgeStateFunction.badChallenge, Transcript.init_concat, i.2, true_and]
        using hi
  have hbound := (prover.run_transcript_probability_le handler init stmtIn witIn
    event).trans htrace
  change Pr{let ⟨stmtIn, extractedWitIn, stmtOut, witOut⟩ ← (OptionT.mk (do
    (simulateQ handler (do
      let ⟨⟨⟨transcript, _, witOut⟩, stmtOut⟩, proveLog, verifyLog⟩ ←
        (Reduction.mk prover verifier).runWithLog stmtIn witIn
      let extractedWitIn ← liftM
        (extractor.toStraightline stmtIn witOut transcript proveLog.fst verifyLog).run
      pure (stmtIn, extractedWitIn, stmtOut, witOut)).run).run' (← init)))}[
    (∀ witIn ∈ extractedWitIn, (stmtIn, witIn) ∉ relIn) ∧ (stmtOut, witOut) ∈ relOut] ≤ _
  rw [backward_game_eq_map, OptionT.run_map]
  rw [OptionT.prEvent_eq_run, OptionT.run_mk, prEvent_run'_init]
  simp only [simulateQ_map, StateT.run_map, ← map_bind, prEvent_map]
  rw [Reduction.run_run_eq_bind, simulateQ_bind]
  change Pr{let result ← (do
    (simulateQ handler (prover.run stmtIn witIn) >>= fun pr =>
      simulateQ handler (do
        let out ← liftComp (verifier.run stmtIn pr.1).run _
        pure (out.map (fun v => (pr, v))))).run (← init))}[_] ≤ _
  simp only [StateT.run_bind, ← bind_assoc]
  refine le_trans ?_ (by exact_mod_cast hbound)
  apply prEvent_bind_le_prEvent_of_support
  intro result hresult hfalse
  simp only [handler, bind_pure_comp, simulateQ_map, StateT.run_map, prEvent_map,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left]
  apply prEvent_eq_zero_of_forall_mem_support
  rintro ⟨out, os⟩ hout
  cases out with
  | none => simp
  | some stmtOut =>
    intro hbad
    apply hfalse
    apply kSF.hasBadRound_of_extractPrefix_invalid stmtIn (.last n) result.1.1
      (extractor.extractOut stmtIn result.1.1 result.1.2.2)
    · apply hfull stmtIn witIn prover result hresult stmtOut _ hbad.2
      rw [StateT.run'_eq, support_map]
      exact ⟨(some stmtOut, os), hout, rfl⟩
    · exact hbad.1 _ rfl

/-- Every output possible after a reachable prover run is possible under fresh initialization.
Only support inclusion is needed, not equality of output distributions or losslessness. -/
def ReachableOutputCompatible
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∀ (WitIn WitOut : Type) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) stmtIn,
    ∀ result ∈ support (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (prover.run stmtIn witIn)).run (← init)),
    ∀ stmtOut,
    some stmtOut ∈ support ((simulateQ impl (verifier.run stmtIn result.1.1).run).run'
      result.2) →
    some stmtOut ∈ support (do
      (simulateQ impl (verifier.run stmtIn result.1.1).run).run' (← init))

/-- Reachable-output compatibility supplies the terminal bridge for ordinary soundness. -/
theorem rbrSoundness_implies_soundness_of_compatible
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (compat : verifier.ReachableOutputCompatible init impl)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrSoundness init impl langIn langOut ε) :
    verifier.soundness init impl langIn langOut (∑ i, ε i) := by
  obtain ⟨sF, hrbr⟩ := h
  apply rbrSoundness_implies_soundness_of_reachable init impl langIn langOut verifier sF ε
  · intro Wi Wo wi p stmt hstmt i
    exact hrbr stmt hstmt Wi Wo wi p i
  · intro Wi Wo wi p stmt _ result hresult stmtOut hout hrel
    by_contra hfalse
    have hz := sF.toFun_full stmt result.1.1 hfalse
    rw [OptionT.prEvent_mk_eq_zero_iff] at hz
    exact hz stmtOut (compat Wi Wo wi p stmt result hresult stmtOut hout) hrel

/-- Reachable-output compatibility also supplies the witness-aware terminal bridge. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness_of_compatible
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (compat : verifier.ReachableOutputCompatible init impl)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut ε) :
    verifier.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  obtain ⟨WitMid, extractor, kSF, hrbr⟩ := h
  apply knowledgeSoundness_of_with init impl
  apply rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith_of_reachable
    init impl relIn relOut verifier WitMid extractor kSF ε hrbr
  intro stmt wi p result hresult stmtOut hout hrel
  apply kSF.toFun_full stmt result.1.1 result.1.2.2
  simp only [Fin.val_last, gt_iff_lt, OptionT.prEvent_mk_pos_iff]
  exact ⟨stmtOut, compat WitIn WitOut wi p stmt result hresult stmtOut hout, hrel⟩

/-- Empty ambient specifications cannot observe the oracle state. This also covers an empty
initialization distribution: there are then no reachable prover outcomes. -/
theorem reachableOutputCompatible_empty
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (verifier : Verifier []ₒ StmtIn StmtOut pSpec) :
    verifier.ReachableOutputCompatible init impl := by
  intro Wi Wo wi p stmt result hresult stmtOut hout
  obtain ⟨initialState, hinit, _⟩ := (mem_support_bind_iff _ _ _).mp hresult
  have hpure := OracleComp.eq_pure_runEmpty (verifier.run stmt result.1.1).run
  rw [hpure] at hout ⊢
  simp only [simulateQ_pure, StateT.run'_pure'] at hout ⊢
  exact (mem_support_bind_iff _ _ _).mpr ⟨initialState, hinit, hout⟩

/-- RBR soundness for an empty ambient specification implies soundness with arbitrary state. -/
theorem rbrSoundness_implies_soundness_empty
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier []ₒ StmtIn StmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrSoundness init impl langIn langOut ε) :
    verifier.soundness init impl langIn langOut (∑ i, ε i) :=
  rbrSoundness_implies_soundness_of_compatible init impl langIn langOut verifier
    (reachableOutputCompatible_empty init impl verifier) ε h

/-- RBR KS for an empty ambient specification implies KS with arbitrary state. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness_empty
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier []ₒ StmtIn StmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut ε) :
    verifier.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  rbrKnowledgeSoundness_implies_knowledgeSoundness_of_compatible init impl relIn relOut verifier
    (reachableOutputCompatible_empty init impl verifier) ε h

/-- Worst-case RBR KS retains its error sum for empty ambient specifications and arbitrary state. -/
theorem rbrKnowledgeSoundnessWorstCase_implies_knowledgeSoundness_empty
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier []ₒ StmtIn StmtOut pSpec)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h : verifier.rbrKnowledgeSoundnessWorstCase init impl relIn relOut ε) :
    verifier.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  rbrKnowledgeSoundness_implies_knowledgeSoundness_empty init impl relIn relOut verifier ε
    (rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl h)

end Verifier
