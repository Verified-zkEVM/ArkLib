/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.ExecutionBadTransitions

/-!
# Backward extraction in the actual reduction game

The verifier runs after the prover, in the shared state left by that prover. Rejection is
excluded from the bad event; extractor failure is not excluded.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Verifier.KnowledgeStateFunction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {W : Fin (n + 1) → Type}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {V : Verifier oSpec StmtIn StmtOut pSpec}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

/-- The actual reduction's extraction-failure event is bounded by bad transcripts produced
by the prover, assuming terminal knowledge at actual verifier-start states. -/
theorem reduction_failure_le_badChallenge_of_reachable
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (hTerminal : ∀ x ∈ support (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.run stmt wit)).run (← init)),
      ∀ out, some out ∈ support ((simulateQ impl (V.run stmt x.1.1).run).run' x.2) →
        (out, x.1.2.2) ∈ relOut →
        K (.last n) stmt x.1.1 (E.extractOut stmt x.1.1 x.1.2.2)) :
    Pr{let x ← OptionT.mk (do (simulateQ
      (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((Reduction.mk P V).run stmt wit).run).run' (← init))}[
      (stmt, E.extractToInput stmt (Fin.last n) x.1.1
        (E.extractOut stmt x.1.1 x.1.2.2)) ∉ relIn ∧ (x.2, x.1.2.2) ∈ relOut] ≤
    Pr{let x ← do (simulateQ
      (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (P.run stmt wit)).run' (← init)}[
      ∃ i, badChallengeOnTranscript init impl K stmt x.1 i] := by
  have hrun : ((Reduction.mk P V).run stmt wit).run = (do
      let x ← P.run stmt wit
      let out ← liftComp (V.run stmt x.1).run (oSpec + [pSpec.Challenge]ₒ)
      pure (out.map (fun y => (x, y)))) := by
    simp only [Reduction.run, OptionT.run_bind, OptionT.run_pure,
      OptionT.run_monadLift, monadLift_self, Option.elimM, bind_map_left, Option.elim_some]
    congr 1
    funext x
    rw [← monadLift_liftM_OptionT (superSpec := oSpec + [pSpec.Challenge]ₒ)
      (V.run stmt x.1).run]
    simp only [OptionT.run_monadLift, monadLift_self, bind_map_left, Option.elim_some]
    congr 1
    funext out
    cases out <;> rfl
  rw [hrun]
  rw [OptionT.prEvent_mk]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_map_left,
    bind_assoc]
  simp only [← bind_assoc]
  apply prEvent_bind_le_prEvent_of_support
  intro x hx hgood
  simp only [liftComp_eq_liftM, QueryImpl.simulateQ_addLift_liftM_left,
    monadLift_self, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind,
    Option.elim_map]
  have hz := verifier_failure_probability_eq_zero_of_local_terminal init impl K
    stmt x.1.1 x.1.2.2 x.2 (hTerminal x hx) hgood
  rw [OptionT.prEvent_mk] at hz
  simp only [StateT.run'_eq, bind_map_left] at hz
  exact hz

/-- Every-state terminal knowledge suffices in particular at reachable states. -/
theorem reduction_failure_le_badChallenge
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hTerminal : K.TerminalFromEveryState init impl)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    Pr{let x ← OptionT.mk (do (simulateQ
      (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((Reduction.mk P V).run stmt wit).run).run' (← init))}[
      (stmt, E.extractToInput stmt (Fin.last n) x.1.1
        (E.extractOut stmt x.1.1 x.1.2.2)) ∉ relIn ∧ (x.2, x.1.2.2) ∈ relOut] ≤
    Pr{let x ← do (simulateQ
      (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (P.run stmt wit)).run' (← init)}[
      ∃ i, badChallengeOnTranscript init impl K stmt x.1 i] := by
  exact reduction_failure_le_badChallenge_of_reachable init impl K P stmt wit
    (fun x _ => hTerminal stmt x.1.1 x.1.2.2 x.2)


/-- The existing reduction execution satisfies the backward-extraction error bound, with
the original sum of averaged RBR errors and a terminal certificate for actual states. -/
theorem reduction_failure_le_sum_of_rbr_of_reachable
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (hTerminal : ∀ x ∈ support (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.run stmt wit)).run (← init)),
      ∀ out, some out ∈ support ((simulateQ impl (V.run stmt x.1.1).run).run' x.2) →
        (out, x.1.2.2) ∈ relOut →
        K (.last n) stmt x.1.1 (E.extractOut stmt x.1.1 x.1.2.2)) :
    Pr{let x ← OptionT.mk (do (simulateQ
      (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((Reduction.mk P V).run stmt wit).run).run' (← init))}[
      (stmt, E.extractToInput stmt (Fin.last n) x.1.1
        (E.extractOut stmt x.1.1 x.1.2.2)) ∉ relIn ∧ (x.2, x.1.2.2) ∈ relOut] ≤
      ∑ i : pSpec.ChallengeIdx, (ε i : ℝ≥0∞) := by
  refine (reduction_failure_le_badChallenge_of_reachable init impl K P stmt wit hTerminal).trans ?_
  calc
    _ = Pr{let x ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.runToRound (Fin.last n) stmt wit)).run' (← init)}[
      ∃ i, badChallengeOnTranscript init impl K stmt x.1 i] := by
        simp only [← bind_assoc]
        apply prEvent_bind_congr
        intro s
        exact P.simulate_run_transcript_probability
          (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) s stmt wit
          (fun tr => ∃ i, badChallengeOnTranscript init impl K stmt tr i)
    _ ≤ _ := exists_badChallenge_probability_le_sum init impl K ε hRbr P stmt wit

/-- Every-state terminal knowledge gives the same sum bound as reachable-state knowledge. -/
theorem reduction_failure_le_sum_of_rbr
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hTerminal : K.TerminalFromEveryState init impl)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    Pr{let x ← OptionT.mk (do (simulateQ
      (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((Reduction.mk P V).run stmt wit).run).run' (← init))}[
      (stmt, E.extractToInput stmt (Fin.last n) x.1.1
        (E.extractOut stmt x.1.1 x.1.2.2)) ∉ relIn ∧ (x.2, x.1.2.2) ∈ relOut] ≤
      ∑ i : pSpec.ChallengeIdx, (ε i : ℝ≥0∞) := by
  exact reduction_failure_le_sum_of_rbr_of_reachable init impl K ε hRbr P stmt wit
    (fun x _ => hTerminal stmt x.1.1 x.1.2.2 x.2)


end Verifier.KnowledgeStateFunction

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {W : Fin (n + 1) → Type}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {V : Verifier oSpec StmtIn StmtOut pSpec}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

/-- Averaged RBR knowledge soundness implies straightline knowledge soundness when terminal
knowledge holds at actual verifier-start states. The extractor performs pure backward extraction. -/
theorem rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hTerminal : ∀ (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) stmt wit,
      ∀ x ∈ support (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (P.run stmt wit)).run (← init)),
        ∀ out, some out ∈ support ((simulateQ impl (V.run stmt x.1.1).run).run' x.2) →
          (out, x.1.2.2) ∈ relOut →
          K (.last n) stmt x.1.1 (E.extractOut stmt x.1.1 x.1.2.2))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E.toStraightline (∑ i, ε i) := by
  intro stmt wit P
  dsimp only
  simp only [Extractor.RoundByRound.toStraightline, OptionT.run_pure, liftM_pure, pure_bind]
  let f := fun x : (pSpec.FullTranscript × StmtOut × WitOut) × StmtOut =>
    (stmt, some (E.extractToInput stmt (Fin.last n) x.1.1
      (E.extractOut stmt x.1.1 x.1.2.2)), x.2, x.1.2.2)
  have he : (do
      let x ← (Reduction.mk P V).runWithLog stmt wit
      pure (f x.1)) = f <$> (Reduction.mk P V).run stmt wit := by
    rw [← Reduction.runWithLog_discard_logs_eq_run]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  rw [he]
  simp only [OptionT.run_map, simulateQ_map, StateT.run'_map', OptionT.prEvent_mk,
    bind_assoc, bind_map_left, Option.elim_map, Function.comp_def, Option.mem_def,
    f, Option.some.injEq, forall_eq']
  have hb := K.reduction_failure_le_sum_of_rbr_of_reachable init impl ε hRbr P stmt wit
    (hTerminal P stmt wit)
  rw [OptionT.prEvent_mk] at hb
  simpa only [ENNReal.ofNNReal_finsetSum, bind_assoc] using hb

/-- An invariant of reachable verifier-start states suffices for terminal knowledge.
The verifier may have state-dependent accepted outputs: no deterministic reference verifier
or full-support initialization is required. The invariant must hold for every adversarial prover. -/
theorem rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_invariant
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (Inv : σ → Prop)
    (hReach : ∀ (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) stmt wit,
      ∀ x ∈ support (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (P.run stmt wit)).run (← init)), Inv x.2)
    (hTerminal : ∀ stmt tr wit state, Inv state →
      ∀ out, some out ∈ support ((simulateQ impl (V.run stmt tr).run).run' state) →
        (out, wit) ∈ relOut → K (.last n) stmt tr (E.extractOut stmt tr wit))
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E.toStraightline (∑ i, ε i) :=
  rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable init impl K
    (fun P stmt wit x hx => hTerminal stmt x.1.1 x.1.2.2 x.2 (hReach P stmt wit x hx))
    ε hRbr

/-- The stronger every-state certificate implies the reachable-state condition. -/
theorem rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_terminal
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hTerminal : K.TerminalFromEveryState init impl)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E.toStraightline (∑ i, ε i) := by
  exact rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable init impl K
    (fun _ stmt _ x _ => hTerminal stmt x.1.1 x.1.2.2 x.2) ε hRbr


/-- State-changing provers and verifiers are allowed when every reachable verifier-start
state remains in the initialization support. The hypothesis concerns only reachability,
not the desired knowledge-soundness conclusion. -/
theorem rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_support_closed
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hClosed : ∀ (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) stmt wit,
      ∀ x ∈ support (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (P.run stmt wit)).run (← init)), x.2 ∈ support init)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E.toStraightline (∑ i, ε i) := by
  apply rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable
    init impl K ?_ ε hRbr
  intro P stmt wit x hx out hout hrel
  exact K.terminal_of_mem_init_support init impl stmt x.1.1 x.1.2.2 x.2 out
    (hClosed P stmt wit x hx) hout hrel

/-- Full-support initialization is a sufficient terminal condition even for genuinely
stateful verifiers. The sum of round errors is unchanged. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness_of_full_support
    [∀ j, SampleableType (pSpec.Challenge j)]
    (hinit : ∀ s, s ∈ support init) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  obtain ⟨W, E, K, hK⟩ := hRbr
  apply (knowledgeSoundness_iff_exists_with init impl relIn relOut V _).mpr
  refine ⟨E.toStraightline, ?_⟩
  apply rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_terminal
    init impl K (K.terminalFromEveryState_of_full_support init impl hinit) ε
  exact rbrKnowledgeSoundnessWith_implies_rbrKnowledgeSoundnessAveragedWith init impl hK

/-- Guarded verifiers supply terminal knowledge without any restriction on the prover's
shared-state effects. Only the original averaged RBR bound is required. -/
theorem rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded
    [∀ j, SampleableType (pSpec.Challenge j)]
    (G : V.GuardedForm) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  obtain ⟨W, E, K, hK⟩ := hRbr
  apply (knowledgeSoundness_iff_exists_with init impl relIn relOut V _).mpr
  exact ⟨E.toStraightline,
    rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_terminal init impl K
      (G.terminalFromEveryState init impl K) ε hK⟩

end Verifier

namespace OracleVerifier

/-- Oracle-verifier version of the guarded RBR-to-plain theorem, using the same underlying
execution and the same sum of round errors. -/
theorem rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {ιIn ιOut : Type} {OStmtIn : ιIn → Type} {OStmtOut : ιOut → Type}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    (G : V.toVerifier.GuardedForm) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  Verifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded init impl G ε hRbr

end OracleVerifier
