/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Calgooon
-/
module

public import ArkLib.OracleReduction.Security.Acceptance
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Round-by-round soundness bridges

This file projects round-by-round knowledge certificates to soundness certificates and accumulates
round-by-round soundness errors through the actual stateful prover execution. The terminal step
requires a current-state certificate; guarded verifiers supply it from their fresh-`init` terminal
field because their verdict depends only on the statement and transcript.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
  {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- A guarded verifier preserves the current oracle state and returns its deterministic verdict
exactly when its guard passes. -/
theorem GuardedForm.run_state {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) (s : σ) (stmt : StmtIn) (tr : pSpec.FullTranscript) :
    (simulateQ impl (V.run stmt tr)).run s =
      pure ((if G.check stmt tr then some (G.out stmt tr) else none), s) := by
  have hr : (V.run stmt tr : OracleComp oSpec (Option StmtOut)) =
      pure (if G.check stmt tr then some (G.out stmt tr) else none) := by
    simp only [Verifier.run, G.verify_eq stmt tr]
    split <;> rfl
  rw [hr, simulateQ_pure, StateT.run_pure]

/-- The positive-probability terminal event of a guarded verifier is exactly its deterministic
accepted verdict, independently of the fresh initialization. -/
theorem GuardedForm.prEvent_pos_iff {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) (stmt : StmtIn) (tr : pSpec.FullTranscript) (Q : StmtOut → Prop) :
    (Pr{let out ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← init)}[Q out] > 0) ↔
      G.check stmt tr = true ∧ Q (G.out stmt tr) :=
  ⟨G.check_and_of_prEvent_pos, fun h ↦ G.prEvent_pos_of_check h.1 h.2⟩

/-- A guarded verifier's fresh-`init` state-function terminal field is valid from every current
shared oracle state. -/
theorem GuardedForm.stateFunction_full {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) {langIn : Set StmtIn} {langOut : Set StmtOut}
    (S : V.StateFunction init impl langIn langOut)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (hS : ¬ S (Fin.last n) stmt tr) (s : σ) :
    Pr{let out ← OptionT.mk ((simulateQ impl (V.run stmt tr)).run' s)}[
      out ∈ langOut] = 0 := by
  apply le_antisymm _ zero_le
  apply le_of_not_gt
  intro hpos
  have hpos' : Pr{let out ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← (pure s : ProbComp σ))}[
      out ∈ langOut] > 0 := by simpa using hpos
  have hp := (G.prEvent_pos_iff stmt tr (fun out ↦ out ∈ langOut)).mp hpos'
  have hf := G.prEvent_pos_of_check (init := init) (impl := impl) hp.1 hp.2
  rw [S.toFun_full stmt tr hS] at hf
  exact (lt_irrefl _ hf)

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- Round-by-round knowledge soundness gives round-by-round soundness at the same challenge errors,
by existentially projecting the knowledge-state witness. -/
theorem rbrSoundness_of_rbrKnowledgeSoundnessWith
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {M : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec M}
    {K : V.KnowledgeStateFunction init impl relIn relOut E}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundnessWith init impl relIn relOut M E K ε) :
    V.rbrSoundness init impl relIn.language relOut.language ε := by
  refine ⟨K.toStateFunction init impl, fun stmt _ i tr ↦ ?_⟩
  refine le_trans (prEvent_mono _ _ _ ?_) (h stmt i tr)
  rintro c ⟨hnot, w, hw⟩
  exact ⟨w, fun hx ↦ hnot ⟨_, hx⟩, hw⟩

/-- The existential round-by-round knowledge certificate also projects to
round-by-round soundness. -/
theorem rbrSoundness_of_rbrKnowledgeSoundness
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.rbrSoundness init impl relIn.language relOut.language ε := by
  obtain ⟨M, E, K, h⟩ := h
  exact rbrSoundness_of_rbrKnowledgeSoundnessWith h

/-- A transcript-event bound gives soundness for any output language when the verifier cannot
output that language outside the event, from every current oracle state. -/
theorem soundness_of_output_event
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (ε : ℝ≥0) (E : StmtIn → pSpec.FullTranscript → Prop)
    (hfull : ∀ stmt ∉ langIn, ∀ tr, ¬ E stmt tr → ∀ s : σ,
      Pr{let out ← OptionT.mk ((simulateQ impl (V.run stmt tr)).run' s)}[
        out ∈ langOut] = 0)
    (hbound : ∀ (Aux Out : Type) (wit : Aux)
      (P : Prover oSpec StmtIn Aux StmtOut Out pSpec)
      (stmt : StmtIn), stmt ∉ langIn → ∀ s : σ,
      Pr{let x ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.run stmt wit)).run s}[E stmt x.1.1] ≤ ε) :
    V.soundness init impl langIn langOut ε := by
  intro Aux Out wit P stmt hstmt
  dsimp only
  rw [OptionT.prEvent_eq_run]
  apply prEvent_bind_le_of_forall_le_of_support _ _ _
  intro s _
  rw [StateT.run'_eq, prEvent_map, Reduction.run_run_eq_bind, simulateQ_bind, StateT.run_bind]
  refine le_trans ?_ (hbound Aux Out wit P stmt hstmt s)
  refine prEvent_bind_le_prEvent_of_support
    ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (P.run stmt wit)).run s) _ (fun x ↦ E stmt x.1.1) _ ?_
  intro x _ hx
  have hz := (OptionT.prEvent_mk_eq_zero_iff _ _).mp (hfull stmt hstmt x.1.1 hx x.2)
  simp only [simulateQ_bind, QueryImpl.addLift_def, liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftM_left, QueryImpl.liftTarget_self, StateT.run_bind]
  apply prEvent_eq_zero_of_forall_mem_support
  intro o ho hbad
  simp only [simulateQ_pure, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at ho
  obtain ⟨z, hzmem, rfl⟩ := ho
  cases he : z.1 with
  | none => simp [he] at hbad
  | some v =>
    apply hz v _ (by simpa [he] using hbad)
    rw [StateT.run'_eq, support_map]
    exact ⟨z, hzmem, he⟩

/-- Fixed-prefix transition errors accumulate through the actual prover execution. A terminal
certificate from every current oracle state then gives ordinary soundness at their sum. -/
theorem soundness_of_rbrSoundness_of_full
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {V : Verifier oSpec StmtIn StmtOut pSpec} {ε : pSpec.ChallengeIdx → ℝ≥0}
    (S : V.StateFunction init impl langIn langOut)
    (hbound : ∀ stmt ∉ langIn, ∀ i : pSpec.ChallengeIdx,
      ∀ tr : Transcript i.1.castSucc pSpec,
      Pr{let c ← $ᵗ (pSpec.Challenge i)}[
        ¬ S i.1.castSucc stmt tr ∧ S i.1.succ stmt (tr.concat c)] ≤ ε i)
    (hfull : ∀ stmt tr, ¬ S (Fin.last n) stmt tr → ∀ s : σ,
      Pr{let out ← OptionT.mk ((simulateQ impl (V.run stmt tr)).run' s)}[
        out ∈ langOut] = 0) :
    V.soundness init impl langIn langOut (∑ i, ε i) := by
  apply soundness_of_output_event langIn langOut V (∑ i, ε i)
    (fun stmt tr ↦ S (Fin.last n) stmt tr) (fun stmt _ ↦ hfull stmt)
  intro Aux Out wit P stmt hstmt s
  rw [ENNReal.ofNNReal_finsetSum]
  have hp := P.prob_state_runToRound_le
    (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) stmt wit
    (fun m tr ↦ S m stmt tr) (badEventRoundError (fun i ↦ (ε i : ℝ≥0∞)))
    (fun hs ↦ hstmt (S.toFun_empty stmt hs))
  have hstep : ∀ (j : Fin n) (tr : Transcript j.castSucc pSpec)
      (st : P.PrvState j.castSucc) (os : σ), ¬ S j.castSucc stmt tr →
      Pr{let x ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.processRound j (pure (tr, st)))).run os}[S j.succ stmt x.1.1] ≤
        badEventRoundError (fun i ↦ (ε i : ℝ≥0∞)) j := by
    intro j tr st os hs
    cases hd : pSpec.dir j with
    | P_to_V =>
      rw [badEventRoundError, dite_eq_right (by simp [hd])]
      exact P.prob_state_processRound_prover_le _ j hd _ tr st os
        (S.toFun_next j hd stmt tr hs)
    | V_to_P =>
      rw [badEventRoundError, dite_eq_left hd]
      refine (P.prob_state_processRound_challenge_le impl j hd _ tr st os).trans ?_
      simpa only [hs, not_false_eq_true, true_and] using hbound stmt hstmt ⟨j, hd⟩ tr
  have hlast := hp hstep (Fin.last n) s
  rw [Prover.errorBudget_last, sum_badEventRoundError] at hlast
  rw [Prover.run, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _
    (fun x ↦ S (Fin.last n) stmt x.1.1) _ ?_).trans hlast
  intro x _ hx
  simp only [simulateQ_bind, StateT.run_bind]
  apply le_antisymm _ zero_le
  apply prEvent_bind_le_of_forall_le_of_support _ _ _
  intro y _
  simp [simulateQ_pure, StateT.run_pure, hx]

/-- For a guarded verifier, round-by-round soundness gives ordinary soundness with
error the sum of the per-challenge errors, allowing arbitrary shared oracle state and provers. -/
theorem GuardedForm.soundness_of_rbrSoundness
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {V : Verifier oSpec StmtIn StmtOut pSpec} (G : V.GuardedForm)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrSoundness init impl langIn langOut ε) :
    V.soundness init impl langIn langOut (∑ i, ε i) := by
  obtain ⟨S, hbound⟩ := h
  exact soundness_of_rbrSoundness_of_full S hbound (G.stateFunction_full S)

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The guarded soundness bridge for an oracle verifier, after materializing its input and output
oracles. The error is the sum of the per-challenge errors. -/
theorem soundness_of_rbrSoundness_of_guarded
    {V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    (G : V.toVerifier.GuardedForm)
    {langIn : Set (StmtIn × ∀ i, OStmtIn i)}
    {langOut : Set (StmtOut × ∀ i, OStmtOut i)}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.toVerifier.rbrSoundness init impl langIn langOut ε) :
    V.soundness init impl langIn langOut (∑ i, ε i) :=
  G.soundness_of_rbrSoundness h

end OracleVerifier
