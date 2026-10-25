/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.BackwardExtraction
public import ArkLib.OracleReduction.Security.Accumulation

/-!
# Prefix event bounds with shared oracle state

The joint execution retains the oracle state until a continuation has been bounded. Averaged
challenge bounds concern the same prover and initial distribution, not arbitrary fresh states.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut σ : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Dropping a round preserves an upper bound on a prefix-only event, including shared state. -/
theorem processRound_prefix_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (init : ProbComp σ) (m : Fin n)
    (prefixRun : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Transcript m.castSucc pSpec × prover.PrvState m.castSucc))
    (event : Transcript m.castSucc pSpec → Prop) :
    Pr{let result ← (do (simulateQ handler (prover.processRound m prefixRun)).run (← init))}[
      event (Fin.init result.1.1)] ≤
    Pr{let result ← (do (simulateQ handler prefixRun).run (← init))}[event result.1.1] := by
  apply prEvent_bind_mono_of_forall_le
  intro os
  cases hdir : pSpec.dir m with
  | P_to_V =>
    rw [processRound_of_dir_eq_P_to_V m hdir, simulateQ_bind, StateT.run_bind]
    apply prEvent_bind_le_prEvent_of_forall_eq_zero
    intro result hfalse
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    apply prEvent_eq_zero_of_forall_mem_support
    intro next hnext
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hnext
    obtain ⟨next, _, rfl⟩ := hnext
    simpa only [Transcript.init_concat] using hfalse
  | V_to_P =>
    rw [processRound_of_dir_eq_V_to_P m hdir, simulateQ_bind, StateT.run_bind]
    apply prEvent_bind_le_prEvent_of_forall_eq_zero
    intro result hfalse
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    apply prEvent_eq_zero_of_forall_mem_support
    intro next hnext
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hnext
    obtain ⟨challenge, _, next, _, rfl⟩ := hnext
    simpa only [Transcript.init_concat] using hfalse

/-- Discard the challenge-receiving continuation without resetting the shared state. -/
theorem processRound_challenge_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (init : ProbComp σ) (i : pSpec.ChallengeIdx)
    (prefixRun : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Transcript i.1.castSucc pSpec × prover.PrvState i.1.castSucc))
    (event : Transcript i.1.succ pSpec → Prop) :
    Pr{let result ← (do (simulateQ handler (prover.processRound i.1 prefixRun)).run (← init))}[
      event result.1.1] ≤
    Pr{let result ← (do (simulateQ handler (do
      let result ← prefixRun
      let challenge ← liftComp (pSpec.getChallenge i) _
      pure (result.1, challenge))).run (← init))}[event (result.1.1.concat result.1.2)] := by
  apply prEvent_bind_mono_of_forall_le
  intro os
  rw [processRound_of_dir_eq_V_to_P i.1 i.2]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply prEvent_bind_mono_of_forall_le
  intro result
  apply prEvent_bind_mono_of_forall_le
  intro challenge
  by_cases hevent : event (result.1.1.concat challenge.1)
  · have hone : Pr{let r ← (pure ((result.1.1, challenge.1), challenge.2) :
        ProbComp _)}[event (r.1.1.concat r.1.2)] = 1 := by
      apply prEvent_eq_one_of_forall_mem_support
      intro r hr
      simp only [mem_support_pure_iff] at hr
      subst r
      exact hevent
    rw [hone]
    exact prEvent_le_one _
  · apply le_trans (le_of_eq ?_) zero_le
    apply prEvent_eq_zero_of_forall_mem_support
    intro next hnext
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hnext
    obtain ⟨next, _, rfl⟩ := hnext
    exact hevent

/-- Actual-prefix challenge bounds accumulate for arbitrary initial distributions and handlers. -/
theorem hasBadRound_probability_le_sum
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (init : ProbComp σ) (stmtIn : StmtIn) (witIn : WitIn)
    (bad : (m : Fin n) → Transcript m.succ pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ENNReal)
    (hprover : ∀ m, pSpec.dir m = .P_to_V → ∀ tr, ¬ bad m tr)
    (hchallenge : ∀ i : pSpec.ChallengeIdx,
      Pr{let result ← (do (simulateQ handler (do
        let result ← prover.runToRound i.1.castSucc stmtIn witIn
        let challenge ← liftComp (pSpec.getChallenge i) _
        pure (result.1, challenge))).run (← init))}[bad i.1 (result.1.1.concat result.1.2)] ≤ ε i) :
    Pr{let result ← (do
      (simulateQ handler (prover.runToRound (.last n) stmtIn witIn)).run (← init))}[
      Transcript.HasBadRound bad (.last n) result.1.1] ≤ ∑ i, ε i := by
  have hcharge : ∀ m,
      Pr{let result ← (do
        (simulateQ handler (prover.runToRound m.succ stmtIn witIn)).run (← init))}[
        bad m result.1.1] ≤ Verifier.badEventRoundError ε m := by
    intro m
    cases hdir : pSpec.dir m with
    | P_to_V =>
      rw [Verifier.badEventRoundError, dite_eq_right (by simp [hdir])]
      apply le_of_eq
      apply prEvent_eq_zero_of_forall_not
      intro r
      exact hprover m hdir r.1.1
    | V_to_P =>
      rw [Verifier.badEventRoundError, dite_eq_left hdir, runToRound_succ]
      exact (prover.processRound_challenge_probability_le handler init
        ⟨m, hdir⟩ _ _).trans (hchallenge ⟨m, hdir⟩)
  have hprefix : ∀ m : Fin (n + 1),
      Pr{let result ← (do
        (simulateQ handler (prover.runToRound m stmtIn witIn)).run (← init))}[
        Transcript.HasBadRound bad m result.1.1] ≤
        errorBudget (Verifier.badEventRoundError ε) m := by
    intro m
    induction m using Fin.induction with
    | zero => simp
    | succ m ih =>
      rw [errorBudget_succ]
      simp only [Transcript.hasBadRound_succ]
      refine (prEvent_or_le _ _ _).trans (add_le_add ?_ (hcharge m))
      refine le_trans ?_ ih
      rw [runToRound_succ]
      exact prover.processRound_prefix_probability_le handler init m _ _
  simpa only [errorBudget_last, Verifier.sum_badEventRoundError] using hprefix (.last n)

/-- The prover's output computation cannot increase a transcript-only event's probability. -/
theorem run_transcript_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (init : ProbComp σ) (stmtIn : StmtIn) (witIn : WitIn)
    (event : FullTranscript pSpec → Prop) :
    Pr{let result ← (do (simulateQ handler (prover.run stmtIn witIn)).run (← init))}[
      event result.1.1] ≤
    Pr{let result ← (do
      (simulateQ handler (prover.runToRound (.last n) stmtIn witIn)).run (← init))}[
      event result.1.1] := by
  apply prEvent_bind_mono_of_forall_le
  intro os
  rw [run, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_le_prEvent_of_forall_eq_zero
  intro result hfalse
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply prEvent_eq_zero_of_forall_mem_support
  intro next hnext
  simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hnext
  obtain ⟨next, _, rfl⟩ := hnext
  exact hfalse

end Prover
