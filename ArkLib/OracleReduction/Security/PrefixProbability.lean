/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.BackwardExtraction
public import ArkLib.OracleReduction.Security.Accumulation

/-!
# Probability bounds for transcript prefixes

Removing a continuation gives an upper bound, not necessarily an equality: the continuation
may abort. These lemmas retain the actual adversarial prefix distribution.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Executing a round cannot increase the probability of an event on its previous transcript.
Neither the prefix nor the continuation is assumed lossless. -/
theorem processRound_prefix_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
    (m : Fin n)
    (prefixRun : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Transcript m.castSucc pSpec × prover.PrvState m.castSucc))
    (event : Transcript m.castSucc pSpec → Prop) :
    Pr{let result ← simulateQ handler (prover.processRound m prefixRun)}[
      event (Fin.init result.1)] ≤
      Pr{let result ← simulateQ handler prefixRun}[event result.1] := by
  cases hdir : pSpec.dir m with
  | P_to_V =>
    rw [processRound_of_dir_eq_P_to_V m hdir, simulateQ_bind]
    apply prEvent_bind_le_prEvent_of_forall_eq_zero
    intro result hfalse
    simp only [bind_pure_comp, simulateQ_map, prEvent_map]
    apply prEvent_eq_zero_of_forall_not
    intro next
    have hinit : Fin.init (result.1.concat next.1) = result.1 := by
      funext j
      exact Transcript.concat_castSucc _ _ j
    exact fun h => hfalse (hinit ▸ h)
  | V_to_P =>
    rw [processRound_of_dir_eq_V_to_P m hdir, simulateQ_bind]
    apply prEvent_bind_le_prEvent_of_forall_eq_zero
    intro result hfalse
    simp only [simulateQ_bind, bind_pure_comp, simulateQ_map]
    apply prEvent_eq_zero_of_forall_mem_support
    intro next hnext
    simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at hnext
    obtain ⟨challenge, _, state, _, rfl⟩ := hnext
    have hinit : Fin.init (result.1.concat challenge) = result.1 := by
      funext j
      exact Transcript.concat_castSucc _ _ j
    exact fun h => hfalse (hinit ▸ h)

/-- A challenge-round event is bounded before the adversary receives the challenge.
Dropping `receiveChallenge` preserves the sampled prefix and challenge, but may increase mass. -/
theorem processRound_challenge_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
    (i : pSpec.ChallengeIdx)
    (prefixRun : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Transcript i.1.castSucc pSpec × prover.PrvState i.1.castSucc))
    (event : Transcript i.1.succ pSpec → Prop) :
    Pr{let result ← simulateQ handler (prover.processRound i.1 prefixRun)}[event result.1] ≤
      Pr{let result ← simulateQ handler (do
        let result ← prefixRun
        let challenge ← liftComp (pSpec.getChallenge i) _
        pure (result.1, challenge))}[event (result.1.concat result.2)] := by
  classical
  rw [processRound_of_dir_eq_V_to_P i.1 i.2]
  simp only [simulateQ_bind, bind_pure_comp, simulateQ_map]
  apply prEvent_bind_mono_of_forall_le
  intro result
  rw [prEvent_map]
  apply prEvent_bind_le_prEvent_of_forall_eq_zero
  intro challenge hfalse
  rw [prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ (fun _ => hfalse)

/-- Union bound along the actual execution. Every round is charged its bad-event probability;
continuations are discarded by domination, so this also covers aborting adversaries. -/
theorem runToRound_hasBadRound_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
    (stmtIn : StmtIn) (witIn : WitIn)
    (bad : (m : Fin n) → Transcript m.succ pSpec → Prop)
    (charge : Fin n → ENNReal)
    (hcharge : ∀ m, Pr{let result ← simulateQ handler (prover.runToRound m.succ stmtIn witIn)}[bad m
      result.1] ≤ charge m)
    (m : Fin (n + 1)) :
    Pr{let result ← simulateQ handler (prover.runToRound m stmtIn witIn)}[
      Transcript.HasBadRound bad m result.1] ≤ errorBudget charge m := by
  induction m using Fin.induction with
  | zero => simp [Transcript.HasBadRound]
  | succ m ih =>
    rw [errorBudget_succ]
    calc
      _ = Pr{let result ← simulateQ handler (prover.runToRound m.succ stmtIn witIn)}[
          Transcript.HasBadRound bad m.castSucc (Fin.init result.1) ∨ bad m result.1] := by
            simp only [Transcript.hasBadRound_succ]
      _ ≤ Pr{let result ← simulateQ handler (prover.runToRound m.succ stmtIn witIn)}[
          Transcript.HasBadRound bad m.castSucc (Fin.init result.1)] +
          Pr{let result ← simulateQ handler (prover.runToRound m.succ stmtIn witIn)}[
            bad m result.1] := prEvent_or_le _ _ _
      _ ≤ Pr{let result ← simulateQ handler (prover.runToRound m.castSucc stmtIn witIn)}[
          Transcript.HasBadRound bad m.castSucc result.1] + charge m := by
            apply add_le_add _ (hcharge m)
            rw [runToRound_succ]
            exact prover.processRound_prefix_probability_le handler m _ _
      _ ≤ _ := add_le_add ih le_rfl

/-- The prover's output computation cannot increase a transcript-only event's probability. -/
theorem run_transcript_probability_le
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
    (stmtIn : StmtIn) (witIn : WitIn) (event : FullTranscript pSpec → Prop) :
    Pr{let result ← simulateQ handler (prover.run stmtIn witIn)}[event result.1] ≤
      Pr{let result ← simulateQ handler (prover.runToRound (.last n) stmtIn witIn)}[
        event result.1] := by
  rw [run, simulateQ_bind]
  apply prEvent_bind_le_prEvent_of_forall_eq_zero
  intro result hfalse
  simp only [bind_pure_comp, simulateQ_map, prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ (fun _ => hfalse)

/-- Averaged bounds on the actual challenge-prefix games accumulate without replacing them
by worst-case bounds over unreachable transcripts. -/
theorem hasBadRound_probability_le_sum
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (handler : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
    (stmtIn : StmtIn) (witIn : WitIn)
    (bad : (m : Fin n) → Transcript m.succ pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ENNReal)
    (hprover : ∀ m, pSpec.dir m = .P_to_V → ∀ tr, ¬ bad m tr)
    (hchallenge : ∀ i : pSpec.ChallengeIdx,
      Pr{let result ← simulateQ handler (do
        let result ← prover.runToRound i.1.castSucc stmtIn witIn
        let challenge ← liftComp (pSpec.getChallenge i) _
        pure (result.1, challenge))}[bad i.1 (result.1.concat result.2)] ≤ ε i) :
    Pr{let result ← simulateQ handler (prover.runToRound (.last n) stmtIn witIn)}[
      Transcript.HasBadRound bad (.last n) result.1] ≤ ∑ i, ε i := by
  have hcharge : ∀ m,
      Pr{let result ← simulateQ handler (prover.runToRound m.succ stmtIn witIn)}[
        bad m result.1] ≤ Verifier.badEventRoundError ε m := by
    intro m
    cases hdir : pSpec.dir m with
    | P_to_V =>
      rw [Verifier.badEventRoundError, dite_eq_right (by simp [hdir])]
      apply le_of_eq
      apply prEvent_eq_zero_of_forall_not
      intro result
      exact hprover m hdir result.1
    | V_to_P =>
      rw [Verifier.badEventRoundError, dite_eq_left hdir, runToRound_succ]
      exact (prover.processRound_challenge_probability_le handler ⟨m, hdir⟩ _ _).trans
        (hchallenge ⟨m, hdir⟩)
  simpa only [errorBudget_last, Verifier.sum_badEventRoundError] using
    prover.runToRound_hasBadRound_probability_le handler stmtIn witIn bad
      (Verifier.badEventRoundError ε) hcharge (.last n)

end Prover
