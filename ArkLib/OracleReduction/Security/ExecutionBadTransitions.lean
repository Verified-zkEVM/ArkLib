/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.BackwardExtraction
public import ArkLib.OracleReduction.Security.ExecutionPrefix
public import ArkLib.OracleReduction.Security.GuardedTerminal

/-!
# Bad-transition marginals of an actual execution

Full-transcript bad events have the same probability as the prefix-and-challenge events in
RBR knowledge soundness. The shared state is threaded through the execution, never reset.
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

private theorem init_concat (i : Fin n) (tr : pSpec.Transcript i.castSucc)
    (c : pSpec.Type i) : Fin.init (tr.concat c) = tr := by
  funext q
  exact Transcript.concat_castSucc c tr q

/-- Each full-transcript bad transition has exactly the probability of its prefix game,
for any initial shared state and any total challenge implementation. -/
theorem badChallenge_probability_eq_prefix
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (qImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : pSpec.ChallengeIdx) :
    Pr{let x ← (simulateQ qImpl (P.runToRound (Fin.last n) stmt wit)).run' s}[
      badChallengeOnTranscript init impl K stmt x.1 i] =
    Pr{let tr ← (simulateQ qImpl (do
      let x ← P.runToRound i.1.castSucc stmt wit
      let c ← pSpec.getChallenge i
      pure (x.1.concat c))).run' s}[
      rbrExtractionFailureEvent K E i stmt (Fin.init tr) (tr (Fin.last i.1.val))] := by
  exact P.simulate_fullRun_challenge_prefix_probability qImpl s stmt wit i
    (fun tr => rbrExtractionFailureEvent K E i stmt (Fin.init tr)
      (tr (Fin.last i.1.val)))

/-- Averaged RBR security bounds the bad transition read from the full interaction.
This uses the original prover-sampled prefix bound, not a fixed-prefix strengthening. -/
theorem badChallenge_probability_le_of_rbr
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : pSpec.ChallengeIdx) :
    Pr{let x ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.runToRound (Fin.last n) stmt wit)).run' (← init)}[
      badChallengeOnTranscript init impl K stmt x.1 i] ≤ ε i := by
  have hb := hRbr stmt wit P i
  apply le_trans ?_ hb
  apply le_of_eq
  simp only [← bind_assoc]
  apply prEvent_bind_congr
  intro s
  rw [badChallenge_probability_eq_prefix]
  rw [← P.runWithLogToRound_discard_log_eq_runToRound i.1.castSucc stmt wit]
  simp only [bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  simp only [init_concat, Transcript.concat_last, rbrExtractionFailureEvent]
  rfl

/-- The probability of any bad transition in the actual full interaction is bounded by the
sum of the original averaged RBR errors. -/
theorem exists_badChallenge_probability_le_sum
    [∀ j, SampleableType (pSpec.Challenge j)]
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hRbr : V.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut W E K ε)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    Pr{let x ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.runToRound (Fin.last n) stmt wit)).run' (← init)}[
      ∃ i, badChallengeOnTranscript init impl K stmt x.1 i] ≤
      ∑ i : pSpec.ChallengeIdx, (ε i : ℝ≥0∞) := by
  classical
  simp only [← bind_assoc]
  refine (prEvent_exists_le (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.runToRound (Fin.last n) stmt wit)).run' (← init))
    (fun i (x : pSpec.Transcript (Fin.last n) × P.PrvState (Fin.last n)) =>
      badChallengeOnTranscript init impl K stmt x.1 i)).trans ?_
  apply Finset.sum_le_sum
  intro i _
  convert badChallenge_probability_le_of_rbr init impl K ε hRbr P stmt wit i using 1
  rw [bind_assoc]

/-- Without a bad transition, an actually accepting verifier cannot validate an output whose
backward-extracted witness is invalid. The verifier starts in the supplied actual state. -/
theorem verifier_failure_probability_eq_zero_of_local_terminal
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (wit : WitOut) (s : σ)
    (hTerminal : ∀ out,
      some out ∈ support ((simulateQ impl (V.run stmt tr).run).run' s) →
      (out, wit) ∈ relOut → K (.last n) stmt tr (E.extractOut stmt tr wit))
    (hgood : ¬ ∃ i, badChallengeOnTranscript init impl K stmt tr i) :
    Pr{let out ← OptionT.mk ((simulateQ impl (V.run stmt tr).run).run' s)}[
      (stmt, E.extractToInput stmt (Fin.last n) tr (E.extractOut stmt tr wit)) ∉ relIn ∧
      (out, wit) ∈ relOut] = 0 := by
  rw [OracleComp.OptionT.prEvent_mk_eq_zero_iff]
  intro out hs hfail
  exact hgood (exists_badChallengeOnTranscript_of_extract_failure init impl K stmt tr wit
    (hTerminal out hs hfail.2) hfail.1)

/-- The every-state terminal certificate specializes to each verifier execution. -/
theorem verifier_failure_probability_eq_zero_of_no_badChallenge
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hTerminal : K.TerminalFromEveryState init impl)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (wit : WitOut) (s : σ)
    (hgood : ¬ ∃ i, badChallengeOnTranscript init impl K stmt tr i) :
    Pr{let out ← OptionT.mk ((simulateQ impl (V.run stmt tr).run).run' s)}[
      (stmt, E.extractToInput stmt (Fin.last n) tr (E.extractOut stmt tr wit)) ∉ relIn ∧
      (out, wit) ∈ relOut] = 0 :=
  verifier_failure_probability_eq_zero_of_local_terminal init impl K stmt tr wit s
    (hTerminal stmt tr wit s) hgood

end Verifier.KnowledgeStateFunction
