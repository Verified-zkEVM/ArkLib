/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Data.Probability.OracleCompBridge

/-!
# Factoring the round-by-round game at a challenge round

The round-by-round (knowledge) soundness games (`Verifier.rbrKnowledgeSoundness`,
`RoundByRound.lean`) all end in the same shape: run a prefix computation (the prover up to
round `i`), draw the challenge `i` uniformly (`challengeQueryImpl`), and test a bad event on
the pair. This file factors the probability core out of that shape once and for all:
`probEvent_challengeRound_le` bounds the game by any `ε` that bounds, for **every** fixed
prefix outcome, the PMF-level probability of the bad event over a uniform challenge
(`Pr_{ let c ← $ᵖ (pSpec.Challenge i)}[…]` — the form the per-round error analyses, e.g.
`BatchingStrategy.separates`, are stated in).

The prefix is an *arbitrary* `OracleComp` over `oSpec + [pSpec.Challenge]ₒ` — no prover
structure is unfolded here — and the event may post-process the pair through an arbitrary
`k : A → pSpec.Challenge i → β` (the games return triples that also carry a query log; take
`β` to be the triple type and `k` the reassembly).

Stated over an arbitrary `oSpec` implementation `impl`, so it applies to the games verbatim.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec ProbabilityTheory
open scoped NNReal ENNReal

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

namespace Verifier

/-- **Challenge-round factoring for RBR games.** If for every outcome `a` of the prefix the
bad event `q ∘ k a` has uniform-challenge probability at most `ε`, then the whole game —
prefix, then uniformly sampled challenge `i`, then `k` — has probability at most `ε`.

This is the bridge from the protocol-level game (`simulateQ` under
`impl.addLift challengeQueryImpl`, the exact shape of `Verifier.rbrKnowledgeSoundness`) to
the PMF-level per-round error analyses (`Pr_{ let c ← $ᵖ _}[…]`, e.g.
`BatchingStrategy.separates`). -/
theorem probEvent_challengeRound_le
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {A β : Type} (mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) A)
    (i : pSpec.ChallengeIdx)
    [Fintype (pSpec.Challenge i)] [Nonempty (pSpec.Challenge i)]
    (k : A → pSpec.Challenge i → β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, Pr_{ let c ← $ᵖ (pSpec.Challenge i)}[q (k a c)] ≤ ε) :
    Pr[q | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let a ← mx
          let c ← liftComp (pSpec.getChallenge i) _
          return k a c)).run' (← init)] ≤ ε := by
  classical
  -- Peel the state-threaded simulation into its three stages (prefix / challenge / return).
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, QueryImpl.addLift_def,
    QueryImpl.simulateQ_add_liftComp_right, simulateQ_pure, StateT.run_pure]
  -- Condition on the initial state, then on the prefix outcome.
  refine probEvent_bind_le_of_forall_le fun s0 _ => ?_
  rw [probEvent_map]
  refine probEvent_bind_le_of_forall_le fun p _ => ?_
  -- The challenge round is a lifted uniform sample (`erw`: the query is under `MonadLift`).
  simp only [getChallenge]
  rw [bind_pure_comp, probEvent_map]
  erw [simulateQ_query]
  simp only [QueryImpl.liftTarget_apply, OracleQuery.cont, OracleQuery.input_query,
    StateT.run_map, StateT.run_monadLift, monadLift_self, challengeQueryImpl]
  rw [bind_pure_comp, probEvent_map]
  -- Land on the PMF side and close with the per-prefix hypothesis.
  rw [probEvent_map]
  -- Re-type the sample at `pSpec.Challenge i` (the oracle-spec `Range` is defeq, not syntactic).
  change probEvent ($ᵗ (pSpec.Challenge i)) _ ≤ ε
  exact le_trans (le_of_eq (probEvent_uniformSample_eq_pr_uniformOfFintype _)) (h p.1)

/-- **Game-shaped variant** of `probEvent_challengeRound_le`: specialized to the literal
prefix-run shape of `Verifier.rbrKnowledgeSoundness` (destructuring `let` over
`Prover.runWithLogToRound`). Unifying that destructuring bind against the plain-bind shape of
the general lemma diverges in `whnf` (structure-eta through the prover term), so this variant
replays the same proof script on the game shape directly — the destructuring matcher is fired
at the constructor level by one `obtain`. -/
theorem probEvent_rbrGame_le
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {StmtIn WitIn StmtOut WitOut : Type}
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : pSpec.ChallengeIdx)
    [Fintype (pSpec.Challenge i)] [Nonempty (pSpec.Challenge i)]
    {q : pSpec.Transcript i.1.castSucc × pSpec.Challenge i
        × QueryLog (oSpec + [pSpec.Challenge]ₒ) → Prop} {ε : ℝ≥0∞}
    (h : ∀ tr log, Pr_{ let c ← $ᵖ (pSpec.Challenge i)}[q (tr, c, log)] ≤ ε) :
    Pr[q | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ ε := by
  classical
  -- Peel the state-threaded simulation (same script as `probEvent_challengeRound_le`).
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, QueryImpl.addLift_def,
    QueryImpl.simulateQ_add_liftComp_right, simulateQ_pure, StateT.run_pure]
  refine probEvent_bind_le_of_forall_le fun s0 _ => ?_
  rw [probEvent_map]
  refine probEvent_bind_le_of_forall_le fun p _ => ?_
  -- Fire the destructuring matcher at the constructor level.
  obtain ⟨⟨⟨tr, st⟩, log⟩, s1⟩ := p
  simp only [getChallenge]
  rw [bind_pure_comp, probEvent_map]
  erw [simulateQ_query]
  simp only [QueryImpl.liftTarget_apply, OracleQuery.cont, OracleQuery.input_query,
    StateT.run_map, StateT.run_monadLift, monadLift_self, challengeQueryImpl]
  rw [bind_pure_comp, probEvent_map]
  rw [probEvent_map]
  change probEvent ($ᵗ (pSpec.Challenge i)) _ ≤ ε
  exact le_trans (le_of_eq (probEvent_uniformSample_eq_pr_uniformOfFintype _)) (h tr log)

end Verifier

end
