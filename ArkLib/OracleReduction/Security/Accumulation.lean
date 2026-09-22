/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.BadEvents

/-!
# Accumulating errors in the actual prover execution

These bounds use `Prover.runToRound`, including its private state and the shared oracle
state. The error is charged only when the predicate was false before a round.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
variable (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- Processing a round factors through its current transcript and private state. -/
theorem processRound_bind (j : Fin n)
    (current : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j current =
      current >>= fun x ↦ prover.processRound j (pure x) := by
  simp only [processRound, pure_bind]

/-- A prefix budget sums the errors of precisely the rounds already executed. -/
noncomputable def errorBudget (ε : Fin n → ℝ≥0∞) (m : Fin (n + 1)) : ℝ≥0∞ :=
  ∑ j : Fin m.val, ε ⟨j.val, Nat.lt_of_lt_of_le j.isLt m.is_le⟩

@[simp]
theorem errorBudget_zero (ε : Fin n → ℝ≥0∞) : errorBudget ε 0 = 0 := by
  simp [errorBudget]

@[simp]
theorem errorBudget_succ (ε : Fin n → ℝ≥0∞) (j : Fin n) :
    errorBudget ε j.succ = errorBudget ε j.castSucc + ε j := by
  exact Fin.sum_univ_castSucc (fun z : Fin (j.val + 1) ↦ ε ⟨z.val, by omega⟩)

@[simp]
theorem errorBudget_last (ε : Fin n → ℝ≥0∞) : errorBudget ε (Fin.last n) = ∑ j, ε j := rfl

/-- Conditional one-step bounds add along an adaptive prover's actual execution.
The event can depend on the entire transcript; the prover and oracle states are retained
throughout the induction. -/
theorem prob_state_runToRound_le {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (stmt : StmtIn) (wit : WitIn)
    (S : (m : Fin (n + 1)) → pSpec.Transcript m → Prop) (ε : Fin n → ℝ≥0∞)
    (hzero : ¬ S 0 default)
    (hstep : ∀ (j : Fin n) (tr : pSpec.Transcript j.castSucc)
      (st : prover.PrvState j.castSucc) (os : σ), ¬ S j.castSucc tr →
      Pr[ fun x ↦ S j.succ x.1.1 |
        (simulateQ impl (prover.processRound j (pure (tr, st)))).run os] ≤ ε j)
    (m : Fin (n + 1)) (os : σ) :
    Pr[ fun x ↦ S m x.1.1 |
      (simulateQ impl (prover.runToRound m stmt wit)).run os] ≤ errorBudget ε m := by
  induction m using Fin.induction with
  | zero =>
    simp [runToRound_zero_of_prover_first, simulateQ_pure, StateT.run_pure, hzero]
  | succ j ih =>
    rw [runToRound_succ, processRound_bind, simulateQ_bind, StateT.run_bind]
    refine (probEvent_bind_le_probEvent_add (p := fun x ↦ S j.castSucc x.1.1)
      (ε := ε j) ?_).trans ?_
    · intro x _ hx
      exact hstep j x.1.1 x.1.2 x.2 hx
    · rw [errorBudget_succ]
      exact add_le_add ih le_rfl

/-- A prover-message round cannot make a transcript predicate true if the predicate is
closed under every possible prover message. This is independent of private oracle calls. -/
theorem prob_state_processRound_prover_le {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (j : Fin n) (hj : pSpec.dir j = .P_to_V)
    (S : pSpec.Transcript j.succ → Prop)
    (tr : pSpec.Transcript j.castSucc) (st : prover.PrvState j.castSucc) (os : σ)
    (hS : ∀ msg, ¬ S (tr.concat msg)) :
    Pr[ fun x ↦ S x.1.1 |
      (simulateQ impl (prover.processRound j (pure (tr, st)))).run os] ≤ 0 := by
  rw [processRound_of_dir_eq_P_to_V j hj]
  simp only [pure_bind, simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro x _
  simp [simulateQ_pure, StateT.run_pure, hS]

/-- In a challenge round, subsequent prover computation cannot increase the probability
of an event that depends only on the appended challenge and the fixed prefix. -/
theorem prob_state_processRound_challenge_le {σ : Type}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (j : Fin n) (hj : pSpec.dir j = .V_to_P)
    (S : pSpec.Transcript j.succ → Prop)
    (tr : pSpec.Transcript j.castSucc) (st : prover.PrvState j.castSucc) (os : σ) :
    Pr[ fun x ↦ S x.1.1 |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (prover.processRound j (pure (tr, st)))).run os] ≤
      Pr[ fun c ↦ S (tr.concat c) | $ᵗ (pSpec.Challenge ⟨j, hj⟩)] := by
  rw [processRound_of_dir_eq_V_to_P j hj]
  have hget : simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (pSpec.getChallenge ⟨j, hj⟩ : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) =
      (liftM ($ᵗ (pSpec.Challenge ⟨j, hj⟩)) : StateT σ ProbComp _) :=
    simulateQ_addLift_challengeQueryImpl_getChallenge impl ⟨j, hj⟩
  simp only [pure_bind, simulateQ_bind]
  rw [hget]
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
  apply probEvent_bind_le_probEvent (p := fun c ↦ S (tr.concat c))
  intro c _ hc
  apply probEvent_eq_zero_iff.mpr
  intro x hx
  simp only [simulateQ_pure, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact hc

end Prover

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- Extend challenge errors by zero on prover-message rounds. -/
noncomputable def badEventRoundError (ε : pSpec.ChallengeIdx → ℝ≥0∞) (j : Fin n) : ℝ≥0∞ :=
  if h : pSpec.dir j = .V_to_P then ε ⟨j, h⟩ else 0

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Extending by zero does not change the total challenge error. -/
theorem sum_badEventRoundError (ε : pSpec.ChallengeIdx → ℝ≥0∞) :
    ∑ j, badEventRoundError ε j = ∑ i, ε i := by
  classical
  let t := Finset.univ.filter (fun j ↦ pSpec.dir j = .V_to_P)
  have hzero : ∑ j ∈ t, badEventRoundError ε j = ∑ j, badEventRoundError ε j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hd : pSpec.dir j ≠ .V_to_P := by simpa only [t, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
    exact dif_neg hd
  rw [← hzero, Finset.sum_subtype (p := fun j ↦ pSpec.dir j = .V_to_P) t (by simp [t])]
  apply Finset.sum_congr rfl
  intro i _
  exact dif_pos i.property

/-- Conditional fresh-event bounds control the probability of having encountered any
bad event, for every adaptive prover and every initial oracle state. -/
theorem prob_badEventState_runToRound_le {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set StmtIn)
    (bad : (i : pSpec.ChallengeIdx) → StmtIn → Transcript i.val.succ pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ℝ≥0∞)
    (hbound : ∀ stmt ∉ langIn, ∀ i : pSpec.ChallengeIdx,
      ∀ tr : Transcript i.val.castSucc pSpec,
      ¬ badEventState langIn bad i.val.castSucc stmt tr →
      Pr[ fun c ↦ bad i stmt (tr.concat c) | $ᵗ (pSpec.Challenge i)] ≤ ε i)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (hstmt : stmt ∉ langIn) (wit : WitIn)
    (m : Fin (n + 1)) (os : σ) :
    Pr[ fun x ↦ badEventState langIn bad m stmt x.1.1 |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (prover.runToRound m stmt wit)).run os] ≤
      Prover.errorBudget (badEventRoundError ε) m := by
  apply prover.prob_state_runToRound_le
  · simpa only [badEventState_zero] using hstmt
  · intro j tr st os hbefore
    cases hdir : pSpec.dir j with
    | P_to_V =>
      rw [badEventRoundError, dif_neg (by simp [hdir])]
      exact prover.prob_state_processRound_prover_le _ j hdir _ tr st os
        (badEventState_prover_next langIn bad j hdir stmt tr hbefore)
    | V_to_P =>
      rw [badEventRoundError, dif_pos hdir]
      refine (prover.prob_state_processRound_challenge_le impl j hdir _ tr st os).trans ?_
      refine le_trans ?_ (hbound stmt hstmt ⟨j, hdir⟩ tr hbefore)
      apply probEvent_mono''
      intro c hc
      obtain ⟨_, hb⟩ := badEventState_new langIn bad stmt tr c hbefore hc
      exact hb

/-- Any terminal transcript event implying a bad event satisfies the accumulated bound.
This includes the prover's output computation and allows arbitrary private witness types. -/
theorem prob_terminal_event_le_of_badEvents {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set StmtIn)
    (bad : (i : pSpec.ChallengeIdx) → StmtIn → Transcript i.val.succ pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ℝ≥0∞)
    (hbound : ∀ stmt ∉ langIn, ∀ i : pSpec.ChallengeIdx,
      ∀ tr : Transcript i.val.castSucc pSpec,
      ¬ badEventState langIn bad i.val.castSucc stmt tr →
      Pr[ fun c ↦ bad i stmt (tr.concat c) | $ᵗ (pSpec.Challenge i)] ≤ ε i)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (hstmt : stmt ∉ langIn) (wit : WitIn)
    (E : pSpec.FullTranscript → Prop)
    (hterminal : ∀ tr, E tr → badEventState langIn bad (Fin.last n) stmt tr)
    (os : σ) :
    Pr[ fun x ↦ E x.1.1 |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (prover.run stmt wit)).run os] ≤ ∑ i, ε i := by
  rw [Prover.run, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := fun x ↦ badEventState langIn bad (Fin.last n) stmt x.1.1) ?_).trans ?_
  · intro x _ hx
    have he : ¬ E x.1.1 := fun h ↦ hx (hterminal x.1.1 h)
    simp only [simulateQ_bind, StateT.run_bind]
    apply le_antisymm _ zero_le
    apply probEvent_bind_le_of_forall_le
    intro y _
    simp [simulateQ_pure, StateT.run_pure, he]
  · simpa only [Prover.errorBudget_last, sum_badEventRoundError] using
      prob_badEventState_runToRound_le impl langIn bad ε hbound prover stmt hstmt wit
        (Fin.last n) os

end Verifier
