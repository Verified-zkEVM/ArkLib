/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Execution
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Transcript-prefix invariance during execution

Later rounds can change the prover and oracle states, but cannot change an earlier transcript.
These lemmas transport events on prefixes without reinitializing the shared oracle.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- A single round cannot alter the transcript accumulated before that round. -/
theorem processRound_preserves_prefix (j : Fin n)
    (tr : pSpec.Transcript j.castSucc) (st : P.PrvState j.castSucc)
    (x : pSpec.Transcript j.succ × P.PrvState j.succ)
    (hx : x ∈ support (P.processRound j (pure (tr, st)))) :
    Fin.init x.1 = tr := by
  cases hd : pSpec.dir j with
  | V_to_P =>
    rw [processRound_of_dir_eq_V_to_P j hd] at hx
    simp only [pure_bind, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hx
    obtain ⟨c, _, f, _, rfl⟩ := hx
    funext i
    exact Transcript.concat_castSucc c tr i
  | P_to_V =>
    rw [processRound_of_dir_eq_P_to_V j hd] at hx
    simp only [pure_bind, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hx
    obtain ⟨⟨msg, st'⟩, _, rfl⟩ := hx
    funext i
    exact Transcript.concat_castSucc msg tr i

/-- Simulating a round with any total stateful implementation still preserves its prior prefix. -/
theorem simulate_processRound_preserves_prefix {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (j : Fin n) (tr : pSpec.Transcript j.castSucc) (st : P.PrvState j.castSucc)
    (x : pSpec.Transcript j.succ × P.PrvState j.succ)
    (hx : x ∈ support ((simulateQ impl (P.processRound j (pure (tr, st)))).run' s)) :
    Fin.init x.1 = tr :=
  P.processRound_preserves_prefix j tr st x
    (support_simulateQ_run'_subset (n := ProbComp) impl _ s hx)

/-- A predicate on the old prefix is unchanged in probability by a simulated round.
The implementation may mutate its state; this statement does not reset it. -/
theorem simulate_processRound_prefix_event {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (j : Fin n) (tr : pSpec.Transcript j.castSucc) (st : P.PrvState j.castSucc)
    (event : pSpec.Transcript j.castSucc → Prop) :
    Pr{let x ← (simulateQ impl (P.processRound j (pure (tr, st)))).run' s}[
      event (Fin.init x.1)] =
    Pr{let _ ← (simulateQ impl (P.processRound j (pure (tr, st)))).run' s}[event tr] := by
  apply le_antisymm
  · apply _root_.prEvent_mono_of_support
    intro x hx h
    rwa [P.simulate_processRound_preserves_prefix impl s j tr st x hx] at h
  · apply _root_.prEvent_mono_of_support
    intro x hx h
    rwa [P.simulate_processRound_preserves_prefix impl s j tr st x hx]

/-- Processing a round first executes its input computation, retaining the resulting state. -/
theorem processRound_eq_bind_current (j : Fin n)
    (current : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    P.processRound j current = current >>= fun x => P.processRound j (pure x) := by
  simp only [processRound, pure_bind]

/-- Extending an arbitrary running computation by one round preserves every event on its
previous transcript, including when its shared oracle state depends on the prefix. -/
theorem simulate_processRound_prefix_probability {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (j : Fin n)
    (current : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × P.PrvState j.castSucc))
    (event : pSpec.Transcript j.castSucc → Prop) :
    Pr{let x ← (simulateQ impl (P.processRound j current)).run' s}[
      event (Fin.init x.1)] =
    Pr{let x ← (simulateQ impl current).run' s}[event x.1] := by
  rw [P.processRound_eq_bind_current, simulateQ_bind, StateT.run'_bind']
  change Pr{let x ← (simulateQ impl current).run s >>= fun x =>
      (simulateQ impl (P.processRound j (pure x.1))).run' x.2}[event (Fin.init x.1)] = _
  have h := prEvent_bind_congr ((simulateQ impl current).run s)
    (fun x => (simulateQ impl (P.processRound j (pure x.1))).run' x.2)
    (fun x => pure x.1) (fun x => event (Fin.init x.1)) (fun x => event x.1)
  apply Eq.trans (h ?_)
  · simp only [StateT.run'_eq, bind_map_left, bind_assoc, pure_bind]
  clear h
  intro x
  rw [P.simulate_processRound_prefix_event]
  by_cases h : event x.1.1 <;> simp [h]

/-- Observing a transcript prefix after later rounds has exactly its original distribution.
The later execution may perform arbitrary stateful oracle queries. -/
theorem simulate_runToRound_prefix_probability {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (stmt : StmtIn) (wit : WitIn) (r k : Fin (n + 1)) (h : k ≤ r)
    (event : pSpec.Transcript k → Prop) :
    Pr{let x ← (simulateQ impl (P.runToRound r stmt wit)).run' s}[
      event (fun q => x.1 (q.castLE h))] =
    Pr{let x ← (simulateQ impl (P.runToRound k stmt wit)).run' s}[event x.1] := by
  induction r using Fin.induction generalizing k with
  | zero =>
    have hk : k = 0 := Fin.ext (Nat.eq_zero_of_le_zero h)
    subst k
    rfl
  | succ j ih =>
    by_cases hk : k = j.succ
    · subst k
      rfl
    have hk : k ≤ j.castSucc := by
      have := k.isLt
      have := j.isLt
      have hne : k.val ≠ j.val + 1 := fun e => hk (Fin.ext e)
      change k.val ≤ j.val
      change k.val ≤ j.val + 1 at h
      omega
    calc
      _ = Pr{let x ← (simulateQ impl (P.runToRound j.castSucc stmt wit)).run' s}[
          event (fun q => x.1 (q.castLE hk))] := by
        rw [runToRound_succ]
        exact P.simulate_processRound_prefix_probability impl s j _
          (fun tr => event (fun q => tr (q.castLE hk)))
      _ = _ := ih k hk event

/-- Receiving a challenge may change the prover and oracle states, but not the distribution
of the transcript ending with that challenge. -/
theorem simulate_challengeRound_transcript_probability {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (i : pSpec.ChallengeIdx)
    (tr : pSpec.Transcript i.1.castSucc) (st : P.PrvState i.1.castSucc)
    (event : pSpec.Transcript i.1.succ → Prop) :
    Pr{let x ← (simulateQ impl (P.processRound i.1 (pure (tr, st)))).run' s}[event x.1] =
    Pr{let c ← (simulateQ impl (pSpec.getChallenge i)).run' s}[event (tr.concat c)] := by
  rw [processRound_of_dir_eq_V_to_P i.1 i.2]
  simp only [pure_bind, simulateQ_bind, StateT.run'_bind']
  have h := prEvent_bind_congr ((simulateQ impl (pSpec.getChallenge i)).run s)
    (fun x => (simulateQ impl (do
      let f ← P.receiveChallenge i st
      pure (tr.concat x.1, f x.1))).run' x.2)
    (fun x => pure x.1) (fun x => event x.1) (fun c => event (tr.concat c))
  simp only [simulateQ_bind, StateT.run'_bind'] at h
  apply Eq.trans (h ?_)
  · simp only [StateT.run'_eq, bind_map_left, bind_assoc, pure_bind]
  clear h
  intro x
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    map_pure, bind_assoc, pure_bind]
  by_cases he : event (tr.concat x.1) <;> simp [he]

/-- A challenge-round transcript event can be measured immediately after the challenge draw,
without executing the prover's state update. The prefix still executes with its actual state. -/
theorem simulate_processChallenge_prefix_probability {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (i : pSpec.ChallengeIdx)
    (current : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.1.castSucc × P.PrvState i.1.castSucc))
    (event : pSpec.Transcript i.1.succ → Prop) :
    Pr{let x ← (simulateQ impl (P.processRound i.1 current)).run' s}[event x.1] =
    Pr{let tr ← (simulateQ impl (do
      let x ← current
      let c ← pSpec.getChallenge i
      pure (x.1.concat c))).run' s}[event tr] := by
  rw [P.processRound_eq_bind_current]
  simp only [simulateQ_bind, StateT.run'_bind']
  apply prEvent_bind_congr
  intro x
  have h := P.simulate_challengeRound_transcript_probability impl x.2 i x.1.1 x.1.2 event
  simpa only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    bind_map_left, bind_assoc, pure_bind] using h

/-- The marginal of a full interaction at a challenge round is exactly the game that runs
the prefix and draws that challenge. No later prover behavior or state update changes it. -/
theorem simulate_fullRun_challenge_prefix_probability {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (stmt : StmtIn) (wit : WitIn) (i : pSpec.ChallengeIdx)
    (event : pSpec.Transcript i.1.succ → Prop) :
    Pr{let x ← (simulateQ impl (P.runToRound (Fin.last n) stmt wit)).run' s}[
      event (fun q => x.1 (q.castLE (Fin.le_last i.1.succ)))] =
    Pr{let tr ← (simulateQ impl (do
      let x ← P.runToRound i.1.castSucc stmt wit
      let c ← pSpec.getChallenge i
      pure (x.1.concat c))).run' s}[event tr] := by
  rw [P.simulate_runToRound_prefix_probability impl s stmt wit (Fin.last n)
    i.1.succ (Fin.le_last _) event, runToRound_succ]
  exact P.simulate_processChallenge_prefix_probability impl s i _ event

/-- Producing the prover's final output can mutate state, but cannot alter any event on the
completed transcript. -/
theorem simulate_run_transcript_probability {σ : Type}
    (impl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (s : σ) (stmt : StmtIn) (wit : WitIn) (event : pSpec.FullTranscript → Prop) :
    Pr{let x ← (simulateQ impl (P.run stmt wit)).run' s}[event x.1] =
    Pr{let x ← (simulateQ impl (P.runToRound (Fin.last n) stmt wit)).run' s}[
      event x.1] := by
  rw [run]
  simp only [simulateQ_bind, StateT.run'_bind']
  have h := prEvent_bind_congr
    ((simulateQ impl (P.runToRound (Fin.last n) stmt wit)).run s)
    (fun x => (simulateQ impl (do
      let out ← P.output x.1.2
      pure (x.1.1, out))).run' x.2)
    (fun x => pure x.1) (fun x => event x.1) (fun x => event x.1)
  simp only [simulateQ_bind, StateT.run'_bind'] at h
  apply Eq.trans (h ?_)
  · simp only [StateT.run'_eq, bind_map_left, bind_assoc, pure_bind]
  clear h
  intro x
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    map_pure, bind_assoc, pure_bind]
  by_cases he : event x.1.1 <;> simp [he]

end Prover
