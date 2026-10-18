/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.RbrGame
public import ArkLib.OracleReduction.Execution

/-! # State independence for stateless and empty ambient oracles

Stateless ambient implementations and fresh challenge queries preserve the shared state.
The empty ambient specification is a special case; the general results also allow nonempty
specifications with randomized, state-independent answers.
-/

@[expose] public section

open OracleComp OracleSpec

namespace ProtocolSpec

/-- A stateless ambient implementation remains stateless when fresh challenges are added.
Unlike the empty-oracle specialization, this permits arbitrary ambient query specifications. -/
theorem simulateQ_statelessAmbient
    {ι σ α : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
    simulateQ ((impl.liftTarget (StateT σ ProbComp)).addLift challengeQueryImpl :
      QueryImpl _ (StateT σ ProbComp)) oa =
      liftM (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp) oa) := by
  have h : ((impl.liftTarget (StateT σ ProbComp)).addLift challengeQueryImpl :
      QueryImpl _ (StateT σ ProbComp)) =
      (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp).liftTarget
        (StateT σ ProbComp) := by
    funext q
    rcases q with q | q <;> rfl
  rw [h, simulateQ_liftTarget]

/-- Stateless ambient queries and challenges have a result distribution independent of state. -/
theorem simulateQ_statelessAmbient_run'
    {ι σ α : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) (state : σ) :
    (simulateQ ((impl.liftTarget (StateT σ ProbComp)).addLift challengeQueryImpl :
      QueryImpl _ (StateT σ ProbComp))
      oa).run' state = simulateQ (impl.addLift challengeQueryImpl) oa := by
  rw [simulateQ_statelessAmbient]
  simp [StateT.run'_eq]

/-- Initializing unused state does not affect event probabilities, even with nonempty
ambient oracles, provided their implementation is stateless. -/
theorem prEvent_statelessAmbient
    {ι σ α : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) (event : α → Prop) :
    Pr{let x ← do
      (simulateQ ((impl.liftTarget (StateT σ ProbComp)).addLift challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp)) oa).run' (← init)}[event x] =
      Pr{let x ←
        simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp) oa}[event x] := by
  let : MeasurableSpace σ := ⊤
  simp only [simulateQ_statelessAmbient_run']
  simp only [_root_.evalDist_bind_const, evalDist_apply_univ_eq_one, one_smul]

/-- A stateless ambient implementation reduces the logged RBR game to a prefix run followed
by a fresh challenge. Ambient queries need not be absent or deterministic. -/
theorem prEvent_rbrGame_statelessAmbient
    {ι σ : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {StmtIn WitIn StmtOut WitOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : pSpec.ChallengeIdx)
    (event : pSpec.Transcript i.1.castSucc → pSpec.Challenge i → Prop) :
    Pr{let ⟨tr, challenge, _log⟩ ← do
      (simulateQ ((impl.liftTarget (StateT σ ProbComp)).addLift challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp)) (do
        let ⟨⟨tr, _⟩, log⟩ ← P.runWithLogToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) _
        return (tr, challenge, log))).run' (← init)}[event tr challenge] =
      Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
           (P.runToRound i.1.castSucc stmt wit)
         let challenge ← $ᵗ (pSpec.Challenge i)}[event x.1 challenge] := by
  rw [prEvent_statelessAmbient]
  rw [← P.runWithLogToRound_discard_log_eq_runToRound i.1.castSucc stmt wit]
  have hc : simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
      (liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)) =
        $ᵗ (pSpec.Challenge i) := by
    rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right]
    exact (simulateQ_spec_query (challengeQueryImpl.liftTarget ProbComp) ⟨i, ()⟩).trans rfl
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_map, bind_map_left,
    bind_assoc, pure_bind]
  exact congrArg (fun draw : ProbComp (pSpec.Challenge i) =>
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runWithLogToRound i.1.castSucc stmt wit)
       let challenge ← draw}[event x.1.1 challenge]) hc

/-- Stateless ambient simulation cannot introduce unsupported program results. -/
theorem support_simulateQ_statelessAmbient_subset
    {ι α : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
    support (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp) oa) ⊆
      support oa := by
  rw [← simulateQ_statelessAmbient_run' impl oa ()]
  exact support_simulateQ_run'_subset
    ((impl.liftTarget (StateT Unit ProbComp)).addLift challengeQueryImpl) oa ()

variable {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)] {σ α : Type}

/-- Stateless simulation of the challenge-only execution of an empty-ambient protocol. -/
def emptyAmbientChallengeImpl : QueryImpl ([]ₒ + [pSpec.Challenge]ₒ) ProbComp :=
  QueryImpl.addLift (fun q => isEmptyElim q : QueryImpl []ₒ ProbComp) challengeQueryImpl

/-- No empty-ambient execution can read or modify the shared oracle state. -/
theorem simulateQ_emptyAmbient
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oa : OracleComp ([]ₒ + [pSpec.Challenge]ₒ) α) :
    simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) oa =
      liftM (simulateQ emptyAmbientChallengeImpl oa) := by
  have h : (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) =
      (emptyAmbientChallengeImpl (pSpec := pSpec)).liftTarget (StateT σ ProbComp) := by
    funext q
    rcases q with q | q
    · exact isEmptyElim q
    · rfl
  rw [h, simulateQ_liftTarget]

/-- The result distribution is independent of the initial shared state. -/
theorem simulateQ_emptyAmbient_run'
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oa : OracleComp ([]ₒ + [pSpec.Challenge]ₒ) α) (state : σ) :
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      oa).run' state = simulateQ emptyAmbientChallengeImpl oa := by
  rw [simulateQ_emptyAmbient]
  simp [StateT.run'_eq]

/-- Averaging over an unused initial state does not change any event probability. -/
theorem prEvent_emptyAmbient
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oa : OracleComp ([]ₒ + [pSpec.Challenge]ₒ) α) (event : α → Prop) :
    Pr{let x ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' (← init)}[event x] =
      Pr{let x ← simulateQ emptyAmbientChallengeImpl oa}[event x] := by
  let : MeasurableSpace σ := ⊤
  simp only [simulateQ_emptyAmbient_run']
  simp only [_root_.evalDist_bind_const, evalDist_apply_univ_eq_one, one_smul]

/-- The logged, stateful RBR game reduces to a stateless prefix run and fresh challenge.
Only the unused query log and shared state are removed; the prover's prefix distribution remains. -/
theorem prEvent_rbrGame_emptyAmbient
    {StmtIn WitIn StmtOut WitOut : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (P : Prover []ₒ StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : pSpec.ChallengeIdx)
    (event : pSpec.Transcript i.1.castSucc → pSpec.Challenge i → Prop) :
    Pr{let ⟨tr, challenge, _log⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) (do
        let ⟨⟨tr, _⟩, log⟩ ← P.runWithLogToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) _
        return (tr, challenge, log))).run' (← init)}[event tr challenge] =
      Pr{let x ← simulateQ emptyAmbientChallengeImpl (P.runToRound i.1.castSucc stmt wit)
         let challenge ← $ᵗ (pSpec.Challenge i)}[event x.1 challenge] := by
  rw [prEvent_emptyAmbient]
  rw [← P.runWithLogToRound_discard_log_eq_runToRound i.1.castSucc stmt wit]
  have hc : simulateQ (emptyAmbientChallengeImpl (pSpec := pSpec))
      (liftComp (pSpec.getChallenge i) ([]ₒ + [pSpec.Challenge]ₒ)) =
        $ᵗ (pSpec.Challenge i) := by
    rw [emptyAmbientChallengeImpl, QueryImpl.addLift_def,
      QueryImpl.simulateQ_add_liftComp_right]
    exact (simulateQ_spec_query (challengeQueryImpl.liftTarget ProbComp) ⟨i, ()⟩).trans rfl
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_map, bind_map_left,
    bind_assoc, pure_bind]
  exact congrArg (fun draw : ProbComp (pSpec.Challenge i) =>
    Pr{let x ← simulateQ emptyAmbientChallengeImpl (P.runWithLogToRound i.1.castSucc stmt wit)
       let challenge ← draw}[event x.1.1 challenge]) hc

/-- A supported challenge-only simulated result is supported by the original program. -/
theorem support_simulateQ_emptyAmbient_subset
    (oa : OracleComp ([]ₒ + [pSpec.Challenge]ₒ) α) :
    support (simulateQ emptyAmbientChallengeImpl oa) ⊆ support oa := by
  let impl : QueryImpl []ₒ (StateT Unit ProbComp) := fun q => isEmptyElim q
  rw [← simulateQ_emptyAmbient_run' impl oa ()]
  exact support_simulateQ_run'_subset (impl.addLift challengeQueryImpl) oa ()

end ProtocolSpec
