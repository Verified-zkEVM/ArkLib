/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Interpreted

/-! # Execution under message interpretation

Interpretation changes the message representation and retains every prover slot, public draw,
and terminal private output.
-/

@[expose] public section

namespace Sumcheck.Core.Interpreted
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R M N : Type} {evaluate : M → R → R} {evaluateN : N → R → R}

/-- Interpret the messages of a complete transcript, preserving its challenges. -/
def mapTranscript (interpret : M → N) : (k : ℕ) →
    PathAlong oracleSig (protocol R M evaluate k) →
    PathAlong oracleSig (protocol R N evaluateN k)
  | 0, _ => PUnit.unit
  | k + 1, ⟨msg, r, rest⟩ => ⟨interpret msg, r, mapTranscript interpret k rest⟩

/-- Equal message evaluation preserves every chronological transcript verdict. -/
theorem verdict_transport {State : ℕ → Type} {T : Type} (checks : RoundChecks R State)
    (finish : State 0 → T) (interpret : M → N)
    (heval : ∀ msg r, evaluateN (interpret msg) r = evaluate msg r) :
    ∀ (k : ℕ) (st : State k) (tr : PathAlong oracleSig (protocol R M evaluate k)),
    verdict evaluateN checks finish k st (mapTranscript interpret k tr) =
      verdict evaluate checks finish k st tr := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    rintro st ⟨msg, r, rest⟩
    have hh : roundVerdict evaluateN (checks k) st (interpret msg) r =
        roundVerdict evaluate (checks k) st msg r := by
      unfold roundVerdict
      congr 1
      exact funext fun x => heval msg x
    simp only [verdict, mapTranscript, message, challenge, tail, hh]
    cases roundVerdict evaluate (checks k) st msg r with
    | none => rfl
    | some mid => exact ih mid rest

/-- Interpret every message slot, challenge-response slot and terminal computation. -/
def transportProver {m : Type → Type} [Monad m] {Out : Type} (interpret : M → N) :
    (k : ℕ) → Focal oracleSig m (protocol R M evaluate k) (fun _ => Out) →
      Focal oracleSig m (protocol R N evaluateN k) (fun _ => Out)
  | 0, prover => prover
  | k + 1, prover => do
      let chosen ← (prover : m ((_msg : M) × m (R →
        Focal oracleSig m (protocol R M evaluate k) (fun _ => Out))))
      let response : m (R → Focal oracleSig m (protocol R N evaluateN k) (fun _ => Out)) := do
        let respond ← chosen.2
        pure fun r => transportProver interpret k (respond r)
      pure (⟨interpret chosen.1, response⟩ : ((_msg : N) ×
        m (R → Focal oracleSig m (protocol R N evaluateN k) (fun _ => Out))))

/-- Interpreting a fold of pure rounds interprets each message it sends and keeps its
transitions and output. -/
theorem transportProver_foldRounds {m : Type → Type} [Monad m] [LawfulMonad m]
    {State : ℕ → Type} {Out : Type} (interpret : M → N)
    (msg : (k : ℕ) → State (k + 1) → M)
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) :
    (k : ℕ) → (st : State k) →
    transportProver (evaluateN := evaluateN) interpret k
        (foldRounds (m := m) (eval := evaluate) msg next finish k st) =
      foldRounds (fun k st => interpret (msg k st)) next finish k st
  | 0, _ => rfl
  | k + 1, st => by
    unfold transportProver
    erw [LawfulMonad.pure_bind]
    dsimp only
    erw [LawfulMonad.pure_bind]
    exact congrArg (pure (f := m)) (congrArg (Sigma.mk (interpret (msg k st)))
      (congrArg (pure (f := m)) (funext fun chal =>
        transportProver_foldRounds interpret msg next finish k _)))

/-- Ambient interpretation maps the message slot and the challenge-response slot separately. -/
theorem simulate_step {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] (impl : QueryImpl ambient m) {Out : Type} (k : ℕ)
    (prover : Prover oracleSig ambient (protocol R M evaluate (k + 1)) (fun _ => Out)) :
    Prover.simulate impl prover =
      (fun (chosen : ((_msg : M) × OracleComp ambient (R →
          Focal oracleSig (OracleComp ambient) (protocol R M evaluate k) (fun _ => Out)))) =>
        (⟨chosen.1, (fun respond r => Prover.simulate impl (respond r)) <$>
          simulateQ impl chosen.2⟩ : ((_msg : M) × m (R →
            Focal oracleSig m (protocol R M evaluate k) (fun _ => Out))))) <$>
        simulateQ impl prover := rfl

/-- Interpreting message carriers commutes with interpreting every ambient prover slot. -/
theorem simulate_transport {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] {Out : Type}
    (impl : QueryImpl ambient m) (interpret : M → N) (k : ℕ)
    (prover : Prover oracleSig ambient (protocol R M evaluate k) (fun _ => Out)) :
    Prover.simulate impl (transportProver (evaluateN := evaluateN) interpret k prover) =
      transportProver interpret k (Prover.simulate impl prover) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [simulate_step, simulate_step]
    dsimp only [transportProver]
    erw [simulateQ_bind]
    rw [_root_.map_bind]
    erw [bind_map_left]
    refine bind_congr (m := m) (fun (chosen : ((_msg : M) × OracleComp ambient (R →
      Focal oracleSig (OracleComp ambient) (protocol R M evaluate k) (fun _ => Out)))) => ?_)
    rcases chosen with ⟨msg, response⟩
    dsimp only
    erw [simulateQ_pure]
    rw [LawfulApplicative.map_pure]
    refine congrArg pure (Sigma.ext rfl (heq_of_eq ?_))
    erw [simulateQ_bind]
    rw [_root_.map_bind]
    erw [bind_map_left]
    refine bind_congr (m := m) fun respond => ?_
    erw [simulateQ_pure]
    rw [LawfulApplicative.map_pure]
    exact congrArg pure (funext fun r => ih (respond r))

/-- Supply the same explicit draw at every public challenge node. -/
def draw {m : Type → Type} (next : m R) : (k : ℕ) →
    QueryImpl (challengeSpec oracleSig (protocol R M evaluate k)) m
  | 0, ⟨node, _⟩ => nomatch node
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => next
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, node⟩⟩, h⟩ => draw next k ⟨node, h⟩

/-- Actual execution of one more round retains both prover slots before drawing. -/
theorem run_step {m : Type → Type} [Monad m] [LawfulMonad m] {Out : Type}
    (next : m R) (k : ℕ)
    (prover : Focal oracleSig m (protocol R M evaluate (k + 1)) (fun _ => Out)) :
    Interaction.TwoParty.Lens.run _ prover (sampler oracleSig _ (draw next (k + 1))) = (do
      let ⟨msg, response⟩ ← (prover : m ((_msg : M) × m (R →
        Focal oracleSig m (protocol R M evaluate k) (fun _ => Out))))
      let respond ← response
      let r ← next
      let ⟨rest, out, u⟩ ← Interaction.TwoParty.Lens.run _ (respond r)
        (sampler oracleSig _ (draw next k))
      pure ⟨⟨msg, r, rest⟩, out, u⟩) := by
  rw [← bind_pure (Interaction.TwoParty.Lens.run _ prover
    (sampler oracleSig _ (draw next (k + 1))))]
  erw [run_sampler_sender rfl]
  refine bind_congr fun chosen => ?_
  erw [run_sampler_receiver rfl]
  rfl

/-- Actual prover-sampler execution commutes with representation interpretation, retaining
arbitrary effects and private outputs. -/
theorem run_transport {m : Type → Type} [Monad m] [LawfulMonad m] {Out : Type}
    (next : m R) (interpret : M → N) : ∀ (k : ℕ)
    (prover : Focal oracleSig m (protocol R M evaluate k) (fun _ => Out)),
    Interaction.TwoParty.Lens.run _ (transportProver (evaluateN := evaluateN) interpret k prover)
      (sampler oracleSig _ (draw next k)) =
      (fun result => (⟨mapTranscript interpret k result.1, result.2.1, result.2.2⟩ :
        ((_tr : PathAlong oracleSig (protocol R N evaluateN k)) × Out × PUnit))) <$>
      Interaction.TwoParty.Lens.run _ prover (sampler oracleSig _ (draw next k)) := by
  intro k
  induction k with
  | zero =>
    intro prover
    simp [protocol, transportProver, sampler, samplerEnd, PureEnd.toStrategy,
      PureEnd.mapOutput, run_done, mapTranscript]
  | succ k ih =>
    intro prover
    rw [run_step, run_step]
    simp only [transportProver, LawfulMonad.bind_assoc, _root_.map_bind]
    refine bind_congr fun chosen => ?_
    rcases chosen with ⟨msg, response⟩
    dsimp only
    erw [LawfulMonad.pure_bind]
    dsimp only
    erw [LawfulMonad.bind_assoc]
    rw [_root_.map_bind]
    refine bind_congr (m := m) fun respond => ?_
    erw [LawfulMonad.pure_bind]
    simp only [_root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr fun r => ?_
    rw [ih]
    simp only [LawfulMonad.bind_pure_comp, Functor.map_map]
    rfl

/-- Close an actual interaction-layer prover-sampler execution by its final resource verdict.
The original input may be arbitrary behavior; no polynomial realization is required by this
executor. -/
def execute {m : Type → Type} [Monad m] {Out Data : Type} {State : ℕ → Type} {T : Type}
    (next : m R) (checks : RoundChecks R State) (finish : State 0 → T) (k : ℕ)
    (st : State k) (data : Data)
    (prover : Focal oracleSig m (protocol R M evaluate k) (fun _ => Out)) :
    m (Out × Option (T × Data)) :=
  (fun result => (result.2.1, (verdict evaluate checks finish k st result.1).map
    (fun t => (t, data)))) <$>
      Interaction.TwoParty.Lens.run _ prover (sampler oracleSig _ (draw next k))

/-- The closed executor is exactly the actual oracle verifier run under the supplied ambient
and public challenge implementations. -/
theorem execute_eq_verifier {ι I : Type} (ambient : OracleSpec ι) {A : I → Type}
    (inputs : OracleFamily I A) {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (next : m R) {Out : Type} {State : ℕ → Type} {T : Type}
    (checks : RoundChecks R State) (finish : State 0 → T) (k : ℕ)
    (st : State k) (data : ∀ i, A i)
    (prover : Prover oracleSig ambient (protocol R M evaluate k) (fun _ => Out)) :
    (fun result => (result.2.1, result.2.2)) <$>
      simulateQ (QueryImpl.addLift impl (draw next k))
        ((verifier ambient inputs checks finish k).run st data prover) =
      execute next checks finish k st data (Prover.simulate impl prover) := by
  rw [verifier_run]
  simp only [simulateQ_bind, simulateQ_pure, _root_.map_bind, LawfulApplicative.map_pure]
  rw [simulateQ_run_simulate_sampler]
  have ha : (fun q => simulateQ (QueryImpl.addLift impl (draw (evaluate := evaluate) next k))
      (liftM ((ambient + challengeSpec oracleSig (protocol R M evaluate k)).query (.inl q)))) =
      impl := funext fun q => QueryImpl.simulateQ_add_query_left _ _ q
  have hc : (fun c => simulateQ (QueryImpl.addLift impl (draw (evaluate := evaluate) next k))
      (liftM ((ambient + challengeSpec oracleSig (protocol R M evaluate k)).query (.inr c)))) =
      draw next k := funext fun c => QueryImpl.simulateQ_add_query_right _ _ c
  rw [ha, hc]
  unfold execute
  rw [map_eq_bind_pure_comp]
  rfl

/-- Closed actual execution commutes with evaluation-preserving representation interpretation,
retaining all prover effects, terminal outputs and the original oracle behavior. -/
theorem execute_transport {m : Type → Type} [Monad m] [LawfulMonad m]
    {Out Data : Type} {State : ℕ → Type} {T : Type} (next : m R)
    (checks : RoundChecks R State) (finish : State 0 → T) (interpret : M → N)
    (heval : ∀ msg r, evaluateN (interpret msg) r = evaluate msg r)
    (k : ℕ) (st : State k) (data : Data)
    (prover : Focal oracleSig m (protocol R M evaluate k) (fun _ => Out)) :
    execute next checks finish k st data
      (transportProver (evaluateN := evaluateN) interpret k prover) =
      execute next checks finish k st data prover := by
  unfold execute
  rw [run_transport, Functor.map_map]
  congr 1
  funext result
  dsimp only [Function.comp_apply]
  rw [verdict_transport checks finish interpret heval]

/-- Equal retained input behaviors give equal closed executions for the same arbitrary prover.
The executor never queries that retained behavior to decide acceptance. -/
theorem execute_input_eq {m : Type → Type} [Monad m] {Out Data : Type} {State : ℕ → Type}
    {T : Type} (next : m R) (checks : RoundChecks R State) (finish : State 0 → T)
    (k : ℕ) (st : State k) (data data' : Data) (h : data = data')
    (prover : Focal oracleSig m (protocol R M evaluate k) (fun _ => Out)) :
    execute next checks finish k st data prover = execute next checks finish k st data' prover := by
  rw [h]


end Sumcheck.Core.Interpreted
