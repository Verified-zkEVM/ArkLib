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

* `transportFocal` interprets the messages of a prover and maps its dependent output.
  `transportProver` is its instance at a constant output type.
* `transportDraw` moves a challenge implementation between message carriers. The challenge nodes
  do not depend on the carrier, and every challenge is a ring element.
* `simulate_transportFocal`, `run_transportFocal` and `transportFocal_foldRounds` state how the
  interpretation commutes with ambient simulation, with the prover-sampler run and with folds of
  pure rounds.
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

/-- Mapping by the identity keeps a transcript. -/
theorem mapTranscript_id : (k : ℕ) → (tr : PathAlong oracleSig (protocol R M evaluate k)) →
    mapTranscript (evaluateN := evaluate) id k tr = tr
  | 0, _ => rfl
  | k + 1, ⟨x, ⟨c, tr⟩⟩ => by
    change (⟨x, ⟨c, mapTranscript (evaluateN := evaluate) id k tr⟩⟩ :
      PathAlong oracleSig (protocol R M evaluate (k + 1))) = ⟨x, ⟨c, tr⟩⟩
    rw [mapTranscript_id k tr]

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

/-! ## Challenge implementations at another carrier -/

/-- Supply the same explicit draw at every public challenge node. -/
def draw {m : Type → Type} (next : m R) : (k : ℕ) →
    QueryImpl (challengeSpec oracleSig (protocol R M evaluate k)) m
  | 0, ⟨node, _⟩ => nomatch node
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => next
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, node⟩⟩, h⟩ => draw next k ⟨node, h⟩

/-- Move a challenge implementation between message carriers. The challenge nodes do not depend
on the carrier, and every challenge is a ring element. -/
def transportDraw {m : Type → Type} : (k : ℕ) →
    ((c : ChallengeNode oracleSig (protocol R N evaluateN k)) →
      m (challengeSpec oracleSig _ c)) →
    (c : ChallengeNode oracleSig (protocol R M evaluate k)) → m (challengeSpec oracleSig _ c)
  | 0, _, ⟨x, _⟩ => nomatch x
  | _ + 1, _, ⟨.inl _, h⟩ => nomatch h
  | k + 1, d, ⟨.inr ⟨_, .inl _⟩, _⟩ => d (headNode k)
  | k + 1, d, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => transportDraw k (tailDraw d) ⟨c, h⟩

/-- Transporting a challenge implementation there and back returns it. -/
theorem transportDraw_transportDraw_apply {m : Type → Type} : (k : ℕ) →
    (d : (c : ChallengeNode oracleSig (protocol R M evaluate k)) →
      m (challengeSpec oracleSig _ c)) →
    (c : ChallengeNode oracleSig (protocol R M evaluate k)) →
    transportDraw (N := N) (evaluateN := evaluateN) k (transportDraw k d) c = d c
  | 0, _, ⟨x, _⟩ => nomatch x
  | _ + 1, _, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, _, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, d, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ =>
    transportDraw_transportDraw_apply k (tailDraw d) ⟨c, h⟩

/-- Transporting a challenge implementation there and back returns it. -/
theorem transportDraw_transportDraw {m : Type → Type} (k : ℕ)
    (d : (c : ChallengeNode oracleSig (protocol R M evaluate k)) →
      m (challengeSpec oracleSig _ c)) :
    transportDraw (N := N) (evaluateN := evaluateN) k (transportDraw k d) = d :=
  funext (transportDraw_transportDraw_apply k d)

/-- Transport commutes with a natural map applied to every draw. -/
theorem transportDraw_natural {m n : Type → Type} (φ : (α : Type) → m α → n α) :
    (k : ℕ) →
    (d : (c : ChallengeNode oracleSig (protocol R N evaluateN k)) →
      m (challengeSpec oracleSig (protocol R N evaluateN k) c)) →
    (c : ChallengeNode oracleSig (protocol R M evaluate k)) →
    transportDraw k (fun c => φ _ (d c)) c = φ _ (transportDraw k d c)
  | 0, _, ⟨x, _⟩ => nomatch x
  | _ + 1, _, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, _, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, d, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => by
    have e := transportDraw_natural φ k (tailDraw d) ⟨c, h⟩
    exact e

/-- Transporting the same explicit draw at every node gives that draw. -/
theorem transportDraw_draw_apply {m : Type → Type} (next : m R) : (k : ℕ) →
    (c : ChallengeNode oracleSig (protocol R M evaluate k)) →
    transportDraw k (draw (M := N) (evaluate := evaluateN) next k) c = draw next k c
  | 0, ⟨x, _⟩ => nomatch x
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => transportDraw_draw_apply next k ⟨c, h⟩

/-- Transporting the same explicit draw at every node gives that draw. -/
theorem transportDraw_draw {m : Type → Type} (next : m R) (k : ℕ) :
    transportDraw k (draw (M := N) (evaluate := evaluateN) next k) =
      draw (M := M) (evaluate := evaluate) next k :=
  funext (transportDraw_draw_apply next k)

/-! ## Provers at another carrier -/

/-- Interpret a prover at another message carrier: every sent message is mapped by `interpret`,
every slot keeps its effects, and the dependent output is mapped by `g`. -/
def transportFocal {m : Type → Type} [Functor m] (interpret : M → N) : (k : ℕ) →
    {Out : PathAlong oracleSig (protocol R M evaluate k) → Type} →
    {Out' : PathAlong oracleSig (protocol R N evaluateN k) → Type} →
    (∀ tr, Out tr → Out' (mapTranscript interpret k tr)) →
    Focal oracleSig m (protocol R M evaluate k) Out →
    Focal oracleSig m (protocol R N evaluateN k) Out'
  | 0, _, _, g, prover => (g ⟨⟩ <$> prover : m _)
  | k + 1, _, _, g, prover => (fun r => ⟨interpret r.1, (fun h chal => transportFocal interpret k
      (fun tail => g ⟨r.1, ⟨chal, tail⟩⟩) (h chal)) <$> r.2⟩) <$> prover

/-- Interpret every message slot and challenge-response slot of a prover with a constant output
type, keeping that output. -/
abbrev transportProver {m : Type → Type} [Functor m] {Out : Type} (interpret : M → N) (k : ℕ)
    (prover : Focal oracleSig m (protocol R M evaluate k) (fun _ => Out)) :
    Focal oracleSig m (protocol R N evaluateN k) (fun _ => Out) :=
  transportFocal interpret k (fun _ => id) prover

/-- Ambient interpretation maps the message slot and the challenge-response slot separately. -/
theorem simulate_step {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] (impl : QueryImpl ambient m) (k : ℕ)
    {Out : PathAlong oracleSig (protocol R M evaluate (k + 1)) → Type}
    (prover : Prover oracleSig ambient (protocol R M evaluate (k + 1)) Out) :
    Prover.simulate impl prover =
      ((fun r => ⟨r.1, (fun h chal => Prover.simulate impl (h chal)) <$>
        simulateQ impl r.2⟩) <$> simulateQ impl prover :
        m ((x : M) × m ((chal : R) →
          Focal oracleSig m (protocol R M evaluate k)
            (fun tail => Out ⟨x, ⟨chal, tail⟩⟩)))) :=
  rfl

/-- Interpreting message carriers commutes with interpreting every ambient prover slot. -/
theorem simulate_transportFocal {ι : Type} {ambient : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl ambient m) (interpret : M → N) : (k : ℕ) →
    {Out : PathAlong oracleSig (protocol R M evaluate k) → Type} →
    {Out' : PathAlong oracleSig (protocol R N evaluateN k) → Type} →
    (g : ∀ tr, Out tr → Out' (mapTranscript interpret k tr)) →
    (prover : Prover oracleSig ambient (protocol R M evaluate k) Out) →
    Prover.simulate impl (transportFocal interpret k g prover) =
      transportFocal interpret k g (Prover.simulate impl prover)
  | 0, _, _, g, prover => by
    change simulateQ impl (g ⟨⟩ <$> prover) = g ⟨⟩ <$> simulateQ impl prover
    rw [simulateQ_map]
  | k + 1, _, _, g, prover => by
    rw [simulate_step, simulate_step]
    change _ <$> simulateQ impl (_ <$> prover) = _ <$> (_ <$> simulateQ impl prover)
    erw [simulateQ_map, Functor.map_map, Functor.map_map]
    refine congrArg (· <$> simulateQ impl prover) (funext fun r => ?_)
    refine congrArg (Sigma.mk (interpret r.1)) ?_
    change _ <$> simulateQ impl (_ <$> r.2) = _ <$> (_ <$> simulateQ impl r.2)
    erw [simulateQ_map, Functor.map_map, Functor.map_map]
    exact congrArg (· <$> simulateQ impl r.2) (funext fun h => funext fun chal =>
      simulate_transportFocal impl interpret k _ (h chal))

/-- Running an interpreted prover against the sampler runs the original prover against the
transported sampler, and maps its transcript and output. -/
theorem run_transportFocal {m : Type → Type} [Monad m] [LawfulMonad m] (interpret : M → N) :
    (k : ℕ) → {Out : PathAlong oracleSig (protocol R M evaluate k) → Type} →
    {Out' : PathAlong oracleSig (protocol R N evaluateN k) → Type} →
    (g : ∀ tr, Out tr → Out' (mapTranscript interpret k tr)) →
    (prover : Focal oracleSig m (protocol R M evaluate k) Out) →
    (d : (c : ChallengeNode oracleSig (protocol R N evaluateN k)) →
      m (challengeSpec oracleSig _ c)) →
    Interaction.TwoParty.Lens.run (protocol R N evaluateN k) (transportFocal interpret k g prover)
        (sampler oracleSig (protocol R N evaluateN k) d) =
      (fun x => ⟨mapTranscript interpret k x.1, g x.1 x.2.1, x.2.2⟩) <$>
        Interaction.TwoParty.Lens.run (protocol R M evaluate k) prover
          (sampler oracleSig (protocol R M evaluate k) (transportDraw k d))
  | 0, Out, Out', g, prover, d => by
    refine (run_done (l := oracleSig) (OutP := Out') (OutC := fun _ => PUnit)
      (g ⟨⟩ <$> prover) (pure ⟨⟩)).trans ?_
    refine Eq.trans ?_ (congrArg (_ <$> ·) (run_done (l := oracleSig) (OutP := Out)
      (OutC := fun _ => PUnit) prover (pure ⟨⟩))).symm
    simp only [bind_map_left, _root_.map_bind, LawfulMonad.pure_bind,
      LawfulApplicative.map_pure]
    rfl
  | k + 1, Out, Out', g, prover, d => by
    rw [run_succ, run_succ]
    dsimp only [transportFocal]
    erw [bind_map_left]
    simp only [_root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr (m := m) fun r => ?_
    erw [bind_map_left]
    refine bind_congr (m := m) fun h => bind_congr (m := m) fun chal => ?_
    rw [run_transportFocal interpret k
      (Out' := fun tail => Out' ⟨interpret r.1, ⟨chal, tail⟩⟩)
      (fun tail => g ⟨r.1, ⟨chal, tail⟩⟩) (h chal) (tailDraw d)]
    simp only [bind_map_left]
    rfl

/-- Actual prover-sampler execution commutes with representation interpretation, retaining
arbitrary effects and private outputs. -/
theorem run_transport {m : Type → Type} [Monad m] [LawfulMonad m] {Out : Type}
    (next : m R) (interpret : M → N) (k : ℕ)
    (prover : Focal oracleSig m (protocol R M evaluate k) (fun _ => Out)) :
    Interaction.TwoParty.Lens.run _ (transportProver (evaluateN := evaluateN) interpret k prover)
      (sampler oracleSig _ (draw next k)) =
      (fun result => (⟨mapTranscript interpret k result.1, result.2.1, result.2.2⟩ :
        ((_tr : PathAlong oracleSig (protocol R N evaluateN k)) × Out × PUnit))) <$>
      Interaction.TwoParty.Lens.run _ prover (sampler oracleSig _ (draw next k)) := by
  rw [run_transportFocal, transportDraw_draw]
  rfl

/-- Interpreting a fold of pure rounds maps its messages and its output. -/
theorem transportFocal_foldRounds {m : Type → Type} [Monad m] [LawfulMonad m]
    {State : ℕ → Type} {Out Out' : Type} (interpret : M → N) (o : Out → Out')
    (msg : (k : ℕ) → State (k + 1) → M)
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) :
    (k : ℕ) → (st : State k) →
    transportFocal (evaluateN := evaluateN) interpret k (fun _ => o)
        (foldRounds (m := m) (eval := evaluate) msg next finish k st) =
      foldRounds (fun k st => interpret (msg k st)) next (fun st => o (finish st)) k st
  | 0, st => LawfulApplicative.map_pure (f := m) o (finish st)
  | k + 1, st => by
    refine (LawfulApplicative.map_pure _ _).trans ?_
    refine congrArg (pure (f := m)) (congrArg (Sigma.mk (interpret (msg k st))) ?_)
    refine (LawfulApplicative.map_pure _ _).trans ?_
    exact congrArg (pure (f := m)) (funext fun chal =>
      transportFocal_foldRounds interpret o msg next finish k _)

/-- Interpreting messages commutes with packing dependent private outputs into a fixed type. -/
theorem transportProver_transportFocal {m : Type → Type} [Monad m] [LawfulMonad m]
    {O : Type} (interpret : M → N) (k : ℕ)
    {Out : PathAlong oracleSig (protocol R M evaluate k) → Type}
    (g : ∀ tr, Out tr → O) (prover : Focal oracleSig m (protocol R M evaluate k) Out) :
    transportProver (evaluateN := evaluateN) interpret k
      (transportFocal (evaluateN := evaluate) id k g prover) =
      transportFocal interpret k g prover := by
  induction k with
  | zero => exact id_map _
  | succ k ih =>
    dsimp only [transportProver, transportFocal]
    erw [Functor.map_map]
    congr 1
    funext r
    refine Sigma.ext rfl (heq_of_eq ?_)
    dsimp only [Function.comp_apply]
    erw [Functor.map_map]
    congr 1
    funext h chal
    exact ih (fun tail => g ⟨r.1, ⟨chal, tail⟩⟩) (h chal)

/-- Close an actual prover-sampler execution by its final resource verdict. The original input
may be arbitrary behavior; no polynomial realization is required by this executor. -/
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
