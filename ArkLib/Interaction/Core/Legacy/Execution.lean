/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.OracleReduction
public import ArkLib.Interaction.Core.Execution
public import ArkLib.Interaction.Core.Security.Completeness
public import ArkLib.OracleReduction.Execution

/-!
# Execution of embedded legacy reductions

This file runs interaction-layer parties on the tree of a legacy protocol in the legacy ambient
monad `OracleComp (oSpec + [pSpec.Challenge]ₒ)`: the prover's shared-oracle queries go to the
left summand, and the sampler draws each challenge from the legacy challenge oracle.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Send shared-oracle queries to the left summand of the legacy ambient spec. -/
def liftShared (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n) :
    QueryImpl oSpec (OracleComp (oSpec + [pSpec.Challenge]ₒ)) :=
  fun q => liftM ((oSpec + [pSpec.Challenge]ₒ).query (.inl q))

theorem simulateQ_liftShared {α : Type} (x : OracleComp oSpec α) :
    simulateQ (liftShared oSpec pSpec) x = (liftM x : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :=
  rfl

/-- The fold of legacy rounds `k, …, n - 1` from a transcript and state before round `k`. -/
def foldFrom {StmtIn WitIn StmtOut WitOut : Type}
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (k m : ℕ) → (h : k + m = n) →
    pSpec.Transcript ⟨k, by omega⟩ × P.PrvState ⟨k, by omega⟩ →
    OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript (Fin.last n) × P.PrvState (Fin.last n))
  | k, 0, h, x => pure (cast (by
      have : (⟨k, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
      rw [this]) x)
  | k, m + 1, h, x => P.processRound ⟨k, by omega⟩ (pure x) >>= foldFrom P (k + 1) m (by omega)

theorem runToRound_last_eq_bind {StmtIn WitIn StmtOut WitOut : Type}
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    (m k : ℕ) → (h : k + m = n) →
    P.runToRound (Fin.last n) stmt wit =
      P.runToRound ⟨k, by omega⟩ stmt wit >>= foldFrom P k m h
  | 0, k, h => by
    subst h
    simp only [foldFrom, cast_eq]
    exact (bind_pure _).symm
  | m + 1, k, h => by
    rw [runToRound_last_eq_bind P stmt wit m (k + 1) (by omega)]
    have := Prover.runToRound_succ (⟨k, by omega⟩ : Fin n) stmt wit P
    simp only [Fin.succ_mk, Fin.castSucc_mk] at this
    rw [this, Prover.processRound_bind, bind_assoc]
    rfl


section Node

variable {StmtIn WitIn StmtOut WitOut : Type}

theorem samplerEnd_message {M : Type → Type} [Monad M] (T : Type)
    (rest : PlainPoly.B (plainPos .P_to_V T) → Protocol.{0})
    (draw : (c : ChallengeNode plainSig (.liftBind (plainPos .P_to_V T) rest)) →
      M (challengeSpec plainSig (.liftBind (plainPos .P_to_V T) rest) c)) :
    samplerEnd plainSig (.liftBind (plainPos .P_to_V T) rest) draw =
      pure (fun x => samplerEnd plainSig (rest (plainSig.toFunB _ x))
        (fun c => draw ⟨.inr ⟨plainSig.toFunB _ x, c.val⟩, c.property⟩)) := rfl

theorem samplerEnd_challenge {M : Type → Type} [Monad M] (T : Type)
    (rest : PlainPoly.B (plainPos .V_to_P T) → Protocol.{0})
    (draw : (c : ChallengeNode plainSig (.liftBind (plainPos .V_to_P T) rest)) →
      M (challengeSpec plainSig (.liftBind (plainPos .V_to_P T) rest) c)) :
    samplerEnd plainSig (.liftBind (plainPos .V_to_P T) rest) draw =
      (fun x => ⟨x, samplerEnd plainSig (rest (plainSig.toFunB _ x))
        (fun c => draw ⟨.inr ⟨plainSig.toFunB _ x, c.val⟩, c.property⟩)⟩) <$>
        draw ⟨.inl ⟨⟩, rfl⟩ := rfl

/-- One counterpart-first exchange at round `j` is one legacy `processRound`. The direction is
generic, so the lemma applies at the node `plainPos (pSpec.dir j) _` of the tree. -/
theorem step_counterpartFirst_roundSlot {β : Type}
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (D : Direction) (hD : pSpec.dir j = D)
    (rest : PlainPoly.B (plainPos D (pSpec.«Type» j)) → Protocol.{0})
    (draw : (c : ChallengeNode plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest)) →
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (challengeSpec plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest) c))
    (hdraw : ∀ hc, draw ⟨.inl ⟨⟩, hc⟩ = (plainMoveEquiv D _).symm <$>
      challengeOracle oSpec pSpec ⟨j, hD.trans (dir_eq_of_owner hc)⟩)
    (st : P.PrvState j.castSucc) (pre : pSpec.Transcript j.castSucc)
    (F : pSpec.Transcript j.succ × P.PrvState j.succ →
      OracleComp (oSpec + [pSpec.Challenge]ₒ) β)
    (K : (x : Move plainSig (plainPos D (pSpec.«Type» j))) → P.PrvState j.succ →
      Counterpart plainSig (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (rest (plainSig.toFunB _ x)) (fun _ => PUnit) →
      OracleComp (oSpec + [pSpec.Challenge]ₒ) β)
    (hK : ∀ x st', K x st' (sampler plainSig (rest (plainSig.toFunB _ x))
      (fun c => draw ⟨.inr ⟨plainSig.toFunB _ x, c.val⟩, c.property⟩)) =
        F (pre.concat (plainMoveEquiv D _ x), st')) :
    step (owner plainSig (plainPos D (pSpec.«Type» j))) .counterpartFirst
        (simulateQ (liftShared oSpec pSpec) (roundSlot P j D hD st))
        (sampler plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest) draw) K =
      P.processRound j (pure (pre, st)) >>= F := by
  dsimp only [sampler, PureEnd.toStrategy] at hK
  cases D with
  | P_to_V =>
    rw [Prover.processRound_of_dir_eq_P_to_V j hD]
    dsimp only [roundSlot, step, Schedule.seq, sampler, PureEnd.toStrategy,
      PureEnd.mapOutput, owner_plainPos_P_to_V]
    simp only [samplerEnd_message, simulateQ_map, simulateQ_liftShared, bind_map_left,
      LawfulMonad.pure_bind, bind_assoc]
    refine bind_congr fun a => ?_
    exact hK a.1 a.2
  | V_to_P =>
    rw [Prover.processRound_of_dir_eq_V_to_P j hD]
    dsimp only [roundSlot, step, Schedule.seq, sampler, PureEnd.toStrategy,
      PureEnd.mapOutput, owner_plainPos_V_to_P]
    rw [samplerEnd_challenge]
    erw [hdraw]
    simp only [LawfulMonad.pure_bind, bind_assoc]
    erw [bind_map_left, bind_map_left, bind_map_left]
    refine bind_congr fun c => bind_congr fun a => ?_
    exact hK _ _


theorem samplerFrom_zero {M : Type → Type} [Monad M]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) (k : ℕ) (h : k + 0 = n) :
    samplerFrom src k 0 h = (pure ⟨⟩ : M PUnit) := rfl

/-- A counterpart-first run whose first node is round `j`, with the embedded slot and a sampler
whose draw at this node is the legacy challenge, is `processRound j` followed by the rest. -/
theorem runWith_roundSlot {β Out : Type}
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (D : Direction) (hD : pSpec.dir j = D)
    (rest : PlainPoly.B (plainPos D (pSpec.«Type» j)) → Protocol.{0})
    (q : (x : Move plainSig (plainPos D (pSpec.«Type» j))) → P.PrvState j.succ →
      Core.Prover plainSig oSpec (rest (plainSig.toFunB _ x)) (fun _ => Out))
    (draw : (c : ChallengeNode plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest)) →
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (challengeSpec plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest) c))
    (hdraw : ∀ hc, draw ⟨.inl ⟨⟩, hc⟩ = (plainMoveEquiv D _).symm <$>
      challengeOracle oSpec pSpec ⟨j, hD.trans (dir_eq_of_owner hc)⟩)
    (st : P.PrvState j.castSucc) (pre : pSpec.Transcript j.castSucc)
    (G : ((_ : PathAlong plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest)) × Out ×
      PUnit) → OracleComp (oSpec + [pSpec.Challenge]ₒ) β)
    (F : pSpec.Transcript j.succ × P.PrvState j.succ →
      OracleComp (oSpec + [pSpec.Challenge]ₒ) β)
    (hK : ∀ x st', (runWith .counterpartFirst (rest (plainSig.toFunB _ x))
        (Prover.simulate (liftShared oSpec pSpec) (q x st'))
        (sampler plainSig (rest (plainSig.toFunB _ x))
          (fun c => draw ⟨.inr ⟨plainSig.toFunB _ x, c.val⟩, c.property⟩)) >>=
        fun r => G ⟨⟨x, r.1⟩, r.2⟩) = F (pre.concat (plainMoveEquiv D _ x), st')) :
    (runWith .counterpartFirst (.liftBind (plainPos D (pSpec.«Type» j)) rest)
        (Prover.simulate (liftShared oSpec pSpec)
          (Choice.map .focal _ q <$> roundSlot P j D hD st))
        (sampler plainSig _ draw) >>= G) =
      P.processRound j (pure (pre, st)) >>= F := by
  rw [runWith_liftBind, step_bind, Prover.simulate_node, step_map_left, simulateQ_map,
    step_map_left]
  refine step_counterpartFirst_roundSlot P j D hD rest draw hdraw st pre F _ fun x st' => ?_
  simp only [bind_assoc, LawfulMonad.pure_bind]
  exact hK x st'

/-- Counterpart-first execution of an embedded legacy prover from round `k` is the legacy fold
of the remaining rounds followed by `output`, for any continuation of the decoded result. -/
theorem runWith_embedFrom {β : Type}
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (g : FullTranscript pSpec → StmtOut × WitOut → OracleComp (oSpec + [pSpec.Challenge]ₒ) β) :
    (m k : ℕ) → (h : k + m = n) → (pre : pSpec.Transcript ⟨k, by omega⟩) →
    (st : P.PrvState ⟨k, by omega⟩) →
    (runWith .counterpartFirst (suffix pSpec k m h)
        (Prover.simulate (liftShared oSpec pSpec) (embedFrom P k m h st))
        (samplerFrom (challengeOracle oSpec pSpec) k m h) >>=
      fun r => g (decodePlainFrom pSpec k m h pre r.1) r.2.1) =
    foldFrom P k m h (pre, st) >>= fun x => liftM (P.output x.2) >>= g x.1
  | 0, k, h, pre, st => by
    subst h
    change (runWith .counterpartFirst (Pure.pure PUnit.unit) _ _ >>= _) = _
    erw [runWith_done]
    simp only [foldFrom, embedFrom, cast_eq, Schedule.seq]
    erw [samplerFrom_zero, LawfulMonad.pure_bind, bind_assoc]
    simp only [LawfulMonad.pure_bind]
    rfl
  | m + 1, k, h, pre, st => by
    change _ = (P.processRound ⟨k, by omega⟩ (pure (pre, st)) >>=
      foldFrom P (k + 1) m (by omega)) >>= _
    rw [bind_assoc]
    exact runWith_roundSlot P ⟨k, by omega⟩ _ rfl (fun _ => suffix pSpec (k + 1) m (by omega))
      (fun _ st' => embedFrom P (k + 1) m (by omega) st') _ (fun _ => rfl) st pre _ _
      (fun x st' => runWith_embedFrom P g m (k + 1) (by omega) _ st')

end Node

/-! ### The common observation -/

section Observation

variable {StmtIn WitIn StmtOut WitOut : Type}
  {StmtOutAt : Path (protocol pSpec) → Type}

/-- Run an embedded interaction under `order`, in the legacy query monad, against a prover on the
plain tree, then decide. The challenge oracle is the legacy `[pSpec.Challenge]ₒ`. -/
def observeWith (order : Schedule) (V : Core.Verifier oSpec (protocol pSpec) StmtIn StmtOutAt)
    (stmt : StmtIn) {Out : PathAlong plainSig (protocol pSpec) → Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) Out) :
    OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Observation plainSig (protocol pSpec) Out StmtOutAt) := do
  let r ← runWith order (protocol pSpec) (p.simulate (liftShared oSpec pSpec))
    (legacySampler pSpec (challengeOracle oSpec pSpec))
  let verdict ← liftComp (V.decide stmt (projectPathAlong plainSig _ r.1)
    (toPlainView _ r.1)).run (oSpec + [pSpec.Challenge]ₒ)
  pure ⟨r.1, r.2.1, verdict⟩

/-- The legacy result of a plain reduction: the prover's transcript and outputs with the
verifier's output statement, or `none` when the verifier rejects. -/
abbrev LegacyResult (pSpec : ProtocolSpec n) (StmtOut WitOut : Type) :=
  Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)

/-- Forget the rejected run and decode the transcript of an accepted one. -/
def finalize
    (r : Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) (fun _ => StmtOut)) :
    LegacyResult pSpec StmtOut WitOut :=
  r.2.2.map fun t => ((decode pSpec r.1, r.2.1), t)

theorem runToRound_zero (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    P.runToRound 0 stmt wit = pure (default, P.input (stmt, wit)) := rfl

/-- The legacy prover run is the fold of every round followed by `output`. -/
theorem prover_run_eq_foldFrom (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    P.run stmt wit = foldFrom P 0 n (Nat.zero_add n) (default, P.input (stmt, wit)) >>=
      fun x => liftM (P.output x.2) >>= fun o => pure (x.1, o) := by
  rw [_root_.Prover.run, runToRound_last_eq_bind P stmt wit n 0 (Nat.zero_add n)]
  erw [runToRound_zero, LawfulMonad.pure_bind]
  rfl

/-- **Execution correspondence.** For every protocol shape, counterpart-first execution of an
embedded legacy reduction is the legacy run, after finalization, as programs in the legacy query
monad. -/
theorem finalize_observeWith_counterpartFirst
    (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)
    (wit : WitIn) :
    finalize <$> observeWith .counterpartFirst (embedVerifier R.verifier) stmt
        (embedProver R.prover stmt wit) = (R.run stmt wit).run := by
  rw [_root_.Reduction.run_run_eq_bind, prover_run_eq_foldFrom]
  refine (Eq.trans ?_ (runWith_embedFrom R.prover (fun tr o =>
      liftComp (R.verifier.verify stmt tr).run (oSpec + [pSpec.Challenge]ₒ) >>=
        fun v => pure (v.map fun t => ((tr, o), t)))
    n 0 (Nat.zero_add n) default (R.prover.input (stmt, wit)))).trans ?_
  · rw [observeWith, map_eq_bind_pure_comp]
    simp only [bind_assoc, LawfulMonad.pure_bind]
    refine bind_congr fun r => bind_congr fun v => ?_
    rfl
  · erw [bind_assoc]
    refine bind_congr fun x => ?_
    erw [bind_assoc]
    refine bind_congr fun o => ?_
    erw [LawfulMonad.pure_bind]
    rfl

end Observation

/-! ### Exchanging slots in distribution -/

section Exchange

variable {κ σ : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}

/-- The handler of the classical experiment: shared state for the ambient oracles, and a
stateless challenge implementation. -/
abbrev expHandler (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) : QueryImpl (ambient + chal) (StateT σ ProbComp) :=
  QueryImpl.addLift impl chImpl

/-- Two programs have the same distribution of output and final state from every initial state. -/
def DistEqFrom (impl : QueryImpl ambient (StateT σ ProbComp)) (chImpl : QueryImpl chal ProbComp)
    {α : Type} (x y : OracleComp (ambient + chal) α) : Prop :=
  ∀ st, (simulateQ (expHandler impl chImpl) x).run st =ᵈ
    (simulateQ (expHandler impl chImpl) y).run st

/-- A program that never reads or writes the shared state. -/
def Stateless (impl : QueryImpl ambient (StateT σ ProbComp)) (chImpl : QueryImpl chal ProbComp)
    {β : Type} (d : OracleComp (ambient + chal) β) : Prop :=
  ∃ q : ProbComp β, ∀ st, (simulateQ (expHandler impl chImpl) d).run st = (fun b => (b, st)) <$> q

namespace DistEqFrom

variable {impl : QueryImpl ambient (StateT σ ProbComp)} {chImpl : QueryImpl chal ProbComp}
  {α β γ : Type}

theorem refl (x : OracleComp (ambient + chal) α) : DistEqFrom impl chImpl x x :=
  fun _ => EvalDistEq.refl _

theorem of_eq {x y : OracleComp (ambient + chal) α} (h : x = y) : DistEqFrom impl chImpl x y :=
  h ▸ refl x

theorem trans {x y z : OracleComp (ambient + chal) α} (h₁ : DistEqFrom impl chImpl x y)
    (h₂ : DistEqFrom impl chImpl y z) : DistEqFrom impl chImpl x z :=
  fun st => (h₁ st).trans (h₂ st)

theorem bind {x y : OracleComp (ambient + chal) α} {f g : α → OracleComp (ambient + chal) β}
    (h : DistEqFrom impl chImpl x y) (hfg : ∀ a, DistEqFrom impl chImpl (f a) (g a)) :
    DistEqFrom impl chImpl (x >>= f) (y >>= g) := fun st => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact (h st).bind fun p => hfg p.1 p.2

/-- A stateless program commutes in distribution with any program. -/
theorem swap {A : OracleComp (ambient + chal) α} {d : OracleComp (ambient + chal) β}
    (hd : Stateless impl chImpl d) (k : α → β → OracleComp (ambient + chal) γ) :
    DistEqFrom impl chImpl (A >>= fun a => d >>= fun b => k a b)
      (d >>= fun b => A >>= fun a => k a b) := fun st => by
  obtain ⟨q, hq⟩ := hd
  simp only [simulateQ_bind, StateT.run_bind, hq, bind_map_left]
  exact EvalDistEq.bind_bind_swap _ _ _

end DistEqFrom

theorem Stateless.map {impl : QueryImpl ambient (StateT σ ProbComp)}
    {chImpl : QueryImpl chal ProbComp} {β γ : Type} {d : OracleComp (ambient + chal) β}
    (h : Stateless impl chImpl d) (f : β → γ) : Stateless impl chImpl (f <$> d) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨f <$> q, fun st => by simp only [simulateQ_map, StateT.run_map, hq, Functor.map_map]⟩

theorem stateless_query_inr (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) (t : chal.Domain) :
    Stateless impl chImpl (liftM (chal.query t) : OracleComp (ambient + chal) _) :=
  ⟨chImpl t, fun st => by
    rw [expHandler, QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_query_right]
    simp [map_eq_bind_pure_comp]⟩

/-- **Exchange in distribution.** On any plain tree, when every challenge draw is stateless,
the two schedules give the same distribution of output and final state, for every prover. -/
theorem distEqFrom_runWith (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) :
    (s : Protocol.{0}) → {Out : PathAlong plainSig s → Type} →
    (p : Focal plainSig (OracleComp (ambient + chal)) s Out) →
    (draw : (c : ChallengeNode plainSig s) →
      OracleComp (ambient + chal) (challengeSpec plainSig s c)) →
    (∀ c, Stateless impl chImpl (draw c)) →
    DistEqFrom impl chImpl
      (runWith .focalFirst s p (sampler plainSig s draw))
      (runWith .counterpartFirst s p (sampler plainSig s draw))
  | .pure ⟨⟩, _, p, _, _ => by
    refine DistEqFrom.of_eq ?_
    erw [runWith_done, runWith_done]
    simp only [Schedule.seq]
    erw [LawfulMonad.pure_bind]
    refine bind_congr fun a => ?_
    erw [LawfulMonad.pure_bind]
  | .liftBind (.message X) rest, _, p, draw, hdraw => by
    rw [runWith_liftBind, runWith_liftBind, sampler_message]
    simp only [step, Schedule.seq, owner_plain_message, LawfulMonad.pure_bind]
    refine DistEqFrom.bind (DistEqFrom.refl _) fun v => DistEqFrom.bind ?_ fun _ =>
      DistEqFrom.refl _
    exact distEqFrom_runWith impl chImpl (rest v.1) v.2 _ fun c => hdraw _
  | .liftBind (.challenge C) rest, _, p, draw, hdraw => by
    rw [runWith_liftBind, runWith_liftBind, sampler_challenge]
    simp only [step, Schedule.seq, owner_plain_challenge, bind_map_left]
    refine DistEqFrom.trans (DistEqFrom.bind (DistEqFrom.refl _) fun f =>
      DistEqFrom.bind (DistEqFrom.refl _) fun x => DistEqFrom.bind
        (distEqFrom_runWith impl chImpl (rest ⟨⟩) (f x) _ fun c => hdraw _)
        fun _ => DistEqFrom.refl _) ?_
    exact DistEqFrom.swap (hdraw _) _

end Exchange

/-! ### Simulating a run -/

section Simulate

variable {κ κ' : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}

/-- Simulating a run against a public-coin sampler, into another oracle computation, simulates
every prover slot and every draw. -/
theorem simulateQ_runWith (F : QueryImpl spec (OracleComp spec')) (order : Schedule)
    (s : Protocol.{0}) {Out : PathAlong plainSig s → Type}
    (p : Focal plainSig (OracleComp spec) s Out)
    (draw : (c : ChallengeNode plainSig s) → OracleComp spec (challengeSpec plainSig s c)) :
    simulateQ F (runWith order s p (sampler plainSig s draw)) =
      runWith order s (Prover.simulate F p)
        (sampler plainSig s (fun c => simulateQ F (draw c))) :=
  simulateQ_runWith_sampler F order s p draw

end Simulate

/-! ### The default schedule -/

section Bridge

variable {StmtIn WitIn StmtOut WitOut : Type}
  {StmtOutAt : Path (protocol pSpec) → Type}

/-- Answer the challenge queries of a layout's tree with the legacy challenge oracle. -/
def Layout.challengeReindex (L : Layout pSpec) (oSpec : OracleSpec ι) :
    QueryImpl (oSpec + challengeSpec L.l L.protocol) (OracleComp (oSpec + [pSpec.Challenge]ₒ)) :=
  QueryImpl.add (liftShared oSpec pSpec)
    (L.draw (challengeOracle oSpec pSpec) 0 n (Nat.zero_add n))

/-- Answer the challenge queries of the plain tree with the legacy challenge oracle. -/
abbrev challengeReindex (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n) :
    QueryImpl (oSpec + challengeSpec plainSig (protocol pSpec))
      (OracleComp (oSpec + [pSpec.Challenge]ₒ)) :=
  (plainLayout pSpec).challengeReindex oSpec

/-- The prover-sampler run of the interaction layer, with its queries reindexed, is the
focal-first run against the legacy sampler. -/
theorem simulateQ_challengeReindex_run {Out : PathAlong plainSig (protocol pSpec) → Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) Out) :
    simulateQ (challengeReindex oSpec pSpec) (TwoParty.Lens.run (protocol pSpec)
      (p.simulate (fun q => liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query
        (.inl q))))
      (sampler plainSig (protocol pSpec) (fun c =>
        liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inr c))))) =
      runWith .focalFirst (protocol pSpec) (p.simulate (liftShared oSpec pSpec))
        (legacySampler pSpec (challengeOracle oSpec pSpec)) := by
  have hl : (fun q => simulateQ (challengeReindex oSpec pSpec)
      (liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inl q)))) =
      liftShared oSpec pSpec :=
    funext fun q => QueryImpl.simulateQ_add_liftM_query_left _ _ q
  have hr : (fun c => simulateQ (challengeReindex oSpec pSpec)
      (liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inr c)))) =
      legacyDraw (challengeOracle oSpec pSpec) 0 n (Nat.zero_add n) :=
    funext fun c => QueryImpl.simulateQ_add_liftM_query_right _ _ c
  rw [TwoParty.Lens.run, simulateQ_runWith, Prover.simulate_simulate, hl, hr]
  rfl

/-- The run of the interaction layer, with its challenges answered by the legacy challenge
oracle, is the focal-first observation. -/
theorem simulateQ_verifier_run (V : Core.Verifier oSpec (protocol pSpec) StmtIn StmtOutAt)
    (stmt : StmtIn) {Out : PathAlong plainSig (protocol pSpec) → Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) Out) :
    simulateQ (challengeReindex oSpec pSpec) (V.run stmt p) = observeWith .focalFirst V stmt p := by
  rw [Core.Verifier.run, observeWith, simulateQ_bind, simulateQ_challengeReindex_run]
  refine bind_congr fun r => ?_
  rcases r with ⟨tr, out, u⟩
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  congr 1
  rw [liftComp_def, liftComp_def]
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) _
  rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  refine (QueryImpl.simulateQ_add_liftM_query_left _ _ t).trans ?_
  rw [liftShared, OracleComp.liftM_eq_liftM_liftM (spec := oSpec)]
  rfl

/-- The challenge implementation of a layout's tree induced by a legacy challenge
implementation: each challenge node draws its round's legacy challenge. -/
def Layout.challengeImpl (L : Layout pSpec) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) :
    QueryImpl (challengeSpec L.l L.protocol) ProbComp :=
  fun c => (L.challengeMove 0 n (Nat.zero_add n) c).symm <$>
    chImpl ⟨L.challengeRound 0 n (Nat.zero_add n) c, ()⟩

/-- The challenge implementation of the plain tree induced by a legacy challenge
implementation. -/
abbrev plainChallengeImpl (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) :
    QueryImpl (challengeSpec plainSig (protocol pSpec)) ProbComp :=
  (plainLayout pSpec).challengeImpl chImpl

theorem stateless_challengeOracle {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) (i : pSpec.ChallengeIdx) :
    Stateless impl chImpl (challengeOracle oSpec pSpec i) :=
  stateless_query_inr impl chImpl ⟨i, ()⟩

/-- Reindexing the challenges moves the handler from a layout's challenge oracle to the legacy
challenge oracle, for any shared-state implementation. -/
theorem Layout.simulateQ_expHandler_challengeReindex (L : Layout pSpec) {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) {α : Type}
    (x : OracleComp (oSpec + challengeSpec L.l L.protocol) α) :
    simulateQ (expHandler impl (L.challengeImpl chImpl)) x =
      simulateQ (expHandler impl chImpl) (simulateQ (L.challengeReindex oSpec) x) := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) x]
  rcases t with q | c
  · exact QueryImpl.simulateQ_add_liftM_query_left _ _ q
  · change simulateQ _ ((L.challengeMove 0 n (Nat.zero_add n) c).symm <$>
      challengeOracle oSpec pSpec (L.challengeRound 0 n (Nat.zero_add n) c)) = _
    simp only [expHandler]
    rw [simulateQ_map, QueryImpl.addLift_def]
    erw [QueryImpl.simulateQ_add_liftM_query_right]
    refine StateT.ext fun s => ?_
    simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
      Layout.challengeImpl, StateT.run_liftM]
    erw [StateT.run_map, StateT.run_liftM]
    simp only [map_eq_bind_pure_comp]
    erw [bind_assoc, bind_map_left]
    refine bind_congr fun _ => ?_
    erw [LawfulMonad.pure_bind]
    rfl

/-- Reindexing the challenges moves the experiment from a layout's challenge oracle to the legacy
challenge oracle. -/
theorem Layout.experiment_challengeReindex (L : Layout pSpec) {σ α : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (x : OracleComp (oSpec + challengeSpec L.l L.protocol) α) :
    experiment init impl (L.challengeImpl chImpl) x =
      experiment init impl chImpl (simulateQ (L.challengeReindex oSpec) x) := by
  unfold experiment
  exact bind_congr fun st =>
    congrArg (fun y => StateT.run' y st) (L.simulateQ_expHandler_challengeReindex impl chImpl x)

/-- Reindexing the challenges moves the handler from the plain tree's challenge oracle to the
legacy challenge oracle, for any shared-state implementation. -/
theorem simulateQ_expHandler_challengeReindex {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) {α : Type}
    (x : OracleComp (oSpec + challengeSpec plainSig (protocol pSpec)) α) :
    simulateQ (expHandler impl (plainChallengeImpl chImpl)) x =
      simulateQ (expHandler impl chImpl) (simulateQ (challengeReindex oSpec pSpec) x) :=
  (plainLayout pSpec).simulateQ_expHandler_challengeReindex impl chImpl x

/-- Reindexing the challenges moves the experiment from the plain tree's challenge oracle to
the legacy challenge oracle. -/
theorem experiment_challengeReindex {σ α : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (x : OracleComp (oSpec + challengeSpec plainSig (protocol pSpec)) α) :
    experiment init impl (plainChallengeImpl chImpl) x =
      experiment init impl chImpl (simulateQ (challengeReindex oSpec pSpec) x) :=
  (plainLayout pSpec).experiment_challengeReindex init impl chImpl x

end Bridge

/-! ### Equality in distribution -/

section Distribution

variable {StmtIn WitIn StmtOut WitOut σ : Type}
  {StmtOutAt : Path (protocol pSpec) → Type}

theorem DistEqFrom.map {κ : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}
    {impl : QueryImpl ambient (StateT σ ProbComp)} {chImpl : QueryImpl chal ProbComp}
    {α β : Type} {x y : OracleComp (ambient + chal) α} (h : DistEqFrom impl chImpl x y)
    (f : α → β) : DistEqFrom impl chImpl (f <$> x) (f <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact h.bind fun _ => DistEqFrom.refl _

/-- The experiment only sees the distribution of output and final state from each initial
state. -/
theorem experiment_evalDistEq {κ : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) {α : Type} {x y : OracleComp (ambient + chal) α}
    (h : DistEqFrom impl chImpl x y) :
    experiment init impl chImpl x =ᵈ experiment init impl chImpl y := by
  unfold experiment
  refine EvalDistEq.bind (EvalDistEq.refl _) fun st => ?_
  simp only [StateT.run'_eq]
  exact (h st).map Prod.fst

/-- The two schedules of the legacy observation agree in distribution, for every prover. -/
theorem distEqFrom_observeWith (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (V : Core.Verifier oSpec (protocol pSpec) StmtIn StmtOutAt) (stmt : StmtIn)
    {Out : PathAlong plainSig (protocol pSpec) → Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) Out) :
    DistEqFrom impl chImpl (observeWith .focalFirst V stmt p)
      (observeWith .counterpartFirst V stmt p) :=
  DistEqFrom.bind (distEqFrom_runWith impl chImpl _ _ _ fun _ =>
    (stateless_challengeOracle impl chImpl _).map _) fun _ => DistEqFrom.refl _

/-- **Observation transfer.** For every prover, the interaction-layer observation under the
reindexed challenge implementation has the distribution of the legacy-indexed observation under
the counterpart-first schedule. -/
theorem experiment_verifier_run_evalDistEq (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (V : Core.Verifier oSpec (protocol pSpec) StmtIn StmtOutAt) (stmt : StmtIn)
    {Out : PathAlong plainSig (protocol pSpec) → Type}
    (p : Core.Prover plainSig oSpec (protocol pSpec) Out) {β : Type}
    (f : Observation plainSig (protocol pSpec) Out StmtOutAt → β) :
    experiment init impl (plainChallengeImpl chImpl) (f <$> V.run stmt p) =ᵈ
      experiment init impl chImpl (f <$> observeWith .counterpartFirst V stmt p) := by
  rw [experiment_challengeReindex, simulateQ_map, simulateQ_verifier_run]
  exact experiment_evalDistEq init impl chImpl ((distEqFrom_observeWith impl chImpl V stmt p).map f)

/-- **Execution correspondence in distribution.** The finalized interaction-layer execution of
the embedded reduction, with challenges drawn by the reindexed legacy challenge implementation,
has the distribution of the legacy execution. -/
theorem experiment_finalize_observe_evalDistEq (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)
    (wit : WitIn) :
    experiment init impl (plainChallengeImpl chImpl)
        (finalize <$> (embedReduction R).observe stmt wit) =ᵈ
      experiment init impl chImpl (R.run stmt wit).run := by
  rw [← finalize_observeWith_counterpartFirst]
  exact experiment_verifier_run_evalDistEq init impl chImpl _ stmt _ finalize

/-- **Execution correspondence as measures.** For every measurable structure on the legacy
result, the two output measures agree. Both experiments are `ProbComp`s, whose answer measure
is the global uniform one; `none` is an outcome of the result type, not missing mass. -/
theorem evalDist_experiment_finalize_observe [MeasurableSpace (LegacyResult pSpec StmtOut WitOut)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)
    (wit : WitIn) :
    𝒟[experiment init impl (plainChallengeImpl chImpl)
        (finalize <$> (embedReduction R).observe stmt wit)] =
      𝒟[experiment init impl chImpl (R.run stmt wit).run] :=
  (experiment_finalize_observe_evalDistEq init impl chImpl R stmt wit).evalDist_eq

end Distribution

/-! ### Pure challenge slots -/

section PureSlots

variable {StmtIn WitIn StmtOut WitOut : Type}
  {StmtOutAt : Path (protocol pSpec) → Type}

/-- A legacy prover whose `receiveChallenge` has no effect before the challenge arrives. -/
def PureChallengeSlots (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  ∀ i st, ∃ f, P.receiveChallenge i st = pure f

/-- At round `j`, an embedded slot whose challenge-node effect is pure reacts purely as an
observer of the sampler. -/
theorem pureObservers_roundSlot {Out : Type}
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (hP : PureChallengeSlots P)
    (j : Fin n) (D : Direction) (hD : pSpec.dir j = D)
    (rest : PlainPoly.B (plainPos D (pSpec.«Type» j)) → Protocol.{0})
    (q : (x : Move plainSig (plainPos D (pSpec.«Type» j))) → P.PrvState j.succ →
      Core.Prover plainSig oSpec (rest (plainSig.toFunB _ x)) (fun _ => Out))
    (draw : (c : ChallengeNode plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest)) →
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (challengeSpec plainSig (.liftBind (plainPos D (pSpec.«Type» j)) rest) c))
    (st : P.PrvState j.castSucc)
    (hq : ∀ x st', PureObservers (l := plainSig) (rest (plainSig.toFunB _ x))
      (Prover.simulate (liftShared oSpec pSpec) (q x st'))
      (sampler plainSig (rest (plainSig.toFunB _ x))
        (fun c => draw ⟨.inr ⟨plainSig.toFunB _ x, c.val⟩, c.property⟩))) :
    PureObservers (l := plainSig) (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
      (.liftBind (plainPos D (pSpec.«Type» j)) rest) (OutP := fun _ => Out)
      (Prover.simulate (l := plainSig) (s := .liftBind (plainPos D (pSpec.«Type» j)) rest)
        (Out := fun _ => Out) (liftShared oSpec pSpec)
        (Choice.map .focal (owner plainSig (plainPos D (pSpec.«Type» j))) q <$>
          roundSlot P j D hD st))
      (sampler plainSig _ draw) := by
  have hp : Prover.simulate (l := plainSig) (s := .liftBind (plainPos D (pSpec.«Type» j)) rest)
      (Out := fun _ => Out) (liftShared oSpec pSpec)
      (Choice.map .focal (owner plainSig (plainPos D (pSpec.«Type» j))) q <$>
        roundSlot P j D hD st) =
      Choice.map .focal _ (fun x st' => Prover.simulate (liftShared oSpec pSpec) (q x st')) <$>
        simulateQ (liftShared oSpec pSpec) (roundSlot P j D hD st) := by
    rw [Prover.simulate_node, simulateQ_map, Functor.map_map]
    exact congrArg (· <$> _) (funext fun a => congrFun (Choice.map_comp _ _ _ _) a)
  cases D with
  | P_to_V =>
    refine ⟨_, PUnit, _, pure ⟨⟩, _, fun _ x => sampler plainSig (rest x)
      (fun c => draw ⟨.inr ⟨x, c.val⟩, c.property⟩), hp, ?_, ⟨_, rfl⟩, ?_⟩
    · refine (sampler_message _ rest draw).trans ?_
      erw [LawfulApplicative.map_pure]
      rfl
    · intro i _
      exact hq i.1 i.2
  | V_to_P =>
    obtain ⟨f, hf⟩ := hP ⟨j, hD⟩ st
    refine ⟨_, _, _, draw ⟨.inl ⟨⟩, rfl⟩, _, fun x => ⟨x, sampler plainSig (rest ⟨⟩)
      (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)⟩, hp, sampler_challenge _ rest draw,
      ⟨f, ?_⟩, ?_⟩
    · change simulateQ _ (P.receiveChallenge ⟨j, hD⟩ st) = _
      rw [hf, simulateQ_pure]
      rfl
    · intro i x
      exact hq x (i x)

/-- An embedded prover with pure challenge slots reacts purely as an observer of the legacy
sampler on the remaining rounds. -/
theorem pureObservers_embedFrom (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hP : PureChallengeSlots P)
    (src : (i : pSpec.ChallengeIdx) → OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) :
    (m k : ℕ) → (h : k + m = n) → (st : P.PrvState ⟨k, by omega⟩) →
    PureObservers (l := plainSig) (suffix pSpec k m h)
      (Prover.simulate (liftShared oSpec pSpec) (embedFrom P k m h st)) (samplerFrom src k m h)
  | 0, _, _, _ => ⟨⟨⟩, rfl⟩
  | m + 1, k, h, st =>
    pureObservers_roundSlot P hP ⟨k, by omega⟩ _ rfl (fun _ => suffix pSpec (k + 1) m (by omega))
      (fun _ st' => embedFrom P (k + 1) m (by omega) st') _ st
      (fun _ st' => pureObservers_embedFrom P hP src m (k + 1) (by omega) st')

/-- **Schedule exchange as program equality.** When the honest prover's challenge slots are
pure, the default and counterpart-first schedules of the embedded execution are the same
program. -/
theorem observeWith_focalFirst_eq (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hP : PureChallengeSlots P) (V : Core.Verifier oSpec (protocol pSpec) StmtIn StmtOutAt)
    (stmt : StmtIn) (wit : WitIn) :
    observeWith .focalFirst V stmt (embedProver P stmt wit) =
      observeWith .counterpartFirst V stmt (embedProver P stmt wit) := by
  have h := runWith_eq_of_pureObservers (l := plainSig) _ _ _
    (pureObservers_embedFrom P hP (challengeOracle oSpec pSpec) n 0 (Nat.zero_add n)
      (P.input (stmt, wit)))
  unfold observeWith
  erw [h]
  rfl

/-- **Execution correspondence as program equality.** When the honest prover's challenge slots
are pure, reindexing the challenges of the finalized interaction-layer execution gives the
legacy execution. -/
theorem simulateQ_finalize_observe (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hP : PureChallengeSlots R.prover) (stmt : StmtIn) (wit : WitIn) :
    simulateQ (challengeReindex oSpec pSpec) (finalize <$> (embedReduction R).observe stmt wit) =
      (R.run stmt wit).run := by
  rw [simulateQ_map, Core.Reduction.observe, simulateQ_verifier_run, ←
    finalize_observeWith_counterpartFirst]
  exact congrArg _ (observeWith_focalFirst_eq R.prover hP _ stmt wit)

end PureSlots

/-! ### Logged execution

The logged runs of both layers keep only the shared-oracle entries of the prover's log. The log is
moved into the experiment's state (`run_ambientLogged`), where the exchange of slots in
distribution applies unchanged, with the logging implementation `logImpl impl` as the shared-state
implementation.
-/

section Logging

variable {κ σ : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}

/-- Record each shared-oracle query and its answer in the state, beside the shared state. -/
def logImpl (impl : QueryImpl ambient (StateT σ ProbComp)) :
    QueryImpl ambient (StateT (σ × QueryLog ambient) ProbComp) :=
  fun q => StateT.mk fun p => (fun r => (r.1, (r.2, p.2 ++ [⟨q, r.1⟩]))) <$> (impl q).run p.1

/-- Log every query of a program, then keep the shared-oracle entries. Challenge entries are
dropped, so their position relative to shared-oracle queries does not matter. -/
def ambientLogged {α : Type} (x : OracleComp (ambient + chal) α) :
    OracleComp (ambient + chal) (α × QueryLog ambient) :=
  (fun z => (z.1, z.2.fst)) <$> (simulateQ (QueryImpl.id' (ambient + chal)).withLogging x).run

theorem ambientLogged_pure {α : Type} (a : α) :
    ambientLogged (ambient := ambient) (chal := chal) (pure a) = pure (a, []) := by
  simp [ambientLogged]
  rfl

theorem ambientLogged_query_bind {α : Type} (t : (ambient + chal).Domain)
    (k : (ambient + chal).Range t → OracleComp (ambient + chal) α) :
    ambientLogged (liftM ((ambient + chal).query t) >>= k) =
      liftM ((ambient + chal).query t) >>= fun u =>
        (fun z => (z.1, QueryLog.fst [⟨t, u⟩] ++ z.2)) <$> ambientLogged (k u) := by
  rcases t with q | c <;> simp [ambientLogged, QueryLog.fst]

/-- Under the experiment's handler, the shared-oracle log of a program is the log kept in the
state by `logImpl`, appended to any starting log. -/
theorem run_ambientLogged (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) {α : Type} (x : OracleComp (ambient + chal) α) (st : σ)
    (w : QueryLog ambient) :
    (fun z => (z.1.1, (z.2, w ++ z.1.2))) <$>
        (simulateQ (expHandler impl chImpl) (ambientLogged x)).run st =
      (simulateQ (expHandler (logImpl impl) chImpl) x).run (st, w) := by
  induction x using OracleComp.inductionOn generalizing st w with
  | pure a => simp [ambientLogged_pure]
  | query_bind t k ih =>
    rw [ambientLogged_query_bind]
    rcases t with q | c
    · simp only [expHandler, QueryImpl.addLift_def, QueryImpl.liftTarget_self] at ih
      simp [expHandler, logImpl, ← ih, QueryLog.fst]
    · simp only [expHandler, QueryImpl.addLift_def, QueryImpl.liftTarget_self] at ih
      simp [expHandler, ← ih, QueryLog.fst]

/-- A function of a full log is invariant under moving challenge entries relative to
shared-oracle entries: it depends on the shared-oracle entries in order and on the challenge
entries in order, but not on how the two are interleaved. Different schedules of the same run
interleave the two kinds of entries differently. -/
def ChallengeMoveInvariant {β : Type} (f : QueryLog (ambient + chal) → β) : Prop :=
  ∀ l l' : QueryLog (ambient + chal), l.fst = l'.fst → l.snd = l'.snd → f l = f l'

/-- A function of the shared-oracle log alone is invariant under moving challenge entries. Both
layers hand extractors only this projection of the prover's log. -/
theorem challengeMoveInvariant_comp_fst {β : Type} (g : QueryLog ambient → β) :
    ChallengeMoveInvariant (chal := chal) (g ∘ QueryLog.fst) :=
  fun _ _ h _ => congrArg g h

/-- Two programs, possibly over different oracle specifications, with the same distribution of
output and final state from every initial state under their handlers. -/
def RunEq {κ₁ κ₂ : Type} {spec₁ : OracleSpec κ₁} {spec₂ : OracleSpec κ₂}
    (H₁ : QueryImpl spec₁ (StateT σ ProbComp)) (H₂ : QueryImpl spec₂ (StateT σ ProbComp))
    {α : Type} (x : OracleComp spec₁ α) (y : OracleComp spec₂ α) : Prop :=
  ∀ st, (simulateQ H₁ x).run st =ᵈ (simulateQ H₂ y).run st

namespace RunEq
variable {κ₁ κ₂ : Type} {spec₁ : OracleSpec κ₁} {spec₂ : OracleSpec κ₂}
  {H₁ : QueryImpl spec₁ (StateT σ ProbComp)} {H₂ : QueryImpl spec₂ (StateT σ ProbComp)}
  {α β : Type}

theorem of_eq {x : OracleComp spec₁ α} {y : OracleComp spec₂ α}
    (h : ∀ st, (simulateQ H₁ x).run st = (simulateQ H₂ y).run st) : RunEq H₁ H₂ x y :=
  fun st => h st ▸ EvalDistEq.refl _

theorem bind {x : OracleComp spec₁ α} {y : OracleComp spec₂ α}
    {f : α → OracleComp spec₁ β} {g : α → OracleComp spec₂ β}
    (h : RunEq H₁ H₂ x y) (hfg : ∀ a, RunEq H₁ H₂ (f a) (g a)) :
    RunEq H₁ H₂ (x >>= f) (y >>= g) := fun st => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact (h st).bind fun p => hfg p.1 p.2

theorem pure (a : α) : RunEq H₁ H₂ (pure a : OracleComp spec₁ α) (pure a) :=
  of_eq fun _ => by simp

end RunEq

/-- Experiments of related programs agree in distribution. -/
theorem experiment_evalDistEq_of_runEq {κ₁ κ₂ : Type} {chal₁ : OracleSpec κ₁}
    {chal₂ : OracleSpec κ₂} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (ch₁ : QueryImpl chal₁ ProbComp) (ch₂ : QueryImpl chal₂ ProbComp) {α : Type}
    {x : OracleComp (ambient + chal₁) α} {y : OracleComp (ambient + chal₂) α}
    (h : RunEq (expHandler impl ch₁) (expHandler impl ch₂) x y) :
    experiment init impl ch₁ x =ᵈ experiment init impl ch₂ y := by
  unfold experiment
  refine EvalDistEq.bind (EvalDistEq.refl _) fun st => ?_
  simp only [StateT.run'_eq]
  exact (h st).map Prod.fst

/-- A lifted shared-oracle program sees only the shared-state implementation. -/
theorem simulateQ_expHandler_liftComp (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) {β : Type} (y : OracleComp ambient β) :
    simulateQ (expHandler impl chImpl) (liftComp y (ambient + chal)) = simulateQ impl y :=
  QueryImpl.simulateQ_liftComp_left_eq_of_apply _ _
    (fun t => by simp [expHandler, QueryImpl.addLift_def]) y

theorem runEq_liftComp {κ₁ κ₂ : Type} {chal₁ : OracleSpec κ₁} {chal₂ : OracleSpec κ₂}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (ch₁ : QueryImpl chal₁ ProbComp)
    (ch₂ : QueryImpl chal₂ ProbComp) {β : Type} (y : OracleComp ambient β) :
    RunEq (expHandler impl ch₁) (expHandler impl ch₂) (liftComp y (ambient + chal₁))
      (liftComp y (ambient + chal₂)) :=
  RunEq.of_eq fun _ => by rw [simulateQ_expHandler_liftComp, simulateQ_expHandler_liftComp]

/-- Logging the shared-oracle queries of a lifted program is lifting its logged run. -/
theorem run_withLogging_inl {β : Type} (y : OracleComp ambient β) :
    (simulateQ (QueryImpl.withLogging ((fun q => liftM ((ambient + chal).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + chal)))) y).run =
      liftComp ((simulateQ ambient.loggingOracle y).run) (ambient + chal) := by
  induction y using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp [loggingOracle] at ih ⊢
    simp only [← ih]
    rfl

/-- `run_ambientLogged` from the empty log, solved for the logged program. -/
theorem run_ambientLogged_nil (impl : QueryImpl ambient (StateT σ ProbComp))
    (chImpl : QueryImpl chal ProbComp) {α : Type} (x : OracleComp (ambient + chal) α) (st : σ) :
    (simulateQ (expHandler impl chImpl) (ambientLogged x)).run st =
      (fun z => ((z.1, z.2.2), z.2.1)) <$>
        (simulateQ (expHandler (logImpl impl) chImpl) x).run (st, []) := by
  rw [← run_ambientLogged impl chImpl x st [], Functor.map_map]
  refine (LawfulFunctor.id_map _).symm.trans (congrArg (· <$> _) (funext fun z => ?_))
  simp

end Logging

section LoggedProver

variable {σ StmtIn WitIn StmtOut WitOut : Type}

/-- Counterpart-first execution of an embedded legacy prover, decoded, is the legacy prover
run. -/
theorem decode_runWith_counterpartFirst (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (fun r => (decode pSpec r.1, r.2.1)) <$> runWith .counterpartFirst (protocol pSpec)
        ((embedProver P stmt wit).simulate (liftShared oSpec pSpec))
        (legacySampler pSpec (challengeOracle oSpec pSpec)) = P.run stmt wit := by
  rw [prover_run_eq_foldFrom, map_eq_bind_pure_comp]
  exact runWith_embedFrom P (fun tr o => pure (tr, o)) n 0 (Nat.zero_add n) default
    (P.input (stmt, wit))

/-- **Logged prover phase.** The interaction-layer prover-sampler run of an embedded legacy
prover, with its shared-oracle log, has the legacy logged prover run's distribution of
decoded result, shared-oracle log and final state, from every state. -/
theorem runEq_ambientLogged_prover (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    RunEq (expHandler impl (plainChallengeImpl chImpl)) (expHandler impl chImpl)
      ((fun z => ((decode pSpec z.1.1, z.1.2.1), z.2)) <$> ambientLogged
        (TwoParty.Lens.run (protocol pSpec)
          ((embedProver P stmt wit).simulate (fun q =>
            liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inl q))))
          (sampler plainSig (protocol pSpec) (fun c =>
            liftM ((oSpec + challengeSpec plainSig (protocol pSpec)).query (.inr c))))))
      (ambientLogged (P.run stmt wit)) := fun st => by
  rw [simulateQ_map, StateT.run_map, run_ambientLogged_nil, run_ambientLogged_nil,
    Functor.map_map, simulateQ_expHandler_challengeReindex, simulateQ_challengeReindex_run,
    ← decode_runWith_counterpartFirst P stmt wit, simulateQ_map, StateT.run_map,
    Functor.map_map]
  exact ((distEqFrom_runWith (logImpl impl) chImpl _ _ _ fun _ =>
    (stateless_challengeOracle (logImpl impl) chImpl _).map _) (st, [])).map _

end LoggedProver

end Interaction.Core.Legacy
