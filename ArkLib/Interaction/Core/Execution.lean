/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Reduction
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Plain execution

Execution uses PolyFun's focal-first runner, then calls the verifier decision. The observation
retains the transcript and prover output on rejection. Ambient failure remains a failure of the
oracle computation, distinct from a returned rejecting verdict.

Simulating a run against a sampler, under either schedule and into any lawful monad, simulates
every prover slot and every draw (`simulateQ_runWith_sampler`). Simulating a simulated prover
composes the two handlers (`Prover.simulate_simulate`).
-/

@[expose] public section

universe u uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp

/-- A completed interaction, including a possibly rejecting verifier verdict. -/
abbrev Observation {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s : FreeM P PUnit.{u + 1}) (Out : PathAlong l s → Type u) (StmtOut : Type u) :=
  (tr : PathAlong l s) × Out tr × Option StmtOut

/-- Run the interaction against an arbitrary focal strategy, and decide at its end. -/
def Verifier.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S T : Type u} {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out) :
    OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) := do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (p.simulate (fun q => liftM ((ambient + challengeSpec plainSig s).query (.inl q))))
    (sampler plainSig s (fun c =>
      liftM ((ambient + challengeSpec plainSig s).query (.inr c))))
  let verdict ← OracleComp.liftComp
    (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run
    (ambient + challengeSpec plainSig s)
  pure ⟨tr, out, verdict⟩

/-- Every possible verdict of a run is a possible verdict of the decision on its transcript. -/
theorem Verifier.verdict_mem_support_run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S T : Type u} {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out)
    {obs : Observation plainSig s Out T} (h : obs ∈ support (V.run stmt p)) :
    obs.2.2 ∈ support
      (V.decide stmt (projectPathAlong plainSig s obs.1) (toPlainView s obs.1)).run := by
  simp only [Verifier.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨⟨tr, out, _⟩, -, verdict, hv, rfl⟩ := h
  simpa only [mem_support_liftComp_iff] using hv

/-- Execute the honest prover and terminal decision, retaining explicit rejection. -/
def Reduction.observe {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S W T : Type u} {Out : PathAlong plainSig s → Type u}
    (R : Reduction ambient s S W T Out) (stmt : S) (wit : W) :
    OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) :=
  R.verifier.run stmt (R.prover stmt wit)

/-- The accepting-result presentation of the same execution. -/
def Reduction.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S W T : Type u} {Out : PathAlong plainSig s → Type u}
    (R : Reduction ambient s S W T Out) (stmt : S) (wit : W) :
    OptionT (OracleComp (ambient + challengeSpec plainSig s))
      ((tr : PathAlong plainSig s) × Out tr × T) :=
  OptionT.mk do
    let ⟨tr, out, verdict⟩ ← R.observe stmt wit
    pure (verdict.map fun t => ⟨tr, out, t⟩)

/-! ### Simulating a run -/

section Simulate

/-- The node equation of `runWith`, as one local exchange. -/
theorem runWith_liftBind {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {M : Type u → Type u} [Monad M] [LawfulMonad M] (order : Schedule)
    (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l (.liftBind a rest) → Type u}
    (p : Focal l M (.liftBind a rest) OutP)
    (c : Counterpart l M (.liftBind a rest) OutC) :
    runWith (l := l) (m := M) order (.liftBind a rest) p c =
      step (owner l a) order p c (fun x pn cn =>
        runWith (l := l) (m := M) order (rest (l.toFunB a x)) pn cn >>= fun r =>
          pure (⟨⟨x, r.1⟩, r.2.1, r.2.2⟩ :
            (t : PathAlong l (.liftBind a rest)) × OutP t × OutC t)) :=
  runWith_node (l := l) (m := M) order a rest p c

/-- At a message node, the sampler draws nothing and continues on the sent message. -/
theorem sampler_message {M : Type u → Type u} [Monad M] [LawfulMonad M] (X : Type u)
    (rest : X → Protocol.{u})
    (draw : (c : ChallengeNode plainSig (.liftBind (PlainPos.message X) rest)) →
      M (challengeSpec plainSig (.liftBind (PlainPos.message X) rest) c)) :
    sampler plainSig (.liftBind (PlainPos.message X) rest) draw =
      pure (fun x => sampler plainSig (rest x) (fun c => draw ⟨.inr ⟨x, c.val⟩, c.property⟩)) := by
  change Choice.map .counterpart .sender _ <$> pure _ = _
  erw [LawfulApplicative.map_pure]
  rfl

/-- At a challenge node, the sampler draws the challenge and continues on it. -/
theorem sampler_challenge {M : Type u → Type u} [Monad M] [LawfulMonad M] (C : Type u)
    (rest : PUnit → Protocol.{u})
    (draw : (c : ChallengeNode plainSig (.liftBind (PlainPos.challenge C) rest)) →
      M (challengeSpec plainSig (.liftBind (PlainPos.challenge C) rest) c)) :
    sampler plainSig (.liftBind (PlainPos.challenge C) rest) draw =
      (fun x => ⟨x, sampler plainSig (rest ⟨⟩)
        (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)⟩) <$> draw ⟨.inl ⟨⟩, rfl⟩ := by
  change Choice.map .counterpart .receiver _ <$> (_ <$> _) = _
  erw [Functor.map_map]
  rfl

variable {κ κ' : Type u} {spec : OracleSpec.{u, u} κ} {spec' : OracleSpec.{u, u} κ'}
  {n : Type u → Type u} [Monad n] [LawfulMonad n]

/-- Simulating a simulated prover composes the two handlers. -/
theorem Prover.simulate_simulate {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    (F : QueryImpl spec' n) (G : QueryImpl spec (OracleComp spec')) :
    (s : FreeM P PUnit.{u + 1}) → {Out : PathAlong l s → Type u} →
    (p : Prover l spec s Out) →
    Prover.simulate F (Prover.simulate G p) = Prover.simulate (fun q => simulateQ F (G q)) p
  | .pure _, _, p => by
    rw [Prover.simulate_done, Prover.simulate_done, Prover.simulate_done]
    exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) p
  | .liftBind a rest, _, p => by
    rw [Prover.simulate_node, Prover.simulate_node, Prover.simulate_node, simulateQ_map,
      Functor.map_map, QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) p]
    refine congrArg (· <$> _) (funext fun v => ?_)
    refine (congrFun (Choice.map_comp _ _ _ _) v).trans ?_
    exact congrArg (fun f => Choice.map .focal (owner l a) f v)
      (funext fun x => funext fun r => Prover.simulate_simulate F G _ r)

/-- Simulating a run against a public-coin sampler, under either schedule, simulates every
prover slot and every draw. -/
theorem simulateQ_runWith_sampler (F : QueryImpl spec n) (order : Schedule) :
    (s : Protocol.{u}) → {Out : PathAlong plainSig s → Type u} →
    (p : Prover plainSig spec s Out) →
    (draw : (c : ChallengeNode plainSig s) → OracleComp spec (challengeSpec plainSig s c)) →
    simulateQ F (runWith order s p (sampler plainSig s draw)) =
      runWith order s (Prover.simulate F p)
        (sampler plainSig s (fun c => simulateQ F (draw c)))
  | .pure ⟨⟩, _, p, _ => by
    erw [runWith_done, runWith_done]
    cases order <;> simp only [Schedule.seq, simulateQ_bind, simulateQ_pure] <;> rfl
  | .liftBind (.message X) rest, _, p, draw => by
    rw [runWith_liftBind, runWith_liftBind, sampler_message, sampler_message]
    rw [Prover.simulate_node]
    cases order
    · simp only [step, Schedule.seq, owner_plain_message]
      erw [simulateQ_bind, bind_map_left]
      refine bind_congr fun v => ?_
      erw [LawfulMonad.pure_bind, LawfulMonad.pure_bind, simulateQ_bind,
        simulateQ_runWith_sampler F .focalFirst (rest v.1) v.2]
      refine bind_congr fun r => ?_
      erw [simulateQ_pure]
      rfl
    · simp only [step, Schedule.seq, owner_plain_message]
      erw [LawfulMonad.pure_bind, LawfulMonad.pure_bind, simulateQ_bind, bind_map_left]
      refine bind_congr fun v => ?_
      erw [simulateQ_bind, simulateQ_runWith_sampler F .counterpartFirst (rest v.1) v.2]
      refine bind_congr fun r => ?_
      erw [simulateQ_pure]
      rfl
  | .liftBind (.challenge C) rest, _, p, draw => by
    rw [runWith_liftBind, runWith_liftBind, sampler_challenge, sampler_challenge]
    rw [Prover.simulate_node]
    cases order
    · simp only [step, Schedule.seq, owner_plain_challenge, bind_map_left]
      erw [simulateQ_bind]
      refine bind_congr fun f => ?_
      erw [simulateQ_bind]
      refine bind_congr fun x => ?_
      erw [simulateQ_bind, simulateQ_runWith_sampler F .focalFirst (rest ⟨⟩) (f x)]
      refine bind_congr fun r => ?_
      erw [simulateQ_pure]
    · simp only [step, Schedule.seq, owner_plain_challenge, bind_map_left]
      erw [simulateQ_bind]
      refine bind_congr fun x => ?_
      erw [simulateQ_bind]
      refine bind_congr fun f => ?_
      erw [simulateQ_bind, simulateQ_runWith_sampler F .counterpartFirst (rest ⟨⟩) (f x)]
      refine bind_congr fun r => ?_
      erw [simulateQ_pure]

end Simulate

end Interaction.Core
