/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Protocol
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Provers and passive verifiers

Provers are PolyFun focal strategies, with an effect slot at every boundary. The sampler
only draws challenges and has pure observation slots and a pure end. The same sampler is a
PolyFun public-coin counterpart, whose replay follows recorded challenges without drawing.
A plain verifier decides once from the completed public transcript. A reduction pairs this
verifier with an honest prover.
-/

@[expose] public section

universe u uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp

/-- The prover uses only the shared oracle interface, and cannot query the challenge service. -/
abbrev Prover {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {ι : Type u} (ambient : OracleSpec.{u, u} ι) (s : FreeM P PUnit.{u + 1})
    (Out : PathAlong l s → Type u) := Focal l (OracleComp ambient) s Out

/-- Interpret each prover slot through an oracle handler using the generic strategy map. -/
def Prover.simulate {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {ι : Type u} {ambient : OracleSpec.{u, u} ι} {m : Type u → Type u} [Monad m]
    (impl : QueryImpl ambient m) {s : FreeM P PUnit.{u + 1}}
    {Out : PathAlong l s → Type u} (p : Prover l ambient s Out) : Focal l m s Out :=
  StrategyOver.map
    (show StrategyOver.Hom (paired l (OracleComp ambient)) .focal (paired l m) .focal from
      { mapNode := fun {pos} {_} {_} {_} f node =>
          Choice.map .focal (owner l pos) f <$> simulateQ impl node })
    (fun _ => simulateQ impl) p

/-- A sampler with a pure terminal payload. Its draws depend only on the indexed source node. -/
def samplerEnd {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} [Monad m] :
    (s : FreeM P PUnit.{u + 1}) →
    ((c : ChallengeNode l s) → m (challengeSpec l s c)) →
    PureEnd l m .counterpart s (fun _ => PUnit.{u + 1})
  | .pure _, _ => ⟨⟩
  | .liftBind a next, draw =>
    match h : owner l a with
    | .sender => by
      exact pure (show Choice .counterpart (owner l a) (Move l a)
        (fun x => PureEnd l m .counterpart (next (l.toFunB a x)) (fun _ => PUnit)) from by
        rw [h]
        exact fun x => samplerEnd l (next (l.toFunB a x))
          (fun c => draw ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩))
    | .receiver => by
      exact (fun x => show Choice .counterpart (owner l a) (Move l a)
        (fun x => PureEnd l m .counterpart (next (l.toFunB a x)) (fun _ => PUnit)) from by
          rw [h]
          exact ⟨x, samplerEnd l (next (l.toFunB a x))
            (fun c => draw ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)⟩) <$>
        draw ⟨.inl ⟨⟩, h⟩

/-- Public-coin counterpart obtained by giving the sampler a pure leaf action. -/
def sampler {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} [Monad m] (s : FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l s) → m (challengeSpec l s c)) :
    Counterpart l m s (fun _ => PUnit.{u + 1}) := (samplerEnd l s draw).toStrategy

/-- The sampler as a PolyFun public-coin counterpart, exposing each draw beside its continuation.

Its conversion to an ordinary counterpart is the runner's sampler, and replaying it follows
recorded challenges without executing any draw.
-/
def publicCoinSampler {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} [Monad m] :
    (s : FreeM P PUnit.{u + 1}) →
    ((c : ChallengeNode l s) → m (challengeSpec l s c)) →
    PublicCoinCounterpart l m s (fun _ => PUnit.{u + 1})
  | .pure _, _ => pure ⟨⟩
  | .liftBind a next, draw =>
    match h : owner l a with
    | .sender => by
      simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using
        (pure fun x => publicCoinSampler l (next (l.toFunB a x))
            (fun c => draw ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) :
          m ((x : Move l a) → PublicCoinCounterpart l m (next (l.toFunB a x))
            (fun _ => PUnit)))
    | .receiver => by
      simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using
        ((draw ⟨.inl ⟨⟩, h⟩, fun x => publicCoinSampler l (next (l.toFunB a x))
            (fun c => draw ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)) :
          m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m (next (l.toFunB a x))
            (fun _ => PUnit)))

/-- The public-coin presentation converts to the plain runner's sampler. -/
theorem toCounterpart_publicCoinSampler {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s : Protocol.{u}) (draw : (c : ChallengeNode plainSig s) → m (challengeSpec plainSig s c)) :
    (publicCoinSampler plainSig s draw).toCounterpart = sampler plainSig s draw := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    cases a with
    | message X =>
      refine Eq.trans (b := pure fun x => (publicCoinSampler plainSig (next x)
        (fun c => draw ⟨.inr ⟨x, c.val⟩, c.property⟩)).toCounterpart)
        (LawfulMonad.pure_bind _ _) ?_
      refine Eq.trans ?_ (LawfulApplicative.map_pure _ _).symm
      congr 1
      funext x
      exact ih x _
    | challenge C =>
      refine Eq.trans (b := draw ⟨.inl ⟨⟩, rfl⟩ >>= fun x =>
        pure ⟨x, (publicCoinSampler plainSig (next ⟨⟩)
          (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)).toCounterpart⟩) rfl ?_
      refine Eq.trans ?_ (Functor.map_map _ _ _).symm
      rw [map_eq_bind_pure_comp]
      congr 1
      funext x
      exact congrArg _ (congrArg _ (ih ⟨⟩ _))

/-- The public-coin presentation converts to the oracle runner's sampler. -/
theorem toCounterpart_publicCoinOracleSampler {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s : OracleProtocol.{u})
    (draw : (c : ChallengeNode oracleSig s) → m (challengeSpec oracleSig s c)) :
    (publicCoinSampler oracleSig s draw).toCounterpart = sampler oracleSig s draw := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    cases a with
    | message X =>
      refine Eq.trans (b := pure fun x => (publicCoinSampler oracleSig (next x)
        (fun c => draw ⟨.inr ⟨x, c.val⟩, c.property⟩)).toCounterpart)
        (LawfulMonad.pure_bind _ _) ?_
      refine Eq.trans ?_ (LawfulApplicative.map_pure _ _).symm
      congr 1
      funext x
      exact ih x _
    | challenge C =>
      refine Eq.trans (b := draw ⟨.inl ⟨⟩, rfl⟩ >>= fun x =>
        pure ⟨x, (publicCoinSampler oracleSig (next ⟨⟩)
          (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)).toCounterpart⟩) rfl ?_
      refine Eq.trans ?_ (Functor.map_map _ _ _).symm
      rw [map_eq_bind_pure_comp]
      congr 1
      funext x
      exact congrArg _ (congrArg _ (ih ⟨⟩ _))
    | oracle X I =>
      refine Eq.trans (b := pure fun _ => (publicCoinSampler oracleSig (next ⟨⟩)
        (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)).toCounterpart)
        (LawfulMonad.pure_bind _ _) ?_
      refine Eq.trans ?_ (LawfulApplicative.map_pure _ _).symm
      congr 1
      funext x
      exact ih ⟨⟩ _

/-- Replay follows recorded plain challenges and executes no draw, even a failing one. -/
theorem replay_publicCoinSampler {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s : Protocol.{u}) (draw : (c : ChallengeNode plainSig s) → m (challengeSpec plainSig s c))
    (tr : PathAlong plainSig s) :
    (publicCoinSampler plainSig s draw).replay tr = pure ⟨⟩ := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    rcases tr with ⟨x, tr⟩
    cases a with
    | message X => exact (LawfulMonad.pure_bind _ _).trans (ih x _ tr)
    | challenge C => exact ih ⟨⟩ _ tr

/-- Replay follows recorded oracle-protocol challenges and executes no draw. -/
theorem replay_publicCoinOracleSampler {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s : OracleProtocol.{u})
    (draw : (c : ChallengeNode oracleSig s) → m (challengeSpec oracleSig s c))
    (tr : PathAlong oracleSig s) :
    (publicCoinSampler oracleSig s draw).replay tr = pure ⟨⟩ := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    rcases tr with ⟨x, tr⟩
    cases a with
    | message X => exact (LawfulMonad.pure_bind _ _).trans (ih x _ tr)
    | challenge C => exact ih ⟨⟩ _ tr
    | oracle X I => exact (LawfulMonad.pure_bind _ _).trans (ih ⟨⟩ _ tr)

/-- A plain verifier's only operation is its terminal decision. -/
structure Verifier {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (s : Protocol.{u}) (StmtIn StmtOut : Type u) where
  /-- Decide from the public transcript after every interaction slot has run. -/
  decide : StmtIn → (p : Path s) → PlainView s p → OptionT (OracleComp ambient) StmtOut

/-- An honest reduction with separately retained prover and verifier outputs. -/
structure Reduction {ι : Type u} (ambient : OracleSpec.{u, u} ι) (s : Protocol.{u})
    (StmtIn WitIn StmtOut : Type u) (Out : PathAlong plainSig s → Type u) where
  /-- Honest focal strategy, including its terminal action. -/
  prover : StmtIn → WitIn → Prover plainSig ambient s Out
  /-- Passive terminal decision. -/
  verifier : Verifier ambient s StmtIn StmtOut

end Interaction.Core
