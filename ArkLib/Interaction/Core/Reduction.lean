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
only draws challenges and has pure observation slots and a pure end. A plain verifier decides
once from the completed public transcript. A reduction pairs this verifier with an honest prover.
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
