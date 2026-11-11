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

universe u uA uι uS uW

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp

/-- The prover uses only the shared oracle interface, and cannot query the challenge service. -/
abbrev Prover {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {ι : Type u} (ambient : OracleSpec.{u, u} ι) (s : FreeM P PUnit.{u + 1})
    (Out : PathAlong l s → Type u) := Focal l (OracleComp ambient) s Out

/-- Interpret each prover slot through an oracle handler, node by node and at the leaf.

The recursion is the generic strategy map at this homomorphism, written out so that its node and
leaf equations are available to importing modules. -/
def Prover.simulate {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {ι : Type u} {ambient : OracleSpec.{u, u} ι} {m : Type u → Type u} [Monad m]
    (impl : QueryImpl ambient m) : {s : FreeM P PUnit.{u + 1}} →
    {Out : PathAlong l s → Type u} → Prover l ambient s Out → Focal l m s Out
  | .pure _, _, p => simulateQ impl p
  | .liftBind a _, _, p =>
    Choice.map .focal (owner l a) (fun _ next => Prover.simulate impl next) <$> simulateQ impl p

/-- At a leaf, simulation interprets the terminal action. -/
theorem Prover.simulate_done {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {ι : Type u} {ambient : OracleSpec.{u, u} ι} {m : Type u → Type u} [Monad m]
    (impl : QueryImpl ambient m)
    {Out : PathAlong l (Pure.pure (f := FreeM P) PUnit.unit) → Type u}
    (p : Prover l ambient (Pure.pure (f := FreeM P) PUnit.unit) Out) :
    Prover.simulate impl p = (simulateQ impl p : m (Out ⟨⟩)) := rfl

/-- At a node, simulation interprets the slot and simulates every continuation. -/
theorem Prover.simulate_node {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {ι : Type u} {ambient : OracleSpec.{u, u} ι} {m : Type u → Type u} [Monad m]
    (impl : QueryImpl ambient m) (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : Prover l ambient (.liftBind a rest) Out) :
    Prover.simulate impl p =
      Choice.map .focal (owner l a) (fun _ next => Prover.simulate impl next) <$>
        simulateQ impl p := rfl

/-- Restrict a node-indexed draw family to a child subtree. -/
def childDraw {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} (a : P.A) (next : P.B a → FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) (b : P.B a)
    (c : ChallengeNode l (next b)) : m (challengeSpec l (next b) c) :=
  draw ⟨.inr ⟨b, c.val⟩, c.property⟩

/-- Draw the move at a receiver root. -/
def rootDraw {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} (a : P.A) (next : P.B a → FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) (h : owner l a = .receiver) :
    m (Move l a) := draw ⟨.inl ⟨⟩, h⟩

/-- A public-coin slot observes sender moves and draws receiver moves. -/
def samplerSlot {m : Type u → Type u} [Applicative m] {X : Type u} {A : X → Type u} :
    (role : TwoParty.Role) → (role = .receiver → m X) →
    ((x : X) → A x) → m (Choice .counterpart role X A)
  | .sender, _, next => pure next
  | .receiver, draw, next => (fun x => ⟨x, next x⟩) <$> draw rfl

/-- Mapping a public-coin slot maps only its continuations. -/
theorem samplerSlot_map {m : Type u → Type u} [Applicative m] [LawfulApplicative m]
    {X : Type u} {A B : X → Type u} (role : TwoParty.Role)
    (draw : role = .receiver → m X) (next : (x : X) → A x) (f : ∀ x, A x → B x) :
    Choice.map .counterpart role f <$> samplerSlot role draw next =
      samplerSlot role draw (fun x => f x (next x)) := by
  cases role <;> simp only [samplerSlot, Choice.map, LawfulApplicative.map_pure,
    Functor.map_map]

/-- Simulation interprets the draw of a public-coin slot. -/
theorem simulateQ_samplerSlot {ι : Type u} {spec : OracleSpec.{u, u} ι}
    {n : Type u → Type u} [Monad n] [LawfulMonad n] {X : Type u} {A : X → Type u}
    (F : QueryImpl spec n) (role : TwoParty.Role)
    (draw : role = .receiver → OracleComp spec X) (next : ∀ x, A x) :
    simulateQ F (samplerSlot role draw next) =
      samplerSlot role (fun h => simulateQ F (draw h)) next := by
  cases role <;> simp only [samplerSlot, simulateQ_pure, simulateQ_map]

/-- A sampler with a pure terminal payload. Its draws depend only on the indexed source node. -/
def samplerEnd {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} [Monad m] :
    (s : FreeM P PUnit.{u + 1}) →
    ((c : ChallengeNode l s) → m (challengeSpec l s c)) →
    PureEnd l m .counterpart s (fun _ => PUnit.{u + 1})
  | .pure _, _ => ⟨⟩
  | .liftBind a next, draw =>
    samplerSlot (owner l a) (rootDraw l a next draw) (fun x =>
      samplerEnd l (next (l.toFunB a x)) (childDraw l a next draw (l.toFunB a x)))

/-- Public-coin counterpart obtained by giving the sampler a pure leaf action. -/
def sampler {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} [Monad m] (s : FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l s) → m (challengeSpec l s c)) :
    Counterpart l m s (fun _ => PUnit.{u + 1}) := (samplerEnd l s draw).toStrategy

/-- At a node, the sampler attaches each child sampler to its public-coin slot. -/
theorem sampler_node {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (a : P.A) (next : P.B a → FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) :
    sampler l (.liftBind a next) draw =
      Choice.map .counterpart (owner l a) (fun x (_ : PUnit.{u + 1}) =>
        sampler l (next (l.toFunB a x)) (childDraw l a next draw (l.toFunB a x))) <$>
          samplerSlot (owner l a) (rootDraw l a next draw) (fun _ => PUnit.unit) := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd, samplerSlot_map]
  rfl

section SamplerLaws

variable {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly}

section Sampler

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- A sender slot built by rewriting with an ownership equation is its pure payload. -/
private theorem cast_map_pure_sender {X : Type} {B B' : X → Type} {r : TwoParty.Role}
    (h : r = .sender) (e : Choice .counterpart r X B = ((x : X) → B x)) (G : (x : X) → B x)
    (Φ : ∀ x, B x → B' x) :
    cast (congrArg (fun r => m (Choice .counterpart r X B')) h)
      (Choice.map .counterpart r Φ <$> (pure (Eq.mpr e G) : m _)) = pure fun x => Φ x (G x) := by
  subst h
  exact map_pure _ _

/-- A receiver slot built by rewriting with an ownership equation maps its draw. -/
private theorem cast_map_map_receiver {X : Type} {B B' : X → Type} {r : TwoParty.Role}
    (h : r = .receiver) (e : Choice .counterpart r X B = ((x : X) × B x))
    (G : X → (x : X) × B x) (mx : m X) (Φ : ∀ x, B x → B' x) :
    cast (congrArg (fun r => m (Choice .counterpart r X B')) h)
      (Choice.map .counterpart r Φ <$> ((fun x => Eq.mpr e (G x)) <$> mx)) =
        (fun x => ⟨(G x).1, Φ _ (G x).2⟩) <$> mx := by
  subst h
  exact Functor.map_map _ _ _

/-- The sampler passes over a sender node. -/
private theorem sampler_sender {a : P.A} {next : P.B a → FreeM P PUnit} (h : owner l a = .sender)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => PUnit)))) h)
      (sampler l (.liftBind a next) d) =
    pure fun x => sampler l (next (l.toFunB a x))
      fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩ := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd]
  split
  · exact cast_map_pure_sender h _ _ _
  · rename_i h'
    cases h.symm.trans h'

/-- The sampler draws at a receiver node, then samples the rest of the protocol. -/
private theorem sampler_receiver {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .receiver)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => PUnit)))) h)
      (sampler l (.liftBind a next) d) =
    (fun x => ⟨x, sampler l (next (l.toFunB a x))
      fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩⟩) <$> d ⟨.inl ⟨⟩, h⟩ := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd]
  split
  · rename_i h'
    cases h.symm.trans h'
  · exact cast_map_map_receiver h _ (fun x => ⟨x, _⟩) _ _

/-- At a sender node the prover sends a move, then the rest of the protocol runs. -/
theorem run_sampler_sender {β : Type} {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .sender) {Out : PathAlong l (.liftBind a next) → Type}
    (p : Focal l m (.liftBind a next) Out)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c))
    (g : ((tr : PathAlong l (.liftBind a next)) × Out tr × PUnit) → m β) :
    (TwoParty.Lens.run (.liftBind a next) p (sampler l _ d) >>= g) =
      (cast (congrArg (fun r => m (Choice .focal r (Move l a)
          (fun x => Focal l m (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)))) h) p >>= fun v =>
        TwoParty.Lens.run (next (l.toFunB a v.1)) v.2
          (sampler l _ fun c => d ⟨.inr ⟨l.toFunB a v.1, c.val⟩, c.property⟩) >>= fun r =>
            g ⟨⟨v.1, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [run_node, step_bind]
  refine (step_sender (owner l a) h _ _ _).trans ?_
  refine bind_congr fun v => ?_
  refine (congrArg (· >>= _) (sampler_sender h d)).trans ?_
  simp only [bind_assoc]
  exact (LawfulMonad.pure_bind (m := m) _ _).trans
    (bind_congr fun _ => LawfulMonad.pure_bind (m := m) _ _)

/-- At a receiver node the prover fixes a reply to each move, the move is drawn, then the rest of
the protocol runs. -/
theorem run_sampler_receiver {β : Type} {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .receiver) {Out : PathAlong l (.liftBind a next) → Type}
    (p : Focal l m (.liftBind a next) Out)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c))
    (g : ((tr : PathAlong l (.liftBind a next)) × Out tr × PUnit) → m β) :
    (TwoParty.Lens.run (.liftBind a next) p (sampler l _ d) >>= g) =
      (cast (congrArg (fun r => m (Choice .focal r (Move l a)
          (fun x => Focal l m (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)))) h) p >>= fun f =>
        (d ⟨.inl ⟨⟩, h⟩ : m (Move l a)) >>= fun x =>
        TwoParty.Lens.run (next (l.toFunB a x)) (f x)
          (sampler l _ fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) >>= fun r =>
            g ⟨⟨x, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [run_node, step_bind]
  refine (step_receiver (owner l a) h _ _ _).trans ?_
  refine bind_congr fun f => ?_
  refine (congrArg (· >>= _) (sampler_receiver h d)).trans ?_
  simp only [bind_assoc]
  exact (bind_map_left (m := m) _ _ _).trans
    (bind_congr fun _ => bind_congr fun _ => LawfulMonad.pure_bind (m := m) _ _)

end Sampler

end SamplerLaws

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

/-- A plain verifier's only operation is its terminal decision.

The output statement type `StmtOut p` may depend on the public shape path `p` of the run. A
verifier with one output type `T` uses the constant family `fun _ => T`.
-/
structure Verifier {ι : Type uι} (ambient : OracleSpec.{uι, u} ι)
    (s : Protocol.{u}) (StmtIn : Type uS) (StmtOut : Path s → Type u) where
  /-- Decide from the public transcript after every interaction slot has run. -/
  decide : StmtIn → (p : Path s) → PlainView s p → OptionT (OracleComp ambient) (StmtOut p)

/-- An honest reduction with separately retained prover and verifier outputs. The verifier's
output statement type is indexed by the shape path. -/
structure Reduction {ι : Type u} (ambient : OracleSpec.{u, u} ι) (s : Protocol.{u})
    (StmtIn : Type uS) (WitIn : Type uW) (StmtOut : Path s → Type u)
    (Out : PathAlong plainSig s → Type u) where
  /-- Honest focal strategy, including its terminal action. -/
  prover : StmtIn → WitIn → Prover plainSig ambient s Out
  /-- Passive terminal decision. -/
  verifier : Verifier ambient s StmtIn StmtOut

/-- Run a verifier only on an accepted statement; a rejected statement stays rejected. -/
def Verifier.onAccept {ι : Type uι} {ambient : OracleSpec.{uι, u} ι}
    {s : Protocol.{u}} {T : Type uS} {U : Path s → Type u} (V : Verifier ambient s T U) :
    Verifier ambient s (Option T) U where
  decide mid p v := match mid with
    | none => failure
    | some t => V.decide t p v

end Interaction.Core
