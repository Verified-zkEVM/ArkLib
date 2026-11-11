/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Protocol
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Provers and passive verifiers

Provers are PolyFun focal strategies, with an effect slot at every boundary. The sampler
only draws challenges and has pure observation slots and a pure end. The same sampler is a
PolyFun public-coin counterpart, whose replay follows recorded challenges without drawing.
A plain verifier decides once from the completed public transcript. A reduction pairs this
verifier with an honest prover.
-/

@[expose] public section

universe u v uA uι uS uW

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

/-- Simulating a simulated prover composes the two handlers. -/
theorem Prover.simulate_simulate {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {κ κ' : Type u} {spec : OracleSpec.{u, u} κ} {spec' : OracleSpec.{u, u} κ'}
    {n : Type u → Type u} [Monad n] [LawfulMonad n]
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

/-- Restrict a node-indexed draw family to a child subtree. -/
def childDraw {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type v} (a : P.A) (next : P.B a → FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) (b : P.B a)
    (c : ChallengeNode l (next b)) : m (challengeSpec l (next b) c) :=
  draw ⟨.inr ⟨b, c.val⟩, c.property⟩

/-- Draw the move at a receiver root. -/
def rootDraw {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type v} (a : P.A) (next : P.B a → FreeM P PUnit.{u + 1})
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
    {m : Type u → Type u} [Monad m] [LawfulApplicative m]
    (a : P.A) (next : P.B a → FreeM P PUnit.{u + 1})
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) :
    sampler l (.liftBind a next) draw =
      Choice.map .counterpart (owner l a) (fun x (_ : PUnit.{u + 1}) =>
        sampler l (next (l.toFunB a x)) (childDraw l a next draw (l.toFunB a x))) <$>
          samplerSlot (owner l a) (rootDraw l a next draw) (fun _ => PUnit.unit) := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd, samplerSlot_map]
  rfl

/-- At a message node, the sampler draws nothing and continues on the sent message. -/
theorem sampler_message {M : Type u → Type u} [Monad M] [LawfulApplicative M] (X : Type u)
    (rest : X → Protocol.{u})
    (draw : (c : ChallengeNode plainSig (.liftBind (PlainPos.message X) rest)) →
      M (challengeSpec plainSig (.liftBind (PlainPos.message X) rest) c)) :
    sampler plainSig (.liftBind (PlainPos.message X) rest) draw =
      pure (fun x => sampler plainSig (rest x) (fun c => draw ⟨.inr ⟨x, c.val⟩, c.property⟩)) := by
  change Choice.map .counterpart .sender _ <$> pure _ = _
  erw [LawfulApplicative.map_pure]
  rfl

/-- At a challenge node, the sampler draws the challenge and continues on it. -/
theorem sampler_challenge {M : Type u → Type u} [Monad M] [LawfulFunctor M] (C : Type u)
    (rest : PUnit → Protocol.{u})
    (draw : (c : ChallengeNode plainSig (.liftBind (PlainPos.challenge C) rest)) →
      M (challengeSpec plainSig (.liftBind (PlainPos.challenge C) rest) c)) :
    sampler plainSig (.liftBind (PlainPos.challenge C) rest) draw =
      (fun x => ⟨x, sampler plainSig (rest ⟨⟩)
        (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)⟩) <$> draw ⟨.inl ⟨⟩, rfl⟩ := by
  change Choice.map .counterpart .receiver _ <$> (_ <$> _) = _
  erw [Functor.map_map]
  rfl

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
