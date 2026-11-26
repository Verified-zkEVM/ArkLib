/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Protocol
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

universe v uA

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp

/-- The prover uses only the shared oracle interface, and cannot query the challenge service. -/
abbrev Prover {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {ι : Type} (ambient : OracleSpec ι) (s : FreeM P Unit)
    (Out : Transcript l s → Type) := Focal l (OracleComp ambient) s Out

/-- Interpret each prover slot through an oracle handler, node by node and at the leaf.

The recursion is the generic strategy map at this homomorphism, written out so that its node and
leaf equations are available to importing modules. -/
def Prover.simulate {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}
    {ι : Type} {ambient : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl ambient m) : {s : FreeM P Unit} →
    {Out : Transcript l s → Type} → Prover l ambient s Out → Focal l m s Out
  | .pure _, _, p => simulateQ impl p
  | .liftBind a _, _, p =>
    Choice.map .focal (owner l a) (fun _ next => Prover.simulate impl next) <$> simulateQ impl p

/-- At a leaf, simulation interprets the prover's final action. -/
theorem Prover.simulate_done {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}
    {ι : Type} {ambient : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl ambient m)
    {Out : Transcript l (Pure.pure (f := FreeM P) PUnit.unit) → Type}
    (p : Prover l ambient (Pure.pure (f := FreeM P) PUnit.unit) Out) :
    Prover.simulate impl p = (simulateQ impl p : m (Out ⟨⟩)) := rfl

/-- At a node, simulation interprets the slot and simulates every continuation. -/
theorem Prover.simulate_node {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}
    {ι : Type} {ambient : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl ambient m) (a : P.A) (rest : P.B a → FreeM P Unit)
    {Out : Transcript l (.liftBind a rest) → Type}
    (p : Prover l ambient (.liftBind a rest) Out) :
    Prover.simulate impl p =
      Choice.map .focal (owner l a) (fun _ next => Prover.simulate impl next) <$>
        simulateQ impl p := rfl

/-- Simulation interprets a computation that constructs a prover, then simulates its moves. -/
theorem Prover.simulate_joinSlot {P : PFunctor.{uA, 0}}
    {l : PFunctor.Lens P rolePoly0} {ι : Type}
    {ambient : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) {s : FreeM P Unit}
    {Out : Transcript l s → Type} (p : OracleComp ambient (Prover l ambient s Out)) :
    Prover.simulate impl (Strategy.joinSlot p) =
      Strategy.joinSlot (Prover.simulate impl <$> simulateQ impl p) := by
  cases s with
  | pure x =>
      simp only [Strategy.joinSlot, Prover.simulate, simulateQ_bind, bind_map_left, id_eq]
  | liftBind a rest =>
      rw [Prover.simulate_node]
      change _ <$> simulateQ impl (p >>= id) = (_ <$> simulateQ impl p) >>= id
      rw [simulateQ_bind, _root_.map_bind, bind_map_left]
      rfl

/-- Simulating a simulated prover composes the two handlers. -/
theorem Prover.simulate_simulate {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}
    {κ κ' : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}
    {n : Type → Type} [Monad n] [LawfulMonad n]
    (F : QueryImpl spec' n) (G : QueryImpl spec (OracleComp spec')) :
    (s : FreeM P Unit) → {Out : Transcript l s → Type} →
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
def childDraw {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {m : Type → Type v} (a : P.A) (next : P.B a → FreeM P Unit)
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) (b : P.B a)
    (c : ChallengeNode l (next b)) : m (challengeSpec l (next b) c) :=
  draw ⟨.inr ⟨b, c.val⟩, c.property⟩

/-- The challenge draw at a receiver root, taken from the draw family at the root node. -/
def rootDraw {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {m : Type → Type v} (a : P.A) (next : P.B a → FreeM P Unit)
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) (h : owner l a = .receiver) :
    m (Move l a) := draw ⟨.inl ⟨⟩, h⟩

/-- The sampler's action at one node: it passes a sender move through and makes the challenge
draw at a receiver move. The draw is any computation in `m`; the sampler assumes nothing about
its distribution. -/
def samplerNode {m : Type → Type} [Applicative m] {X : Type} {A : X → Type} :
    (role : TwoParty.Role) → (role = .receiver → m X) →
    ((x : X) → A x) → m (Choice .counterpart role X A)
  | .sender, _, next => pure next
  | .receiver, draw, next => (fun x => ⟨x, next x⟩) <$> draw rfl

section Nodes

variable {m : Type → Type} [Applicative m]

/-- At a sender node, the sampler returns the continuation unchanged. -/
private theorem cast_samplerNode_sender {X : Type} {B : X → Type} {r : TwoParty.Role}
    (h : r = .sender) (draw : r = .receiver → m X) (next : ∀ x, B x) :
    cast (congrArg (fun r => m (Choice .counterpart r X B)) h)
      (samplerNode r draw next) = pure next := by
  subst h
  rfl

/-- At a receiver node, the sampler maps the continuation over the root draw. -/
private theorem cast_samplerNode_receiver {X : Type} {B : X → Type} {r : TwoParty.Role}
    (h : r = .receiver) (draw : r = .receiver → m X) (next : ∀ x, B x) :
    cast (congrArg (fun r => m (Choice .counterpart r X B)) h)
      (samplerNode r draw next) = (fun x => ⟨x, next x⟩) <$> draw h := by
  subst h
  rfl

end Nodes

/-- Mapping the sampler's action at a node maps only its continuations. -/
theorem samplerNode_map {m : Type → Type} [Applicative m] [LawfulApplicative m]
    {X : Type} {A B : X → Type} (role : TwoParty.Role)
    (draw : role = .receiver → m X) (next : (x : X) → A x) (f : ∀ x, A x → B x) :
    Choice.map .counterpart role f <$> samplerNode role draw next =
      samplerNode role draw (fun x => f x (next x)) := by
  cases role <;> simp only [samplerNode, Choice.map, LawfulApplicative.map_pure,
    Functor.map_map]

/-- Simulation interprets the challenge draw of the sampler's action at a node. -/
theorem simulateQ_samplerNode {ι : Type} {spec : OracleSpec ι}
    {n : Type → Type} [Monad n] [LawfulMonad n] {X : Type} {A : X → Type}
    (F : QueryImpl spec n) (role : TwoParty.Role)
    (draw : role = .receiver → OracleComp spec X) (next : ∀ x, A x) :
    simulateQ F (samplerNode role draw next) =
      samplerNode role (fun h => simulateQ F (draw h)) next := by
  cases role <;> simp only [samplerNode, simulateQ_pure, simulateQ_map]

/-- A sampler that returns a pure value at each leaf. Its challenge draws depend only on the
indexed source node. -/
def samplerEnd {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {m : Type → Type} [Monad m] :
    (s : FreeM P Unit) →
    ((c : ChallengeNode l s) → m (challengeSpec l s c)) →
    PureEnd l m .counterpart s (fun _ => Unit)
  | .pure _, _ => ⟨⟩
  | .liftBind a next, draw =>
    samplerNode (owner l a) (rootDraw l a next draw) (fun x =>
      samplerEnd l (next (l.toFunB a x)) (childDraw l a next draw (l.toFunB a x)))

/-- The counterpart that makes the challenge draws, obtained by giving the sampler a pure leaf
action. The draws may be any computations. Uniform public-coin sampling is a condition on the
draw family that an interpretation supplies, not an assumption of the sampler. -/
def sampler {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {m : Type → Type} [Monad m] (s : FreeM P Unit)
    (draw : (c : ChallengeNode l s) → m (challengeSpec l s c)) :
    Counterpart l m s (fun _ => Unit) := (samplerEnd l s draw).toStrategy

/-- At a node, the sampler makes the node's challenge draw, if any, and attaches each child
sampler to the move. -/
theorem sampler_node {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {m : Type → Type} [Monad m] [LawfulApplicative m]
    (a : P.A) (next : P.B a → FreeM P Unit)
    (draw : (c : ChallengeNode l (.liftBind a next)) →
      m (challengeSpec l (.liftBind a next) c)) :
    sampler l (.liftBind a next) draw =
      Choice.map .counterpart (owner l a) (fun x (_ : Unit) =>
        sampler l (next (l.toFunB a x)) (childDraw l a next draw (l.toFunB a x))) <$>
          samplerNode (owner l a) (rootDraw l a next draw) (fun _ => PUnit.unit) := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd, samplerNode_map]
  rfl

/-- At a message node, the sampler draws nothing and continues on the sent message. -/
theorem sampler_message {M : Type → Type} [Monad M] [LawfulApplicative M] (X : Type)
    (rest : X → Protocol)
    (draw : (c : ChallengeNode plainSig (.liftBind (PlainPos.message X) rest)) →
      M (challengeSpec plainSig (.liftBind (PlainPos.message X) rest) c)) :
    sampler plainSig (.liftBind (PlainPos.message X) rest) draw =
      pure (fun x => sampler plainSig (rest x) (fun c => draw ⟨.inr ⟨x, c.val⟩, c.property⟩)) := by
  change Choice.map .counterpart .sender _ <$> pure _ = _
  erw [LawfulApplicative.map_pure]
  rfl

/-- At a challenge node, the sampler draws the challenge and continues on it. -/
theorem sampler_challenge {M : Type → Type} [Monad M] [LawfulFunctor M] (C : Type)
    (rest : PUnit → Protocol)
    (draw : (c : ChallengeNode plainSig (.liftBind (PlainPos.challenge C) rest)) →
      M (challengeSpec plainSig (.liftBind (PlainPos.challenge C) rest) c)) :
    sampler plainSig (.liftBind (PlainPos.challenge C) rest) draw =
      (fun x => ⟨x, sampler plainSig (rest ⟨⟩)
        (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)⟩) <$> draw ⟨.inl ⟨⟩, rfl⟩ := by
  change Choice.map .counterpart .receiver _ <$> (_ <$> _) = _
  erw [Functor.map_map]
  rfl

section SamplerLaws

variable {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly0}

section Sampler

variable {m : Type → Type} [Monad m]

/-- The sampler passes over a sender node. -/
private theorem sampler_sender [LawfulApplicative m] {a : P.A}
    {next : P.B a → FreeM P Unit}
    (h : owner l a = .sender)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => Unit)))) h)
      (sampler l (.liftBind a next) d) =
    pure fun x => sampler l (next (l.toFunB a x))
      fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩ := by
  rw [sampler_node, samplerNode_map]
  exact cast_samplerNode_sender h _ _

/-- The sampler draws at a receiver node, then samples the rest of the protocol. -/
private theorem sampler_receiver [LawfulFunctor m] {a : P.A}
    {next : P.B a → FreeM P Unit}
    (h : owner l a = .receiver)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => Unit)))) h)
      (sampler l (.liftBind a next) d) =
    (fun x => ⟨x, sampler l (next (l.toFunB a x))
      fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩⟩) <$> d ⟨.inl ⟨⟩, h⟩ := by
  change _ = (fun x => (⟨x, sampler l (next (l.toFunB a x))
      (childDraw l a next d (l.toFunB a x))⟩ :
      (x : Move l a) × Counterpart l m (next (l.toFunB a x)) (fun _ => Unit))) <$>
    rootDraw l a next d h
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd]
  generalize rootDraw l a next d = draw at *
  generalize owner l a = r at draw h ⊢
  subst h
  simp only [samplerNode, Choice.map, Functor.map_map]
  rfl

/-- At a sender node the prover sends a move, then the rest of the protocol runs. -/
theorem run_sampler_sender [LawfulMonad m] {β : Type} {a : P.A}
    {next : P.B a → FreeM P Unit}
    (h : owner l a = .sender) {Out : Transcript l (.liftBind a next) → Type}
    (p : Focal l m (.liftBind a next) Out)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c))
    (g : ((tr : Transcript l (.liftBind a next)) × Out tr × Unit) → m β) :
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
theorem run_sampler_receiver [LawfulMonad m] {β : Type} {a : P.A}
    {next : P.B a → FreeM P Unit}
    (h : owner l a = .receiver) {Out : Transcript l (.liftBind a next) → Type}
    (p : Focal l m (.liftBind a next) Out)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c))
    (g : ((tr : Transcript l (.liftBind a next)) × Out tr × Unit) → m β) :
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
def publicCoinSampler {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)
    {m : Type → Type} [Monad m] :
    (s : FreeM P Unit) →
    ((c : ChallengeNode l s) → m (challengeSpec l s c)) →
    PublicCoinCounterpart l m s (fun _ => Unit)
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
theorem toCounterpart_publicCoinSampler {m : Type → Type} [Monad m] [LawfulMonad m]
    (s : Protocol) (draw : (c : ChallengeNode plainSig s) → m (challengeSpec plainSig s c)) :
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
theorem toCounterpart_publicCoinOracleSampler {m : Type → Type} [Monad m] [LawfulMonad m]
    (s : OracleProtocol)
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
theorem replay_publicCoinSampler {m : Type → Type} [Monad m] [LawfulMonad m]
    (s : Protocol) (draw : (c : ChallengeNode plainSig s) → m (challengeSpec plainSig s c))
    (tr : Transcript plainSig s) :
    (publicCoinSampler plainSig s draw).replay tr = pure ⟨⟩ := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    rcases tr with ⟨x, tr⟩
    cases a with
    | message X => exact (LawfulMonad.pure_bind _ _).trans (ih x _ tr)
    | challenge C => exact ih ⟨⟩ _ tr

/-- Replay follows recorded oracle-protocol challenges and executes no draw. -/
theorem replay_publicCoinOracleSampler {m : Type → Type} [Monad m] [LawfulMonad m]
    (s : OracleProtocol)
    (draw : (c : ChallengeNode oracleSig s) → m (challengeSpec oracleSig s c))
    (tr : Transcript oracleSig s) :
    (publicCoinSampler oracleSig s draw).replay tr = pure ⟨⟩ := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    rcases tr with ⟨x, tr⟩
    cases a with
    | message X => exact (LawfulMonad.pure_bind _ _).trans (ih x _ tr)
    | challenge C => exact ih ⟨⟩ _ tr
    | oracle X I => exact (LawfulMonad.pure_bind _ _).trans (ih ⟨⟩ _ tr)

/-- A plain verifier's only operation is its final decision.

The output statement type `StmtOut p` may depend on the public shape path `p` of the run. A
verifier with one output type `T` uses the constant family `fun _ => T`.
-/
structure Verifier {ι : Type} (ambient : OracleSpec.{0, 0} ι)
    (s : Protocol) (StmtIn : Type) (StmtOut : Path s → Type) where
  /-- Decide from the public transcript after every interaction slot has run. -/
  decide : StmtIn → (p : Path s) → PlainView s p → OptionT (OracleComp ambient) (StmtOut p)

/-- An honest reduction with separately retained prover and verifier outputs. The verifier's
output statement type is indexed by the shape path. -/
structure Reduction {ι : Type} (ambient : OracleSpec ι) (s : Protocol)
    (StmtIn : Type) (WitIn : Type) (StmtOut : Path s → Type)
    (Out : Transcript plainSig s → Type) where
  /-- Honest focal strategy, including its action at the leaf. -/
  prover : StmtIn → WitIn → Prover plainSig ambient s Out
  /-- Passive final decision. -/
  verifier : Verifier ambient s StmtIn StmtOut

/-- Decide with a verifier on an accepted statement, and reject a rejected one. In a run, the
interaction still takes place after a rejected statement and the decision then rejects
(`Verifier.onAccept_run_none`). -/
def Verifier.onAccept {ι : Type} {ambient : OracleSpec.{0, 0} ι}
    {s : Protocol} {T : Type} {U : Path s → Type} (V : Verifier ambient s T U) :
    Verifier ambient s (Option T) U where
  decide mid p v := match mid with
    | none => failure
    | some t => V.decide t p v

end Interaction
