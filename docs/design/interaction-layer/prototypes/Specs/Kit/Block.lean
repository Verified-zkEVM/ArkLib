/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.Implications

/-!
# Message blocks of the proof kit

A *message block* is a list of prover messages. Each message is either a plain message, which the
verifier reads in full and which may select a branch of the tree, or an oracle message with its
query interface, which the verifier reads only through queries. A round of the kit
(`Specs.Kit.Iteration`) is a block followed by one challenge, and an iteration has a prefix block
before its first round and a suffix block after its last.

This module provides the block and everything the kit needs to work through a block once:

* the tree `Block.then ms rest`, which sends the messages of `ms` in order and continues with
  `rest`;
* the values of a block (`Block.Values`), what the verifier's view keeps of them
  (`Block.ViewValues`), the oracle bundle of its oracle messages (`Block.bundle`) and that
  bundle's data (`Block.data`);
* splitting a transcript of `Block.then ms rest` into the block's values and a transcript of
  `rest` (`Block.split`, `Block.splitView`, `Block.join`);
* routing the oracle messages of a path through `Block.then ms rest` into the block's bundle and
  the bundle of the rest (`Block.route`);
* the challenge nodes and draws of `Block.then ms rest`: a block has no challenge node of its own
  (`Block.tailNode`, `Block.noChallenge`), and a draw restricts to the rest (`Block.restrictDraw`)
  and extends from it (`Block.lift`);
* walking a state function through the block (`Block.walk`) and its lemmas: at the root it is the
  block's starting proposition (`Block.walk_root`), its sender moves and challenge flips compose
  block by block (`Block.Flips`, `Block.walk_flips`, `Block.walk_flips_tail`), and at a leaf it is
  what the rest says (`Block.walk_leaf`);
* one challenge followed by `rest` (`chalThen`) with the same operations (`Chal.walk`,
  `Chal.walk_flips`, `Chal.walk_leaf`, `Chal.lift`).

## Design choices

* **A block is a list.** The kit's round needs any number of messages, each plain or oracle, with
  types that may depend on the round. A `List Msg` gives all of this, and every operation is a
  structural recursion over the list. The tree `Block.then` continues with a constant
  `fun _ => rest`, so a plain message never changes the shape of the rest of the tree; shape
  selection by a message belongs to the spec layer's branch nodes (design section 8), not to the
  kit.
* **Routes into a path-independent bundle.** The oracle messages that a verifier may query along a
  path `p` form `oracleMessageBundle s p`, whose type depends on `p`. A block's own bundle does
  not. `Block.route` maps the first to the block's bundle and the rest's bundle once, and the
  lemma `Block.route_f` computes the materialized data from the transcript with a right-hand side
  that does not depend on the path. Statements about the verifier therefore never transport data
  along a path equation.
* **State functions are walked in continuation-passing style.** `Block.walk ms inside after`
  stays at `inside` while the block is incomplete and hands the block's values to `after` once it
  is complete. The three lemmas of a state function (sender moves, challenges, leaves) are proved
  once for a block by induction on the list, and the iteration only composes them.
* **Spines are cased with the `cases` tactic.** v0 recorded that a term-mode match on cursor spines
  does not reduce when the partial transcript is a variable (v0, open problem 3). `Block.walk`
  follows the working pattern of v0 and `Sumcheck.foldPrefix`.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec MeasureTheory

/-! ## Messages -/

/-- One prover message: a plain message, which the verifier reads in full, or an oracle message
with its query interface, which the verifier reads only through queries. -/
inductive Msg : Type 1
  | plain (X : Type)
  | oracle (X : Type) (I : OracleInterface X)

namespace Msg

/-- The tree position of a message. -/
@[reducible]
def pos : Msg → OraclePos
  | plain X => .message X
  | oracle X I => .oracle X I

/-- The value of a message. -/
@[reducible]
def Val (m : Msg) : Type := Move oracleSig m.pos

/-- What the verifier's view keeps of a message: the value of a plain message, a marker for an
oracle message. -/
@[reducible]
def ViewVal (m : Msg) : Type := Move viewSig m.pos

/-- Forget the payload of an oracle message. -/
def erase (m : Msg) (x : m.Val) : m.ViewVal := eraseOracle.map m.pos x

/-- Every message belongs to the prover. -/
theorem owner_pos (m : Msg) : owner oracleSig m.pos = .sender := by
  cases m <;> rfl

/-- No message position is a challenge position. -/
theorem not_receiver (m : Msg) (h : owner oracleSig m.pos = .receiver) : False := by
  rw [owner_pos] at h
  cases h

end Msg

/-! ## Blocks -/

/-- A block of prover messages, sent in order. -/
abbrev Block := List Msg

/-- The tree that sends the messages of `ms` in order and continues with `rest`. -/
def Block.then : Block → OracleProtocol → OracleProtocol
  | [], rest => rest
  | m :: ms, rest => .liftBind m.pos fun _ => Block.then ms rest

namespace Block

/-- The values of the messages of a block. -/
def Values : Block → Type
  | [] => PUnit
  | m :: ms => m.Val × Values ms

/-- What the verifier's view keeps of the messages of a block. -/
def ViewValues : Block → Type
  | [] => PUnit
  | m :: ms => m.ViewVal × ViewValues ms

/-- Forget the oracle payloads of a block's values. -/
def erase : (ms : Block) → ms.Values → ms.ViewValues
  | [], _ => ⟨⟩
  | m :: ms, (x, xs) => (m.erase x, erase ms xs)

/-- The oracle bundle of the oracle messages of a block, in order. It has the shape of
`oracleMessageBundle`: a plain message adds nothing, an oracle message adds its interface on the
left. -/
@[reducible]
def bundle : Block → OracleBundle
  | [] => .empty
  | .plain _ :: ms => bundle ms
  | .oracle X I :: ms => (OracleBundle.of X I).sum (bundle ms)

/-- The data of a block's bundle: its oracle messages. -/
def data : (ms : Block) → ms.Values → (bundle ms).Data
  | [], _ => ()
  | .plain _ :: ms, (_, xs) => data ms xs
  | .oracle _ _ :: ms, (x, xs) => (x, data ms xs)

variable {rest : OracleProtocol}

/-- Split a transcript of `ms.then rest` into the block's values and a transcript of `rest`. -/
def split : (ms : Block) → Transcript oracleSig (ms.then rest) →
    ms.Values × Transcript oracleSig rest
  | [], tr => (⟨⟩, tr)
  | _ :: ms, ⟨x, tr⟩ => ((x, (split ms tr).1), (split ms tr).2)

/-- Split a view transcript of `ms.then rest` into the view of the block and a view transcript of
`rest`. -/
def splitView : (ms : Block) → Transcript viewSig (ms.then rest) →
    ms.ViewValues × Transcript viewSig rest
  | [], tr => (⟨⟩, tr)
  | _ :: ms, ⟨x, tr⟩ => ((x, (splitView ms tr).1), (splitView ms tr).2)

/-- Join a block's values and a transcript of `rest`. -/
def join : (ms : Block) → ms.Values → Transcript oracleSig rest →
    Transcript oracleSig (ms.then rest)
  | [], _, tr => tr
  | _ :: ms, (x, xs), tr => ⟨x, join ms xs tr⟩

@[simp]
theorem split_join : ∀ (ms : Block) (xs : ms.Values) (tr : Transcript oracleSig rest),
    split ms (join ms xs tr) = (xs, tr)
  | [], ⟨⟩, _ => rfl
  | _ :: ms, (x, xs), tr => by
    change ((x, (split ms (join ms xs tr)).1), (split ms (join ms xs tr)).2) = _
    rw [split_join ms xs tr]
    rfl

/-- The view of a transcript splits into the erased values and the view of the rest. -/
theorem splitView_erase : ∀ (ms : Block) (tr : Transcript oracleSig (ms.then rest)),
    splitView ms (Transcript.mapMoves eraseOracle tr) =
      (erase ms (split ms tr).1, Transcript.mapMoves eraseOracle (split ms tr).2)
  | [], _ => rfl
  | .plain _ :: ms, ⟨x, tr⟩ => by
    change ((Msg.erase _ x, (splitView ms (Transcript.mapMoves eraseOracle tr)).1),
      (splitView ms (Transcript.mapMoves eraseOracle tr)).2) = _
    rw [splitView_erase ms tr]
    rfl
  | .oracle _ _ :: ms, ⟨x, tr⟩ => by
    change ((Msg.erase _ x, (splitView ms (Transcript.mapMoves eraseOracle tr)).1),
      (splitView ms (Transcript.mapMoves eraseOracle tr)).2) = _
    rw [splitView_erase ms tr]
    rfl

/-! ## Routing oracle messages -/

/-- The path through `rest` that a path through `ms.then rest` continues with. -/
def tailPath : (ms : Block) → Path (ms.then rest) → Path rest
  | [], p => p
  | _ :: ms, ⟨_, p⟩ => tailPath ms p

/-- Route the oracle messages of a path through `ms.then rest` into the block's bundle and a
bundle `F` that the oracle messages of every path through `rest` route into. -/
def route : (ms : Block) → {F : OracleBundle} →
    ((p : Path rest) → OracleMap (oracleMessageBundle rest p) F) →
    (p : Path (ms.then rest)) → OracleMap (oracleMessageBundle (ms.then rest) p) ((bundle ms).sum F)
  | [], F, R, p => (OracleMap.emptyLeft F).comp (R p)
  | .plain _ :: ms, _, R, ⟨_, p⟩ => route ms R p
  | .oracle X I :: ms, _, R, ⟨_, p⟩ =>
      (OracleMap.sumAssocSymm _ _ _).comp ((OracleMap.id (OracleBundle.of X I)).par (route ms R p))

/-- **The route on a transcript.** Routing the oracle messages of a transcript gives the block's
data and the routed data of the rest. The right-hand side does not depend on the path. -/
theorem route_f : ∀ (ms : Block) {F : OracleBundle}
    (R : (p : Path rest) → OracleMap (oracleMessageBundle rest p) F)
    (tr : Transcript oracleSig (ms.then rest)),
    (route ms R (Transcript.path tr)).f (oracleMessages _ tr) =
      (data ms (split ms tr).1,
        (R (Transcript.path (split ms tr).2)).f (oracleMessages rest (split ms tr).2))
  | [], _, _, _ => rfl
  | .plain _ :: ms, _, R, ⟨_, tr⟩ => route_f ms R tr
  | .oracle _ _ :: ms, _, R, ⟨x, tr⟩ => by
    change ((x, ((route ms R (Transcript.path tr)).f (oracleMessages _ tr)).1),
      ((route ms R (Transcript.path tr)).f (oracleMessages _ tr)).2) = _
    rw [route_f ms R tr]
    rfl

/-! ## Challenge nodes -/

/-- The challenge node of `rest` that a challenge node of `ms.then rest` lies on. A block has no
challenge node of its own. -/
def tailNode : (ms : Block) → ChallengeNode oracleSig (ms.then rest) →
    ChallengeNode oracleSig rest
  | [], c => c
  | m :: _, ⟨.inl _, h⟩ => (m.not_receiver h).elim
  | _ :: ms, ⟨.inr ⟨_, c⟩, h⟩ => tailNode ms ⟨c, h⟩

/-- A block followed by the end of the protocol has no challenge node. -/
theorem noChallenge : (ms : Block) → ChallengeNode oracleSig (ms.then (.pure PUnit.unit)) → False
  | [], ⟨c, _⟩ => nomatch c
  | m :: _, ⟨.inl _, h⟩ => m.not_receiver h
  | _ :: ms, ⟨.inr ⟨_, c⟩, h⟩ => noChallenge ms ⟨c, h⟩

/-- The draw at the challenge nodes of `rest`, after the block's values `xs`. -/
def restrictDraw : (ms : Block) → ms.Values →
    QueryImpl (challengeSpec oracleSig (ms.then rest)) ProbComp →
    QueryImpl (challengeSpec oracleSig rest) ProbComp
  | [], _, draw => draw
  | m :: ms, (x, xs), draw =>
      restrictDraw ms xs (fun c => draw ⟨.inr ⟨oracleSig.toFunB m.pos x, c.1⟩, c.2⟩)

/-- Extend a draw at the challenge nodes of `rest` to `ms.then rest`. A block has no challenge
node of its own. -/
def lift : (ms : Block) → QueryImpl (challengeSpec oracleSig rest) ProbComp →
    QueryImpl (challengeSpec oracleSig (ms.then rest)) ProbComp
  | [], g => g
  | m :: ms, g => fun c => match c with
    | ⟨.inl _, h⟩ => (m.not_receiver h).elim
    | ⟨.inr ⟨_, c⟩, h⟩ => lift ms g ⟨c, h⟩

/-- Restricting an extended draw gives back the draw. -/
theorem restrictDraw_lift (g : QueryImpl (challengeSpec oracleSig rest) ProbComp) :
    ∀ (ms : Block) (xs : ms.Values), restrictDraw ms xs (lift ms g) = g
  | [], _ => rfl
  | _ :: ms, (_, xs) => restrictDraw_lift g ms xs

/-- A function on the challenge nodes of `rest`, after the block's values `xs`. -/
def restrict {α : Type} : (ms : Block) → ms.Values →
    (ChallengeNode oracleSig (ms.then rest) → α) → ChallengeNode oracleSig rest → α
  | [], _, g => g
  | m :: ms, (x, xs), g =>
      restrict ms xs (fun c => g ⟨.inr ⟨oracleSig.toFunB m.pos x, c.1⟩, c.2⟩)

/-- Restricting a function of the tail node gives back the function. -/
theorem restrict_tailNode {α : Type} (g : ChallengeNode oracleSig rest → α) :
    ∀ (ms : Block) (xs : ms.Values), restrict ms xs (fun c => g (tailNode ms c)) = g
  | [], _ => rfl
  | _ :: ms, (_, xs) => restrict_tailNode g ms xs

/-- Summing a function of the tail node over the challenge nodes of a path sums it over the
challenge nodes of the rest of the path. -/
theorem sum_challengeNodesOn (g : ChallengeNode oracleSig rest → ℝ≥0∞) :
    ∀ (ms : Block) (p : Path (ms.then rest)),
    ∑ c ∈ challengeNodesOn oracleSig (ms.then rest) p, g (tailNode ms c) =
      ∑ c ∈ challengeNodesOn oracleSig rest (tailPath ms p), g c
  | [], _ => rfl
  | .plain _ :: ms, ⟨_, p⟩ => by
    simp only [Block.then, challengeNodesOn, owner, oracleSig]
    exact (Finset.sum_map _ _ _).trans (sum_challengeNodesOn g ms p)
  | .oracle _ _ :: ms, ⟨_, p⟩ => by
    simp only [Block.then, challengeNodesOn, owner, oracleSig]
    exact (Finset.sum_map _ _ _).trans (sum_challengeNodesOn g ms p)

/-! ## Walking a state function through a block -/

/-- A predicate on the positions of a tree: a cursor spine and the full moves made along it. -/
abbrev SpineProp (t : OracleProtocol) : Type 1 :=
  ∀ {u : OracleProtocol}, (sp : Cursor.Spine t u) → PartialTranscriptAt oracleSig sp → Prop

/-- Walk a state function through a block: it is `inside` until the block is complete and
`after xs` on the rest, where `xs` are the block's values. -/
def walk : (ms : Block) → Prop → (ms.Values → SpineProp rest) → SpineProp (ms.then rest)
  | [], _, after => fun sp history => after ⟨⟩ sp history
  | _ :: ms, inside, after => fun sp history => by
    cases sp with
    | root => exact inside
    | down _ tail => exact walk ms inside (fun xs => after (history.1.1, xs)) tail history.2

/-- At the start of a block the walk is `inside`, or the block is empty and the walk is `after`. -/
theorem walk_root {inside : Prop} :
    ∀ (ms : Block) {after : ms.Values → SpineProp rest},
    walk ms inside after (.root _) ⟨⟩ → inside ∨ ∃ xs, after xs (.root rest) ⟨⟩
  | [], _, h => .inr ⟨⟨⟩, h⟩
  | _ :: _, _, h => .inl h

/-- The walk starts at `inside` when every continuation starts at `inside`. -/
theorem walk_root_eq {inside : Prop} :
    ∀ (ms : Block) {after : ms.Values → SpineProp rest},
    (∀ xs, after xs (.root rest) ⟨⟩ = inside) → walk ms inside after (.root _) ⟨⟩ = inside
  | [], _, h => h ⟨⟩
  | _ :: _, _, _ => rfl

/-- The probability bounds of a state function on a tree, for one statement: a prover message
never makes a false state function true, and at every challenge the draw `draw` makes it true
with probability at most the error `E` of the challenge's node. -/
structure Flips (t : OracleProtocol) (F : SpineProp t)
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (E : ChallengeNode oracleSig t → ℝ≥0∞) : Prop where
  send : ∀ {a : OraclePos} {next : OraclePoly.B a → OracleProtocol}
    (sp : Cursor.Spine t (.liftBind a next)) (history : PartialTranscriptAt oracleSig sp),
    owner oracleSig a = .sender → ¬ F sp history → ∀ x,
      ¬ F (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
        (PartialTranscriptAt.snoc oracleSig sp history x)
  flip : ∀ {a : OraclePos} {next : OraclePoly.B a → OracleProtocol}
    (sp : Cursor.Spine t (.liftBind a next)) (hrecv : owner oracleSig a = .receiver)
    (history : PartialTranscriptAt oracleSig sp),
    letI : MeasurableSpace (Move oracleSig a) := ⊤
    𝒟[sampleAt oracleSig draw sp hrecv]
      {x | ¬ F sp history ∧ F (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
        (PartialTranscriptAt.snoc oracleSig sp history x)} ≤ E (spineChallenge oracleSig sp hrecv)

/-- At a leaf the state function holds whenever `G` holds of the completed transcript. -/
def LeafOK (t : OracleProtocol) (F : SpineProp t) (G : Transcript oracleSig t → Prop) : Prop :=
  ∀ (sp : Cursor.Spine t (.pure PUnit.unit)) (history : PartialTranscriptAt oracleSig sp),
    G (PartialTranscriptAt.complete oracleSig sp history) → F sp history

/-- A walk that starts false stays false at the end of the block when every continuation starts
false. -/
theorem walk_root_not {inside : Prop} :
    ∀ (ms : Block) {after : ms.Values → SpineProp rest},
    ¬ inside → (∀ xs, ¬ after xs (.root rest) ⟨⟩) → ¬ walk ms inside after (.root _) ⟨⟩
  | [], _, _, hafter => hafter ⟨⟩
  | _ :: _, _, hin, _ => hin

/-- **Walking preserves the probability bounds.** If every continuation satisfies them, with the
draw and the errors restricted to the rest, and starts false whenever `inside` is false, the walk
satisfies them. -/
theorem walk_flips {inside : Prop} :
    ∀ (ms : Block) {after : ms.Values → SpineProp rest}
      {draw : QueryImpl (challengeSpec oracleSig (ms.then rest)) ProbComp}
      {E : ChallengeNode oracleSig (ms.then rest) → ℝ≥0∞},
    (∀ xs, ¬ inside → ¬ after xs (.root rest) ⟨⟩) →
    (∀ xs, Flips rest (after xs) (restrictDraw ms xs draw) (restrict ms xs E)) →
      Flips (ms.then rest) (walk ms inside after) draw E
  | [], _, _, _, _, hafter => hafter ⟨⟩
  | m :: ms, after, draw, E, hin, hafter => by
    have ih := fun (x : m.Val) => walk_flips (inside := inside) ms
      (after := fun xs => after (x, xs))
      (draw := fun c => draw ⟨.inr ⟨oracleSig.toFunB m.pos x, c.1⟩, c.2⟩)
      (E := fun c => E ⟨.inr ⟨oracleSig.toFunB m.pos x, c.1⟩, c.2⟩)
      (fun xs => hin (x, xs)) (fun xs => hafter (x, xs))
    refine ⟨fun sp history hown hfalse x => ?_, fun sp hrecv history => ?_⟩
    · cases sp with
      | root =>
        exact walk_root_not ms hfalse fun xs => hin (x, xs) hfalse
      | down b tail =>
        obtain ⟨⟨y, rfl⟩, rest⟩ := history
        exact (ih y).send tail rest hown hfalse x
    · cases sp with
      | root => exact (m.not_receiver hrecv).elim
      | down b tail =>
        obtain ⟨⟨y, rfl⟩, rest⟩ := history
        exact (ih y).flip tail hrecv rest

/-- **Walking preserves the probability bounds, with errors read below the block.** This is
`walk_flips` for errors that depend only on the challenge node of the rest. -/
theorem walk_flips_tail {inside : Prop} (ms : Block) {after : ms.Values → SpineProp rest}
    {draw : QueryImpl (challengeSpec oracleSig (ms.then rest)) ProbComp}
    {E' : ChallengeNode oracleSig rest → ℝ≥0∞}
    (hin : ∀ xs, ¬ inside → ¬ after xs (.root rest) ⟨⟩)
    (hafter : ∀ xs, Flips rest (after xs) (restrictDraw ms xs draw) E') :
    Flips (ms.then rest) (walk ms inside after) draw (fun c => E' (tailNode ms c)) :=
  walk_flips ms hin fun xs => by
    rw [restrict_tailNode]
    exact hafter xs

/-- **Walking preserves the leaf law.** -/
theorem walk_leaf {inside : Prop} :
    ∀ (ms : Block) {after : ms.Values → SpineProp rest}
      {G : Transcript oracleSig (ms.then rest) → Prop},
    (∀ xs, LeafOK rest (after xs) (fun tr => G (join ms xs tr))) →
      LeafOK (ms.then rest) (walk ms inside after) G
  | [], _, _, hafter => hafter ⟨⟩
  | m :: ms, after, G, hafter => by
    intro sp history hG
    cases sp with
    | down b tail =>
      obtain ⟨⟨y, rfl⟩, rest⟩ := history
      exact walk_leaf (inside := inside) ms (after := fun xs => after (y, xs))
        (G := fun tr => G ⟨y, tr⟩) (fun xs => hafter (y, xs)) tail rest hG

/-- A constant state function on a block followed by the end of the protocol satisfies the
probability bounds: no prover message changes it and there is no challenge. -/
theorem flips_const (P : Prop) (ms : Block)
    (draw : QueryImpl (challengeSpec oracleSig (ms.then (.pure PUnit.unit))) ProbComp)
    (E : ChallengeNode oracleSig (ms.then (.pure PUnit.unit)) → ℝ≥0∞) :
    Flips (ms.then (.pure PUnit.unit)) (fun _ _ => P) draw E where
  send _ _ _ h _ := h
  flip _ _ _ := by
    simp only [not_and_self_iff, Set.ofPred_false, measure_empty, zero_le]

end Block

/-! ## One challenge -/

/-- The tree that draws one challenge and continues with `rest`. -/
@[reducible]
def chalThen (C : Type) (rest : OracleProtocol) : OracleProtocol :=
  .liftBind (.challenge C) fun _ => rest

namespace Chal

variable {C : Type} {rest : OracleProtocol}

/-- A state function around one challenge: `before` until the challenge, then `after c`. -/
def walk (before : Prop) (after : C → Block.SpineProp rest) : Block.SpineProp (chalThen C rest) :=
  fun sp history => by
    cases sp with
    | root => exact before
    | down _ tail => exact after history.1.1 tail history.2

/-- The draw of the rest of the tree. -/
def restDraw (draw : QueryImpl (challengeSpec oracleSig (chalThen C rest)) ProbComp) :
    QueryImpl (challengeSpec oracleSig rest) ProbComp :=
  fun c => draw ⟨.inr ⟨⟨⟩, c.1⟩, c.2⟩

/-- The challenge node of the challenge. -/
def node : ChallengeNode oracleSig (chalThen C rest) := ⟨.inl ⟨⟩, rfl⟩

/-- The draw of the challenge. -/
def headDraw (draw : QueryImpl (challengeSpec oracleSig (chalThen C rest)) ProbComp) : ProbComp C :=
  draw node

/-- Extend a draw at the challenge nodes of `rest` by the draw `here` of the challenge. -/
def lift (here : ProbComp C) (g : QueryImpl (challengeSpec oracleSig rest) ProbComp) :
    QueryImpl (challengeSpec oracleSig (chalThen C rest)) ProbComp := fun c =>
  match c with
  | ⟨.inl _, _⟩ => here
  | ⟨.inr ⟨_, c⟩, h⟩ => g ⟨c, h⟩

/-- **The probability bounds around one challenge.** The challenge flips the state function with
probability at most its node's error, and the rest satisfies the bounds. -/
theorem walk_flips {before : Prop} {after : C → Block.SpineProp rest}
    {draw : QueryImpl (challengeSpec oracleSig (chalThen C rest)) ProbComp}
    {E : ChallengeNode oracleSig (chalThen C rest) → ℝ≥0∞}
    (hchal : letI : MeasurableSpace C := ⊤
      𝒟[headDraw draw] {c | ¬ before ∧ after c (.root rest) ⟨⟩} ≤ E node)
    (hrest : ∀ c, Block.Flips rest (after c) (restDraw draw)
      (fun c' => E ⟨.inr ⟨⟨⟩, c'.1⟩, c'.2⟩)) :
    Block.Flips (chalThen C rest) (walk before after) draw E := by
  refine ⟨fun sp history hown hfalse x => ?_, fun sp hrecv history => ?_⟩
  · cases sp with
    | root => cases hown
    | down b tail =>
      obtain ⟨⟨c, rfl⟩, rest⟩ := history
      exact (hrest c).send tail rest hown hfalse x
  · cases sp with
    | root =>
      have hs : sampleAt oracleSig draw (.root _) hrecv = headDraw draw := LawfulFunctor.id_map _
      rw [hs]
      exact hchal
    | down b tail =>
      obtain ⟨⟨c, rfl⟩, rest⟩ := history
      exact (hrest c).flip tail hrecv rest

/-- **The leaf law around one challenge.** -/
theorem walk_leaf {before : Prop} {after : C → Block.SpineProp rest}
    {G : Transcript oracleSig (chalThen C rest) → Prop}
    (hrest : ∀ c, Block.LeafOK rest (after c) (fun tr => G ⟨c, tr⟩)) :
    Block.LeafOK (chalThen C rest) (walk before after) G := by
  intro sp history hG
  cases sp with
  | down b tail =>
    obtain ⟨⟨c, rfl⟩, rest⟩ := history
    exact hrest c tail rest hG

end Chal

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.Block.split_join
#print axioms Specs.Kit.Block.splitView_erase
#print axioms Specs.Kit.Block.route_f
#print axioms Specs.Kit.Block.restrictDraw_lift
#print axioms Specs.Kit.Block.sum_challengeNodesOn
#print axioms Specs.Kit.Block.walk_flips
#print axioms Specs.Kit.Block.walk_flips_tail
#print axioms Specs.Kit.Block.walk_leaf
#print axioms Specs.Kit.Chal.walk_flips
#print axioms Specs.Kit.Chal.walk_leaf
