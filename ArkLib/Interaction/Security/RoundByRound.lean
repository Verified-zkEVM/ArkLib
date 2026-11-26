/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.Knowledge
public import PolyFun.PFunctor.Free.Cursor

/-!
# Round-by-round security

Full moves decorate PolyFun cursor spines, so states and extractors can inspect prefix oracle
messages as well as public messages and challenges. Soundness states are false at false roots,
remain false across sender moves and rule out valid acceptance at a false leaf. Knowledge states
carry intermediate witnesses and extract them backwards. Both error bounds quantify each fixed
prefix before drawing one challenge. Generic knowledge draws and their local errors may depend on
the entire earlier history; node-indexed draws and errors are specializations.

## Oracle verifiers

`OracleVerifier.rbrKnowledgeSoundness` takes a draw over `viewSig` and reads it through
`PrefixDraw.ofView`, which erases oracle messages from the history before the draw receives it.
Its state function, witness carriers, backward maps and error keep the full prefix. A view draw
may still depend on earlier public messages and challenges, and an effectful draw may use its
ambient handler. A public-coin reading also needs every draw to be a fresh uniform sample; no
definition here assumes that. Node-indexed oracle draws factor through the view
(`OracleVerifier.rbrKnowledgeSoundnessOfNodes_iff`).

## Data lies in `Type`

Moves, statements, witness carriers and output carriers lie in `Type`, as the universe policy of
record D2 (`docs/design/interaction-rebuild/D2-ownership-and-universes.md`) requires. Two
universes stay general: the position universe of the move functor, and the result universe
`vDraw` of the monad in which a `PrefixDraw` draws its moves. `sampleAt` and the probability
bounds built on it, such as `KnowledgeStateFunction.BoundedAt` and
`KnowledgeStateFunction.LocallyBounded`, draw moves in `ProbComp`.

## Knowledge states and the literature

`KnowledgeStateFunction` and `rbrKnowledgeSoundness` generalize the knowledge-state formulation of
round-by-round knowledge soundness in [BCFW25] (Definitions 4.1 and 4.2) and [ABF26]
(Appendix A.1):

* The local event puts the existential over the witness after the challenge inside the event on
  the sampled challenge. A challenge is bad if some witness makes the state true after it while
  the step map's image of that witness makes the state false before it.
* The root and leaf laws transport valid witnesses in one direction: a true root state extracts a
  valid input witness, and a valid output witness gives a true leaf state.
* The step map may change witnesses across prover moves as well as across challenges.
* Both papers also bound extraction time. The backward maps here are total functions with no
  computational restriction; `MeasuredExtraction.lean` attaches stage programs and budgets.

[ACFY24] (Section 3.1) calls its own variant without a time bound round-by-round soundness.

## References

* [Bünz, B., Chiesa, A., Fenzi, G., and Wang, W., *Linear time accumulation
    schemes*][BCFW25]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
-/

@[expose] public section

universe uA vDraw

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal


variable {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly0)

/-- The partial transcript at a round position `sp`: the full moves made so far along the cursor,
including the oracle messages the verifier's view erases. -/
@[implicit_reducible]
def PartialTranscriptAt : {s t : FreeM P Unit} → Cursor.Spine s t → Type
  | _, _, .root _ => PUnit
  | _, _, .down (a := a) b tail =>
    {x : Move l a // l.toFunB a x = b} × PartialTranscriptAt tail

/-- Extend a full prefix by one move using cursor composition. -/
def PartialTranscriptAt.snoc {a : P.A} {next : P.B a → FreeM P Unit} :
    {s : FreeM P Unit} → (sp : Cursor.Spine s (.liftBind a next)) →
    PartialTranscriptAt l sp → (x : Move l a) →
    PartialTranscriptAt l (sp.comp (.down (l.toFunB a x) (.root _)))
  | _, .root _, _, x => ⟨⟨x, rfl⟩, ⟨⟩⟩
  | _, .down b tail, history, x => by
    rcases history with ⟨⟨y, h⟩, rest⟩
    exact ⟨⟨y, h⟩, PartialTranscriptAt.snoc tail rest x⟩

/-- A full prefix at a leaf is a completed transcript. -/
def PartialTranscriptAt.complete : {s : FreeM P Unit} →
    (sp : Cursor.Spine s (.pure PUnit.unit)) → PartialTranscriptAt l sp → Transcript l s
  | _, .root _, _ => ⟨⟩
  | _, .down b tail, history => by
    rcases history with ⟨⟨x, h⟩, rest⟩
    exact ⟨x, h.symm ▸ PartialTranscriptAt.complete tail rest⟩

/-- Case analysis of a nonempty full prefix at its first move. -/
def PartialTranscriptAt.downCases {a : P.A} {next : P.B a → FreeM P Unit}
    {t : FreeM P Unit}
    {motive : (b : P.B a) → (tail : Cursor.Spine (next b) t) →
      PartialTranscriptAt l (.down b tail) → Sort*}
    (h : ∀ x tail history, motive (l.toFunB a x) tail ⟨⟨x, rfl⟩, history⟩)
    (b : P.B a) (tail : Cursor.Spine (next b) t) (history : PartialTranscriptAt l (.down b tail)) :
    motive b tail history := by
  rcases history with ⟨⟨x, rfl⟩, history⟩
  exact h x tail history

/-- Present every move of a full prefix through a move map into another signature lens, at the
same cursor. Each move keeps its source branch, so the cursor is unchanged.

This is the prefix counterpart of `Transcript.mapMoves`. It belongs next to PolyFun's cursor and
move-map operations (`PolyFun.PFunctor.Free.Cursor` and `PolyFun.PFunctor.Free.Path.MapMoves`)
and should move there with them. -/
def PartialTranscriptAt.mapMoves {l' : PFunctor.Lens P rolePoly0}
    (g : PathAlong.MoveMap l l') :
    {s t : FreeM P Unit} → (sp : Cursor.Spine s t) →
    PartialTranscriptAt l sp → PartialTranscriptAt l' sp
  | _, _, .root _, _ => ⟨⟩
  | _, _, .down (a := a) _ tail, history =>
    (⟨⟨g.map a history.1.1, (g.branch a history.1.1).trans history.1.2⟩,
      PartialTranscriptAt.mapMoves g tail history.2⟩ :
      {y : Move l' a // l'.toFunB a y = _} × PartialTranscriptAt l' tail)

/-- The structural node reached by a cursor ending at an interaction node. -/
def spineNode {a : P.A} {next : P.B a → FreeM P Unit} :
    {s : FreeM P Unit} → Cursor.Spine s (.liftBind a next) → Node s
  | _, .root _ => .inl ⟨⟩
  | _, .down b tail => .inr ⟨b, spineNode tail⟩

/-- Node lookup preserves the position at the end of the cursor. -/
theorem spineNode_position {a : P.A} {next : P.B a → FreeM P Unit} :
    {s : FreeM P Unit} → (sp : Cursor.Spine s (.liftBind a next)) →
    Node.position _ (spineNode sp) = a
  | _, .root _ => rfl
  | _, .down _ tail => spineNode_position tail

/-- A receiver cursor identifies its challenge without using any full runtime move. -/
def spineChallenge {s : FreeM P Unit} {a : P.A} {next : P.B a → FreeM P Unit}
    (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver) : ChallengeNode l s :=
  ⟨spineNode sp, (congrArg (owner l) (spineNode_position sp)).trans h⟩

/-- Draw a fresh move at the receiver position selected by a structural prefix. -/
def sampleAt {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)
    {s : FreeM P Unit} {a : P.A} {next : P.B a → FreeM P Unit}
    (draw : QueryImpl (challengeSpec l s) ProbComp)
    (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver) : ProbComp (Move l a) :=
  (fun x => Eq.mp (congrArg (Move l) (spineNode_position sp)) x) <$>
    draw (spineChallenge l sp h)

/-- A challenge action at each receiver prefix, with access to all earlier moves.

The history is the full prefix at the signature `l`. At `oracleSig` it contains every oracle
message in full, so a draw can read oracle messages that a passive oracle verifier reaches only
through bundle queries in its final decision. State functions, the generic counterpart and
extraction use this full history. An oracle-verifier API that exposes a prefix draw should index it
by the `viewSig` prefix, or require it to factor through that view. -/
abbrev PrefixDraw (m : Type → Type vDraw) (s : FreeM P Unit) :=
  ∀ {a next}, (sp : Cursor.Spine s (.liftBind a next)) → owner l a = .receiver →
    PartialTranscriptAt l sp → m (Move l a)

/-- A local error at the same receiver prefix and history as its draw. -/
abbrev PrefixError (s : FreeM P Unit) := PrefixDraw l (fun _ => ℝ≥0∞) s

/-- Errors indexed only by structural nodes ignore the full prefix history. -/
def PrefixError.ofNodes {s : FreeM P Unit}
    (ε : ChallengeNode l s → ℝ≥0∞) : PrefixError l s :=
  fun sp h _ => ε (spineChallenge l sp h)

/-- Challenge programs may depend on the entire full prefix, including erased challenges and
oracle messages, and may issue queries to the supplied specification `spec`. -/
abbrev PrefixChallengePrograms {ι : Type} (spec : OracleSpec.{0, 0} ι)
    (s : FreeM P Unit) := PrefixDraw l (OracleComp spec) s

/-- Draw at one receiver prefix using its complete history. -/
abbrev prefixSampleAt {m : Type → Type vDraw} {s : FreeM P Unit}
    (draw : PrefixDraw l m s) {a next} (sp : Cursor.Spine s (.liftBind a next))
    (h : owner l a = .receiver) (history : PartialTranscriptAt l sp) : m (Move l a) :=
  draw sp h history

/-- A node-indexed draw is the prefix draw that ignores the full history. -/
def PrefixDraw.ofNodes {m : Type → Type vDraw} [Functor m] {s : FreeM P Unit}
    (draw : (c : ChallengeNode l s) → m (challengeSpec l s c)) : PrefixDraw l m s :=
  fun sp h _ => (fun x => Eq.mp (congrArg (Move l) (spineNode_position sp)) x) <$>
    draw (spineChallenge l sp h)

/-- Ignoring history recovers node-indexed sampling at the same receiver cursor. -/
theorem prefixSampleAt_ofNodes {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)
    {s : FreeM P Unit} (draw : QueryImpl (challengeSpec l s) ProbComp)
    {a next} (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
    (history : PartialTranscriptAt l sp) :
    prefixSampleAt l (PrefixDraw.ofNodes l draw) sp h history = sampleAt l draw sp h := rfl

section View

/-- The view signature gives every oracle position the owner it has in the oracle signature. -/
@[simp] theorem owner_viewSig (a : OraclePos) : owner viewSig a = owner oracleSig a := by
  cases a <;> rfl

/-- At a receiver position, the verifier's view records the whole move. -/
theorem move_viewSig_of_receiver {a : OraclePos} (h : owner oracleSig a = .receiver) :
    Move viewSig a = Move oracleSig a := by
  cases a with
  | challenge => rfl
  | message => nomatch h
  | oracle => nomatch h

/-- An oracle-verifier draw that reads only the verifier's view of the prefix. The full history
passes through `eraseOracle` before the draw receives it, so two histories that differ only in
oracle messages give the same draw. A view draw may still read earlier public messages and
challenges, and an effectful draw may still use its ambient handler; this restriction says nothing
about the challenge distribution. -/
def PrefixDraw.ofView {m : Type → Type vDraw} {s : OracleProtocol}
    (draw : PrefixDraw viewSig m s) : PrefixDraw oracleSig m s :=
  fun sp h history => cast (congrArg m (move_viewSig_of_receiver h))
    (draw sp ((owner_viewSig _).trans h) (PartialTranscriptAt.mapMoves oracleSig eraseOracle sp
      history))

/-- The draw at an oracle prefix is the view draw at the erased prefix. -/
theorem prefixSampleAt_ofView {m : Type → Type vDraw} {s : OracleProtocol}
    (draw : PrefixDraw viewSig m s) {a next} (sp : Cursor.Spine s (.liftBind a next))
    (h : owner oracleSig a = .receiver) (history : PartialTranscriptAt oracleSig sp) :
    prefixSampleAt oracleSig (PrefixDraw.ofView draw) sp h history =
      cast (congrArg m (move_viewSig_of_receiver h))
        (draw sp ((owner_viewSig _).trans h)
          (PartialTranscriptAt.mapMoves oracleSig eraseOracle sp history)) := rfl

/-- A node-indexed oracle draw as a view draw. It ignores the history. -/
def PrefixDraw.ofNodesView {m : Type → Type vDraw} [Functor m] {s : OracleProtocol}
    (draw : (c : ChallengeNode oracleSig s) → m (challengeSpec oracleSig s c)) :
    PrefixDraw viewSig m s :=
  fun sp h _ => cast (congrArg m (move_viewSig_of_receiver
      ((owner_viewSig _).symm.trans h)).symm)
    ((fun x => Eq.mp (congrArg (Move oracleSig) (spineNode_position sp)) x) <$>
      draw (spineChallenge oracleSig sp ((owner_viewSig _).symm.trans h)))

/-- A node-indexed oracle draw factors through the verifier's view. -/
theorem PrefixDraw.ofView_ofNodesView {m : Type → Type vDraw} [Functor m]
    {s : OracleProtocol}
    (draw : (c : ChallengeNode oracleSig s) → m (challengeSpec oracleSig s c)) :
    (PrefixDraw.ofView (PrefixDraw.ofNodesView draw) : PrefixDraw oracleSig m s) =
      (fun {a next} => PrefixDraw.ofNodes oracleSig draw (a := a) (next := next)) := by
  funext a next sp h history
  simp only [PrefixDraw.ofView, PrefixDraw.ofNodesView, PrefixDraw.ofNodes, cast_cast, cast_eq]

end View

/-- The passive counterpart whose next draw can depend on the full prefix. It passes each
actual sender move, an oracle message included, to the later draws. -/
def prefixSampler {m : Type → Type} [Monad m] :
    (s : FreeM P Unit) → PrefixDraw l m s →
    Counterpart l m s (fun _ => Unit)
  | .pure _, _ => pure ⟨⟩
  | .liftBind a next, d =>
    samplerNode (owner l a) (fun h => d (.root _) h ⟨⟩) (fun x =>
      prefixSampler (next (l.toFunB a x))
        (fun sp h history => d (.down (l.toFunB a x) sp) h ⟨⟨x, rfl⟩, history⟩))

private theorem cast_prefixSampler {m : Type → Type} [Monad m]
    {a : P.A} {next : P.B a → FreeM P Unit} {r : TwoParty.Role}
    (h : owner l a = r) (d : PrefixDraw l m (.liftBind a next)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => Unit)))) h)
      (prefixSampler l (.liftBind a next) d) =
    samplerNode r (fun hr => d (.root _) (h.trans hr) ⟨⟩) (fun x =>
      prefixSampler l (next (l.toFunB a x))
        (fun sp h history => d (.down (l.toFunB a x) sp) h ⟨⟨x, rfl⟩, history⟩)) := by
  cases h
  rfl

/-- Execute a focal strategy with passive challenges selected from its full prefix. -/
def runPrefixChallenges {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (s : FreeM P Unit) {Out : Transcript l s → Type}
    (p : Focal l (OracleComp spec) s Out) (d : PrefixChallengePrograms l spec s) :
    OracleComp spec ((tr : Transcript l s) × Out tr × Unit) :=
  TwoParty.Lens.run s p (prefixSampler l s d)

/-- Prefix-dependent execution is the ordinary focal-first Core runner with its passive
counterpart. It does not restart or replay the focal strategy. -/
theorem runPrefixChallenges_eq_run {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (s : FreeM P Unit) :
    ∀ {Out : Transcript l s → Type} (p : Focal l (OracleComp spec) s Out)
      (d : PrefixChallengePrograms l spec s),
      runPrefixChallenges l s p d = TwoParty.Lens.run s p (prefixSampler l s d) :=
  fun _ _ => rfl

/-- At a leaf, the focal strategy's output action runs before the sampler's pure final action. -/
theorem runPrefixChallenges_done {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {Out : Transcript l (.pure PUnit.unit) → Type} (p : OracleComp spec (Out ⟨⟩))
    (d : PrefixChallengePrograms l spec (.pure PUnit.unit)) :
    runPrefixChallenges l (.pure PUnit.unit) p d = (do
      let out ← p
      pure ⟨⟨⟩, out, ⟨⟩⟩) := by
  simp only [runPrefixChallenges, prefixSampler, FreeM.pure_eq_pure, run_done,
    LawfulMonad.pure_bind]

/-- At a sender node, the focal strategy supplies the move before the passive sampler observes
it. -/
theorem runPrefixChallenges_sender {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {a : P.A} {next : P.B a → FreeM P Unit}
    {Out : Transcript l (.liftBind a next) → Type} (h : owner l a = .sender)
    (p : Focal l (OracleComp spec) (.liftBind a next) Out)
    (d : PrefixChallengePrograms l spec (.liftBind a next)) :
    runPrefixChallenges l (.liftBind a next) p d = (do
      let v ← cast (congrArg (fun r => OracleComp spec (Choice .focal r (Move l a)
        (fun x => Focal l (OracleComp spec) (next (l.toFunB a x))
          (fun tr => Out ⟨x, tr⟩)))) h) p
      let r ← runPrefixChallenges l (next (l.toFunB a v.1)) v.2
        (fun sp h history => d (.down (l.toFunB a v.1) sp) h ⟨⟨v.1, rfl⟩, history⟩)
      pure ⟨⟨v.1, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [runPrefixChallenges, run_node, step_sender (owner l a) h, cast_prefixSampler l h]
  simp only [samplerNode, LawfulMonad.pure_bind]
  rfl

/-- At a receiver node, the focal strategy supplies its continuation before the
history-selected challenge is drawn. -/
theorem runPrefixChallenges_receiver {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {a : P.A} {next : P.B a → FreeM P Unit}
    {Out : Transcript l (.liftBind a next) → Type} (h : owner l a = .receiver)
    (p : Focal l (OracleComp spec) (.liftBind a next) Out)
    (d : PrefixChallengePrograms l spec (.liftBind a next)) :
    runPrefixChallenges l (.liftBind a next) p d = (do
      let f ← cast (congrArg (fun r => OracleComp spec (Choice .focal r (Move l a)
        (fun x => Focal l (OracleComp spec) (next (l.toFunB a x))
          (fun tr => Out ⟨x, tr⟩)))) h) p
      let x ← d (.root _) h ⟨⟩
      let r ← runPrefixChallenges l (next (l.toFunB a x)) (f x)
        (fun sp h history => d (.down (l.toFunB a x) sp) h ⟨⟨x, rfl⟩, history⟩)
      pure ⟨⟨x, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [runPrefixChallenges, run_node, step_receiver (owner l a) h, cast_prefixSampler l h]
  simp only [samplerNode, bind_map_left]
  rfl

/-- A state predicate on every full prefix, with root, sender and leaf obligations. -/
structure StateFunction (s : FreeM P Unit) (S : Type)
    (admissible language : S → Prop) (accepts : S → Transcript l s → Prop) where
  toFun : ∀ {t}, (sp : Cursor.Spine s t) → PartialTranscriptAt l sp → S → Prop
  root : ∀ stmt, admissible stmt → toFun (.root s) ⟨⟩ stmt → language stmt
  send : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next)) history stmt,
    owner l a = .sender → ¬ toFun sp history stmt → ∀ x,
      ¬ toFun (sp.comp (.down (l.toFunB a x) (.root _)))
        (PartialTranscriptAt.snoc l sp history x) stmt
  leaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) history stmt,
    ¬ toFun sp history stmt → ¬ accepts stmt (PartialTranscriptAt.complete l sp history)

/-- Worst-case-per-prefix round-by-round soundness; there is no adversary-model argument. -/
def rbrSoundness {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)
    {S : Type} (s : FreeM P Unit)
    (admissible language : S → Prop) (accepts : S → Transcript l s → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  ∃ F : StateFunction l s S admissible language accepts,
    ∀ stmt, admissible stmt → ¬ language stmt →
    ∀ (a : P.A) (next : P.B a → FreeM P Unit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PartialTranscriptAt l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ F.toFun sp history stmt ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PartialTranscriptAt.snoc l sp history x) stmt} ≤ ε (spineChallenge l sp h)

/-- Intermediate witnesses and backwards extraction at full transcript prefixes.

Every witness carrier may depend on the input statement. Intermediate carriers may also read
all earlier moves, including oracle messages, and output carriers may read the complete
transcript. Statements and all witnesses lie in `Type`; protocol positions keep the move
functor's universe. The root extraction obligation applies within the input promise.
-/
structure KnowledgeStateFunction (s : FreeM P Unit) (S : Type)
    (W : S → Transcript l s → Type) (Win : S → Type) (admissible : S → Prop)
    (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop) where
  Witness : ∀ (_stmt : S) {t} (sp : Cursor.Spine s t), PartialTranscriptAt l sp → Type
  toFun : ∀ (stmt : S) {t} (sp : Cursor.Spine s t) (history : PartialTranscriptAt l sp),
    Witness stmt sp history → Prop
  extractRoot : ∀ stmt, Witness stmt (.root s) ⟨⟩ → Win stmt
  extractStep : ∀ (stmt : S) {a next} (sp : Cursor.Spine s (.liftBind a next))
    (history : PartialTranscriptAt l sp) (x : Move l a),
    Witness stmt (sp.comp (.down (l.toFunB a x) (.root _)))
        (PartialTranscriptAt.snoc l sp history x) → Witness stmt sp history
  extractLeaf : ∀ (stmt : S) (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PartialTranscriptAt l sp),
    W stmt (PartialTranscriptAt.complete l sp history) → Witness stmt sp history
  root : ∀ stmt, admissible stmt → ∀ wit,
    toFun stmt (.root s) ⟨⟩ wit → relIn stmt (extractRoot stmt wit)
  send : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next)) history stmt,
    owner l a = .sender → ∀ x wit,
      toFun stmt (sp.comp (.down (l.toFunB a x) (.root _)))
        (PartialTranscriptAt.snoc l sp history x) wit →
      toFun stmt sp history (extractStep stmt sp history x wit)
  leaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) history stmt wit,
    validOutput stmt (PartialTranscriptAt.complete l sp history) wit →
      toFun stmt sp history (extractLeaf stmt sp history wit)

/-- At each receiver prefix, the history-selected challenge defeats backwards extraction with
probability at most that prefix's error, uniformly over later witnesses. -/
def rbrKnowledgeSoundness {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)
    {S : Type} {Win : S → Type} (s : FreeM P Unit)
    {W : S → Transcript l s → Type} (admissible : S → Prop)
    (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop)
    (draw : PrefixDraw l ProbComp s) (ε : PrefixError l s) : Prop :=
  ∃ F : KnowledgeStateFunction l s S W Win admissible relIn validOutput,
    ∀ stmt, admissible stmt →
    ∀ (a : P.A) (next : P.B a → FreeM P Unit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PartialTranscriptAt l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[prefixSampleAt l draw sp h history] {x | ∃ wit,
        ¬ F.toFun stmt sp history (F.extractStep stmt sp history x wit) ∧
        F.toFun stmt (sp.comp (.down (l.toFunB a x) (.root _)))
          (PartialTranscriptAt.snoc l sp history x) wit} ≤ ε sp h history

/-- Knowledge soundness for node-indexed draws and errors, as a prefix specialization. -/
abbrev rbrKnowledgeSoundnessOfNodes {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)
    {S : Type} {Win : S → Type} (s : FreeM P Unit)
    {W : S → Transcript l s → Type} (admissible : S → Prop)
    (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  rbrKnowledgeSoundness l s admissible relIn validOutput
    (PrefixDraw.ofNodes l draw) (PrefixError.ofNodes l ε)

/-- Valid plain acceptance from some ambient state at the fixed complete transcript.
Leaf obligations therefore cover state changes made during the interaction. The event is a
predicate on the output statement type at the transcript's shape path. -/
def Verifier.validAcceptance {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : S) (tr : Transcript plainSig s)
    (event : T tr.path → Prop) : Prop :=
  letI : MeasurableSpace (Option (T tr.path)) := ⊤
  ∃ state : σ, 0 < 𝒟[((simulateQ impl
    (V.decide stmt (Transcript.path tr) (toPlainView s tr)).run).run' state :
      ProbComp (Option (T tr.path)))] {v | ∃ t, v = some t ∧ event t}

/-- Positive acceptance is a supported accepted result, including its final ambient state. -/
theorem Verifier.validAcceptance_iff_support {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι} {s : Protocol} {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S) (tr : Transcript plainSig s)
    (langOut : T tr.path → Prop) :
    V.validAcceptance impl stmt tr langOut ↔
      ∃ state t final, (some t, final) ∈ support
        ((simulateQ impl (V.decide stmt tr.path
          (toPlainView s tr)).run).run state) ∧ langOut t := by
  let : MeasurableSpace (Option (T tr.path)) := ⊤
  unfold Verifier.validAcceptance
  simp only [← prEvent_eq_evalDist _ _ measurable_from_top, prEvent_pos_iff,
    StateT.run'_eq, _root_.support_map, Set.mem_image]
  constructor
  · rintro ⟨state, v, ⟨⟨result, final⟩, hr, rfl⟩, t, rfl, ht⟩
    exact ⟨state, t, final, hr, ht⟩
  · rintro ⟨state, t, final, hr, ht⟩
    exact ⟨state, some t, ⟨(some t, final), hr, rfl⟩, t, rfl, ht⟩

/-- Classical acceptance quantifies over the possible ambient states at the end of the run. -/
theorem Verifier.validAcceptance_iff_validAcceptanceUsing {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : S) (tr : Transcript plainSig s)
    (event : (p : Path s) → T p → Prop) :
    V.validAcceptance impl stmt tr (event tr.path) ↔
      ∃ state : σ, V.validAcceptanceUsing impl (fun x => x.run' state)
        event stmt tr := by
  unfold Verifier.validAcceptance Verifier.validAcceptanceUsing
  dsimp only
  let : MeasurableSpace (Option (T tr.path)) := ⊤
  exact exists_congr fun state => by rw [prEvent_eq_evalDist_of_discrete]

/-- The plain verifier's default round-by-round soundness form. The output language is indexed
by the shape path and judged at the transcript's path. -/
abbrev Verifier.rbrSoundness {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : PathProblem s T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Interaction.rbrSoundness plainSig s (input.admissible ()) (input.language ())
    (fun stmt tr => V.validAcceptance impl stmt tr
      (output.language tr.path)) draw ε

/-- The plain verifier's default round-by-round knowledge form. The output witness type `W stmt tr`
and the output relation are indexed by the input statement and completed transcript. -/
abbrev Verifier.rbrKnowledgeSoundness {ι σ : Type} {S : Type} {Win : S → Type}
    {ambient : OracleSpec ι} {s : Protocol} {T : Path s → Type}
    {W : S → Transcript plainSig s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S → Prop) (relIn : (stmt : S) → Win stmt → Prop)
    (relOut : (stmt : S) → (tr : Transcript plainSig s) → T tr.path → W
    stmt tr → Prop)
    (draw : PrefixDraw plainSig ProbComp s)
    (ε : PrefixError plainSig s) : Prop :=
  Interaction.rbrKnowledgeSoundness plainSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut stmt tr t wit)) draw ε

/-- Node-indexed knowledge soundness is the shared prefix predicate ignoring history. -/
abbrev Verifier.rbrKnowledgeSoundnessOfNodes {ι σ : Type} {S : Type} {Win : S → Type}
    {ambient : OracleSpec ι} {s : Protocol} {T : Path s → Type}
    {W : S → Transcript plainSig s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S → Prop) (relIn : (stmt : S) → Win stmt → Prop)
    (relOut : (stmt : S) → (tr : Transcript plainSig s) → T tr.path → W
    stmt tr → Prop)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Verifier.rbrKnowledgeSoundness V impl admissible relIn relOut
    (PrefixDraw.ofNodes plainSig draw) (PrefixError.ofNodes plainSig ε)

namespace OracleVerifier
variable {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol}
  {T : Path s → Type} {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- Oracle acceptance from a possible ambient state at the end of the run, with actual input and
path oracle messages. The event is a predicate on the output statement and oracle data at the
transcript's shape path. -/
def validAcceptance (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × inputs.Data) (tr : Transcript oracleSig s)
    (event : OracleVerifier.Output T outputs tr.path → Prop) : Prop :=
  let p := Transcript.path tr
  let view := toView s tr
  let pathData : (pathBundle inputs s p).Data := (stmt.2, oracleMessages s tr)
  letI : MeasurableSpace (Option (T p)) := ⊤
  let handler : QueryImpl (ambient + (pathBundle inputs s p).spec)
      (StateT σ ProbComp) := QueryImpl.addLift impl
        ((pathBundle inputs s p).answer pathData)
  ∃ state : σ, 0 < 𝒟[(simulateQ handler (V.decide stmt.1 p view).run).run' state]
      {v | ∃ t, v = some t ∧ event (t, (V.outputMap stmt.1 p view).f pathData)}

/-- Positive oracle acceptance has a supported accepted result and a final ambient state. -/
theorem validAcceptance_iff_support (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × inputs.Data) (tr : Transcript oracleSig s)
    (langOut : OracleVerifier.Output T outputs tr.path → Prop) :
    V.validAcceptance impl stmt tr langOut ↔
      ∃ state t final, (some t, final) ∈ support
        ((simulateQ impl (V.decideWith stmt.1 tr.path
          (toView s tr) (stmt.2, oracleMessages s tr))).run state) ∧
        langOut (t, (V.outputMap stmt.1 tr.path (toView s tr)).f
          (stmt.2, oracleMessages s tr)) := by
  let : MeasurableSpace (Option (T tr.path)) := ⊤
  simp only [validAcceptance, OracleVerifier.simulateQ_decideWith,
    ← prEvent_eq_evalDist _ _ measurable_from_top, prEvent_pos_iff,
    StateT.run'_eq, _root_.support_map, Set.mem_image]
  constructor
  · rintro ⟨state, v, ⟨⟨result, final⟩, hr, rfl⟩, t, rfl, ht⟩
    exact ⟨state, t, final, hr, ht⟩
  · rintro ⟨state, t, final, hr, ht⟩
    exact ⟨state, some t, ⟨(some t, final), hr, rfl⟩, t, rfl, ht⟩

/-- Classical acceptance quantifies over the possible ambient states at the end of the run. -/
theorem validAcceptance_iff_validAcceptanceUsing
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × inputs.Data) (tr : Transcript oracleSig s)
    (event : (p : Path s) → OracleVerifier.Output T outputs p → Prop) :
    V.validAcceptance impl stmt tr (event tr.path) ↔
      ∃ state : σ, V.validAcceptanceUsing impl (fun x => x.run' state)
        event stmt tr := by
  unfold validAcceptance validAcceptanceUsing
  dsimp only
  let : MeasurableSpace (Option (T tr.path)) := ⊤
  exact exists_congr fun state => by rw [prEvent_eq_evalDist_of_discrete]

/-- Worst-case-per-prefix oracle soundness with the full input admissibility boundary. The
output language is indexed by the shape path and judged at the transcript's path. -/
abbrev rbrSoundness (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Interaction.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
    (fun stmt tr => V.validAcceptance impl stmt tr
      (output.language tr.path)) draw ε

/-- Worst-case-per-prefix oracle knowledge. The challenge draw reads only the verifier's view
of each prefix (`PrefixDraw.ofView`): public messages, challenges and a marker for each oracle
message. The state function, its witness carriers and backward maps, and the error read the full
prefix, oracle messages included. The output witness type `W stmt tr` and the output relation are
indexed by the input statement, including its oracle data, and the completed transcript. -/
abbrev rbrKnowledgeSoundness {Win : (S × inputs.Data) → Type}
    {W : (S × inputs.Data) → Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × inputs.Data → Prop) (relIn : (stmt : S × inputs.Data) → Win stmt → Prop)
    (relOut : (stmt : S × inputs.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T outputs tr.path → W stmt tr → Prop)
    (draw : PrefixDraw viewSig ProbComp s)
    (ε : PrefixError oracleSig s) : Prop :=
  Interaction.rbrKnowledgeSoundness oracleSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut stmt tr t wit))
    (PrefixDraw.ofView draw) ε

/-- Node-indexed knowledge soundness is the shared prefix predicate ignoring history. A node
draw factors through the verifier's view (`rbrKnowledgeSoundnessOfNodes_iff`). -/
abbrev rbrKnowledgeSoundnessOfNodes {Win : (S × inputs.Data) → Type}
    {W : (S × inputs.Data) → Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × inputs.Data → Prop) (relIn : (stmt : S × inputs.Data) → Win stmt → Prop)
    (relOut : (stmt : S × inputs.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T outputs tr.path → W stmt tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Interaction.rbrKnowledgeSoundness oracleSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut stmt tr t wit))
    (PrefixDraw.ofNodes oracleSig draw) (PrefixError.ofNodes oracleSig ε)

/-- Node-indexed oracle knowledge is view-restricted knowledge at the node draw read through
the view. -/
theorem rbrKnowledgeSoundnessOfNodes_iff {Win : (S × inputs.Data) → Type}
    {W : (S × inputs.Data) → Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × inputs.Data → Prop) (relIn : (stmt : S × inputs.Data) → Win stmt → Prop)
    (relOut : (stmt : S × inputs.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T outputs tr.path → W stmt tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) :
    rbrKnowledgeSoundnessOfNodes V impl admissible relIn relOut draw ε ↔
      rbrKnowledgeSoundness V impl admissible relIn relOut
        (PrefixDraw.ofNodesView draw) (PrefixError.ofNodes oracleSig ε) := by
  rw [rbrKnowledgeSoundness, PrefixDraw.ofView_ofNodesView]

end OracleVerifier

end Interaction
