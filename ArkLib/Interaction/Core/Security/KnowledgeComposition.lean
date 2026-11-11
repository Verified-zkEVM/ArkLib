/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Composition
public import ArkLib.Interaction.Core.Security.RoundByRound

/-!
# Composing knowledge state functions

A knowledge state function extracts backwards along a completed transcript: the leaf map turns an
output witness into a witness at the terminal cursor, the step maps move it to earlier cursors, and
the root map returns an input witness (`KnowledgeStateFunction.extractAlong`). Output witness types
form a family over statements and completed transcripts. Extraction from a cursor (`extractFrom`)
takes its output
witness at the transcript that completes the cursor's prefix with the rest of the transcript
(`PrefixMoves.completeWith`); along a whole transcript it takes a witness at that transcript.
The round-by-round error of a state function is a bound on the probability of a bad challenge at
every receiver prefix (`KnowledgeStateFunction.LocallyBounded`), which is exactly
`rbrKnowledgeSoundness`.

`KnowledgeStateFunction.append` composes a state function on a prefix protocol with a family of
state functions on the suffixes, one for each completed prefix transcript, so suffix witness
carriers may read prefix oracle payloads. The intermediate witness type is a family over prefix
transcripts: the suffix at `tr₁` takes input witnesses in `(fun stmt => Wmid stmt tr₁)`, and its
    output family is
the composite family along `PathAlong.append` at `tr₁`. The seam condition says that the suffix
root state implies the prefix's valid output on the witness the suffix root map extracts.
Extraction along an appended transcript is suffix extraction followed by prefix extraction
(`extractAlong_append`), the terminal state is the suffix terminal state
(`toFun_terminalWitness_append`), and the composite is locally bounded by the prefix and suffix
errors combined along the protocol with `combineDraw`, the same combinator that combines the draws
(`LocallyBounded.append`).

`KnowledgeStateFunction.guard` restricts a state function to admissible statements and
`KnowledgeStateFunction.comap` changes its statement type; both keep the local bound. The
theorem `rbrKnowledgeSoundness_append` composes the security statements themselves, with a seam
stated between the suffix input relation and the prefix output relation under the input promise;
`rbrKnowledgeSoundness_append_of_mid` is its special case where the suffix statement is a
function of the prefix statement and transcript.
-/

@[expose] public section

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

variable {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly)

/-! ### Transcripts as cursors -/

/-- The terminal cursor reached by a completed transcript. -/
def completeSpine : {s : FreeM P PUnit.{1}} → PathAlong l s → Cursor.Spine s (.pure ⟨⟩)
  | .pure _, _ => .root _
  | .liftBind a _, ⟨x, tr⟩ => .down (l.toFunB a x) (completeSpine tr)

/-- The full moves of a completed transcript, decorating its terminal cursor. -/
def completeMoves : {s : FreeM P PUnit.{1}} → (tr : PathAlong l s) →
    PrefixMoves l (completeSpine l tr)
  | .pure _, _ => ⟨⟩
  | .liftBind _ _, ⟨x, tr⟩ => ⟨⟨x, rfl⟩, completeMoves tr⟩

/-- Completing the full moves of a transcript returns the transcript. -/
@[simp] theorem complete_completeMoves : {s : FreeM P PUnit.{1}} → (tr : PathAlong l s) →
    PrefixMoves.complete l (completeSpine l tr) (completeMoves l tr) = tr
  | .pure _, _ => rfl
  | .liftBind a next, ⟨x, tr⟩ =>
    congrArg (Sigma.mk (β := fun y => PathAlong l (next (l.toFunB a y))) x)
      (complete_completeMoves (s := next _) tr)

/-- The terminal cursor of a transcript has one edge per move. -/
@[simp] theorem length_completeSpine_liftBind {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (x : Move l a) (tr : PathAlong l (next (l.toFunB a x))) :
    (completeSpine l (s := .liftBind a next) ⟨x, tr⟩).length =
      (completeSpine l tr).length + 1 := rfl

/-- The completed transcript through a full prefix followed by the rest of a transcript below its
cursor. -/
def PrefixMoves.completeWith {s : FreeM P PUnit.{1}} : {t : FreeM P PUnit.{1}} →
    (sp : Cursor.Spine s t) → PrefixMoves l sp → PathAlong l t → PathAlong l s
  | .pure _, sp, history, _ => PrefixMoves.complete l sp history
  | .liftBind _ _, sp, history, ⟨x, tr⟩ =>
    PrefixMoves.completeWith (sp.comp (.down _ (.root _))) (PrefixMoves.snoc l sp history x) tr

/-- Below a first move, completing a prefix with a transcript keeps the move. -/
@[simp] theorem PrefixMoves.completeWith_down {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (x : Move l a) : {t : FreeM P PUnit.{1}} → (sp : Cursor.Spine (next (l.toFunB a x)) t) →
    (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    PrefixMoves.completeWith l (s := .liftBind a next) (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr =
      ⟨x, PrefixMoves.completeWith l sp history tr⟩
  | .pure _, _, _, _ => rfl
  | .liftBind _ _, sp, history, ⟨y, tr⟩ =>
    PrefixMoves.completeWith_down x (sp.comp _) (PrefixMoves.snoc l sp history y) tr

/-- Completing the empty prefix with a transcript returns the transcript. -/
@[simp] theorem PrefixMoves.completeWith_root : {s : FreeM P PUnit.{1}} → (tr : PathAlong l s) →
    PrefixMoves.completeWith l (.root s) ⟨⟩ tr = tr
  | .pure _, _ => rfl
  | .liftBind a next, ⟨x, tr⟩ =>
    (PrefixMoves.completeWith_down l (next := next) x (.root _) ⟨⟩ tr).trans
      (congrArg (Sigma.mk (β := fun y => PathAlong l (next (l.toFunB a y))) x)
        (PrefixMoves.completeWith_root tr))

namespace KnowledgeStateFunction

variable {l} {s : FreeM P PUnit.{1}} {S : Type} {Win : S → Type} {W : S → PathAlong l s → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
  (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput)

/-! ### Backward extraction along a transcript -/

/-- Extract backwards to the witness at a cursor, along the remaining transcript below that
cursor, from an output witness at the completed transcript through the cursor's prefix. -/
def extractFrom (stmt : S) : {t : FreeM P PUnit.{1}} → (sp : Cursor.Spine s t) →
    (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    W stmt (PrefixMoves.completeWith l sp history tr) → F.Witness stmt sp history
  | .pure _, sp, history, _, w => F.extractLeaf stmt sp history w
  | .liftBind _ _, sp, history, ⟨x, tr⟩, w =>
    F.extractStep stmt sp history x
      (extractFrom stmt _ (PrefixMoves.snoc l sp history x) tr w)

/-- At a completed cursor, extraction is the leaf map. -/
@[simp] theorem extractFrom_pure (stmt : S) (sp : Cursor.Spine s (.pure ⟨⟩))
    (history : PrefixMoves l sp) (tr : PathAlong l (.pure ⟨⟩ : FreeM P PUnit.{1}))
    (w : W stmt (PrefixMoves.complete l sp history)) :
    F.extractFrom stmt sp history tr w = F.extractLeaf stmt sp history w := rfl

/-- At a node, extraction applies the node's step map to the witness extracted below it. This
covers public messages, oracle messages and challenges alike. -/
@[simp] theorem extractFrom_liftBind (stmt : S) {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp) (x : Move l a)
    (tr : PathAlong l (next (l.toFunB a x)))
    (w : W stmt (PrefixMoves.completeWith l sp history (t := .liftBind a next) ⟨x, tr⟩)) :
    F.extractFrom stmt sp history (s := s) (t := .liftBind a next) ⟨x, tr⟩ w =
      F.extractStep stmt sp history x
        (F.extractFrom stmt _ (PrefixMoves.snoc l sp history x) tr w) := rfl

/-- Backward extraction along a completed transcript: the leaf map, then the step maps from the
last move to the first, then the root map. -/
def extractAlong (stmt : S) (tr : PathAlong l s) (w : W stmt tr) : Win stmt :=
  F.extractRoot stmt (F.extractFrom stmt (.root s) ⟨⟩ tr
    (cast (congrArg (W stmt) (PrefixMoves.completeWith_root l tr).symm) w))

/-- The witness at the terminal cursor of a transcript, given an output witness. -/
def terminalWitness (stmt : S) (tr : PathAlong l s) (w : W stmt tr) :
    F.Witness stmt (completeSpine l tr) (completeMoves l tr) :=
  F.extractLeaf stmt _ _ (cast (congrArg (W stmt) (complete_completeMoves l tr).symm) w)

/-- A receiver transition on the remaining transcript that fails backwards preservation for
exactly the witness extracted from the supplied terminal witness. -/
def BadChallengeFrom (stmt : S) : {t : FreeM P PUnit.{1}} →
    (sp : Cursor.Spine s t) → (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    W stmt (PrefixMoves.completeWith l sp history tr) → Prop
  | .pure _, _, _, _, _ => False
  | .liftBind a _, sp, history, ⟨x, tr⟩, w =>
    (owner l a = .receiver ∧
      ¬ F.toFun stmt sp history (F.extractFrom stmt sp history ⟨x, tr⟩ w) ∧
      F.toFun stmt (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp history x)
        (F.extractFrom stmt _ (PrefixMoves.snoc l sp history x) tr w)) ∨
    BadChallengeFrom stmt _ (PrefixMoves.snoc l sp history x) tr w

/-- A bad receiver transition along a completed transcript, retaining the suffix extraction
of the supplied output witness at that transition. -/
def BadChallengeAlong (stmt : S) (tr : PathAlong l s) (w : W stmt tr) : Prop :=
  F.BadChallengeFrom stmt (.root s) ⟨⟩ tr
    (cast (congrArg (W stmt) (PrefixMoves.completeWith_root l tr).symm) w)

/-- A valid terminal witness either extracts to a true state at a prefix or encounters a bad
receiver transition on the remaining transcript. -/
theorem state_or_badChallengeFrom (stmt : S) : {t : FreeM P PUnit.{1}} →
    (sp : Cursor.Spine s t) → (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    (w : W stmt (PrefixMoves.completeWith l sp history tr)) →
    validOutput stmt (PrefixMoves.completeWith l sp history tr) w →
    F.toFun stmt sp history (F.extractFrom stmt sp history tr w) ∨
      F.BadChallengeFrom stmt sp history tr w
  | .pure _, sp, history, _, w, hv => Or.inl (F.leaf sp history stmt w hv)
  | .liftBind a _, sp, history, ⟨x, tr⟩, w, hv => by
    classical
    obtain good | bad := state_or_badChallengeFrom stmt _
      (PrefixMoves.snoc l sp history x) tr w hv
    · by_cases before : F.toFun stmt sp history (F.extractFrom stmt sp history ⟨x, tr⟩ w)
      · exact Or.inl before
      · cases ho : owner l a with
        | sender => exact Or.inl (F.send sp history stmt ho x _ good)
        | receiver => exact Or.inr (Or.inl ⟨ho, before, good⟩)
    · exact Or.inr (Or.inr bad)

/-- Failure to extract a valid input witness from a valid output identifies a bad receiver
transition with the witness extracted from that same output, for every protocol tree. -/
theorem extraction_failure_implies_badChallengeAlong (stmt : S) (tr : PathAlong l s)
    (w : W stmt tr) (hadm : admissible stmt) (hv : validOutput stmt tr w)
    (hf : ¬ relIn stmt (F.extractAlong stmt tr w)) : F.BadChallengeAlong stmt tr w := by
  have hv' : validOutput stmt (PrefixMoves.completeWith l (.root s) ⟨⟩ tr)
      (cast (congrArg (W stmt) (PrefixMoves.completeWith_root l tr).symm) w) := by
    have he : (⟨PrefixMoves.completeWith l (.root s) ⟨⟩ tr,
        cast (congrArg (W stmt) (PrefixMoves.completeWith_root l tr).symm) w⟩ :
        (tr : PathAlong l s) × W stmt tr) = ⟨tr, w⟩ :=
      Sigma.ext (PrefixMoves.completeWith_root l tr) (cast_heq _ _)
    exact (congrArg (fun z : (tr : PathAlong l s) × W stmt tr =>
      validOutput stmt z.1 z.2) he).mpr hv
  obtain good | bad := F.state_or_badChallengeFrom stmt (.root s) ⟨⟩ tr _ hv'
  · exact (hf (F.root stmt hadm _ good)).elim
  · exact bad

/-! ### Local errors -/

/-- The challenges at a receiver prefix that turn a state which is false on the extracted earlier
witness into a true state after the challenge. -/
def badChallenge {a : P.A} {next : P.B a → FreeM P PUnit.{1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp) (stmt : S) :
    Set (Move l a) :=
  {x | ∃ wit, ¬ F.toFun stmt sp history (F.extractStep stmt sp history x wit) ∧
    F.toFun stmt (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x) wit}

/-- For one statement, every receiver prefix draws a bad challenge with probability at most the
error of its challenge node. -/
def BoundedAt (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞)
    (stmt : S) : Prop :=
  ∀ (a : P.A) (next : P.B a → FreeM P PUnit.{1}) (sp : Cursor.Spine s (.liftBind a next))
    (h : owner l a = .receiver) (history : PrefixMoves l sp),
    letI : MeasurableSpace (Move l a) := ⊤
    𝒟[sampleAt l draw sp h] (F.badChallenge sp history stmt) ≤ ε (spineChallenge l sp h)

/-- Every admissible statement has the local error bound at every receiver prefix. -/
def LocallyBounded (draw : QueryImpl (challengeSpec l s) ProbComp)
    (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  ∀ stmt, admissible stmt → F.BoundedAt draw ε stmt

end KnowledgeStateFunction

/-- Round-by-round knowledge soundness is the existence of a locally bounded knowledge state
function. -/
theorem rbrKnowledgeSoundness_iff_exists_locallyBounded {s : FreeM P PUnit.{1}} {S : Type} {Win : S
    → Type}
    {W : S → PathAlong l s → Type} {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
    {draw : QueryImpl (challengeSpec l s) ProbComp} {ε : ChallengeNode l s → ℝ≥0∞} :
    rbrKnowledgeSoundness l s admissible relIn validOutput draw ε ↔
      ∃ F : KnowledgeStateFunction l s S W Win admissible relIn validOutput,
        F.LocallyBounded draw ε := Iff.rfl

namespace KnowledgeStateFunction

variable {l}

/-! ### Restriction below a first move -/

/-- The state function below a first move. Its input witnesses are the witnesses after that
move, so its root obligation is vacuous; every other field is the original one. -/
def child {a : P.A} {next : P.B a → FreeM P PUnit.{1}} {S : Type} {Win : S → Type}
    {W : S → PathAlong l (.liftBind a next) → Type} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    (F : KnowledgeStateFunction l (.liftBind a next) S W Win admissible relIn validOutput)
    (x : Move l a) :
    KnowledgeStateFunction l (next (l.toFunB a x)) S (fun stmt tr => W stmt ⟨x, tr⟩)
      (fun stmt => F.Witness stmt (.down (l.toFunB a x) (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩) (fun _ => False)
      (fun _ _ => True) (fun stmt tr w => validOutput stmt ⟨x, tr⟩ w) where
  Witness stmt {_} sp history := F.Witness stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩
  toFun stmt {_} sp history := F.toFun stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩
  extractRoot _ w := w
  extractStep stmt {_ _} sp history := F.extractStep stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩
  extractLeaf stmt sp history := F.extractLeaf stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩
  root _ h := h.elim
  send sp history := F.send (.down _ sp) ⟨⟨x, rfl⟩, history⟩
  leaf sp history := F.leaf (.down _ sp) ⟨⟨x, rfl⟩, history⟩

/-! ### Sequential composition -/

variable {S : Type}

/-- Witness types along the composite. -/
def appendWitness : {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    (W₁ : ∀ (_stmt : S) {t} (sp : Cursor.Spine s₁ t), PrefixMoves l sp → Type) →
    (W₂ : (tr₁ : PathAlong l s₁) →
      ∀ (_stmt : S) {t} (sp : Cursor.Spine (s₂ (projectPathAlong l s₁ tr₁)) t), PrefixMoves l sp →
        Type) →
    ∀ (_stmt : S) {t} (sp : Cursor.Spine (s₁.append s₂) t), PrefixMoves l sp → Type
  | .pure _, _, _, W₂, stmt, _, sp, history => W₂ ⟨⟩ stmt sp history
  | .liftBind _ _, _, W₁, _, stmt, _, .root _, _ => W₁ stmt (.root _) ⟨⟩
  | .liftBind a cont, s₂, W₁, W₂, stmt, _, .down b tail, history =>
    PrefixMoves.downCases l (a := a) (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩))
      (motive := fun _ _ _ => Type)
      (fun x tail history => appendWitness (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (fun stmt {_} sp history => W₁ stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩) (fun tr => W₂ ⟨x, tr⟩)
        stmt tail history)
      b tail history

/-- The composite state on the witness types `appendWitness`: the prefix state before the seam and
the suffix state after it. -/
def appendToFun :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ {t} (sp : Cursor.Spine (s₁.append s₂) t) (history : PrefixMoves l sp) (stmt : S),
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history → Prop
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, F₂, _, sp, history => fun stmt => (F₂ ⟨⟩).toFun stmt
    sp history
  | .liftBind _ _, _, _, _, _, _, _, _, _, _, _, F₁, _, _, .root _, _ => fun stmt => F₁.toFun stmt
    (.root _) ⟨⟩
  | .liftBind a cont, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂, t,
      .down b tail, history =>
    PrefixMoves.downCases l (a := a) (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩))
      (t := t)
      (motive := fun b tail history => (stmt : S) →
        appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt (.down b tail) history
          →
          Prop)
      (fun x tail history => appendToFun (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) tail history)
      b tail history

/-- Input extraction of the composite: through the prefix leaf and the suffix input extraction
when the prefix is a leaf, and the prefix input extraction otherwise. -/
def appendExtractRoot :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (stmt : S) → appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt (.root _) ⟨⟩ →
      Win stmt
  | .pure _, _, _, _, _, _, _, _, _, _, _, F₁, F₂ => fun stmt w =>
    F₁.extractRoot stmt (F₁.extractLeaf stmt (.root _) ⟨⟩ ((F₂ ⟨⟩).extractRoot stmt w))
  | .liftBind _ _, _, _, _, _, _, _, _, _, _, _, F₁, _ => F₁.extractRoot

/-- Backward extraction of the composite: the prefix step, entering the suffix through
`appendExtractRoot` where a move reaches the seam, and the suffix step after it. -/
def appendExtractStep :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ {a' : P.A} {next' : P.B a' → FreeM P PUnit.{1}}
      (sp : Cursor.Spine (s₁.append s₂) (.liftBind a' next')) (history : PrefixMoves l sp),
      (stmt : S) → (y : Move l a') →
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt
        (sp.comp (.down (l.toFunB a' y) (.root _))) (PrefixMoves.snoc l sp history y) →
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, F₂, _, _, sp, history =>
    fun stmt => (F₂ ⟨⟩).extractStep stmt sp history
  | .liftBind a _, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂, _, _,
      .root _, _ => fun stmt y w =>
    F₁.extractStep stmt (.root _) ⟨⟩ y (appendExtractRoot
        (s₂ := fun p => s₂ ⟨l.toFunB a y, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨y, tr⟩) (W := fun stmt tr => W stmt ⟨y, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨y, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨y, tr⟩) (relMid := fun tr => relMid ⟨y, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨y, tr⟩ w)
        (F₁.child y) (fun tr => F₂ ⟨y, tr⟩) stmt w)
  | .liftBind a cont, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂,
      a', next',
      .down b tail, history =>
    PrefixMoves.downCases l (a := a) (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩))
      (t := .liftBind a' next')
      (motive := fun b (tail : Cursor.Spine ((cont b).append (fun p => s₂ ⟨b, p⟩))
          (.liftBind a' next')) history =>
        let sp : Cursor.Spine ((FreeM.liftBind a cont).append s₂) (.liftBind a' next') :=
          .down (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩)) b tail
        (stmt : S) → (y : Move l a') →
        appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt
          (sp.comp (.down (l.toFunB a' y) (.root (next' (l.toFunB a' y)))))
          (PrefixMoves.snoc l sp history y) →
        appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history)
      (fun x tail history => appendExtractStep (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) tail history)
      b tail history

/-- Leaf extraction of the composite, which is the suffix leaf extraction. -/
def appendExtractLeaf :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ (sp : Cursor.Spine (s₁.append s₂) (.pure ⟨⟩)) (history : PrefixMoves l sp) (stmt : S),
      W stmt (PrefixMoves.complete l sp history) →
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, F₂, sp, history => fun stmt => (F₂ ⟨⟩).extractLeaf
    stmt sp history
  | .liftBind a cont, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂,
      .down b tail, history =>
    PrefixMoves.downCases l (a := a) (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩))
      (t := .pure ⟨⟩)
      (motive := fun b tail history => (stmt : S) → W stmt (PrefixMoves.complete l (.down b tail)
        history) →
        appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt (.down b tail) history)
      (fun x tail history => appendExtractLeaf (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) tail history)
      b tail history

/-- The composite root state implies the prefix root state at a witness with the same input
extraction. -/
theorem appendToFun_root :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ stmt w, appendToFun F₁ F₂ (.root _) ⟨⟩ stmt w →
      ∃ w₁, appendExtractRoot F₁ F₂ stmt w = F₁.extractRoot stmt w₁ ∧
        F₁.toFun stmt (.root _) ⟨⟩ w₁
  | .pure _, _, _, _, _, _, _, _, _, _, _, F₁, _, seam, stmt, w, h =>
    ⟨_, rfl, F₁.leaf _ _ stmt _ (seam ⟨⟩ stmt w h)⟩
  | .liftBind _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, w, h => ⟨w, rfl, h⟩

/-- The composite state is preserved backwards across sender moves. -/
theorem appendToFun_send :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ {a' : P.A} {next' : P.B a' → FreeM P PUnit.{1}}
      (sp : Cursor.Spine (s₁.append s₂) (.liftBind a' next')) (history : PrefixMoves l sp) stmt,
      owner l a' = .sender → ∀ y w,
      appendToFun F₁ F₂ (sp.comp (.down (l.toFunB a' y) (.root _)))
        (PrefixMoves.snoc l sp history y) stmt w →
      appendToFun F₁ F₂ sp history stmt (appendExtractStep F₁ F₂ sp history stmt y w)
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, F₂, _, _, _, sp, history, stmt, ho, y, w, h =>
    (F₂ ⟨⟩).send sp history stmt ho y w h
  | .liftBind a _, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂,
      seam, _, _, .root _, _, stmt, ho, y, w, h => by
    obtain ⟨w₁, he, h₁⟩ := appendToFun_root (s₂ := fun p => s₂ ⟨l.toFunB a y, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨y, tr⟩) (W := fun stmt tr => W stmt ⟨y, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨y, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨y, tr⟩) (relMid := fun tr => relMid ⟨y, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨y, tr⟩ w)
          (F₁.child y) (fun tr => F₂ ⟨y, tr⟩) (fun tr => seam ⟨y, tr⟩) stmt w h
    replace he : _ = w₁ := he
    subst he
    exact F₁.send (.root _) ⟨⟩ stmt ho y _ h₁
  | .liftBind a _, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂,
      seam, _, _, .down _ tail, history, stmt, ho, y, w, h => by
    rcases history with ⟨⟨x, rfl⟩, history⟩
    exact appendToFun_send (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) tail history stmt ho y w
          h

/-- Accepted suffix outputs give the composite state at the leaf. -/
theorem appendToFun_leaf :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (sp : Cursor.Spine (s₁.append s₂) (.pure ⟨⟩)) (history : PrefixMoves l sp) stmt w,
      validOutput stmt (PrefixMoves.complete l sp history) w →
      appendToFun F₁ F₂ sp history stmt (appendExtractLeaf F₁ F₂ sp history stmt w)
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, F₂, _, sp, history, stmt, w, h =>
    (F₂ ⟨⟩).leaf sp history stmt w h
  | .liftBind a _, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂, seam,
      .down _ tail, history, stmt, w, h => by
    rcases history with ⟨⟨x, rfl⟩, history⟩
    exact appendToFun_leaf (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) tail history stmt w h

section append

variable {s₁ : FreeM P PUnit.{1}} {s₂ : Path s₁ → FreeM P PUnit.{1}}
  {Wmid : S → PathAlong l s₁ → Type} {W : S → PathAlong l (s₁.append s₂) → Type} {Win : S → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop}
  {admissible₂ : PathAlong l s₁ → S → Prop}
  {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop}

/-- Sequential composition of knowledge state functions. The suffix state functions are indexed
by the prefix transcript, so their states, witnesses and extractors may read every prefix
payload. The seam asks that a suffix root state extracts a witness that the prefix accepts as a
valid output on that transcript. -/
def append (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) :
    KnowledgeStateFunction l (s₁.append s₂) S W Win admissible relIn validOutput where
  Witness := appendWitness F₁.Witness (fun tr => (F₂ tr).Witness)
  toFun stmt {_} sp history := appendToFun F₁ F₂ sp history stmt
  extractRoot := appendExtractRoot F₁ F₂
  extractStep stmt {_ _} sp history := appendExtractStep F₁ F₂ sp history stmt
  extractLeaf stmt sp history := appendExtractLeaf F₁ F₂ sp history stmt
  root stmt hadm w h := by
    obtain ⟨w₁, he, h₁⟩ := appendToFun_root F₁ F₂ seam stmt w h
    exact he ▸ F₁.root stmt hadm w₁ h₁
  send := appendToFun_send F₁ F₂ seam
  leaf := appendToFun_leaf F₁ F₂ seam

/-- A composite root state comes from a prefix root state with the same input extraction. -/
theorem root_append
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) (w : (append F₁ F₂ seam).Witness stmt (.root _) ⟨⟩)
    (h : (append F₁ F₂ seam).toFun stmt (.root _) ⟨⟩ w) :
    ∃ w₁, (append F₁ F₂ seam).extractRoot stmt w = F₁.extractRoot stmt w₁ ∧
      F₁.toFun stmt (.root _) ⟨⟩ w₁ :=
  appendToFun_root F₁ F₂ seam stmt w h

end append

/-- Backward extraction below a first move is the extraction of the restricted state function.
The output witness is transported to the completed transcript of either side. -/
theorem extractFrom_child {a : P.A} {next : P.B a → FreeM P PUnit.{1}} {Win : S → Type}
    {W : S → PathAlong l (.liftBind a next) → Type} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    (F : KnowledgeStateFunction l (.liftBind a next) S W Win admissible relIn validOutput)
    (stmt : S) (x : Move l a) : ∀ {t : FreeM P PUnit.{1}}
      (sp : Cursor.Spine (next (l.toFunB a x)) t) (history : PrefixMoves l sp)
      (tr : PathAlong l t) {α : Type} (w : α)
      (e : α = W stmt (PrefixMoves.completeWith l (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr))
      (e' : α = W stmt ⟨x, PrefixMoves.completeWith l sp history tr⟩),
      F.extractFrom stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr (cast e w) =
        (F.child x).extractFrom stmt sp history tr (cast e' w)
  | .pure _, _, _, _, _, _, _, _ => rfl
  | .liftBind _ _, sp, history, ⟨y, tr⟩, _, w, e, e' =>
    congrArg ((F.child x).extractStep stmt sp history y)
      (extractFrom_child F stmt x (sp.comp _) (PrefixMoves.snoc l sp history y) tr w e e')

/-- Direct-family form of `extractFrom_child`: an output witness of the restricted state function's
completed transcript is passed unchanged to the restricted extraction, and transported by
`PrefixMoves.completeWith_down` on the left. -/
theorem extractFrom_child_family {a : P.A} {next : P.B a → FreeM P PUnit.{1}} {Win : S → Type}
    {W : S → PathAlong l (.liftBind a next) → Type} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    (F : KnowledgeStateFunction l (.liftBind a next) S W Win admissible relIn validOutput)
    (stmt : S) (x : Move l a) {t : FreeM P PUnit.{1}}
    (sp : Cursor.Spine (next (l.toFunB a x)) t) (history : PrefixMoves l sp)
    (tr : PathAlong l t) (w : W stmt ⟨x, PrefixMoves.completeWith l sp history tr⟩) :
    F.extractFrom stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr
        (cast (congrArg (W stmt) (PrefixMoves.completeWith_down l x sp history tr).symm) w) =
      (F.child x).extractFrom stmt sp history tr w :=
  extractFrom_child F stmt x sp history tr w _ rfl

/-- Over a leaf prefix, backward extraction of the composite is suffix extraction. -/
theorem extractFrom_append_pure {u : PUnit.{1}}
    {s₂ : Path (FreeM.pure (P := P) u) → FreeM P PUnit.{1}}
    {Wmid : S → PathAlong l (FreeM.pure u) → Type} {W : S → PathAlong l ((FreeM.pure u).append s₂) →
      Type}
    {Win : S → Type} {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validMid : (stmt : S) → (tr : PathAlong l (FreeM.pure u)) → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong l (FreeM.pure u) → S → Prop}
    {relMid : (tr₁ : PathAlong l (FreeM.pure u)) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l ((FreeM.pure u).append s₂)) → W stmt tr → Prop}
    (F₁ : KnowledgeStateFunction l (FreeM.pure u) S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l (FreeM.pure u)) →
      KnowledgeStateFunction l (s₂ (projectPathAlong l _ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l _ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l _ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) : ∀ {t : FreeM P PUnit.{1}} (sp : Cursor.Spine (s₂ ⟨⟩) t)
      (history : PrefixMoves l sp) (tr : PathAlong l t)
      (w : W stmt (PrefixMoves.completeWith l sp history tr)),
      (append (s₂ := s₂) F₁ F₂ seam).extractFrom stmt sp history tr w =
        (F₂ ⟨⟩).extractFrom stmt sp history tr w
  | .pure _, _, _, _, _ => rfl
  | .liftBind _ _, sp, history, ⟨y, tr⟩, w =>
    congrArg ((F₂ ⟨⟩).extractStep stmt sp history y)
      (extractFrom_append_pure F₁ F₂ seam stmt (sp.comp _) (PrefixMoves.snoc l sp history y)
        tr w)

/-- Below a first prefix move, backward extraction of the composite is extraction of the
composite of the restricted prefix state function with the matching suffix family. The output
witness is transported to the completed transcript of either side. -/
theorem extractFrom_append_down {a : P.A} {cont : P.B a → FreeM P PUnit.{1}}
    {s₂ : Path (FreeM.liftBind a cont) → FreeM P PUnit.{1}}
    {Wmid : S → PathAlong l (FreeM.liftBind a cont) → Type}
    {W : S → PathAlong l ((FreeM.liftBind a cont).append s₂) → Type} {Win : S → Type}
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validMid : (stmt : S) → (tr : PathAlong l (FreeM.liftBind a cont)) → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong l (FreeM.liftBind a cont) → S → Prop}
    {relMid : (tr₁ : PathAlong l (FreeM.liftBind a cont)) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l ((FreeM.liftBind a cont).append s₂)) →
      W stmt tr → Prop}
    (F₁ : KnowledgeStateFunction l (FreeM.liftBind a cont) S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l (FreeM.liftBind a cont)) →
      KnowledgeStateFunction l (s₂ (projectPathAlong l _ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l _ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l _ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) (x : Move l a) : ∀ {t : FreeM P PUnit.{1}}
      (sp : Cursor.Spine ((cont (l.toFunB a x)).append (fun p => s₂ ⟨l.toFunB a x, p⟩)) t)
      (history : PrefixMoves l sp) (tr : PathAlong l t) {α : Type} (w : α)
      (e : α = W stmt (PrefixMoves.completeWith l (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr))
      (e' : α = W stmt ⟨x, PrefixMoves.completeWith l sp history tr⟩),
      (append (s₂ := s₂) F₁ F₂ seam).extractFrom stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr
          (cast e w) =
        (append (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩)).extractFrom
            stmt sp history tr (cast e' w)
  | .pure _, _, _, _, _, _, _, _ => rfl
  | .liftBind _ _, sp, history, ⟨y, tr⟩, _, w, e, e' =>
    congrArg ((append (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩)).extractStep
            stmt sp history y)
      (extractFrom_append_down F₁ F₂ seam stmt x (sp.comp _) (PrefixMoves.snoc l sp history y)
        tr w e e')

/-- Direct-family form of `extractFrom_append_down`: an output witness of the composite's
completed transcript below the first move is passed unchanged to the restricted composite's
extraction, and transported by `PrefixMoves.completeWith_down` on the left. -/
theorem extractFrom_append_down_family {a : P.A} {cont : P.B a → FreeM P PUnit.{1}}
    {s₂ : Path (FreeM.liftBind a cont) → FreeM P PUnit.{1}}
    {Wmid : S → PathAlong l (FreeM.liftBind a cont) → Type}
    {W : S → PathAlong l ((FreeM.liftBind a cont).append s₂) → Type} {Win : S → Type}
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validMid : (stmt : S) → (tr : PathAlong l (FreeM.liftBind a cont)) → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong l (FreeM.liftBind a cont) → S → Prop}
    {relMid : (tr₁ : PathAlong l (FreeM.liftBind a cont)) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l ((FreeM.liftBind a cont).append s₂)) →
      W stmt tr → Prop}
    (F₁ : KnowledgeStateFunction l (FreeM.liftBind a cont) S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l (FreeM.liftBind a cont)) →
      KnowledgeStateFunction l (s₂ (projectPathAlong l _ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l _ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l _ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) (x : Move l a) {t : FreeM P PUnit.{1}}
    (sp : Cursor.Spine ((cont (l.toFunB a x)).append (fun p => s₂ ⟨l.toFunB a x, p⟩)) t)
    (history : PrefixMoves l sp) (tr : PathAlong l t)
    (w : W stmt ⟨x, PrefixMoves.completeWith l sp history tr⟩) :
    (append (s₂ := s₂) F₁ F₂ seam).extractFrom stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr
        (cast (congrArg (W stmt) (PrefixMoves.completeWith_down l
          (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩)) x sp history tr).symm) w) =
      (append (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩)).extractFrom
          stmt sp history tr w :=
  extractFrom_append_down F₁ F₂ seam stmt x sp history tr w _ rfl

/-- Backward extraction along an appended transcript runs the suffix extraction and then the
prefix extraction from its input witness. -/
theorem extractAlong_append :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (stmt : S) (tr₁ : PathAlong l s₁) (tr₂ : PathAlong l (s₂ (projectPathAlong l s₁ tr₁)))
      (w : W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)),
      (append (s₂ := s₂) F₁ F₂ seam).extractAlong stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w =
        F₁.extractAlong stmt tr₁ ((F₂ tr₁).extractAlong stmt tr₂ w)
  | .pure _, _, _, _, _, _, _, _, _, _, _, F₁, F₂, seam, stmt, _, tr₂, _ =>
    congrArg (fun z => F₁.extractRoot stmt (F₁.extractLeaf stmt (.root _) ⟨⟩
      ((F₂ ⟨⟩).extractRoot stmt z)))
      (extractFrom_append_pure F₁ F₂ seam stmt (.root _) ⟨⟩ tr₂ _)
  | .liftBind a _, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂, seam,
      stmt, ⟨x, tr₁⟩, tr₂, w =>
    congrArg (fun z => F₁.extractRoot stmt (F₁.extractStep stmt (.root _) ⟨⟩ x z))
      (((congrArg (appendExtractRoot (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) stmt)
        (extractFrom_append_down F₁ F₂ seam stmt x (.root _) ⟨⟩ _ w
          (congrArg (W stmt) (PrefixMoves.completeWith_root l _).symm)
          (congrArg (fun tr => W stmt ⟨x, tr⟩) (PrefixMoves.completeWith_root l _).symm))).trans
        (extractAlong_append (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) stmt tr₁ tr₂ w)).trans
        (extractFrom_child F₁ stmt x (.root _) ⟨⟩ tr₁ ((F₂ ⟨x, tr₁⟩).extractAlong stmt tr₂ w)
          (congrArg (Wmid stmt) (PrefixMoves.completeWith_root l (s := .liftBind a _) ⟨x,
            tr₁⟩).symm)
          (congrArg (fun tr => Wmid stmt ⟨x, tr⟩) (PrefixMoves.completeWith_root l tr₁).symm)).symm)

/-- At a completed composite transcript, the composite state on the terminal witness is the
suffix state on its own terminal witness. -/
theorem toFun_terminalWitness_append :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (stmt : S) (tr₁ : PathAlong l s₁) (tr₂ : PathAlong l (s₂ (projectPathAlong l s₁ tr₁)))
      (w : W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)),
      (append (s₂ := s₂) F₁ F₂ seam).toFun
          stmt (completeSpine l (PathAlong.append l s₁ s₂ tr₁ tr₂)) (completeMoves l _)
          ((append (s₂ := s₂) F₁ F₂ seam).terminalWitness stmt _ w) ↔
        (F₂ tr₁).toFun stmt (completeSpine l tr₂) (completeMoves l tr₂)
          ((F₂ tr₁).terminalWitness stmt tr₂ w)
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | .liftBind a _, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂, seam,
      stmt, ⟨x, tr₁⟩, tr₂, w =>
    toFun_terminalWitness_append (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) stmt tr₁ tr₂ w

/-- A bound for a state function survives restriction below a first move, with the draws and
errors restricted to the challenge nodes below it. -/
theorem BoundedAt.child {a : P.A} {next : P.B a → FreeM P PUnit.{1}} {Win : S → Type}
    {W : S → PathAlong l (.liftBind a next) → Type} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    {F : KnowledgeStateFunction l (.liftBind a next) S W Win admissible relIn validOutput}
    {draw : QueryImpl (challengeSpec l (.liftBind a next)) ProbComp}
    {ε : ChallengeNode l (.liftBind a next) → ℝ≥0∞} {stmt : S} (h : F.BoundedAt draw ε stmt)
    (x : Move l a) :
    (F.child x).BoundedAt (fun c => draw ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
      (fun c => ε ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) stmt :=
  fun a' next' sp ho history => h a' next' (.down _ sp) ho ⟨⟨x, rfl⟩, history⟩

/-- Bounds compose along the composite: prefix challenges keep the prefix bound and suffix
challenges keep the bound of the suffix state function at their prefix transcript. -/
theorem BoundedAt.append :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type} → {W : S → PathAlong l (s₁.append s₂) → Type} → {Win : S →
      Type} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (draw₁ : QueryImpl (challengeSpec l s₁) ProbComp)
      (draw₂ : (p : Path s₁) → QueryImpl (challengeSpec l (s₂ p)) ProbComp)
      (ε₁ : ChallengeNode l s₁ → ℝ≥0∞) (ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞)
      (stmt : S), F₁.BoundedAt draw₁ ε₁ stmt →
      (∀ tr₁, (F₂ tr₁).BoundedAt (draw₂ (projectPathAlong l s₁ tr₁))
        (ε₂ (projectPathAlong l s₁ tr₁)) stmt) →
      (append (s₂ := s₂) F₁ F₂ seam).BoundedAt (combineDraw l s₁ s₂ draw₁ draw₂)
        (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) stmt
  | .pure _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h₂ => h₂ ⟨⟩
  | .liftBind a cont, s₂, Wmid, W, _, _, _, validMid, admissible₂, relMid, validOutput, F₁, F₂,
      seam, draw₁, draw₂, ε₁, ε₂, stmt, h₁, h₂ => by
    intro a' next' sp ho history
    cases sp with
    | root =>
      refine le_trans (measure_mono ?_) (h₁ a cont (.root _) ho ⟨⟩)
      rintro y ⟨wit, hbad, hgood⟩
      obtain ⟨w₁, he, hw₁⟩ := appendToFun_root (s₂ := fun p => s₂ ⟨l.toFunB a y, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨y, tr⟩) (W := fun stmt tr => W stmt ⟨y, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨y, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨y, tr⟩) (relMid := fun tr => relMid ⟨y, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨y, tr⟩ w)
          (F₁.child y) (fun tr => F₂ ⟨y, tr⟩) (fun tr => seam ⟨y, tr⟩) stmt wit hgood
      replace he : _ = w₁ := he
      subst he
      exact ⟨_, hbad, hw₁⟩
    | down _ tail =>
      rcases history with ⟨⟨x, rfl⟩, history⟩
      exact BoundedAt.append (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩)
        (fun c => draw₁ ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) (fun p => draw₂ ⟨_, p⟩)
        (fun c => ε₁ ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) (fun p => ε₂ ⟨_, p⟩) stmt
        (h₁.child x) (fun tr => h₂ ⟨x, tr⟩) a' next' tail ho history

section restrict

variable {s : FreeM P PUnit.{1}} {Win : S → Type} {W : S → PathAlong l s → Type} {admissible : S →
    Prop}
  {relIn : (stmt : S) → Win stmt → Prop} {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt
    tr → Prop}

/-- The state function whose states, and valid outputs, apply to admissible statements only. -/
def guard (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput) :
    KnowledgeStateFunction l s S W Win admissible relIn
      (fun stmt tr w => admissible stmt → validOutput stmt tr w) where
  Witness := F.Witness
  toFun stmt {_} sp history w := admissible stmt → F.toFun stmt sp history w
  extractRoot := F.extractRoot
  extractStep := F.extractStep
  extractLeaf := F.extractLeaf
  root stmt hadm w h := F.root stmt hadm w (h hadm)
  send sp history stmt ho x w h hadm := F.send sp history stmt ho x w (h hadm)
  leaf sp history stmt w h hadm := F.leaf sp history stmt w (h hadm)

/-- Guarding keeps the bound at an admissible statement. -/
theorem BoundedAt.guard {F : KnowledgeStateFunction l s S W Win admissible relIn validOutput}
    {draw : QueryImpl (challengeSpec l s) ProbComp} {ε : ChallengeNode l s → ℝ≥0∞} {stmt : S}
    (h : F.BoundedAt draw ε stmt) (hadm : admissible stmt) : F.guard.BoundedAt draw ε stmt :=
  fun a next sp ho history => by
    refine le_trans (measure_mono ?_) (h a next sp ho history)
    rintro x ⟨wit, hbad, hgood⟩
    exact ⟨wit, fun h' => hbad fun _ => h', hgood hadm⟩

/-- Conjoin a statement predicate to all states and to the extracted input relation.
The output obligation supplies the same predicate at every terminal cursor. -/
def condition (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput)
    (gate : S → Prop)
    {validOutput' : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
    (hout : ∀ stmt tr w, validOutput' stmt tr w → gate stmt ∧ validOutput stmt tr w) :
    KnowledgeStateFunction l s S W Win admissible (fun stmt w => gate stmt ∧ relIn stmt w)
      validOutput' where
  Witness := F.Witness
  toFun stmt {_} sp history w := gate stmt ∧ F.toFun stmt sp history w
  extractRoot := F.extractRoot
  extractStep := F.extractStep
  extractLeaf := F.extractLeaf
  root stmt ha w h := ⟨h.1, F.root stmt ha w h.2⟩
  send sp history stmt ho x w h := ⟨h.1, F.send sp history stmt ho x w h.2⟩
  leaf sp history stmt w h :=
    ⟨(hout stmt _ w h).1, F.leaf sp history stmt w (hout stmt _ w h).2⟩

/-- Conjoining a statement predicate does not enlarge the local bad-challenge event. -/
theorem BoundedAt.condition {F : KnowledgeStateFunction l s S W Win admissible relIn validOutput}
    {gate : S → Prop}
    {validOutput' : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
    {hout : ∀ stmt tr w, validOutput' stmt tr w → gate stmt ∧ validOutput stmt tr w}
    {draw : QueryImpl (challengeSpec l s) ProbComp} {ε : ChallengeNode l s → ℝ≥0∞} {stmt : S}
    (h : F.BoundedAt draw ε stmt) : (F.condition gate hout).BoundedAt draw ε stmt := by
  intro a next sp ho history
  refine le_trans (measure_mono ?_) (h a next sp ho history)
  rintro x ⟨w, hbad, hgood⟩
  exact ⟨w, fun h' => hbad ⟨hgood.1, h'⟩, hgood.2⟩

/-- Pull back statements and output witnesses, and map the extracted input witnesses. -/
def comap {S' : Type} {Win' : S' → Type} {W' : S' → PathAlong l s → Type}
    (f : S' → S) (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput)
    (inputMap : ∀ stmt, Win (f stmt) → Win' stmt)
    (outputMap : ∀ stmt tr, W' stmt tr → W (f stmt) tr)
    {validOutput' : (stmt : S') → (tr : PathAlong l s) → W' stmt tr → Prop}
    (hout : ∀ stmt tr w, validOutput' stmt tr w →
      validOutput (f stmt) tr (outputMap stmt tr w)) :
    KnowledgeStateFunction l s S' W' Win' (fun stmt => admissible (f stmt))
      (fun stmt w => ∃ v, relIn (f stmt) v ∧ inputMap stmt v = w) validOutput' where
  Witness stmt := F.Witness (f stmt)
  toFun stmt := F.toFun (f stmt)
  extractRoot stmt w := inputMap stmt (F.extractRoot (f stmt) w)
  extractStep stmt := F.extractStep (f stmt)
  extractLeaf stmt sp history w := F.extractLeaf (f stmt) sp history (outputMap stmt _ w)
  root stmt h w hw := ⟨_, F.root (f stmt) h w hw, rfl⟩
  send sp history stmt := F.send sp history (f stmt)
  leaf sp history stmt w h := F.leaf sp history (f stmt) _ (hout stmt _ w h)

/-- Pulling back statements and witness maps keeps the original local bound. -/
theorem BoundedAt.comap {S' : Type} {Win' : S' → Type} {W' : S' → PathAlong l s → Type}
    {f : S' → S} {F : KnowledgeStateFunction l s S W Win admissible relIn validOutput}
    {inputMap : ∀ stmt, Win (f stmt) → Win' stmt}
    {outputMap : ∀ stmt tr, W' stmt tr → W (f stmt) tr}
    {validOutput' : (stmt : S') → (tr : PathAlong l s) → W' stmt tr → Prop}
    {hout : ∀ stmt tr w, validOutput' stmt tr w →
      validOutput (f stmt) tr (outputMap stmt tr w)}
    {draw : QueryImpl (challengeSpec l s) ProbComp} {ε : ChallengeNode l s → ℝ≥0∞} {stmt : S'}
    (h : F.BoundedAt draw ε (f stmt)) :
    (F.comap f inputMap outputMap hout).BoundedAt draw ε stmt := h

end restrict

section security

variable {s₁ : FreeM P PUnit.{1}} {s₂ : Path s₁ → FreeM P PUnit.{1}}
  {Wmid : S → PathAlong l s₁ → Type} {W : S → PathAlong l (s₁.append s₂) → Type} {Win : S → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop}
  {admissible₂ : PathAlong l s₁ → S → Prop}
  {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop}

/-- Local bounds compose: with suffix admissibility implied by prefix admissibility, the
composite is bounded by the prefix errors at prefix challenges and the suffix errors at suffix
challenges. -/
theorem LocallyBounded.append
    {F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid}
    {F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction l (s₂ (projectPathAlong l s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)}
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    {draw₁ : QueryImpl (challengeSpec l s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec l (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode l s₁ → ℝ≥0∞} {ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞}
    (h₁ : F₁.LocallyBounded draw₁ ε₁)
    (h₂ : ∀ tr₁, (F₂ tr₁).LocallyBounded (draw₂ (projectPathAlong l s₁ tr₁))
      (ε₂ (projectPathAlong l s₁ tr₁)))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt) :
    (append F₁ F₂ seam).LocallyBounded (combineDraw l s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) :=
  fun stmt h => BoundedAt.append F₁ F₂ seam draw₁ draw₂ ε₁ ε₂ stmt (h₁ stmt h)
    fun tr₁ => h₂ tr₁ stmt (hadm tr₁ stmt h)

end security

end KnowledgeStateFunction

section security

variable {s₁ : FreeM P PUnit.{1}} {s₂ : Path s₁ → FreeM P PUnit.{1}} {S : Type} {Win : S → Type}
  {Wmid : S → PathAlong l s₁ → Type} {W : S → PathAlong l (s₁.append s₂) → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop}
  {draw₁ : QueryImpl (challengeSpec l s₁) ProbComp}
  {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec l (s₂ p)) ProbComp}
  {ε₁ : ChallengeNode l s₁ → ℝ≥0∞} {ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞}

/-- Round-by-round knowledge soundness composes sequentially. The suffix is knowledge sound at
every prefix transcript for a transcript-dependent intermediate relation; on admissible
statements, suffix admissibility holds and the intermediate relation implies a valid prefix
output. The composite error is the prefix error at prefix challenges and the suffix error at
suffix challenges. -/
theorem rbrKnowledgeSoundness_append {admissible₂ : PathAlong l s₁ → S → Prop}
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
    (h₁ : rbrKnowledgeSoundness l s₁ admissible relIn validMid draw₁ ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundness l (s₂ (projectPathAlong l s₁ tr₁)) (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)
      (draw₂ (projectPathAlong l s₁ tr₁)) (ε₂ (projectPathAlong l s₁ tr₁)))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt)
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ stmt w → validMid stmt tr₁ w) :
    rbrKnowledgeSoundness l (s₁.append s₂) admissible relIn validOutput
      (combineDraw l s₁ s₂ draw₁ draw₂) (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  obtain ⟨F₁, hF₁⟩ := h₁
  choose F₂ hF₂ using h₂
  exact ⟨KnowledgeStateFunction.append F₁.guard F₂
      (fun tr₁ stmt w h hadm' => glue tr₁ stmt _ hadm'
        ((F₂ tr₁).root stmt (hadm tr₁ stmt hadm') w h)),
    KnowledgeStateFunction.LocallyBounded.append _
      (fun stmt h => KnowledgeStateFunction.BoundedAt.guard (hF₁ stmt h) h) hF₂ hadm⟩

/-- Sequential composition through a deterministic intermediate statement. The suffix is knowledge
sound for its own statements; `mid` computes the suffix statement from the input statement and
the prefix transcript, and composite valid outputs are suffix valid outputs at that statement. -/
theorem rbrKnowledgeSoundness_append_of_mid {T : Type} (mid : S → PathAlong l s₁ → T)
    {Wmid₂ : PathAlong l s₁ → T → Type}
    {W₂ : (tr₁ : PathAlong l s₁) → T →
      PathAlong l (s₂ (projectPathAlong l s₁ tr₁)) → Type}
    {admissible₂ : PathAlong l s₁ → T → Prop}
    {relMid : (tr₁ : PathAlong l s₁) → (t : T) → Wmid₂ tr₁ t → Prop}
    {validOutput₂ : (tr₁ : PathAlong l s₁) → (t : T) →
      (tr₂ : PathAlong l (s₂ (projectPathAlong l s₁ tr₁))) → W₂ tr₁ t tr₂ → Prop}
    (h₁ : rbrKnowledgeSoundness l s₁ admissible relIn
      (fun stmt tr w => validMid stmt tr w) draw₁ ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundness l (s₂ (projectPathAlong l s₁ tr₁))
      (admissible₂ tr₁) (relMid tr₁) (validOutput₂ tr₁)
      (draw₂ (projectPathAlong l s₁ tr₁)) (ε₂ (projectPathAlong l s₁ tr₁)))
    (midWitness : ∀ stmt tr₁, Wmid₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ (mid stmt tr₁) w →
      validMid stmt tr₁ (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ w, validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w →
      validOutput₂ tr₁ (mid stmt tr₁) tr₂ (outWitness stmt tr₁ tr₂ w)) :
    rbrKnowledgeSoundness l (s₁.append s₂) admissible relIn validOutput
      (combineDraw l s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  apply rbrKnowledgeSoundness_append l (admissible₂ := fun tr stmt =>
    admissible₂ tr (mid stmt tr))
    (relMid := fun tr stmt w => ∃ v, relMid tr (mid stmt tr) v ∧ midWitness stmt tr v = w) h₁
  · intro tr₁
    obtain ⟨F, hF⟩ := h₂ tr₁
    exact ⟨F.comap (fun stmt => mid stmt tr₁) (fun stmt => midWitness stmt tr₁)
        (fun stmt tr₂ => outWitness stmt tr₁ tr₂) (fun stmt tr₂ w => hout stmt tr₁ tr₂ w),
      fun stmt h => hF _ h⟩
  · exact hadm
  · rintro tr₁ stmt w ha ⟨v, hv, rfl⟩
    exact glue tr₁ stmt v ha hv

end security

/-- A positive composite acceptance decomposes into two supported accepted decisions, with
exactly the same ambient state at their boundary. -/
theorem Verifier.validAcceptance_append {ι σ S T U : Type} {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T U)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : U → Prop) (stmt : S)
    (tr₁ : PathAlong plainSig s₁)
    (tr₂ : PathAlong plainSig (s₂ (projectPathAlong plainSig s₁ tr₁)))
    (h : (V₁.append V₂).validAcceptance impl langOut stmt
      (PathAlong.append plainSig s₁ s₂ tr₁ tr₂)) :
    ∃ state mid between out final,
      (some mid, between) ∈ support ((simulateQ impl
        (V₁.decide stmt (projectPathAlong plainSig s₁ tr₁) (toPlainView s₁ tr₁)).run).run state) ∧
      (some out, final) ∈ support ((simulateQ impl
        ((V₂ (projectPathAlong plainSig s₁ tr₁)).decide mid
          (projectPathAlong plainSig _ tr₂) (toPlainView _ tr₂)).run).run between) ∧
      langOut out := by
  obtain ⟨state, out, final, hr, ho⟩ := (Verifier.validAcceptance_iff_support ..).mp h
  rw [Verifier.append_decide_pathAlong] at hr
  simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨⟨_ | mid, between⟩, hp, hs⟩ := (mem_support_bind_iff _ _ _).mp hr
  · simp at hs
  · exact ⟨state, mid, between, out, final, hp, hs, ho⟩

/-- Standalone verifier knowledge theorems compose at an identified middle claim. The prefix
may use ambient effects; every supported accepted prefix result must equal the named claim.
The suffix theorem is stated solely for the suffix verifier and its own output relation. -/
theorem Verifier.rbrKnowledgeSoundness_append {ι σ S T U : Type} {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {Win : S → Type} {Wmid : S → PathAlong plainSig s₁ → Type}
    {Win₂ : PathAlong plainSig s₁ → T → Type} {W : S → PathAlong plainSig (s₁.append s₂) → Type}
    {W₂ : (tr₁ : PathAlong plainSig s₁) → T →
      PathAlong plainSig (s₂ (projectPathAlong plainSig s₁ tr₁)) → Type}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T U)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {relOut₁ : (stmt : S) → (tr : PathAlong plainSig s₁) → T → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong plainSig s₁ → T → Prop}
    {relMid : (tr₁ : PathAlong plainSig s₁) → (t : T) → Win₂ tr₁ t → Prop}
    {relOut₂ : (tr₁ : PathAlong plainSig s₁) → (t : T) →
      (tr₂ : PathAlong plainSig (s₂ (projectPathAlong plainSig s₁ tr₁))) → U → W₂ tr₁ t tr₂ → Prop}
    {relOut : (stmt : S) → (tr : PathAlong plainSig (s₁.append s₂)) → U → W stmt tr → Prop}
    {draw₁ : QueryImpl (challengeSpec plainSig s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec plainSig (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode plainSig s₁ → ℝ≥0∞}
    {ε₂ : (p : Path s₁) → ChallengeNode plainSig (s₂ p) → ℝ≥0∞}
    (mid : S → PathAlong plainSig s₁ → T)
    (accepted : ∀ stmt tr state t final,
      (some t, final) ∈ support ((simulateQ impl
        (V₁.decide stmt (projectPathAlong plainSig s₁ tr) (toPlainView s₁ tr)).run).run state) →
      t = mid stmt tr)
    (midWitness : ∀ stmt tr₁, Win₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (PathAlong.append plainSig s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (h₁ : V₁.rbrKnowledgeSoundness impl admissible relIn relOut₁ draw₁ ε₁)
    (h₂ : ∀ tr₁, (V₂ (projectPathAlong plainSig s₁ tr₁)).rbrKnowledgeSoundness impl
      (admissible₂ tr₁) (relMid tr₁) (relOut₂ tr₁) (draw₂ (projectPathAlong plainSig s₁ tr₁))
      (ε₂ (projectPathAlong plainSig s₁ tr₁)))
    (hadm : ∀ stmt tr₁, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ stmt tr₁ w, relMid tr₁ (mid stmt tr₁) w →
      relOut₁ stmt tr₁ (mid stmt tr₁) (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ out w,
      relOut stmt (PathAlong.append plainSig s₁ s₂ tr₁ tr₂) out w →
      relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) :
    (V₁.append V₂).rbrKnowledgeSoundness impl admissible relIn relOut
      (combineDraw plainSig s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) plainSig s₁ s₂ ε₁ ε₂) := by
  let valid := fun stmt tr w =>
    (V₁.append V₂).validAcceptance impl (fun out => relOut stmt tr out w) stmt tr
  let gate := fun tr₁ stmt => V₁.validAcceptance impl (fun t => t = mid stmt tr₁) stmt tr₁
  have decompose : ∀ stmt tr₁ tr₂ w,
      valid stmt (PathAlong.append plainSig s₁ s₂ tr₁ tr₂) w → gate tr₁ stmt ∧
      (V₂ (projectPathAlong plainSig s₁ tr₁)).validAcceptance impl
        (fun out => relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w))
        (mid stmt tr₁) tr₂ := by
    intro stmt tr₁ tr₂ w h
    obtain ⟨state, t, between, out, final, hp, hs, ho⟩ :=
      V₁.validAcceptance_append V₂ impl _ stmt tr₁ tr₂ h
    obtain rfl := accepted stmt tr₁ state t between hp
    exact ⟨(Verifier.validAcceptance_iff_support ..).mpr ⟨state, _, between, hp, rfl⟩,
      (Verifier.validAcceptance_iff_support ..).mpr
        ⟨between, out, final, hs, hout stmt tr₁ tr₂ out w ho⟩⟩
  apply Core.rbrKnowledgeSoundness_append plainSig h₁
    (admissible₂ := fun tr₁ stmt => admissible₂ tr₁ (mid stmt tr₁))
    (relMid := fun tr₁ stmt w => gate tr₁ stmt ∧
      ∃ v, relMid tr₁ (mid stmt tr₁) v ∧ midWitness stmt tr₁ v = w)
  · intro tr₁
    obtain ⟨F, hF⟩ := h₂ tr₁
    let G := F.comap (fun stmt => mid stmt tr₁) (fun stmt => midWitness stmt tr₁)
      (fun stmt tr₂ => outWitness stmt tr₁ tr₂)
      (fun stmt tr₂ w h => (decompose stmt tr₁ tr₂ w h).2)
    exact ⟨G.condition (gate tr₁) (fun stmt tr₂ w h => ⟨(decompose stmt tr₁ tr₂ w h).1, h⟩),
      fun stmt h => KnowledgeStateFunction.BoundedAt.condition (hF _ h)⟩
  · exact fun tr₁ stmt h => hadm stmt tr₁ h
  · rintro tr₁ stmt w _ ⟨hg, v, hv, rfl⟩
    obtain ⟨state, t, final, hp, ht⟩ := (Verifier.validAcceptance_iff_support ..).mp hg
    exact (Verifier.validAcceptance_iff_support ..).mpr
      ⟨state, t, final, hp, ht.symm ▸ glue stmt tr₁ v hv⟩

/-- A prefix that returns its middle claim without effects satisfies verifier knowledge
composition from the two standalone knowledge theorems. -/
theorem Verifier.rbrKnowledgeSoundness_append_of_pure {ι σ S T U : Type} {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {Win : S → Type} {Wmid : S → PathAlong plainSig s₁ → Type}
    {Win₂ : PathAlong plainSig s₁ → T → Type} {W : S → PathAlong plainSig (s₁.append s₂) → Type}
    {W₂ : (tr₁ : PathAlong plainSig s₁) → T →
      PathAlong plainSig (s₂ (projectPathAlong plainSig s₁ tr₁)) → Type}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T U)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {relOut₁ : (stmt : S) → (tr : PathAlong plainSig s₁) → T → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong plainSig s₁ → T → Prop}
    {relMid : (tr₁ : PathAlong plainSig s₁) → (t : T) → Win₂ tr₁ t → Prop}
    {relOut₂ : (tr₁ : PathAlong plainSig s₁) → (t : T) →
      (tr₂ : PathAlong plainSig (s₂ (projectPathAlong plainSig s₁ tr₁))) → U → W₂ tr₁ t tr₂ → Prop}
    {relOut : (stmt : S) → (tr : PathAlong plainSig (s₁.append s₂)) → U → W stmt tr → Prop}
    {draw₁ : QueryImpl (challengeSpec plainSig s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec plainSig (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode plainSig s₁ → ℝ≥0∞}
    {ε₂ : (p : Path s₁) → ChallengeNode plainSig (s₂ p) → ℝ≥0∞}
    (mid : S → PathAlong plainSig s₁ → T)
    (decision : ∀ stmt tr, V₁.decide stmt (projectPathAlong plainSig s₁ tr)
      (toPlainView s₁ tr) = pure (mid stmt tr))
    (midWitness : ∀ stmt tr₁, Win₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (PathAlong.append plainSig s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (h₁ : V₁.rbrKnowledgeSoundness impl admissible relIn relOut₁ draw₁ ε₁)
    (h₂ : ∀ tr₁, (V₂ (projectPathAlong plainSig s₁ tr₁)).rbrKnowledgeSoundness impl
      (admissible₂ tr₁) (relMid tr₁) (relOut₂ tr₁) (draw₂ (projectPathAlong plainSig s₁ tr₁))
      (ε₂ (projectPathAlong plainSig s₁ tr₁)))
    (hadm : ∀ stmt tr₁, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ stmt tr₁ w, relMid tr₁ (mid stmt tr₁) w →
      relOut₁ stmt tr₁ (mid stmt tr₁) (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ out w,
      relOut stmt (PathAlong.append plainSig s₁ s₂ tr₁ tr₂) out w →
      relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) :
    (V₁.append V₂).rbrKnowledgeSoundness impl admissible relIn relOut
      (combineDraw plainSig s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) plainSig s₁ s₂ ε₁ ε₂) := by
  apply Verifier.rbrKnowledgeSoundness_append V₁ V₂ impl mid _ midWitness outWitness
    h₁ h₂ hadm glue hout
  intro stmt tr state t final h
  rw [decision] at h
  simp only [OptionT.run_pure, simulateQ_pure, StateT.run_pure, _root_.support_pure,
    Set.mem_singleton_iff,
    Prod.mk.injEq, Option.some.injEq] at h
  exact h.1

/-- Positive oracle acceptance decomposes into supported accepted middle and final results.
The suffix uses the prefix's final ambient state and the actual routed resource data. -/
theorem OracleVerifier.validAcceptance_append {ι I J K σ S T U : Type}
    {ambient : OracleSpec ι} {A : I → Type} {B : J → Type} {C : K → Type}
    {inputs : OracleFamily I A} {middle : OracleFamily J B} {outputs : OracleFamily K C}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) T U middle outputs)
    (compatible : V₁.OutputCompatibility V₂) (impl : QueryImpl ambient (StateT σ ProbComp))
    (langOut : U × (∀ k, C k) → Prop) (stmt : S × (∀ i, A i))
    (tr : PathAlong oracleSig (s₁.append s₂))
    (h : (V₁.append V₂ compatible).validAcceptance impl langOut stmt tr) :
    let p := projectPathAlong oracleSig _ tr
    let v := toView _ tr
    let data := sumData stmt.2 (payloads _ tr)
    ∃ state mid between out final,
      (some mid, between) ∈ support ((simulateQ impl
        (V₁.decideWith stmt.1 (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
          ((OracleVerifier.prefixRoute (inputs := inputs) p).f data))).run state) ∧
      (some out, final) ∈ support ((simulateQ impl
        ((V₂ (Path.split s₁ s₂ p).1).decideWith mid (Path.split s₁ s₂ p).2
          (View.split s₁ s₂ p v).2
          ((OracleVerifier.suffixRoute V₁ stmt.1 p v).f data))).run between) ∧
      langOut (out, ((V₂ (Path.split s₁ s₂ p).1).outputMap mid (Path.split s₁ s₂ p).2
        (View.split s₁ s₂ p v).2).f ((OracleVerifier.suffixRoute V₁ stmt.1 p v).f data)) := by
  obtain ⟨state, out, final, hr, ho⟩ := (OracleVerifier.validAcceptance_iff_support ..).mp h
  obtain ⟨mid, between, hp, hs⟩ := V₁.support_append V₂ compatible impl stmt.1
    (projectPathAlong oracleSig _ tr) (toView _ tr) (sumData stmt.2 (payloads _ tr))
    state final out hr
  have hp' : some mid ∈ support (V₁.decideWith stmt.1
      (Path.split s₁ s₂ (projectPathAlong oracleSig _ tr)).1
      (View.split s₁ s₂ _ (toView _ tr)).1
      ((OracleVerifier.prefixRoute (inputs := inputs)
        (projectPathAlong oracleSig _ tr)).f (sumData stmt.2 (payloads _ tr)))) := by
    apply OracleComp.support_simulateQ_run'_subset impl _ state
    rw [StateT.run'_eq, _root_.support_map]
    exact ⟨(some mid, between), hp, rfl⟩
  have he := compatible.agrees stmt.1 (projectPathAlong oracleSig _ tr) (toView _ tr)
    (sumData stmt.2 (payloads _ tr)) mid hp'
  change langOut (out, (compatible.outputMap stmt.1 _ _).f _) at ho
  rw [he] at ho
  exact ⟨state, mid, between, out, final, hp, hs, ho⟩

end Interaction.Core
