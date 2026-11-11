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
errors combined along the protocol with `combinePrefixDraw`, which also combines the draws
(`LocallyBounded.append`).

`KnowledgeStateFunction.guard` restricts a state function to admissible statements and
`KnowledgeStateFunction.comap` changes its statement type; both keep the local bound. The
theorem `rbrKnowledgeSoundness_append_prefix` composes the security statements themselves. Its seam
is stated between the suffix input relation and the prefix output relation under the input promise;
`rbrKnowledgeSoundness_append_of_mid_prefix` is its special case where the suffix statement is a
function of the prefix statement and transcript.
-/

@[expose] public section

universe v uS uW uK uO uM uO₂ uS' uW' uT uI wI wJ wK uW₂ uA u

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

variable {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})

/-! ### Transcripts as cursors -/

/-- The terminal cursor reached by a completed transcript. -/
def completeSpine : {s : FreeM P PUnit.{u + 1}} → PathAlong l s → Cursor.Spine s (.pure ⟨⟩)
  | .pure _, _ => .root _
  | .liftBind a _, ⟨x, tr⟩ => .down (l.toFunB a x) (completeSpine tr)

/-- The full moves of a completed transcript, decorating its terminal cursor. -/
def completeMoves : {s : FreeM P PUnit.{u + 1}} → (tr : PathAlong l s) →
    PrefixMoves l (completeSpine l tr)
  | .pure _, _ => ⟨⟩
  | .liftBind _ _, ⟨x, tr⟩ => ⟨⟨x, rfl⟩, completeMoves tr⟩

/-- Completing the full moves of a transcript returns the transcript. -/
@[simp] theorem complete_completeMoves : {s : FreeM P PUnit.{u + 1}} → (tr : PathAlong l s) →
    PrefixMoves.complete l (completeSpine l tr) (completeMoves l tr) = tr
  | .pure _, _ => rfl
  | .liftBind a next, ⟨x, tr⟩ =>
    congrArg (Sigma.mk (β := fun y => PathAlong l (next (l.toFunB a y))) x)
      (complete_completeMoves (s := next _) tr)

/-- The terminal cursor of a transcript has one edge per move. -/
@[simp] theorem length_completeSpine_liftBind {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}}
    (x : Move l a) (tr : PathAlong l (next (l.toFunB a x))) :
    (completeSpine l (s := .liftBind a next) ⟨x, tr⟩).length =
      (completeSpine l tr).length + 1 := rfl

/-- The completed transcript through a full prefix followed by the rest of a transcript below its
cursor. -/
def PrefixMoves.completeWith {s : FreeM P PUnit.{u + 1}} : {t : FreeM P PUnit.{u + 1}} →
    (sp : Cursor.Spine s t) → PrefixMoves l sp → PathAlong l t → PathAlong l s
  | .pure _, sp, history, _ => PrefixMoves.complete l sp history
  | .liftBind _ _, sp, history, ⟨x, tr⟩ =>
    PrefixMoves.completeWith (sp.comp (.down _ (.root _))) (PrefixMoves.snoc l sp history x) tr

/-- Below a first move, completing a prefix with a transcript keeps the move. -/
@[simp] theorem PrefixMoves.completeWith_down {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}}
    (x : Move l a) : {t : FreeM P PUnit.{u + 1}} → (sp : Cursor.Spine (next (l.toFunB a x)) t) →
    (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    PrefixMoves.completeWith l (s := .liftBind a next) (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr =
      ⟨x, PrefixMoves.completeWith l sp history tr⟩
  | .pure _, _, _, _ => rfl
  | .liftBind _ _, sp, history, ⟨y, tr⟩ =>
    PrefixMoves.completeWith_down x (sp.comp _) (PrefixMoves.snoc l sp history y) tr

/-- Completing the empty prefix with a transcript returns the transcript. -/
@[simp] theorem PrefixMoves.completeWith_root : {s : FreeM P PUnit.{u + 1}} → (tr : PathAlong l s) →
    PrefixMoves.completeWith l (.root s) ⟨⟩ tr = tr
  | .pure _, _ => rfl
  | .liftBind a next, ⟨x, tr⟩ =>
    (PrefixMoves.completeWith_down l (next := next) x (.root _) ⟨⟩ tr).trans
      (congrArg (Sigma.mk (β := fun y => PathAlong l (next (l.toFunB a y))) x)
        (PrefixMoves.completeWith_root tr))

/-- Combine prefix actions. The suffix family is selected by the full first transcript;
errors use this same combinator with a constant result family. -/
def combinePrefixDraw {m : Type u → Type v} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    PrefixDraw l m s₁ →
    ((tr₁ : PathAlong l s₁) → PrefixDraw l m (s₂ (projectPathAlong l s₁ tr₁))) →
    PrefixDraw l m (s₁.append s₂)
  | .pure _, _, _, draw₂ => draw₂ ⟨⟩
  | .liftBind a next, s₂, draw₁, draw₂ => fun sp h history => by
    cases sp with
    | root => exact draw₁ (.root _) h ⟨⟩
    | down b tail =>
      rcases history with ⟨⟨x, rfl⟩, history⟩
      exact combinePrefixDraw (next (l.toFunB a x)) (fun p => s₂ ⟨l.toFunB a x, p⟩)
        (fun sp h history => draw₁ (.down _ sp) h ⟨⟨x, rfl⟩, history⟩)
        (fun tr => draw₂ ⟨x, tr⟩) tail h history

/-- Append passive samplers, selecting the suffix sampler from the full first transcript. -/
def appendPrefixSampler {m : Type u → Type u} [Monad m]
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (draw₁ : PrefixDraw l m s₁)
    (draw₂ : (tr₁ : PathAlong l s₁) → PrefixDraw l m (s₂ (projectPathAlong l s₁ tr₁))) :
    Counterpart l m (s₁.append s₂) (fun _ => PUnit.{u + 1}) :=
  Counterpart.appendFlatM (prefixSampler l s₁ draw₁)
    (fun tr _ => prefixSampler l _ (draw₂ tr))

/-- Appending prefix samplers is exactly sampling with the combined full-prefix draw. -/
theorem appendPrefixSampler_eq_combinePrefixDraw {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (draw₁ : PrefixDraw l m s₁)
    (draw₂ : (tr₁ : PathAlong l s₁) → PrefixDraw l m (s₂ (projectPathAlong l s₁ tr₁))) :
    appendPrefixSampler l s₁ s₂ draw₁ draw₂ =
      prefixSampler l (s₁.append s₂) (combinePrefixDraw l s₁ s₂ draw₁ draw₂) := by
  induction s₁ using FreeM.rec with
  | pure x =>
    cases x
    have pureSlot {t : FreeM P PUnit.{u + 1}}
        (c : Counterpart l m t (fun _ => PUnit.{u + 1})) :
        Strategy.joinSlot (pure c) = c := by
      cases t <;> simp only [Strategy.joinSlot, LawfulMonad.pure_bind, id_eq]
    change Strategy.joinSlot ((fun _ : PUnit.{u + 1} =>
      prefixSampler l (s₂ ⟨⟩) (draw₂ ⟨⟩)) <$> pure ⟨⟩) = _
    rw [LawfulApplicative.map_pure]
    exact pureSlot _
  | liftBind a next ih =>
    simp only [appendPrefixSampler, Counterpart.appendFlatM, PureEnd.graft, prefixSampler,
      FreeM.append_liftBind, samplerSlot_map]
    congr 1
    funext x
    exact ih (l.toFunB a x) (fun p => s₂ ⟨l.toFunB a x, p⟩)
      (fun sp h history => draw₁ (.down _ sp) h ⟨⟨x, rfl⟩, history⟩)
      (fun tr => draw₂ ⟨x, tr⟩)

/-- Combining node draws through the full-prefix interface recovers the node combination. -/
theorem combinePrefixDraw_ofNodes {m : Type u → Type v} [Functor m]
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (draw₁ : (c : ChallengeNode l s₁) → m (challengeSpec l s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode l (s₂ p)) → m (challengeSpec l (s₂ p) c)) :
    (combinePrefixDraw l s₁ s₂ (PrefixDraw.ofNodes l draw₁)
        (fun tr => PrefixDraw.ofNodes l (draw₂ (projectPathAlong l s₁ tr))) :
      PrefixDraw l m (s₁.append s₂)) =
      (fun {a next} => PrefixDraw.ofNodes l (combineDraw l s₁ s₂ draw₁ draw₂)
        (a := a) (next := next)) := by
  induction s₁ using FreeM.rec with
  | pure _ => rfl
  | liftBind a next ih =>
    funext a' next' sp h history
    cases sp with
    | root => rfl
    | down b tail =>
      rcases history with ⟨⟨x, rfl⟩, history⟩
      exact congrArg (fun d : PrefixDraw l m _ => d tail h history)
        (ih (l.toFunB a x) (fun p => s₂ ⟨l.toFunB a x, p⟩)
          (fun c => draw₁ ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
          (fun p => draw₂ ⟨l.toFunB a x, p⟩))

/-- Combining node errors is the history-independent case of combining prefix errors. -/
theorem combinePrefixError_ofNodes
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (ε₁ : ChallengeNode l s₁ → ℝ≥0∞)
    (ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞) :
    (combinePrefixDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ (PrefixError.ofNodes l ε₁)
        (fun tr => PrefixError.ofNodes l (ε₂ (projectPathAlong l s₁ tr))) :
      PrefixError l (s₁.append s₂)) =
      (fun {a next} => PrefixError.ofNodes l
        (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) (a := a) (next := next)) := by
  induction s₁ using FreeM.rec with
  | pure _ => rfl
  | liftBind a next ih =>
    funext a' next' sp h history
    cases sp with
    | root => rfl
    | down b tail =>
      rcases history with ⟨⟨x, rfl⟩, history⟩
      exact congrArg (fun d : PrefixError l _ => d tail h history)
        (ih (l.toFunB a x) (fun p => s₂ ⟨l.toFunB a x, p⟩)
          (fun c => ε₁ ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
          (fun p => ε₂ ⟨l.toFunB a x, p⟩))

namespace KnowledgeStateFunction

variable {l} {s : FreeM P PUnit.{u + 1}} {S : Type uS} {Win : S → Type uW}
    {W : S → PathAlong l s → Type uO}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
  (F : KnowledgeStateFunction.{_, _, uK} l s S W Win admissible relIn validOutput)

/-! ### Backward extraction along a transcript -/

/-- Backward extraction determined solely by the prefix carriers and the step and leaf maps. -/
def extractFromMaps
    (Witness : ∀ (_stmt : S) {t : FreeM P PUnit.{u + 1}} (sp : Cursor.Spine s t),
      PrefixMoves l sp → Type uK)
    (stepMap : ∀ (stmt : S) {a next} (sp : Cursor.Spine s (.liftBind a next))
      (history : PrefixMoves l sp) (x : Move l a),
      Witness stmt (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp history x) → Witness stmt sp history)
    (leafMap : ∀ (stmt : S) (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp),
      W stmt (PrefixMoves.complete l sp history) → Witness stmt sp history)
    (stmt : S) : {t : FreeM P PUnit.{u + 1}} → (sp : Cursor.Spine s t) →
    (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    W stmt (PrefixMoves.completeWith l sp history tr) → Witness stmt sp history
  | .pure _, sp, history, _, w => leafMap stmt sp history w
  | .liftBind _ _, sp, history, ⟨x, tr⟩, w =>
    stepMap stmt sp history x
      (extractFromMaps Witness stepMap leafMap stmt _ (PrefixMoves.snoc l sp history x) tr w)

/-- Extract backwards to the witness at a cursor, along the remaining transcript below that
cursor, from an output witness at the completed transcript through the cursor's prefix. -/
def extractFrom (stmt : S) : {t : FreeM P PUnit.{u + 1}} → (sp : Cursor.Spine s t) →
    (history : PrefixMoves l sp) → (tr : PathAlong l t) →
    W stmt (PrefixMoves.completeWith l sp history tr) → F.Witness stmt sp history :=
  extractFromMaps F.Witness F.extractStep F.extractLeaf stmt

/-- At a completed cursor, extraction is the leaf map. -/
@[simp] theorem extractFrom_pure (stmt : S) (sp : Cursor.Spine s (.pure ⟨⟩))
    (history : PrefixMoves l sp) (tr : PathAlong l (.pure ⟨⟩ : FreeM P PUnit.{u + 1}))
    (w : W stmt (PrefixMoves.complete l sp history)) :
    F.extractFrom stmt sp history tr w = F.extractLeaf stmt sp history w := rfl

/-- At a node, extraction applies the node's step map to the witness extracted below it. This
covers public messages, oracle messages and challenges alike. -/
@[simp] theorem extractFrom_liftBind (stmt : S) {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}}
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
def BadChallengeFrom (stmt : S) : {t : FreeM P PUnit.{u + 1}} →
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
theorem state_or_badChallengeFrom (stmt : S) : {t : FreeM P PUnit.{u + 1}} →
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
def badChallenge {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}}
    (sp : Cursor.Spine s (.liftBind a next)) (history : PrefixMoves l sp) (stmt : S) :
    Set (Move l a) :=
  {x | ∃ wit, ¬ F.toFun stmt sp history (F.extractStep stmt sp history x wit) ∧
    F.toFun stmt (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x) wit}

end KnowledgeStateFunction

namespace KnowledgeStateFunction

variable {l}

/-! ### Restriction below a first move -/

/-- The state function below a first move. Its input witnesses are the witnesses after that
move, so its root obligation is vacuous; every other field is the original one. -/
def child {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}} {S : Type uS} {Win : S → Type uW}
    {W : S → PathAlong l (.liftBind a next) → Type uO} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    (F : KnowledgeStateFunction.{_, _, uK} l (.liftBind a next) S W Win admissible relIn
    validOutput)
    (x : Move l a) :
    KnowledgeStateFunction.{_, _, uK} l (next (l.toFunB a x)) S (fun stmt tr => W stmt ⟨x, tr⟩)
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

/-- Keep the same prefix witnesses and extraction maps, with the root witness itself as the
input witness and a vacuous input relation. -/
def withRootWitness {s : FreeM P PUnit.{u + 1}} {S : Type uS} {Win : S → Type uW}
    {W : S → PathAlong l s → Type uO} {admissible : S → Prop}
    {relIn : (stmt : S) → Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
    (F : KnowledgeStateFunction.{uS, uW, uK, uO} l s S W Win admissible relIn validOutput) :
    KnowledgeStateFunction.{uS, uK, uK, uO} l s S W
      (fun stmt => F.Witness stmt (.root s) ⟨⟩) (fun _ => False) (fun _ _ => True)
      validOutput where
  Witness := F.Witness
  toFun := F.toFun
  extractRoot _ w := w
  extractStep := F.extractStep
  extractLeaf := F.extractLeaf
  root _ _ _ _ := trivial
  send := F.send
  leaf := F.leaf

/-! ### Sequential composition -/

variable {S : Type uS}

/-- Witness types along the composite. -/
def appendWitness : {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    (W₁ : ∀ (_stmt : S) {t} (sp : Cursor.Spine s₁ t), PrefixMoves l sp → Type uK) →
    (W₂ : (tr₁ : PathAlong l s₁) →
      ∀ (_stmt : S) {t} (sp : Cursor.Spine (s₂ (projectPathAlong l s₁ tr₁)) t), PrefixMoves l sp →
        Type uK) →
    ∀ (_stmt : S) {t} (sp : Cursor.Spine (s₁.append s₂) t), PrefixMoves l sp → Type uK
  | .pure _, _, _, W₂, stmt, _, sp, history => W₂ ⟨⟩ stmt sp history
  | .liftBind _ _, _, W₁, _, stmt, _, .root _, _ => W₁ stmt (.root _) ⟨⟩
  | .liftBind a cont, s₂, W₁, W₂, stmt, _, .down b tail, history =>
    PrefixMoves.downCases l (a := a) (next := fun b => (cont b).append (fun p => s₂ ⟨b, p⟩))
      (motive := fun _ _ _ => Type uK)
      (fun x tail history => appendWitness (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (fun stmt {_} sp history => W₁ stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩) (fun tr => W₂ ⟨x, tr⟩)
        stmt tail history)
      b tail history

/-- The composite state on the witness types `appendWitness`: the prefix state before the seam and
the suffix state after it. -/
def appendToFunAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
      (fun x tail history => appendToFunAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) tail history)
      b tail history

/-- The same composition law with an independent input-witness universe. -/
def appendToFun :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ {t} (sp : Cursor.Spine (s₁.append s₂) t) (history : PrefixMoves l sp) (stmt : S),
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history → Prop := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂
  exact appendToFunAux F₁.withRootWitness F₂

/-- Input extraction of the composite: through the prefix leaf and the suffix input extraction
when the prefix is a leaf, and the prefix input extraction otherwise. -/
def appendExtractRoot :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
def appendExtractStepAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ {a' : P.A} {next' : P.B a' → FreeM P PUnit.{u + 1}}
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
      (fun x tail history => appendExtractStepAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) tail history)
      b tail history

/-- The same composition law with an independent input-witness universe. -/
def appendExtractStep :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ {a' : P.A} {next' : P.B a' → FreeM P PUnit.{u + 1}}
      (sp : Cursor.Spine (s₁.append s₂) (.liftBind a' next')) (history : PrefixMoves l sp),
      (stmt : S) → (y : Move l a') →
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt
        (sp.comp (.down (l.toFunB a' y) (.root _))) (PrefixMoves.snoc l sp history y) →
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂
  exact appendExtractStepAux F₁.withRootWitness F₂

/-- Leaf extraction of the composite, which is the suffix leaf extraction. -/
def appendExtractLeafAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
      (fun x tail history => appendExtractLeafAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
        (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
        (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
        (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
        (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
        (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) tail history)
      b tail history

/-- The same composition law with an independent input-witness universe. -/
def appendExtractLeaf :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    ∀ (sp : Cursor.Spine (s₁.append s₂) (.pure ⟨⟩)) (history : PrefixMoves l sp) (stmt : S),
      W stmt (PrefixMoves.complete l sp history) →
      appendWitness (s₂ := s₂) F₁.Witness (fun tr => (F₂ tr).Witness) stmt sp history := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂
  exact appendExtractLeafAux F₁.withRootWitness F₂

/-- The composite root state implies the prefix root state at a witness with the same input
extraction. -/
theorem appendToFun_root :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
theorem appendToFun_sendAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ {a' : P.A} {next' : P.B a' → FreeM P PUnit.{u + 1}}
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
    exact appendToFun_sendAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) tail history stmt ho y w
          h

/-- The same composition law with an independent input-witness universe. -/
theorem appendToFun_send :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ {a' : P.A} {next' : P.B a' → FreeM P PUnit.{u + 1}}
      (sp : Cursor.Spine (s₁.append s₂) (.liftBind a' next')) (history : PrefixMoves l sp) stmt,
      owner l a' = .sender → ∀ y w,
      appendToFun F₁ F₂ (sp.comp (.down (l.toFunB a' y) (.root _)))
        (PrefixMoves.snoc l sp history y) stmt w →
      appendToFun F₁ F₂ sp history stmt (appendExtractStep F₁ F₂ sp history stmt y w) := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂ seam
  exact appendToFun_sendAux F₁.withRootWitness F₂ seam

/-- Accepted suffix outputs give the composite state at the leaf. -/
theorem appendToFun_leafAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
    exact appendToFun_leafAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) tail history stmt w h

/-- The same composition law with an independent input-witness universe. -/
theorem appendToFun_leaf :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (sp : Cursor.Spine (s₁.append s₂) (.pure ⟨⟩)) (history : PrefixMoves l sp) stmt w,
      validOutput stmt (PrefixMoves.complete l sp history) w →
      appendToFun F₁ F₂ sp history stmt (appendExtractLeaf F₁ F₂ sp history stmt w) := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂ seam
  exact appendToFun_leafAux F₁.withRootWitness F₂ seam


section append

variable {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
  {Wmid : S → PathAlong l s₁ → Type uM}
    {W : S → PathAlong l (s₁.append s₂) → Type uO} {Win : S → Type uW}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop}
  {admissible₂ : PathAlong l s₁ → S → Prop}
  {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop}

/-- Sequential composition of knowledge state functions. The suffix state functions are indexed
by the prefix transcript, so their states, witnesses and extractors may read every prefix
payload. The seam asks that a suffix root state extracts a witness that the prefix accepts as a
valid output on that transcript. -/
def append (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) :
    KnowledgeStateFunction.{_, _, uK} l (s₁.append s₂) S W Win admissible relIn validOutput where
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
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
theorem extractFrom_child {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}} {Win : S → Type uW}
    {W : S → PathAlong l (.liftBind a next) → Type uO} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    (F : KnowledgeStateFunction.{_, _, uK} l (.liftBind a next) S W Win admissible relIn
    validOutput)
    (stmt : S) (x : Move l a) : ∀ {t : FreeM P PUnit.{u + 1}}
      (sp : Cursor.Spine (next (l.toFunB a x)) t) (history : PrefixMoves l sp)
      (tr : PathAlong l t) {α : Type uO} (w : α)
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
theorem extractFrom_child_family {a : P.A}
    {next : P.B a → FreeM P PUnit.{u + 1}} {Win : S → Type uW}
    {W : S → PathAlong l (.liftBind a next) → Type uO} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    (F : KnowledgeStateFunction.{_, _, uK} l (.liftBind a next) S W Win admissible relIn
    validOutput)
    (stmt : S) (x : Move l a) {t : FreeM P PUnit.{u + 1}}
    (sp : Cursor.Spine (next (l.toFunB a x)) t) (history : PrefixMoves l sp)
    (tr : PathAlong l t) (w : W stmt ⟨x, PrefixMoves.completeWith l sp history tr⟩) :
    F.extractFrom stmt (.down _ sp) ⟨⟨x, rfl⟩, history⟩ tr
        (cast (congrArg (W stmt) (PrefixMoves.completeWith_down l x sp history tr).symm) w) =
      (F.child x).extractFrom stmt sp history tr w :=
  extractFrom_child F stmt x sp history tr w _ rfl

/-- Over a leaf prefix, backward extraction of the composite is suffix extraction. -/
theorem extractFrom_append_pure {u : PUnit.{u + 1}}
    {s₂ : Path (FreeM.pure (P := P) u) → FreeM P PUnit.{u + 1}}
    {Wmid : S → PathAlong l (FreeM.pure u) → Type uM}
      {W : S → PathAlong l ((FreeM.pure u).append s₂) →
      Type uO}
    {Win : S → Type uW} {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validMid : (stmt : S) → (tr : PathAlong l (FreeM.pure u)) → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong l (FreeM.pure u) → S → Prop}
    {relMid : (tr₁ : PathAlong l (FreeM.pure u)) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l ((FreeM.pure u).append s₂)) → W stmt tr → Prop}
    (F₁ : KnowledgeStateFunction.{_, _, uK} l (FreeM.pure u) S Wmid Win admissible relIn validMid)
    (F₂ : (tr₁ : PathAlong l (FreeM.pure u)) →
      KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l _ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l _ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l _ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) : ∀ {t : FreeM P PUnit.{u + 1}} (sp : Cursor.Spine (s₂ ⟨⟩) t)
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
theorem extractFrom_append_down {a : P.A} {cont : P.B a → FreeM P PUnit.{u + 1}}
    {s₂ : Path (FreeM.liftBind a cont) → FreeM P PUnit.{u + 1}}
    {Wmid : S → PathAlong l (FreeM.liftBind a cont) → Type uM}
    {W : S → PathAlong l ((FreeM.liftBind a cont).append s₂) → Type uO} {Win : S → Type uW}
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validMid : (stmt : S) → (tr : PathAlong l (FreeM.liftBind a cont)) → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong l (FreeM.liftBind a cont) → S → Prop}
    {relMid : (tr₁ : PathAlong l (FreeM.liftBind a cont)) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l ((FreeM.liftBind a cont).append s₂)) →
      W stmt tr → Prop}
    (F₁ : KnowledgeStateFunction.{_, _, uK} l (FreeM.liftBind a cont) S Wmid Win admissible
    relIn validMid)
    (F₂ : (tr₁ : PathAlong l (FreeM.liftBind a cont)) →
      KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l _ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l _ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l _ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) (x : Move l a) : ∀ {t : FreeM P PUnit.{u + 1}}
      (sp : Cursor.Spine ((cont (l.toFunB a x)).append (fun p => s₂ ⟨l.toFunB a x, p⟩)) t)
      (history : PrefixMoves l sp) (tr : PathAlong l t) {α : Type uO} (w : α)
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
theorem extractFrom_append_down_family {a : P.A} {cont : P.B a → FreeM P PUnit.{u + 1}}
    {s₂ : Path (FreeM.liftBind a cont) → FreeM P PUnit.{u + 1}}
    {Wmid : S → PathAlong l (FreeM.liftBind a cont) → Type uM}
    {W : S → PathAlong l ((FreeM.liftBind a cont).append s₂) → Type uO} {Win : S → Type uW}
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validMid : (stmt : S) → (tr : PathAlong l (FreeM.liftBind a cont)) → Wmid stmt tr → Prop}
    {admissible₂ : PathAlong l (FreeM.liftBind a cont) → S → Prop}
    {relMid : (tr₁ : PathAlong l (FreeM.liftBind a cont)) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l ((FreeM.liftBind a cont).append s₂)) →
      W stmt tr → Prop}
    (F₁ : KnowledgeStateFunction.{_, _, uK} l (FreeM.liftBind a cont) S Wmid Win admissible
    relIn validMid)
    (F₂ : (tr₁ : PathAlong l (FreeM.liftBind a cont)) →
      KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l _ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l _ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l _ s₂ tr₁ tr₂) w))
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    (stmt : S) (x : Move l a) {t : FreeM P PUnit.{u + 1}}
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
theorem extractAlong_appendAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
        (extractAlong_appendAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) stmt tr₁ tr₂ w)).trans
        (extractFrom_child F₁ stmt x (.root _) ⟨⟩ tr₁ ((F₂ ⟨x, tr₁⟩).extractAlong stmt tr₂ w)
          (congrArg (Wmid stmt) (PrefixMoves.completeWith_root l (s := .liftBind a _) ⟨x,
            tr₁⟩).symm)
          (congrArg (fun tr => Wmid stmt ⟨x, tr⟩) (PrefixMoves.completeWith_root l tr₁).symm)).symm)

/-- The same composition law with an independent input-witness universe. -/
theorem extractAlong_append :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (stmt : S) (tr₁ : PathAlong l s₁) (tr₂ : PathAlong l (s₂ (projectPathAlong l s₁ tr₁)))
      (w : W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)),
      (append (s₂ := s₂) F₁ F₂ seam).extractAlong stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w =
        F₁.extractAlong stmt tr₁ ((F₂ tr₁).extractAlong stmt tr₂ w) := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂ seam
    stmt tr₁ tr₂ w
  have h := extractAlong_appendAux F₁.withRootWitness F₂ seam stmt tr₁ tr₂ w
  cases s₁ using FreeM.rec with
  | pure x => exact congrArg (F₁.extractRoot stmt) h
  | liftBind a next ih => exact congrArg (F₁.extractRoot stmt) h

/-- At a completed composite transcript, the composite state on the terminal witness is the
suffix state on its own terminal witness. -/
theorem toFun_terminalWitness_appendAux :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
    toFun_terminalWitness_appendAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩) stmt tr₁ tr₂ w

/-- The same composition law with an independent input-witness universe. -/
theorem toFun_terminalWitness_append :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
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
          ((F₂ tr₁).terminalWitness stmt tr₂ w) := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂ seam
  exact toFun_terminalWitness_appendAux F₁.withRootWitness F₂ seam

variable {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly}

variable {s : FreeM P PUnit.{1}} {Win : S → Type uW}
  {W : S → PathAlong l s → Type uO} {admissible : S → Prop}
  {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
  (F : KnowledgeStateFunction.{uS, uW, uK, uO} l s S W Win admissible relIn validOutput)

/-- For one statement, every receiver prefix draws a bad challenge with probability at most the
error at that same full prefix. -/
def BoundedAt (draw : PrefixDraw l ProbComp s) (ε : PrefixError l s)
    (stmt : S) : Prop :=
  ∀ (a : P.A) (next : P.B a → FreeM P PUnit.{1}) (sp : Cursor.Spine s (.liftBind a next))
    (h : owner l a = .receiver) (history : PrefixMoves l sp),
    letI : MeasurableSpace (Move l a) := ⊤
    𝒟[prefixSampleAt l draw sp h history] (F.badChallenge sp history stmt) ≤ ε sp h history

/-- Every admissible statement has the local error bound at every receiver prefix. -/
def LocallyBounded (draw : PrefixDraw l ProbComp s)
    (ε : PrefixError l s) : Prop :=
  ∀ stmt, admissible stmt → F.BoundedAt draw ε stmt

/-- Node-indexed bounds are the specialization ignoring the full prefix history. -/
abbrev BoundedAtOfNodes (draw : QueryImpl (challengeSpec l s) ProbComp)
    (ε : ChallengeNode l s → ℝ≥0∞) (stmt : S) : Prop :=
  F.BoundedAt (PrefixDraw.ofNodes l draw) (PrefixError.ofNodes l ε) stmt

/-- Node-indexed local boundedness uses the same prefix certificate. -/
abbrev LocallyBoundedOfNodes (draw : QueryImpl (challengeSpec l s) ProbComp)
    (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  F.LocallyBounded (PrefixDraw.ofNodes l draw) (PrefixError.ofNodes l ε)

end KnowledgeStateFunction

variable {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly)

/-- Round-by-round knowledge soundness is the existence of a locally bounded knowledge state
function. -/
theorem rbrKnowledgeSoundness_iff_exists_locallyBounded {s : FreeM P PUnit.{1}} {S : Type uS}
    {Win : S → Type uW}
    {W : S → PathAlong l s → Type uO} {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop}
    {draw : PrefixDraw l ProbComp s} {ε : PrefixError l s} :
    rbrKnowledgeSoundness.{_, _, uK} l s admissible relIn validOutput draw ε ↔
      ∃ F : KnowledgeStateFunction.{_, _, uK} l s S W Win admissible relIn validOutput,
        F.LocallyBounded draw ε := Iff.rfl

namespace KnowledgeStateFunction

variable {l} {S : Type uS}

/-- A bound survives restriction below a first move by prepending that actual move to both
the draw history and the error history. -/
theorem BoundedAt.child {a : P.A} {next : P.B a → FreeM P PUnit.{1}} {Win : S → Type uW}
    {W : S → PathAlong l (.liftBind a next) → Type uO} {admissible : S → Prop} {relIn : (stmt : S) →
      Win stmt → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l (.liftBind a next)) → W stmt tr → Prop}
    {F : KnowledgeStateFunction.{_, _, uK} l (.liftBind a next) S W Win admissible relIn
    validOutput}
    {draw : PrefixDraw l ProbComp (.liftBind a next)}
    {ε : PrefixError l (.liftBind a next)} {stmt : S} (h : F.BoundedAt draw ε stmt)
    (x : Move l a) :
    (F.child x).BoundedAt (fun sp ho history => draw (.down _ sp) ho ⟨⟨x, rfl⟩, history⟩)
      (fun sp ho history => ε (.down _ sp) ho ⟨⟨x, rfl⟩, history⟩) stmt :=
  fun a' next' sp ho history => h a' next' (.down _ sp) ho ⟨⟨x, rfl⟩, history⟩

/-- Bounds compose along the composite: prefix challenges keep the prefix bound and suffix
challenges keep the bound of the suffix state function at their prefix transcript. -/
theorem BoundedAt.appendAux :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uK} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (draw₁ : PrefixDraw l ProbComp s₁)
      (draw₂ : (tr₁ : PathAlong l s₁) → PrefixDraw l ProbComp (s₂ (projectPathAlong l s₁ tr₁)))
      (ε₁ : PrefixError l s₁)
      (ε₂ : (tr₁ : PathAlong l s₁) → PrefixError l (s₂ (projectPathAlong l s₁ tr₁)))
      (stmt : S), F₁.BoundedAt draw₁ ε₁ stmt →
      (∀ tr₁, (F₂ tr₁).BoundedAt (draw₂ tr₁)
        (ε₂ tr₁) stmt) →
      (append (s₂ := s₂) F₁ F₂ seam).BoundedAt (combinePrefixDraw l s₁ s₂ draw₁ draw₂)
        (combinePrefixDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) stmt
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
      exact BoundedAt.appendAux (s₂ := fun p => s₂ ⟨l.toFunB a x, p⟩)
          (Wmid := fun stmt tr => Wmid stmt ⟨x, tr⟩) (W := fun stmt tr => W stmt ⟨x, tr⟩)
          (validMid := fun stmt tr w => validMid stmt ⟨x, tr⟩ w)
          (admissible₂ := fun tr => admissible₂ ⟨x, tr⟩) (relMid := fun tr => relMid ⟨x, tr⟩)
          (validOutput := fun stmt tr w => validOutput stmt ⟨x, tr⟩ w)
          (F₁.child x) (fun tr => F₂ ⟨x, tr⟩) (fun tr => seam ⟨x, tr⟩)
        (fun sp ho history => draw₁ (.down _ sp) ho ⟨⟨x, rfl⟩, history⟩) (fun tr => draw₂ ⟨x, tr⟩)
        (fun sp ho history => ε₁ (.down _ sp) ho ⟨⟨x, rfl⟩, history⟩) (fun tr => ε₂ ⟨x, tr⟩) stmt
        (h₁.child x) (fun tr => h₂ ⟨x, tr⟩) a' next' tail ho history

/-- The same composition law with an independent input-witness universe. -/
theorem BoundedAt.append :
    {s₁ : FreeM P PUnit.{1}} → {s₂ : Path s₁ → FreeM P PUnit.{1}} →
    {Wmid : S → PathAlong l s₁ → Type uM} → {W : S → PathAlong l (s₁.append s₂) → Type uO} →
    {Win : S → Type uW} →
    {admissible : S → Prop} → {relIn : (stmt : S) → Win stmt → Prop} →
    {validMid : (stmt : S) → (tr : PathAlong l s₁) → Wmid stmt tr → Prop} →
    {admissible₂ : PathAlong l s₁ → S → Prop} →
    {relMid : (tr₁ : PathAlong l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong l (s₁.append s₂)) → W stmt tr → Prop} →
    (F₁ : KnowledgeStateFunction.{_, _, uK} l s₁ S Wmid Win admissible relIn validMid) →
    (F₂ : (tr₁ : PathAlong l s₁) → KnowledgeStateFunction.{_, _, uK} l (s₂ (projectPathAlong l
    s₁ tr₁))
      S (fun stmt tr₂ => W stmt (PathAlong.append l s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (PathAlong.append l s₁ s₂ tr₁ tr₂) w)) →
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w)) →
    ∀ (draw₁ : PrefixDraw l ProbComp s₁)
      (draw₂ : (tr₁ : PathAlong l s₁) → PrefixDraw l ProbComp (s₂ (projectPathAlong l s₁ tr₁)))
      (ε₁ : PrefixError l s₁)
      (ε₂ : (tr₁ : PathAlong l s₁) → PrefixError l (s₂ (projectPathAlong l s₁ tr₁)))
      (stmt : S), F₁.BoundedAt draw₁ ε₁ stmt →
      (∀ tr₁, (F₂ tr₁).BoundedAt (draw₂ tr₁)
        (ε₂ tr₁) stmt) →
      (append (s₂ := s₂) F₁ F₂ seam).BoundedAt (combinePrefixDraw l s₁ s₂ draw₁ draw₂)
        (combinePrefixDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) stmt := by
  intro s₁ s₂ Wmid W Win admissible relIn validMid admissible₂ relMid validOutput F₁ F₂ seam
  exact BoundedAt.appendAux F₁.withRootWitness F₂ seam

end KnowledgeStateFunction

end Interaction.Core
