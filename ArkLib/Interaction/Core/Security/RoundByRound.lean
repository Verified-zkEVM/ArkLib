/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.Knowledge
public import PolyFun.PFunctor.Free.Cursor

/-!
# Round-by-round security

Full moves decorate PolyFun cursor spines, so states and extractors can inspect prefix oracle
payloads as well as public messages and challenges. Soundness states are false at false roots,
remain false across sender moves and rule out valid acceptance at a false leaf. Knowledge states
carry intermediate witnesses and extract them backwards. Both error bounds quantify each fixed
prefix before drawing one fresh challenge; their indices contain only shape choices.
-/

@[expose] public section

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

variable {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly)

/-- Full runtime moves decorating a structural cursor, including erased payloads. -/
@[implicit_reducible]
def PrefixMoves : {s t : FreeM P PUnit} → Cursor.Spine s t → Type
  | _, _, .root _ => PUnit
  | _, _, .down (a := a) b tail =>
    {x : Move l a // l.toFunB a x = b} × PrefixMoves tail

/-- Extend a full prefix by one move using cursor composition. -/
def PrefixMoves.snoc {a : P.A} {next : P.B a → FreeM P PUnit} :
    {s : FreeM P PUnit} → (sp : Cursor.Spine s (.liftBind a next)) →
    PrefixMoves l sp → (x : Move l a) →
    PrefixMoves l (sp.comp (.down (l.toFunB a x) (.root _)))
  | _, .root _, _, x => ⟨⟨x, rfl⟩, ⟨⟩⟩
  | _, .down b tail, history, x => by
    rcases history with ⟨⟨y, h⟩, rest⟩
    exact ⟨⟨y, h⟩, PrefixMoves.snoc tail rest x⟩

/-- A terminal full prefix is a completed transcript. -/
def PrefixMoves.complete : {s : FreeM P PUnit} →
    (sp : Cursor.Spine s (.pure PUnit.unit)) → PrefixMoves l sp → PathAlong l s
  | _, .root _, _ => ⟨⟩
  | _, .down b tail, history => by
    rcases history with ⟨⟨x, h⟩, rest⟩
    exact ⟨x, h.symm ▸ PrefixMoves.complete tail rest⟩

/-- Case analysis of a nonempty full prefix at its first move. -/
def PrefixMoves.downCases {a : P.A} {next : P.B a → FreeM P PUnit} {t : FreeM P PUnit}
    {motive : (b : P.B a) → (tail : Cursor.Spine (next b) t) →
      PrefixMoves l (.down b tail) → Sort*}
    (h : ∀ x tail history, motive (l.toFunB a x) tail ⟨⟨x, rfl⟩, history⟩)
    (b : P.B a) (tail : Cursor.Spine (next b) t) (history : PrefixMoves l (.down b tail)) :
    motive b tail history := by
  rcases history with ⟨⟨x, rfl⟩, history⟩
  exact h x tail history

/-- The structural node reached by a cursor ending at an interaction node. -/
def spineNode {a : P.A} {next : P.B a → FreeM P PUnit} :
    {s : FreeM P PUnit} → Cursor.Spine s (.liftBind a next) → Node s
  | _, .root _ => .inl ⟨⟩
  | _, .down b tail => .inr ⟨b, spineNode tail⟩

/-- Node lookup preserves the position at the end of the cursor. -/
theorem spineNode_position {a : P.A} {next : P.B a → FreeM P PUnit} :
    {s : FreeM P PUnit} → (sp : Cursor.Spine s (.liftBind a next)) →
    Node.position _ (spineNode sp) = a
  | _, .root _ => rfl
  | _, .down _ tail => spineNode_position tail

/-- A receiver cursor identifies its challenge without using any full runtime move. -/
def spineChallenge {s : FreeM P PUnit} {a : P.A} {next : P.B a → FreeM P PUnit}
    (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver) : ChallengeNode l s :=
  ⟨spineNode sp, (congrArg (owner l) (spineNode_position sp)).trans h⟩

/-- Draw a fresh move at the receiver position selected by a structural prefix. -/
def sampleAt {s : FreeM P PUnit} {a : P.A} {next : P.B a → FreeM P PUnit}
    (draw : QueryImpl (challengeSpec l s) ProbComp)
    (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver) : ProbComp (Move l a) :=
  (fun x => Eq.mp (congrArg (Move l) (spineNode_position sp)) x) <$>
    draw (spineChallenge l sp h)

/-- A state predicate on every full prefix, with root, sender and terminal obligations. -/
structure StateFunction (s : FreeM P PUnit) (S : Type)
    (admissible language : S → Prop) (accepts : S → PathAlong l s → Prop) where
  toFun : ∀ {t}, (sp : Cursor.Spine s t) → PrefixMoves l sp → S → Prop
  root : ∀ stmt, admissible stmt → toFun (.root s) ⟨⟩ stmt → language stmt
  send : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next)) history stmt,
    owner l a = .sender → ¬ toFun sp history stmt → ∀ x,
      ¬ toFun (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp history x) stmt
  leaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) history stmt,
    ¬ toFun sp history stmt → ¬ accepts stmt (PrefixMoves.complete l sp history)

/-- Worst-case-per-prefix round-by-round soundness; there is no adversary-model argument. -/
def rbrSoundness {S : Type} (s : FreeM P PUnit)
    (admissible language : S → Prop) (accepts : S → PathAlong l s → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  ∃ F : StateFunction l s S admissible language accepts,
    ∀ stmt, admissible stmt → ¬ language stmt →
    ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ F.toFun sp history stmt ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x) stmt} ≤ ε (spineChallenge l sp h)

/-- Intermediate witnesses and backwards extraction at full transcript prefixes.

Every witness carrier may depend on the input statement. Intermediate carriers may also read
all earlier moves, including oracle payloads, and output carriers may read the complete
transcript. The root extraction obligation applies within the input promise.
-/
structure KnowledgeStateFunction (s : FreeM P PUnit) (S : Type)
    (W : S → PathAlong l s → Type) (Win : S → Type) (admissible : S → Prop)
    (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop) where
  Witness : ∀ (_stmt : S) {t} (sp : Cursor.Spine s t), PrefixMoves l sp → Type
  toFun : ∀ (stmt : S) {t} (sp : Cursor.Spine s t) (history : PrefixMoves l sp),
    Witness stmt sp history → Prop
  extractRoot : ∀ stmt, Witness stmt (.root s) ⟨⟩ → Win stmt
  extractStep : ∀ (stmt : S) {a next} (sp : Cursor.Spine s (.liftBind a next))
    (history : PrefixMoves l sp) (x : Move l a),
    Witness stmt (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp history x) → Witness stmt sp history
  extractLeaf : ∀ (stmt : S) (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp),
    W stmt (PrefixMoves.complete l sp history) → Witness stmt sp history
  root : ∀ stmt, admissible stmt → ∀ wit,
    toFun stmt (.root s) ⟨⟩ wit → relIn stmt (extractRoot stmt wit)
  send : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next)) history stmt,
    owner l a = .sender → ∀ x wit,
      toFun stmt (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp history x) wit →
      toFun stmt sp history (extractStep stmt sp history x wit)
  leaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) history stmt wit,
    validOutput stmt (PrefixMoves.complete l sp history) wit →
      toFun stmt sp history (extractLeaf stmt sp history wit)

/-- A fresh challenge rarely defeats backwards extraction, uniformly over later witnesses. -/
def rbrKnowledgeSoundness {S : Type} {Win : S → Type} (s : FreeM P PUnit)
    {W : S → PathAlong l s → Type} (admissible : S → Prop)
    (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  ∃ F : KnowledgeStateFunction l s S W Win admissible relIn validOutput,
    ∀ stmt, admissible stmt →
    ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ∃ wit,
        ¬ F.toFun stmt sp history (F.extractStep stmt sp history x wit) ∧
        F.toFun stmt (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x) wit} ≤ ε (spineChallenge l sp h)

/-- Valid plain acceptance from some ambient state at the fixed complete transcript.
Terminal obligations therefore cover state changes made during the interaction. -/
def Verifier.validAcceptance {ι σ S T : Type} {ambient : OracleSpec ι} {s : Protocol}
    (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T → Prop)
    (stmt : S) (tr : PathAlong plainSig s) : Prop :=
  letI : MeasurableSpace (Option T) := ⊤
  ∃ state : σ, 0 < 𝒟[((simulateQ impl
    (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run).run' state :
      ProbComp (Option T))] {v | ∃ t, v = some t ∧ langOut t}

/-- Positive acceptance is a supported accepted result, including its final ambient state. -/
theorem Verifier.validAcceptance_iff_support {ι σ S T : Type} {ambient : OracleSpec ι}
    {s : Protocol} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T → Prop)
    (stmt : S) (tr : PathAlong plainSig s) :
    V.validAcceptance impl langOut stmt tr ↔
      ∃ state t final, (some t, final) ∈ support
        ((simulateQ impl (V.decide stmt (projectPathAlong plainSig s tr)
          (toPlainView s tr)).run).run state) ∧ langOut t := by
  let : MeasurableSpace (Option T) := ⊤
  unfold Verifier.validAcceptance
  simp only [← prEvent_eq_evalDist _ _ measurable_from_top, prEvent_pos_iff,
    StateT.run'_eq, _root_.support_map, Set.mem_image]
  constructor
  · rintro ⟨state, v, ⟨⟨result, final⟩, hr, rfl⟩, t, rfl, ht⟩
    exact ⟨state, t, final, hr, ht⟩
  · rintro ⟨state, t, final, hr, ht⟩
    exact ⟨state, some t, ⟨(some t, final), hr, rfl⟩, t, rfl, ht⟩

/-- The plain verifier's default round-by-round soundness form. -/
abbrev Verifier.rbrSoundness {ι σ S T : Type} {ambient : OracleSpec ι} {s : Protocol}
    (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : StatementProblem T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
    (V.validAcceptance impl (output.language ())) draw ε

/-- The plain verifier's default round-by-round knowledge form. The output witness type `W stmt tr`
and the output relation are indexed by the input statement and completed transcript. -/
abbrev Verifier.rbrKnowledgeSoundness {ι σ S T : Type} {Win : S → Type} {ambient : OracleSpec ι}
    {s : Protocol} {W : S → PathAlong plainSig s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S → Prop) (relIn : (stmt : S) → Win stmt → Prop)
    (relOut : (stmt : S) → (tr : PathAlong plainSig s) → T → W stmt tr → Prop)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Core.rbrKnowledgeSoundness plainSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl (fun t => relOut stmt tr t wit) stmt tr) draw ε

namespace OracleVerifier
variable {ι I J σ S T : Type} {ambient : OracleSpec ι} {s : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}

/-- Oracle acceptance from a possible terminal state, with actual input and path payloads. -/
def validAcceptance (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T × (∀ j, B j) → Prop)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s) : Prop :=
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources := sumData stmt.2 (payloads s tr)
  letI : MeasurableSpace (Option T) := ⊤
  let handler : QueryImpl (ambient + (sumFamily inputs (pathFamily s p)).spec)
      (StateT σ ProbComp) := QueryImpl.addLift impl
        ((sumFamily inputs (pathFamily s p)).behaviorOfRealizations resources)
  ∃ state : σ, 0 < 𝒟[(simulateQ handler (V.decide stmt.1 p view).run).run' state]
      {v | ∃ t, v = some t ∧ langOut (t, (V.outputMap stmt.1 p view).f resources)}

/-- Positive oracle acceptance has a supported accepted result and a final ambient state. -/
theorem validAcceptance_iff_support (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (langOut : T × (∀ j, B j) → Prop)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s) :
    V.validAcceptance impl langOut stmt tr ↔
      ∃ state t final, (some t, final) ∈ support
        ((simulateQ impl (V.decideWith stmt.1 (projectPathAlong oracleSig s tr)
          (toView s tr) (sumData stmt.2 (payloads s tr)))).run state) ∧
        langOut (t, (V.outputMap stmt.1 (projectPathAlong oracleSig s tr) (toView s tr)).f
          (sumData stmt.2 (payloads s tr))) := by
  let : MeasurableSpace (Option T) := ⊤
  simp only [validAcceptance, OracleVerifier.simulateQ_decideWith,
    ← prEvent_eq_evalDist _ _ measurable_from_top, prEvent_pos_iff,
    StateT.run'_eq, _root_.support_map, Set.mem_image]
  constructor
  · rintro ⟨state, v, ⟨⟨result, final⟩, hr, rfl⟩, t, rfl, ht⟩
    exact ⟨state, t, final, hr, ht⟩
  · rintro ⟨state, t, final, hr, ht⟩
    exact ⟨state, some t, ⟨(some t, final), hr, rfl⟩, t, rfl, ht⟩

/-- Worst-case-per-prefix oracle soundness with the full input admissibility boundary. -/
abbrev rbrSoundness (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i)))
    (output : StatementProblem (T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
    (V.validAcceptance impl (output.language ())) draw ε

/-- Worst-case-per-prefix oracle knowledge with full payload-bearing prefix access. The output
witness type `W stmt tr` and the output relation are indexed by the input statement, including
its oracle data, and the completed transcript. -/
abbrev rbrKnowledgeSoundness {Win : (S × (∀ i, A i)) → Type}
    {W : (S × (∀ i, A i)) → PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × (∀ i, A i) → Prop) (relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop)
    (relOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig s) →
      (T × (∀ j, B j)) → W stmt tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Core.rbrKnowledgeSoundness oracleSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl (fun t => relOut stmt tr t wit) stmt tr) draw ε

end OracleVerifier

end Interaction.Core
