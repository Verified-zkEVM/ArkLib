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

universe uS uW uK uI wI wJ

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

/-- A state predicate on every full prefix, with root, sender and terminal obligations. The
statement may lie in any universe. -/
structure StateFunction (s : FreeM P PUnit) (S : Type uS)
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
def rbrSoundness {S : Type uS} (s : FreeM P PUnit)
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

/-- Intermediate witnesses and their backwards extraction at full transcript prefixes.

Witness types, states and extractors may all read the full prefix, including oracle payloads.
The output witness type `W tr` is indexed by the completed transcript `tr`, and the leaf
extractor receives a witness of the type at the transcript its prefix completes. The input
witness type `Win` is fixed. The statement, the input witness and the intermediate witnesses
each lie in their own universe: the extractors are plain functions, so the root extractor may
map a large intermediate witness to a small input witness and back. As for soundness states,
the root extraction obligation applies only within the input promise.
-/
structure KnowledgeStateFunction (s : FreeM P PUnit) (S : Type uS) (W : PathAlong l s → Type)
    (Win : Type uW) (admissible : S → Prop) (relIn : S → Win → Prop)
    (validOutput : (stmt : S) → (tr : PathAlong l s) → W tr → Prop) where
  Witness : ∀ {t} (sp : Cursor.Spine s t), PrefixMoves l sp → Type uK
  toFun : ∀ {t} (sp : Cursor.Spine s t) (history : PrefixMoves l sp), S →
    Witness sp history → Prop
  extractRoot : S → Witness (.root s) ⟨⟩ → Win
  extractStep : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next))
    (history : PrefixMoves l sp), S → (x : Move l a) →
      Witness (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x) →
        Witness sp history
  extractLeaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp), S →
    W (PrefixMoves.complete l sp history) → Witness sp history
  root : ∀ stmt, admissible stmt → ∀ wit,
    toFun (.root s) ⟨⟩ stmt wit → relIn stmt (extractRoot stmt wit)
  send : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next)) history stmt,
    owner l a = .sender → ∀ x wit,
      toFun (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp history x) stmt wit →
      toFun sp history stmt (extractStep sp history stmt x wit)
  leaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) history stmt wit,
    validOutput stmt (PrefixMoves.complete l sp history) wit →
      toFun sp history stmt (extractLeaf sp history stmt wit)

/-- Worst-case-per-prefix knowledge: a fresh challenge rarely defeats backwards extraction.
The output witness type `W tr` is indexed by the completed transcript `tr`. The intermediate
witnesses of the state function lie in the universe `uK`, which is a parameter of this
definition. -/
def rbrKnowledgeSoundness {S : Type uS} {Win : Type uW} (s : FreeM P PUnit)
    {W : PathAlong l s → Type}
    (admissible : S → Prop) (relIn : S → Win → Prop)
    (validOutput : (stmt : S) → (tr : PathAlong l s) → W tr → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  ∃ F : KnowledgeStateFunction.{uS, uW, uK} l s S W Win admissible relIn validOutput,
    ∀ stmt, admissible stmt →
    ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ∃ wit,
        ¬ F.toFun sp history stmt (F.extractStep sp history stmt x wit) ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x) stmt wit} ≤ ε (spineChallenge l sp h)

/-- Move a knowledge state function to a larger universe of intermediate witnesses. Each new
intermediate witness is an old one in a larger universe; the states, extractors and obligations
are the old ones. -/
def KnowledgeStateFunction.lift.{v} {s : FreeM P PUnit} {S : Type uS} {W : PathAlong l s → Type}
    {Win : Type uW} {admissible : S → Prop} {relIn : S → Win → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l s) → W tr → Prop}
    (F : KnowledgeStateFunction.{uS, uW, uK} l s S W Win admissible relIn validOutput) :
    KnowledgeStateFunction.{uS, uW, max uK v} l s S W Win admissible relIn validOutput where
  Witness sp history := ULift.{v} (F.Witness sp history)
  toFun sp history stmt wit := F.toFun sp history stmt wit.down
  extractRoot stmt wit := F.extractRoot stmt wit.down
  extractStep sp history stmt x wit := ULift.up (F.extractStep sp history stmt x wit.down)
  extractLeaf sp history stmt wit := ULift.up (F.extractLeaf sp history stmt wit)
  root stmt ha wit h := F.root stmt ha wit.down h
  send sp history stmt ho x wit h := F.send sp history stmt ho x wit.down h
  leaf sp history stmt wit h := F.leaf sp history stmt wit h

/-- Round-by-round knowledge soundness with intermediate witnesses in a universe `uK` implies
it with intermediate witnesses in any larger universe, at the same error. -/
theorem rbrKnowledgeSoundness.lift.{v} {S : Type uS} {Win : Type uW} {s : FreeM P PUnit}
    {W : PathAlong l s → Type} {admissible : S → Prop} {relIn : S → Win → Prop}
    {validOutput : (stmt : S) → (tr : PathAlong l s) → W tr → Prop}
    {draw : QueryImpl (challengeSpec l s) ProbComp} {ε : ChallengeNode l s → ℝ≥0∞}
    (h : rbrKnowledgeSoundness.{uS, uW, uK} l s admissible relIn validOutput draw ε) :
    rbrKnowledgeSoundness.{uS, uW, max uK v} l s admissible relIn validOutput draw ε := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F.lift, fun stmt ha a next sp ho hist => ?_⟩
  simpa only [KnowledgeStateFunction.lift, ULift.exists] using hF stmt ha a next sp ho hist

/-- Valid plain acceptance from some ambient state at the fixed complete transcript.
Terminal obligations therefore cover state changes made during the interaction. The event is a
predicate on the output statement type at the transcript's shape path. The input statement may
lie in any universe. -/
def Verifier.validAcceptance {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : S) (tr : PathAlong plainSig s)
    (event : T (projectPathAlong plainSig s tr) → Prop) : Prop :=
  letI : MeasurableSpace (Option (T (projectPathAlong plainSig s tr))) := ⊤
  ∃ state : σ, 0 < 𝒟[((simulateQ impl
    (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run).run' state :
      ProbComp (Option (T (projectPathAlong plainSig s tr))))] {v | ∃ t, v = some t ∧ event t}

/-- Classical acceptance quantifies over the possible terminal states. -/
theorem Verifier.validAcceptance_iff_validAcceptanceUsing {ι σ : Type} {S : Type uS}
    {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : S) (tr : PathAlong plainSig s)
    (event : (p : Path s) → T p → Prop) :
    V.validAcceptance impl stmt tr (event (projectPathAlong plainSig s tr)) ↔
      ∃ state : σ, V.validAcceptanceUsing impl (fun x => x.run' state)
        event stmt tr := by
  unfold Verifier.validAcceptance Verifier.validAcceptanceUsing
  dsimp only
  let : MeasurableSpace (Option (T (projectPathAlong plainSig s tr))) := ⊤
  exact exists_congr fun state => by rw [prEvent_eq_evalDist_of_discrete]

/-- The plain verifier's default round-by-round soundness form. The output language is indexed
by the shape path and judged at the transcript's path. -/
abbrev Verifier.rbrSoundness {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : PathProblem s T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
    (fun stmt tr => V.validAcceptance impl stmt tr
      (output.language (projectPathAlong plainSig s tr))) draw ε

/-- The plain verifier's default round-by-round knowledge form. The output witness type `W tr`
and the output relation `relOut tr` are indexed by the completed transcript `tr`, and the output
statement has the type at its shape path. -/
abbrev Verifier.rbrKnowledgeSoundness {ι σ : Type} {S : Type uS} {Win : Type uW}
    {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {W : PathAlong plainSig s → Type}
    (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S → Prop) (relIn : S → Win → Prop)
    (relOut : (tr : PathAlong plainSig s) → T (projectPathAlong plainSig s tr) → W tr → Prop)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Core.rbrKnowledgeSoundness.{uS, uW, uK} plainSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut tr t wit)) draw ε

namespace OracleVerifier
variable {ι σ : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
  {T : Path s → Type} {A : I → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : OracleFamily.{uI, 0, wI} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}

/-- Oracle acceptance from a possible terminal state, with actual input and path payloads. The
event is a predicate on the output statement and oracle data at the transcript's shape path.
The input statement, the input index and the input query type may lie in any universe. -/
def validAcceptance (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s)
    (event : OracleVerifier.Output T B (projectPathAlong oracleSig s tr) → Prop) : Prop :=
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (stmt.2, payloads s tr)
  letI : MeasurableSpace (Option (T p)) := ⊤
  let handler : QueryImpl (ambient + (pathResources inputs s p).spec)
      (StateT σ ProbComp) := QueryImpl.addLift impl
        ((pathResources inputs s p).answer resources)
  ∃ state : σ, 0 < 𝒟[(simulateQ handler (V.decide stmt.1 p view).run).run' state]
      {v | ∃ t, v = some t ∧ event (t, (V.outputMap stmt.1 p view).f resources)}

/-- Classical acceptance quantifies over the possible terminal states. -/
theorem validAcceptance_iff_validAcceptanceUsing (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s)
    (event : (p : Path s) → OracleVerifier.Output T B p → Prop) :
    V.validAcceptance impl stmt tr (event (projectPathAlong oracleSig s tr)) ↔
      ∃ state : σ, V.validAcceptanceUsing impl (fun x => x.run' state)
        event stmt tr := by
  unfold validAcceptance validAcceptanceUsing
  dsimp only
  let : MeasurableSpace (Option (T (projectPathAlong oracleSig s tr))) := ⊤
  exact exists_congr fun state => by rw [prEvent_eq_evalDist_of_discrete]

/-- Worst-case-per-prefix oracle soundness with the full input admissibility boundary. The
output language is indexed by the shape path and judged at the transcript's path. -/
abbrev rbrSoundness (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i)))
    (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
    (fun stmt tr => V.validAcceptance impl stmt tr
      (output.language (projectPathAlong oracleSig s tr))) draw ε

/-- Worst-case-per-prefix oracle knowledge with full payload-bearing prefix access. The output
witness type `W tr` and the output relation `relOut tr` are indexed by the completed
transcript `tr`, and the output statement and oracle data have the types at its shape path. -/
abbrev rbrKnowledgeSoundness {Win : Type uW} {W : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × (∀ i, A i) → Prop) (relIn : (S × (∀ i, A i)) → Win → Prop)
    (relOut : (tr : PathAlong oracleSig s) →
      OracleVerifier.Output T B (projectPathAlong oracleSig s tr) → W tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Core.rbrKnowledgeSoundness.{max uS uI, uW, uK} oracleSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl stmt tr (fun t => relOut tr t wit)) draw ε

end OracleVerifier

end Interaction.Core
