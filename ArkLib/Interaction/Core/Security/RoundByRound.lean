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

/-- Intermediate witnesses and their backwards extraction at full transcript prefixes.

Witness types, states and extractors may all read the full prefix, including oracle payloads.
As for soundness states, the root extraction obligation applies only within the input promise.
-/
structure KnowledgeStateFunction (s : FreeM P PUnit) (S W Win : Type)
    (admissible : S → Prop) (relIn : S → Win → Prop)
    (validOutput : S → PathAlong l s → W → Prop) where
  Witness : ∀ {t} (sp : Cursor.Spine s t), PrefixMoves l sp → Type
  toFun : ∀ {t} (sp : Cursor.Spine s t) (history : PrefixMoves l sp), S →
    Witness sp history → Prop
  extractRoot : S → Witness (.root s) ⟨⟩ → Win
  extractStep : ∀ {a next} (sp : Cursor.Spine s (.liftBind a next))
    (history : PrefixMoves l sp), S → (x : Move l a) →
      Witness (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x) →
        Witness sp history
  extractLeaf : ∀ (sp : Cursor.Spine s (.pure ⟨⟩)) (history : PrefixMoves l sp), S → W →
    Witness sp history
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

/-- Worst-case-per-prefix knowledge: a fresh challenge rarely defeats backwards extraction. -/
def rbrKnowledgeSoundness {S W Win : Type} (s : FreeM P PUnit)
    (admissible : S → Prop) (relIn : S → Win → Prop)
    (validOutput : S → PathAlong l s → W → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞) : Prop :=
  ∃ F : KnowledgeStateFunction l s S W Win admissible relIn validOutput,
    ∀ stmt, admissible stmt →
    ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ∃ wit,
        ¬ F.toFun sp history stmt (F.extractStep sp history stmt x wit) ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x) stmt wit} ≤ ε (spineChallenge l sp h)

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

/-- The plain verifier's default round-by-round soundness form. -/
abbrev Verifier.rbrSoundness {ι σ S T : Type} {ambient : OracleSpec ι} {s : Protocol}
    (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : StatementProblem T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
    (V.validAcceptance impl (output.language ())) draw ε

/-- The plain verifier's default round-by-round knowledge form. -/
abbrev Verifier.rbrKnowledgeSoundness {ι σ S T W Win : Type} {ambient : OracleSpec ι}
    {s : Protocol} (V : Verifier ambient s S T)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S → Prop) (relIn : S → Win → Prop) (relOut : T → W → Prop)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) : Prop :=
  Core.rbrKnowledgeSoundness plainSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl (fun t => relOut t wit) stmt tr) draw ε

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

/-- Worst-case-per-prefix oracle soundness with the full input admissibility boundary. -/
abbrev rbrSoundness (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i)))
    (output : StatementProblem (T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
    (V.validAcceptance impl (output.language ())) draw ε

/-- Worst-case-per-prefix oracle knowledge with full payload-bearing prefix access. -/
abbrev rbrKnowledgeSoundness {W Win : Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (admissible : S × (∀ i, A i) → Prop) (relIn : (S × (∀ i, A i)) → Win → Prop)
    (relOut : (T × (∀ j, B j)) → W → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞) : Prop :=
  Core.rbrKnowledgeSoundness oracleSig s admissible relIn
    (fun stmt tr wit => V.validAcceptance impl (fun t => relOut t wit) stmt tr) draw ε

end OracleVerifier

end Interaction.Core
