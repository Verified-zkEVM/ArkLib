/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Security.KnowledgeComposition
import ArkLibTest.Interaction.Core.Support

/-!
# Knowledge composition across an oracle seam

The prefix prover sends a natural-number oracle and the verifier draws a Boolean challenge; the
prefix verifier returns the challenge as its statement and exports the sent oracle. A fixed-shape
suffix sends one more oracle, and the suffix verifier accepts its input statement. The prefix
state function has witness carrier `Fin (payload + 1)` after the oracle message, which is also its
output witness carrier, and each suffix state function, indexed by the prefix transcript, takes
input witnesses in that carrier and output witnesses in `Fin (payload + 1) × Unit`, with identity
root and leaf maps. Composition with `KnowledgeStateFunction.append` extracts along both challenge
values from these carriers, its terminal witness is the output witness itself, and the security
statements compose at the verifier level, with the prefix acceptance as the seam.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp MeasureTheory
open scoped ENNReal

namespace Interaction.Core.KnowledgeCompositionTests

/-- The carriers of no input oracles. -/
abbrev NoData : PEmpty.{1} → Type := fun i => i.elim

/-- No input oracles. -/
@[instance_reducible] def noInputs : OracleFamily.{0, 0, 0} PEmpty NoData := ⟨fun i => i.elim⟩

/-- The input data of `noInputs`. -/
def noData : ∀ i, NoData i := fun i => i.elim

/-- One exported scalar oracle. -/
@[instance_reducible] def exportFamily : OracleFamily.{0, 0, 0} PUnit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The prefix sends a natural-number oracle, then draws a Boolean challenge. -/
@[instance_reducible] def firstProtocol : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) fun _ =>
    .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- The suffix sends one natural-number oracle. -/
@[instance_reducible] def secondProtocol : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) fun _ => .pure ⟨⟩

/-- The payload of a natural-number oracle message. -/
abbrev payload : Move oracleSig (.oracle Nat OracleInterface.instDefault) → Nat := id

/-- A Boolean challenge. -/
abbrev bit : Move oracleSig (.challenge Bool) → Bool := id

/-- The suffix, whose shape does not depend on the prefix path. -/
abbrev suffix : Path firstProtocol → OracleProtocol := fun _ => secondProtocol

/-- The prefix protocol followed by the oracle-message suffix. -/
abbrev combined : OracleProtocol := firstProtocol.append suffix

/-- The prefix verifier returns the challenge from its view and exports the sent oracle. -/
def firstVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} OracleSpec.emptySpec firstProtocol
    Unit (fun _ => Bool) noInputs
    (fun _ => exportFamily) where
  decide _ _ v := pure (show Bool from v.val.2.1)
  outputMap _ p _ := (OracleMap.embedding (pathFamily firstProtocol p) (fun _ => .inl ⟨⟩)).comp
    (OracleMap.snd _ _)

/-- The suffix verifier accepts its input statement and passes the export through. -/
def secondVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} OracleSpec.emptySpec secondProtocol
    Bool (fun _ => Bool)
    exportFamily
    (fun _ => exportFamily) where
  decide stmt _ _ := pure stmt
  outputMap _ _ _ := OracleMap.fst _ _

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible :
    OracleVerifier.OutputCompatibility firstVerifier (fun _ => secondVerifier) where
  outputMap stmt p v :=
    (secondVerifier.outputMap false (Path.split firstProtocol suffix p).2
      (View.split firstProtocol suffix p v).2).comp
      (OracleVerifier.suffixRoute firstVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The appended verifier. -/
def composed := firstVerifier.append (fun _ => secondVerifier) compatible

/-- A completed prefix transcript. -/
abbrev firstPath (n : Nat) (b : Bool) : PathAlong oracleSig firstProtocol := ⟨n, b, ⟨⟩⟩

-- KnowledgeComposition row 1, restated: the prefix `outputMap.f` returns the sent payload.
/-- The exported oracle of every completed prefix transcript is its sent payload. -/
example (n : Nat) (b : Bool) :
    (firstVerifier.outputMap () (projectPathAlong oracleSig firstProtocol (firstPath n b))
      (toView firstProtocol (firstPath n b))).f
        (noData, payloads firstProtocol (firstPath n b)) ⟨⟩ = n := rfl

/-! ### Runs -/

/-- The prefix prover sends `7` and keeps it as private memory. -/
def firstProver : Prover oracleSig OracleSpec.emptySpec firstProtocol (fun _ => Nat) :=
  pure ⟨(7 : Nat), pure fun _ => pure (7 : Nat)⟩

/-- The suffix prover sends `5` after a true challenge and `99` after a false one, with private
output `41` or `73`. -/
def secondProver (tr : PathAlong oracleSig firstProtocol) (_ : Nat) :
    OracleComp OracleSpec.emptySpec
      (Prover oracleSig OracleSpec.emptySpec secondProtocol (fun _ => Nat)) :=
  pure (pure ⟨(cond (bit tr.2.1) 5 99 : Nat), pure (cond (bit tr.2.1) 41 73 : Nat)⟩)

/-- The whole prover. -/
def prover : Prover oracleSig OracleSpec.emptySpec combined (fun _ => Nat) :=
  Prover.append firstProver secondProver

/-- Answers the only challenge of the composite with `b`. -/
def handler (b : Bool) :
    QueryImpl (OracleSpec.emptySpec + challengeSpec oracleSig combined) Id
  | .inl i => i.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => (pure b : Id Bool)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

/-- The sent payload, the challenge, the private output, and the claim with its exported oracle,
of the composite run with challenge `b`. -/
def observed (b : Bool) : Nat × Bool × Nat × Option (Bool × Nat) :=
  let result := simulateQ (handler b) (composed.run () noData prover)
  (payload result.1.1, bit result.1.2.1, result.2.1,
    result.2.2.map (fun z => (z.1, z.2 ⟨⟩)))

-- KnowledgeComposition row 3, restated on a fixed-shape suffix: the challenge changes the
-- intermediate statement, the suffix message and the private output, for both challenges.
/-- The composite run returns the prefix payload, the challenge, the suffix private output and
the claim, with the exported oracle read from the prefix payload. -/
theorem observed_eq (b : Bool) :
    observed b = (7, b, if b then 41 else 73, some (b, 7)) := by
  cases b <;> kernel_rfl

-- KnowledgeComposition row 4, restated: evaluation of the run of row 3.
/-- info: (7, true, 41, some (true, 7)) -/
#guard_msgs in
#eval observed true

/-! ### Challenge sampling

The composite challenge is drawn by the prefix draw, and the suffix draw is consulted only on the
suffix, which has no challenge.
-/

/-- The prefix draws `true`. -/
def firstDraw : QueryImpl (challengeSpec oracleSig firstProtocol) ProbComp
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => (pure true : ProbComp Bool)
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- The suffix has no challenge. -/
def secondDraw (p : Path firstProtocol) : QueryImpl (challengeSpec oracleSig (suffix p)) ProbComp
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- The prefix prover over `ProbComp`. -/
def firstProbProver : Focal oracleSig ProbComp firstProtocol (fun _ => Nat) :=
  pure ⟨(7 : Nat), pure fun _ => pure (7 : Nat)⟩

/-- The suffix prover over `ProbComp`. -/
def secondProbProver : Focal oracleSig ProbComp secondProtocol (fun _ => Nat) :=
  pure ⟨(5 : Nat), pure (41 : Nat)⟩

-- KnowledgeComposition row 5 (`first_fresh`), restated as R2: the prefix sampler draws the
-- challenge with `firstDraw`.
/-- The prefix run under `sampler oracleSig firstProtocol firstDraw` has challenge `true`. -/
example : (fun z => (payload z.1.1, bit z.1.2.1, z.2.1)) <$>
    TwoParty.Lens.run firstProtocol firstProbProver (sampler oracleSig firstProtocol firstDraw) =
      (pure (7, true, 7) : ProbComp (Nat × Bool × Nat)) := rfl

-- KnowledgeComposition row 6 (`second_fresh`), restated as R2: the suffix sampler, at every
-- prefix path, requests no challenge.
/-- The suffix run under `sampler oracleSig _ (secondDraw p)` returns the suffix message. -/
example (p : Path firstProtocol) : (fun z => (payload z.1.1, z.2.1)) <$>
    TwoParty.Lens.run secondProtocol secondProbProver
      (sampler oracleSig secondProtocol (secondDraw p)) =
      (pure (5, 41) : ProbComp (Nat × Nat)) := rfl

-- KnowledgeComposition row 7 (`composite_fresh`), restated as R2: the appended sampler is the
-- sampler of the composite with `combineDraw`.
/-- Appending the samplers samples the composite with the combined draw. -/
theorem appendSampler_eq_combineDraw :
    appendSampler firstProtocol suffix firstDraw secondDraw =
      sampler oracleSig combined (combineDraw oracleSig firstProtocol suffix firstDraw
        secondDraw) :=
  appendOracleSampler_eq firstProtocol suffix firstDraw secondDraw

/-! ### State functions -/

/-- The input statement: a unit statement and no input data. -/
abbrev Stmt := Unit × (∀ i, NoData i)

/-- Ambient queries have no answer. -/
def impl : QueryImpl OracleSpec.emptySpec (StateT Unit ProbComp) := fun i => i.elim

/-- The prefix accepts with a true claim exactly when the challenge is true. -/
theorem firstVerifier_validAcceptance_iff (stmt : Stmt) (tr : PathAlong oracleSig firstProtocol) :
    firstVerifier.validAcceptance impl stmt tr (fun z => z.1 = true) ↔ bit tr.2.1 = true := by
  rcases tr with ⟨n, b, ⟨⟩⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change (∃ _ : Unit, 0 < 𝒟[(pure (some b) : ProbComp (Option Bool))]
    {v | ∃ t, v = some t ∧ t = true}) ↔ b = true
  cases b <;> simp

/-- The composite accepts with a true claim exactly when the challenge is true. -/
theorem composed_validAcceptance_iff (stmt : Stmt) (tr : PathAlong oracleSig combined) :
    composed.validAcceptance impl stmt tr (fun z => z.1 = true) ↔ bit tr.2.1 = true := by
  rcases tr with ⟨n, b, m, ⟨⟩⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change (∃ _ : Unit, 0 < 𝒟[(pure (some b) : ProbComp (Option Bool))]
    {v | ∃ t, v = some t ∧ t = true}) ↔ b = true
  cases b <;> simp

/-- The prefix output witnesses: numbers below the sent payload plus one. -/
abbrev MidWitness (tr : PathAlong oracleSig firstProtocol) : Type := Fin (payload tr.1 + 1)

/-- The composite output witnesses: numbers below the prefix payload plus one, with a unit. -/
abbrev OutWitness (tr : PathAlong oracleSig combined) : Type := Fin (payload tr.1 + 1) × Unit

/-- The prefix valid output: acceptance with a true claim. -/
abbrev validMid (stmt : Stmt) (tr : PathAlong oracleSig firstProtocol) (_ : MidWitness tr) :
    Prop :=
  firstVerifier.validAcceptance impl stmt tr (fun z => z.1 = true)

/-- The composite valid output: acceptance with a true claim. -/
abbrev validOutput (stmt : Stmt) (tr : PathAlong oracleSig combined) (_ : OutWitness tr) : Prop :=
  composed.validAcceptance impl stmt tr (fun z => z.1 = true)

/-- The suffix input relation: the prefix challenge was true. -/
abbrev relMid (tr₁ : PathAlong oracleSig firstProtocol) (_ : Stmt) (_ : MidWitness tr₁) : Prop :=
  bit tr₁.2.1 = true

/-- The prefix state function. After the oracle message `n`, witnesses lie in `Fin (n + 1)`, the
carrier of its output witnesses, and the leaf map is the identity; the state is false until the
challenge, and then holds exactly when the challenge is true. -/
def firstState : KnowledgeStateFunction oracleSig firstProtocol Stmt (fun _ => MidWitness) (fun _ =>
    Nat)
    (fun _ => True) (fun _ _ => False) validMid where
  Witness _ {_} sp history := match sp, history with
    | .root _, _ => Nat
    | .down _ _, history => Fin (payload history.1.1 + 1)
  toFun _ {_} sp history _ := match sp, history with
    | .root _, _ => False
    | .down _ (.root _), _ => False
    | .down _ (.down _ _), history => bit history.2.1.1 = true
  extractRoot _ w := w
  extractStep _ {_ _} sp _ _ w := by
    cases sp with
    | root => exact w.val
    | down _ tail =>
      cases tail with
      | root => exact w
      | down _ tail => cases tail
  extractLeaf _ sp history w := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail
        exact w
  root _ _ _ h := h
  send sp _ _ ho _ _ h := by
    cases sp with
    | root => exact h
    | down _ tail =>
      cases tail with
      | root => exact nomatch ho
      | down _ tail => cases tail
  leaf sp history stmt _ h := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail
        rcases history with ⟨⟨n, rfl⟩, ⟨⟨b, rfl⟩, ⟨⟩⟩⟩
        exact (firstVerifier_validAcceptance_iff stmt ⟨n, b, ⟨⟩⟩).1 h

/-- The suffix state function after the prefix transcript `tr₁`. Its witnesses lie in
`Fin (n + 1)` for the prefix payload `n`, paired with a unit after the suffix message; these are
the carriers of its input and output witnesses, and its root and leaf maps are identities. Its
state holds exactly when the prefix challenge was true. -/
def secondState (tr₁ : PathAlong oracleSig firstProtocol) :
    KnowledgeStateFunction oracleSig (suffix (projectPathAlong oracleSig firstProtocol tr₁)) Stmt
      (fun _ tr₂ => OutWitness (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂))
      (fun _ => MidWitness tr₁) (fun _ => True) (relMid tr₁)
      (fun stmt tr₂ w => validOutput stmt (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)
        w) where
  Witness _ {_} sp _ := match sp with
    | .root _ => Fin (payload tr₁.1 + 1)
    | .down _ _ => Fin (payload tr₁.1 + 1) × Unit
  toFun _ {_} _ _ _ := bit tr₁.2.1 = true
  extractRoot _ w := w
  extractStep _ {_ _} sp _ _ w := by
    cases sp with
    | root => exact w.1
    | down _ tail => cases tail
  extractLeaf _ sp _ w := by
    cases sp with
    | down _ tail =>
      cases tail
      exact w
  root _ _ _ h := h
  send _ _ _ _ _ _ h := h
  leaf sp history stmt _ h := by
    cases sp with
    | down _ tail =>
      cases tail
      rcases history with ⟨⟨m, rfl⟩, ⟨⟩⟩
      exact (composed_validAcceptance_iff stmt
        (PathAlong.append oracleSig firstProtocol suffix tr₁ ⟨m, ⟨⟩⟩)).1 h

/-- The seam: a suffix root state extracts a witness the prefix accepts. -/
theorem seam (tr₁ : PathAlong oracleSig firstProtocol) (stmt : Stmt)
    (w : (secondState tr₁).Witness stmt (.root _) ⟨⟩) (h : (secondState tr₁).toFun stmt (.root _) ⟨⟩
      w) :
    validMid stmt tr₁ ((secondState tr₁).extractRoot stmt w) :=
  (firstVerifier_validAcceptance_iff stmt tr₁).2 h

/-- The composite state function. -/
def compositeState := KnowledgeStateFunction.append firstState secondState seam

/-- The input statement. -/
def stmt₀ : Stmt := ((), noData)

/-- Failed extraction keeps the supplied terminal witness when identifying a receiver step. -/
example (n : Nat) (w : Fin (n + 1)) :
    firstState.BadChallengeAlong stmt₀ (firstPath n true) w :=
  firstState.extraction_failure_implies_badChallengeAlong stmt₀ (firstPath n true) w trivial
    ((firstVerifier_validAcceptance_iff stmt₀ _).2 rfl) id

/-- The composite transcript with challenge `true`. -/
def truePath : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstProtocol suffix (firstPath 7 true) ⟨(5 : Nat), ⟨⟩⟩

/-- The composite transcript with challenge `false`. -/
def falsePath : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstProtocol suffix (firstPath 7 false) ⟨(99 : Nat), ⟨⟩⟩

-- KnowledgeComposition row 2, restated with `extractAlong`: the carrier after the message reads
-- the payload.
/-- Prefix extraction on payload `7` takes its output witness in `Fin 8`. -/
example : firstState.extractAlong stmt₀ (firstPath 7 true) (⟨6, by decide⟩ : Fin 8) = 6 := rfl

/-- info: 6 -/
#guard_msgs in
#eval firstState.extractAlong stmt₀ (firstPath 7 true) (⟨6, by decide⟩ : Fin 8)

/-- The output witnesses of the composite at every transcript are the carrier `Fin (n + 1) × Unit`
of the prefix payload `n`. -/
example (n : Nat) (b : Bool) (m : Nat) :
    OutWitness (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) =
      (Fin (n + 1) × Unit) := rfl

-- KnowledgeComposition rows 8 and 9, restated with `extractAlong_append`, for every payload,
-- challenge, suffix message and output witness in the carrier of the payload.
/-- Composite extraction is suffix extraction followed by prefix extraction, and returns the
value of the output witness. -/
theorem compositeState_extractAlong (n : Nat) (b : Bool) (m : Nat) (w : Fin (n + 1) × Unit) :
    compositeState.extractAlong stmt₀
      (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) w = w.1.val :=
  (KnowledgeStateFunction.extractAlong_append firstState secondState seam stmt₀ (firstPath n b)
    ⟨m, ⟨⟩⟩ w).trans rfl

-- KnowledgeComposition row 8.
example : compositeState.extractAlong stmt₀ truePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit) = 6 :=
  compositeState_extractAlong 7 true 5 _

-- KnowledgeComposition row 9: the false challenge.
example : compositeState.extractAlong stmt₀ falsePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit) = 6 :=
  compositeState_extractAlong 7 false 99 _

-- KnowledgeComposition row 10.
/-- info: 6 -/
#guard_msgs in
#eval compositeState.extractAlong stmt₀ truePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)

-- KnowledgeComposition row 11.
/-- info: 6 -/
#guard_msgs in
#eval compositeState.extractAlong stmt₀ falsePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)

-- KnowledgeComposition row 12: the composite terminal witness is the claim's own carrier, and
-- the composite terminal state, the suffix terminal state by `toFun_terminalWitness_append`, holds
-- exactly when the composite accepts (R1).
/-- On the true path, the composite terminal witness of an output witness in `Fin 8 × Unit` keeps
its value. -/
example : (compositeState.terminalWitness stmt₀ truePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)).1.val = 6 := rfl

/-- At every composite transcript, the terminal witness carrier is the output witness carrier and
the terminal witness is the output witness. -/
example (n : Nat) (b : Bool) (m : Nat) (w : Fin (n + 1) × Unit) :
    compositeState.terminalWitness stmt₀
      (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) w = w := rfl

/-- The composite terminal state holds exactly when the composite accepts. -/
example (n : Nat) (b : Bool) (m : Nat) (w : Fin (n + 1) × Unit) :
    compositeState.toFun stmt₀
        (completeSpine oracleSig
          (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩))
        (completeMoves oracleSig _)
        (compositeState.terminalWitness stmt₀
          (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) w) ↔
      validOutput stmt₀
        (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) w :=
  (KnowledgeStateFunction.toFun_terminalWitness_append firstState secondState seam stmt₀
    (firstPath n b) ⟨m, ⟨⟩⟩ w).trans (composed_validAcceptance_iff stmt₀
      (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩)).symm

-- Direct-family corollaries: the witness is given in the family at the completed transcript.
/-- The prefix protocol after its oracle message. -/
abbrev afterFirst : OracleProtocol := .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- Prefix extraction below the oracle message `n` is the extraction of the restricted state
function on the same output witness. -/
example (n : Move oracleSig (.oracle Nat OracleInterface.instDefault))
    (tr : PathAlong oracleSig afterFirst)
    (w : MidWitness ⟨n, PrefixMoves.completeWith oracleSig (.root afterFirst) ⟨⟩ tr⟩) :
    firstState.extractFrom stmt₀ (.down (oracleSig.toFunB _ n) (.root afterFirst))
        ⟨⟨n, rfl⟩, ⟨⟩⟩ tr
        (cast (congrArg MidWitness
          (PrefixMoves.completeWith_down oracleSig (next := fun _ => afterFirst) n
            (.root afterFirst) ⟨⟩ tr).symm) w) =
      (firstState.child n).extractFrom stmt₀ (.root afterFirst) ⟨⟩ tr w :=
  KnowledgeStateFunction.extractFrom_child_family firstState stmt₀ n (.root afterFirst) ⟨⟩ tr w

/-- The direct-family corollary for composites applies to an output witness given in the family at
the completed transcript, without a transport argument. -/
example (n : Move oracleSig (.oracle Nat OracleInterface.instDefault))
    (tr : PathAlong oracleSig (afterFirst.append fun p => suffix ⟨oracleSig.toFunB _ n, p⟩))
    (w : OutWitness ⟨n, PrefixMoves.completeWith oracleSig (.root _) ⟨⟩ tr⟩) : True := by
  have _ := KnowledgeStateFunction.extractFrom_append_down_family firstState secondState seam
    stmt₀ n (.root _) ⟨⟩ tr w
  trivial

/-! ### Security -/

-- KnowledgeComposition fixture `firstCertificate`: the prefix at error one.
/-- The prefix verifier is round-by-round knowledge sound with error one. -/
theorem first_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness.{0, 0, 0, 0, 0, 0} firstVerifier impl (fun _ => True)
    (fun _ (_ : Nat) => False)
      (fun _ tr z (_ : MidWitness tr) => z.1 = true) firstDraw (fun _ => 1) :=
  ⟨firstState, fun _ _ a _ _ _ _ => by
    let : MeasurableSpace (Move oracleSig a) := ⊤
    exact evalDist_apply_le_one _ _⟩

-- KnowledgeComposition fixtures `suffixCertificate` and `secondCertificate`: every suffix at
-- error one.
/-- Every suffix state function is locally bounded with error one. -/
theorem second_rbrKnowledgeSoundness (tr₁ : PathAlong oracleSig firstProtocol) :
    rbrKnowledgeSoundness.{0, 0, 0} oracleSig (suffix (projectPathAlong oracleSig firstProtocol
    tr₁))
      (fun _ => True) (relMid tr₁)
      (fun stmt tr₂ w => validOutput stmt (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)
        w)
      (secondDraw (projectPathAlong oracleSig firstProtocol tr₁)) (fun _ => 1) :=
  ⟨secondState tr₁, fun _ _ a _ _ _ _ => by
    let : MeasurableSpace (Move oracleSig a) := ⊤
    exact evalDist_apply_le_one _ _⟩

-- KnowledgeComposition fixture `compositeCertificate`, through `LocallyBounded.append`.
/-- The composite state function is locally bounded by the combined errors. -/
example : compositeState.LocallyBounded
    (combineDraw oracleSig firstProtocol suffix firstDraw secondDraw)
    (combineDraw (m := fun _ => ℝ≥0∞) oracleSig firstProtocol suffix (fun _ => 1)
      (fun _ _ => 1)) :=
  KnowledgeStateFunction.LocallyBounded.append seam
    (fun _ _ a _ _ _ _ => by
      let : MeasurableSpace (Move oracleSig a) := ⊤
      exact evalDist_apply_le_one _ _)
    (fun _ _ _ a _ _ _ _ => by
      let : MeasurableSpace (Move oracleSig a) := ⊤
      exact evalDist_apply_le_one _ _)
    (fun _ _ h => h)

-- KnowledgeComposition fixtures `compositeCertificate` and `compositeEndpoint`, at the verifier
-- level: the seam is the prefix acceptance.
/-- The appended verifier is round-by-round knowledge sound with the combined errors. -/
theorem composed_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness.{0, 0, 0, 0, 0, 0} composed impl (fun _ => True) (fun
    _ (_ : Nat) => False)
      (fun _ tr z (_ : OutWitness tr) => z.1 = true)
      (combineDraw oracleSig firstProtocol suffix firstDraw secondDraw)
      (combineDraw (m := fun _ => ℝ≥0∞) oracleSig firstProtocol suffix (fun _ => 1)
        (fun _ _ => 1)) :=
  rbrKnowledgeSoundness_append oracleSig first_rbrKnowledgeSoundness second_rbrKnowledgeSoundness
    (fun _ _ h => h) (fun tr₁ stmt _ _ h => (firstVerifier_validAcceptance_iff stmt tr₁).2 h)

/-- The suffix state function over the suffix statement, a Boolean claim, after the prefix
transcript `tr₁`; its witness carriers read the prefix payload. -/
def suffixState (tr₁ : PathAlong oracleSig firstProtocol) :
    KnowledgeStateFunction oracleSig (suffix (projectPathAlong oracleSig firstProtocol tr₁)) Bool
      (fun _ tr₂ => OutWitness (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂))
      (fun _ => MidWitness tr₁) (fun _ => True) (fun t _ => t = true) (fun t _ _ => t = true) where
  Witness _ {_} sp _ := match sp with
    | .root _ => Fin (payload tr₁.1 + 1)
    | .down _ _ => Fin (payload tr₁.1 + 1) × Unit
  toFun t {_} _ _ _ := t = true
  extractRoot _ w := w
  extractStep _ {_ _} sp _ _ w := by
    cases sp with
    | root => exact w.1
    | down _ tail => cases tail
  extractLeaf _ sp _ w := by
    cases sp with
    | down _ tail =>
      cases tail
      exact w
  root _ _ _ h := h
  send _ _ _ _ _ _ h := h
  leaf _ _ _ _ h := h

-- KnowledgeComposition fixture `compositeCertificate` (`sequentialClosed`): the suffix statement
-- is the prefix challenge, a function of the prefix transcript.
/-- The appended verifier is knowledge sound from a suffix stated over its own statement. -/
example :
    OracleVerifier.rbrKnowledgeSoundness.{0, 0, 0, 0, 0, 0} composed impl (fun _ => True) (fun
    _ (_ : Nat) => False)
      (fun _ tr z (_ : OutWitness tr) => z.1 = true)
      (combineDraw oracleSig firstProtocol suffix firstDraw secondDraw)
      (combineDraw (m := fun _ => ℝ≥0∞) oracleSig firstProtocol suffix (fun _ => 1)
        (fun _ _ => 1)) :=
  rbrKnowledgeSoundness_append_of_mid oracleSig (T := fun _ => Bool)
    (fun _ tr₁ => bit tr₁.2.1)
    first_rbrKnowledgeSoundness
    (fun tr₁ => ⟨suffixState tr₁, fun _ _ a _ _ _ _ => by
      let : MeasurableSpace (Move oracleSig a) := ⊤
      exact evalDist_apply_le_one _ _⟩)
    (fun _ _ w => w) (fun _ _ _ w => w)
    (fun _ _ _ => trivial) (fun tr₁ stmt _ _ h => (firstVerifier_validAcceptance_iff stmt tr₁).2 h)
    (fun stmt tr₁ tr₂ _ h => (composed_validAcceptance_iff stmt
      (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)).1 h)

/-- An empty protocol used to check statement-indexed verifier composition. -/
abbrev indexedProtocol : Protocol := .pure ⟨⟩

/-- A verifier that returns its input natural-number statement. -/
def indexedVerifier : Verifier OracleSpec.emptySpec indexedProtocol Nat (fun _ => Nat) where
  decide n _ _ := pure n

/-- The empty protocol has no challenge. -/
def indexedDraw : QueryImpl (challengeSpec plainSig indexedProtocol) ProbComp :=
  fun c => c.val.elim

/-- A standalone knowledge state function at statement `n`, with witness type `Fin (n + 1)`. -/
def indexedCertificate : KnowledgeStateFunction plainSig indexedProtocol Nat
    (fun n _ => Fin (n + 1)) (fun n => Fin (n + 1)) (fun _ => True) (fun _ _ => True)
    (fun n tr w => indexedVerifier.validAcceptance impl n tr (fun _ => w.val ≤ n)) where
  Witness n {_} _ _ := Fin (n + 1)
  toFun _ {_} _ _ _ := True
  extractRoot _ w := w
  extractStep _ {_ _} sp := nomatch sp
  extractLeaf _ _ _ w := w
  root _ _ _ _ := trivial
  send sp := nomatch sp
  leaf _ _ _ _ _ := trivial

/-- The standalone verifier theorem quantifies statement-indexed input and output witnesses. -/
theorem indexed_standalone : Verifier.rbrKnowledgeSoundness.{0, 0, 0} indexedVerifier impl (fun
    _ => True)
    (fun n (_ : Fin (n + 1)) => True) (fun n _ _ (w : Fin (n + 1)) => w.val ≤ n)
    indexedDraw (fun _ => 0) :=
  ⟨indexedCertificate, fun _ _ _ _ sp => nomatch sp⟩

/-- Verifier composition uses the suffix's standalone theorem at its own statement and witness
family. Both witness maps are identities in the carrier selected by the statement. -/
theorem indexed_composed :
    Verifier.rbrKnowledgeSoundness.{0, 0, 0}
      (indexedVerifier.append (fun _ => indexedVerifier)) impl
    (fun _ => True) (fun n (_ : Fin (n + 1)) => True)
    (fun n _ _ (w : Fin (n + 1)) => w.val ≤ n)
    (combineDraw plainSig indexedProtocol (fun _ => indexedProtocol) indexedDraw
      (fun _ => indexedDraw))
    (combineDraw (m := fun _ => ℝ≥0∞) plainSig indexedProtocol (fun _ => indexedProtocol)
      (fun _ => 0) (fun _ _ => 0)) := by
  apply Verifier.rbrKnowledgeSoundness_append_of_pure indexedVerifier (fun _ => indexedVerifier)
    impl (fun n _ => n) (fun _ _ => rfl) (fun _ _ w => w) (fun _ _ _ w => w)
    indexed_standalone (fun _ => indexed_standalone)
  · exact fun _ _ _ => trivial
  · intro n tr w _
    exact Nat.le_of_lt_succ w.isLt
  · exact fun _ _ _ _ _ _ _ h => h

/-- A shared counter for checking the ambient state at a composition boundary. -/
abbrev seamSpec : OracleSpec Unit := Unit →ₒ Nat

/-- Each counter read returns its old value and increments the state. -/
def seamHandler : QueryImpl seamSpec (StateT Nat ProbComp) := fun _ => do
  let n ← get
  set (n + 1)
  pure n

/-- The prefix returns the counter value that it reads. -/
def seamFirst : Verifier seamSpec indexedProtocol Unit (fun _ => Nat) where
  decide _ _ _ := OptionT.mk do
    let n ← liftM (seamSpec.query ())
    pure (some n)

/-- The suffix accepts only if it reads the successor of the prefix result. -/
def seamSecond : Verifier seamSpec indexedProtocol Nat (fun _ => Nat) where
  decide n _ _ := OptionT.mk do
    let next ← liftM (seamSpec.query ())
    pure (if next = n + 1 then some next else none)

/-- Decomposing the accepted composite retains state one at the seam, rather than choosing
an unrelated state for the suffix. -/
example : ∃ mid between,
    (some mid, between) ∈ support ((simulateQ seamHandler
      (seamFirst.decide () ⟨⟩ (toPlainView indexedProtocol ⟨⟩)).run).run 0) ∧
    (some 1, 2) ∈ support ((simulateQ seamHandler
      (seamSecond.decide mid ⟨⟩ (toPlainView indexedProtocol ⟨⟩)).run).run between) ∧
    between = 1 := by
  have hc : (some 1, 2) ∈ support ((simulateQ seamHandler
      ((seamFirst.append (fun _ => seamSecond)).decide () ⟨⟩
        (toPlainView (indexedProtocol.append (fun _ => indexedProtocol)) ⟨⟩)).run).run 0) := by
    change (some 1, 2) ∈ support (pure (some 1, 2) : ProbComp (Option Nat × Nat))
    simp
  obtain ⟨mid, between, hp, hs⟩ := seamFirst.support_append (fun _ => seamSecond)
    seamHandler () ⟨⟩ (toPlainView (indexedProtocol.append (fun _ => indexedProtocol)) ⟨⟩)
    0 2 1 hc
  have hb : between = 1 := by
    change (some mid, between) ∈ support (pure (some 0, 1) : ProbComp (Option Nat × Nat)) at hp
    have hp' : (some mid, between) = (some 0, 1) := by simpa using hp
    exact congrArg Prod.snd hp'
  exact ⟨mid, between, hp, hs, hb⟩

/-- An empty oracle specification with a higher-universe index and ordinary response types. -/
abbrev largeSpec : OracleSpec.{1, 0} PEmpty.{2} := fun _ => PUnit

/-- A counter implementation in a monad whose result universe is larger than its input universe. -/
def largeSeamHandler : QueryImpl seamSpec (StateT Nat (OracleComp largeSpec)) := fun _ => do
  let n ← get
  set (n + 1)
  pure n

/-- The decision-fold law permits an independently larger target monad universe. -/
example : ((simulateQ largeSeamHandler
    ((seamFirst.append (fun _ => seamSecond)).decide () ⟨⟩
      (toPlainView (indexedProtocol.append (fun _ => indexedProtocol)) ⟨⟩)).run).run 0) =
      (pure (some 1, 2) : OracleComp largeSpec (Option Nat × Nat)) := by
  rw [Verifier.simulateQ_append_run]
  rfl

-- KnowledgeComposition fixture `emptyExtractor`, restated on an `Empty` message.
/-- Empty message carriers and empty witnesses need no fabricated message or witness. -/
def emptyState : KnowledgeStateFunction plainSig
    (.liftBind (.message Empty) fun _ => .pure ⟨⟩ : Protocol.{0}) Unit (fun _ _ => Empty) (fun _ =>
      Empty)
    (fun _ => True) (fun _ _ => False) (fun _ _ _ => True) where
  Witness _ {_} _ _ := Empty
  toFun _ {_} _ _ _ := False
  extractRoot _ w := w
  extractStep _ {_ _} sp _ x _ := by
    cases sp with
    | root => exact Empty.elim x
    | down _ tail => cases tail
  extractLeaf _ _ _ w := w
  root _ _ _ h := h
  send _ _ _ _ _ _ h := h
  leaf _ _ _ w _ := w.elim

end Interaction.Core.KnowledgeCompositionTests

run_cmd do
  for decl in [``Interaction.Core.KnowledgeStateFunction.extractAlong_append,
      ``Interaction.Core.KnowledgeStateFunction.toFun_terminalWitness_append,
      ``Interaction.Core.KnowledgeStateFunction.LocallyBounded.append,
      ``Interaction.Core.rbrKnowledgeSoundness_append,
      ``Interaction.Core.rbrKnowledgeSoundness_append_of_mid,
      ``Interaction.Core.KnowledgeStateFunction.extraction_failure_implies_badChallengeAlong,
      ``Interaction.Core.Verifier.validAcceptance_append,
      ``Interaction.Core.OracleVerifier.validAcceptance_append,
      ``Interaction.Core.Verifier.rbrKnowledgeSoundness_append,
      ``Interaction.Core.Verifier.rbrKnowledgeSoundness_append_of_pure,
      ``Interaction.Core.KnowledgeCompositionTests.indexed_standalone,
      ``Interaction.Core.KnowledgeCompositionTests.indexed_composed,
      ``Interaction.Core.KnowledgeCompositionTests.observed_eq,
      ``Interaction.Core.KnowledgeCompositionTests.compositeState_extractAlong,
      ``Interaction.Core.KnowledgeCompositionTests.composed_rbrKnowledgeSoundness] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
