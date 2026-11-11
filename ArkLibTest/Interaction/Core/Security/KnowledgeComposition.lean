/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Security.KnowledgeComposition
import ArkLibTest.Interaction.Core.Support

/-!
# Knowledge composition across an oracle seam

The prefix prover sends a natural-number oracle, receives a Boolean challenge and sends a public
Boolean selector. The selector chooses a public unit-message suffix or an oracle-message suffix.
The challenge changes the returned claim and private output independently of that choice. Witness
carriers depend on the prefix payload. The tests extract on both challenges and both suffix shapes,
identify terminal relations and close the exported oracle with data from the same execution.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp MeasureTheory
open scoped ENNReal

-- Disposition IDs refer to docs/design/interaction-layer/knowledge-composition-disposition.md.

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

/-- The prefix sends an oracle, draws a challenge and sends a public shape selector. -/
@[instance_reducible] def firstProtocol : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) fun _ =>
    .liftBind (.challenge Bool) fun _ =>
      .liftBind (.message Bool) fun _ => .pure ⟨⟩

/-- A public selector chooses a public unit message or a natural-number oracle message. -/
@[instance_reducible] def secondProtocol (choice : Bool) : OracleProtocol :=
  if choice then .liftBind (.message Unit) fun _ => .pure ⟨⟩
  else .liftBind (.oracle Nat OracleInterface.instDefault) fun _ => .pure ⟨⟩

/-- The payload of a natural-number oracle message. -/
abbrev payload : Move oracleSig (.oracle Nat OracleInterface.instDefault) → Nat := id

/-- A Boolean challenge. -/
abbrev bit : Move oracleSig.{0, 0} (.challenge Bool) → Bool := id

/-- The suffix shape depends only on the public prover selector. -/
abbrev suffix : Path firstProtocol → OracleProtocol := fun p => secondProtocol p.2.2.1

/-- The prefix protocol followed by the selected suffix. -/
abbrev combined : OracleProtocol := firstProtocol.append suffix

/-- The prefix verifier returns the challenge from its view and exports the sent oracle. -/
def firstVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} OracleSpec.emptySpec firstProtocol
    Unit (fun _ => Bool) noInputs
    (fun _ => exportFamily) where
  decide _ _ v := pure (show Bool from v.val.2.1)
  outputMap _ p _ := (OracleMap.embedding (pathFamily firstProtocol p) (fun _ => .inl ⟨⟩)).comp
    (OracleMap.snd _ _)

/-- The suffix verifier accepts its input statement and passes the export through. -/
def secondVerifier (p : Path firstProtocol) : OracleVerifier.{0, 0, 0, 0, 0, 0, 0}
    OracleSpec.emptySpec (suffix p)
    Bool (fun _ => Bool)
    exportFamily
    (fun _ => exportFamily) where
  decide stmt _ _ := pure stmt
  outputMap _ _ _ := OracleMap.fst _ _

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible :
    OracleVerifier.OutputCompatibility firstVerifier secondVerifier where
  outputMap stmt p v :=
    ((secondVerifier (Path.split firstProtocol suffix p).1).outputMap false
      (Path.split firstProtocol suffix p).2
      (View.split firstProtocol suffix p v).2).comp
      (OracleVerifier.suffixRoute firstVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The appended verifier. -/
def composed := firstVerifier.append secondVerifier compatible

/-- A completed prefix transcript. -/
abbrev firstPath (n : Nat) (b : Bool) (choice : Bool) :
    PathAlong oracleSig firstProtocol := ⟨n, b, choice, ⟨⟩⟩

-- Disposition KC-093.
/-- The exported oracle of every completed prefix transcript is its sent payload. -/
example (n : Nat) (b : Bool) (choice : Bool) :
    (firstVerifier.outputMap () (projectPathAlong oracleSig firstProtocol (firstPath n b choice))
      (toView firstProtocol (firstPath n b choice))).f
        (noData, payloads firstProtocol (firstPath n b choice)) ⟨⟩ = n := rfl

/-- A completed suffix transcript at either public selector value. -/
def secondPath (choice : Bool) (m : Nat) : PathAlong oracleSig (secondProtocol choice) := by
  cases choice
  · exact ⟨m, ⟨⟩⟩
  · exact ⟨(), ⟨⟩⟩

/-- The composite exports the prefix payload on either selected suffix shape and either
challenge. -/
theorem composed_export_eq (n : Nat) (b choice : Bool) (m : Nat) :
    let tr := PathAlong.append oracleSig firstProtocol suffix
      (firstPath n b choice) (secondPath choice m)
    (composed.outputMap () (projectPathAlong oracleSig combined tr) (toView combined tr)).f
      (noData, payloads combined tr) ⟨⟩ = n := by
  dsimp only
  cases choice <;> kernel_rfl

/-! ### Runs -/

/-- The prefix prover sends `7` and keeps it as private memory. -/
def firstProver (choice : Bool) : Prover oracleSig
    OracleSpec.emptySpec firstProtocol (fun _ => Nat) :=
  pure ⟨(7 : Nat), pure fun _ => pure ⟨choice, pure (7 : Nat)⟩⟩

/-- The suffix prover sends `5` after a true challenge and `99` after a false one, with private
output `41` or `73`. -/
def secondProver (tr : PathAlong oracleSig firstProtocol) (_ : Nat) :
    OracleComp OracleSpec.emptySpec
      (Prover oracleSig OracleSpec.emptySpec
        (suffix (projectPathAlong oracleSig firstProtocol tr)) (fun _ => Nat)) := by
  rcases tr with ⟨n, b, choice, ⟨⟩⟩
  cases choice
  · exact pure (pure ⟨(cond b 5 99 : Nat), pure (cond b 41 73 : Nat)⟩)
  · exact pure (pure ⟨(), pure (cond b 41 73 : Nat)⟩)

/-- The whole prover. -/
def prover (choice : Bool) : Prover oracleSig OracleSpec.emptySpec combined (fun _ => Nat) :=
  Prover.append (firstProver choice) secondProver

/-- Answers the only challenge of the composite with `b`. -/
def handler (b : Bool) :
    QueryImpl (OracleSpec.emptySpec + challengeSpec oracleSig combined) Id
  | .inl i => i.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => (pure b : Id Bool)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨choice, node⟩⟩⟩, h⟩ => by
      cases choice <;> rcases node with (_ | ⟨_, node⟩)
      all_goals first | cases h | cases node

/-- The sent payload, the challenge, the private output, and the claim with its exported oracle,
of the composite run with challenge `b`. -/
def observed (choice b : Bool) : Nat × Bool × Nat × Option (Bool × Nat) :=
  let result := simulateQ (handler b) (composed.run () noData (prover choice))
  (payload result.1.1, bit result.1.2.1, result.2.1,
    result.2.2.map (fun z => (z.1, z.2 ⟨⟩)))

-- Disposition KC-207.
/-- The composite run returns the prefix payload, the challenge, the suffix private output and
the claim, with the exported oracle read from the prefix payload. -/
theorem observed_eq (choice b : Bool) :
    observed choice b = (7, b, if b then 41 else 73, some (b, 7)) := by
  cases choice <;> cases b <;> kernel_rfl

-- Disposition KC-215.
/-- info: (7, true, 41, some (true, 7)) -/
#guard_msgs in
#eval observed true true

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [observed false false == (7, false, 73, some (false, 7)),
  observed false true == (7, true, 41, some (true, 7)),
  observed true false == (7, false, 73, some (false, 7)),
  observed true true == (7, true, 41, some (true, 7))]

/-! ### Challenge sampling

The composite challenge is drawn by the prefix draw, and the suffix draw is consulted only on the
suffix, which has no challenge.
-/

/-- The prefix draws `true`. -/
def firstDraw : QueryImpl (challengeSpec oracleSig firstProtocol) ProbComp
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => (pure true : ProbComp Bool)
  | ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

/-- The suffix has no challenge. -/
def secondDraw (p : Path firstProtocol) :
    QueryImpl (challengeSpec oracleSig (suffix p)) ProbComp := by
  rcases p with ⟨_, _, choice, ⟨⟩⟩
  cases choice
  all_goals
    exact fun c => match c with
      | ⟨.inl _, h⟩ => nomatch h
      | ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- The prefix prover over `ProbComp`. -/
def firstProbProver (choice : Bool) : Focal oracleSig ProbComp firstProtocol (fun _ => Nat) :=
  pure ⟨(7 : Nat), pure fun _ => pure ⟨choice, pure (7 : Nat)⟩⟩

/-- The suffix prover over `ProbComp`. -/
def secondProbProver (choice : Bool) :
    Focal oracleSig ProbComp (secondProtocol choice) (fun _ => Nat) := by
  cases choice
  · exact pure ⟨(5 : Nat), pure (41 : Nat)⟩
  · exact pure ⟨(), pure (41 : Nat)⟩

/-- The actual suffix message, with its public or oracle constructor. -/
def secondMessage (choice : Bool) (tr : PathAlong oracleSig (secondProtocol choice)) :
    Unit ⊕ Nat := by
  cases choice
  · exact .inr (payload tr.1)
  · exact .inl tr.1

-- Disposition KC-219.
/-- The prefix run under `sampler oracleSig firstProtocol firstDraw` has challenge `true`. -/
example (choice : Bool) : (fun z => (payload z.1.1, bit z.1.2.1, z.2.1)) <$>
    TwoParty.Lens.run firstProtocol (firstProbProver choice)
      (sampler oracleSig firstProtocol firstDraw) =
      (pure (7, true, 7) : ProbComp (Nat × Bool × Nat)) := rfl

-- Disposition KC-234.
/-- The suffix run under `sampler oracleSig _ (secondDraw p)` returns the suffix message. -/
example (p : Path firstProtocol) : (fun z => (secondMessage p.2.2.1 z.1, z.2.1)) <$>
    TwoParty.Lens.run (suffix p) (secondProbProver p.2.2.1)
      (sampler oracleSig (suffix p) (secondDraw p)) =
      (pure (if (show Bool from p.2.2.1) then Sum.inl () else Sum.inr 5, 41) :
        ProbComp ((Unit ⊕ Nat) × Nat)) := by
  rcases p with ⟨_, _, choice, ⟨⟩⟩
  cases choice <;> rfl

-- Disposition KC-249.
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
  rcases tr with ⟨n, b, choice, ⟨⟩⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change (∃ _ : Unit, 0 < 𝒟[(pure (some b) : ProbComp (Option Bool))]
    {v | ∃ t, v = some t ∧ t = true}) ↔ b = true
  cases b <;> simp

/-- The composite accepts with a true claim exactly when the challenge is true. -/
theorem composed_validAcceptance_iff (stmt : Stmt) (tr : PathAlong oracleSig combined) :
    composed.validAcceptance impl stmt tr (fun z => z.1 = true) ↔ bit tr.2.1 = true := by
  rcases tr with ⟨n, b, choice, tr⟩
  cases choice <;> rcases tr with ⟨m, ⟨⟩⟩
  all_goals
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
      | down _ tail =>
        cases tail with
        | root => exact w
        | down _ tail => cases tail
  extractLeaf _ sp history w := by
    cases sp with
    | down _ tail =>
      cases tail with
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
      | down _ tail =>
        cases tail with
        | root => exact h
        | down _ tail => cases tail
  leaf sp history stmt _ h := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail with
        | down _ tail =>
          cases tail
          rcases history with ⟨⟨n, rfl⟩, ⟨⟨b, rfl⟩, ⟨⟨choice, rfl⟩, ⟨⟩⟩⟩⟩
          exact (firstVerifier_validAcceptance_iff stmt ⟨n, b, choice, ⟨⟩⟩).1 h

/-- The suffix state function after the prefix transcript `tr₁`. Its witnesses lie in
`Fin (n + 1)` for the prefix payload `n`, paired with a unit after the suffix message; these are
the carriers of its input and output witnesses, and its root and leaf maps are identities. Its
state holds exactly when the prefix challenge was true. -/
def secondState (tr₁ : PathAlong oracleSig firstProtocol) :
    KnowledgeStateFunction oracleSig (suffix (projectPathAlong oracleSig firstProtocol tr₁)) Stmt
      (fun _ tr₂ => OutWitness (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂))
      (fun _ => MidWitness tr₁) (fun _ => True) (relMid tr₁)
      (fun stmt tr₂ w => validOutput stmt (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)
        w) := by
  rcases tr₁ with ⟨n, b, choice, ⟨⟩⟩
  cases choice
  · exact {
      Witness _ {_} sp _ := match sp with
        | .root _ => Fin (payload n + 1)
        | .down _ _ => Fin (payload n + 1) × Unit
      toFun _ {_} _ _ _ := b = true
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
            (PathAlong.append oracleSig firstProtocol suffix ⟨n, b, false, ⟨⟩⟩ ⟨m, ⟨⟩⟩)).1 h
    }
  · exact {
      Witness _ {_} sp _ := match sp with
        | .root _ => Fin (payload n + 1)
        | .down _ _ => Fin (payload n + 1) × Unit
      toFun _ {_} _ _ _ := b = true
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
            (PathAlong.append oracleSig firstProtocol suffix ⟨n, b, true, ⟨⟩⟩ ⟨m, ⟨⟩⟩)).1 h
    }

/-- The seam: a suffix root state extracts a witness the prefix accepts. -/
theorem seam (tr₁ : PathAlong oracleSig firstProtocol) (stmt : Stmt)
    (w : (secondState tr₁).Witness stmt (.root _) ⟨⟩) (h : (secondState tr₁).toFun stmt (.root _) ⟨⟩
      w) :
    validMid stmt tr₁ ((secondState tr₁).extractRoot stmt w) := by
  rcases tr₁ with ⟨n, b, choice, ⟨⟩⟩
  cases choice <;> exact (firstVerifier_validAcceptance_iff stmt _).2 h

/-- The composite state function. -/
def compositeState := KnowledgeStateFunction.append firstState secondState seam

/-- The input statement. -/
def stmt₀ : Stmt := ((), noData)

/-- Failed extraction keeps the supplied terminal witness when identifying a receiver step. -/
example (n : Nat) (choice : Bool) (w : Fin (n + 1)) :
    firstState.BadChallengeAlong stmt₀ (firstPath n true choice) w :=
  firstState.extraction_failure_implies_badChallengeAlong stmt₀ (firstPath n true choice) w trivial
    ((firstVerifier_validAcceptance_iff stmt₀ _).2 rfl) id

/-- The composite transcript with challenge `true`. -/
def truePath : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstProtocol suffix (firstPath 7 true true) (secondPath true 5)

/-- The composite transcript with challenge `false`. -/
def falsePath : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstProtocol suffix (firstPath 7 false false) (secondPath false 99)

-- Disposition KC-095.
/-- Prefix extraction on payload `7` takes its output witness in `Fin 8`. -/
example : firstState.extractAlong stmt₀ (firstPath 7 true true) (⟨6, by decide⟩ : Fin 8) = 6 := rfl

/-- info: 6 -/
#guard_msgs in
#eval firstState.extractAlong stmt₀ (firstPath 7 true true) (⟨6, by decide⟩ : Fin 8)

/-- The output witnesses of the composite at every transcript are the carrier `Fin (n + 1) × Unit`
of the prefix payload `n`. -/
example (n : Nat) (b : Bool) (choice : Bool) (m : Nat) :
    OutWitness (PathAlong.append oracleSig firstProtocol suffix (firstPath n b choice)
      (secondPath choice m)) =
      (Fin (n + 1) × Unit) := by cases choice <;> rfl

-- Disposition KC-268, KC-271.
/-- Composite extraction is suffix extraction followed by prefix extraction, and returns the
value of the output witness. -/
theorem compositeState_extractAlong (n : Nat) (b : Bool) (choice : Bool) (m : Nat)
    (w : Fin (n + 1) × Unit) :
    compositeState.extractAlong stmt₀
      (PathAlong.append oracleSig firstProtocol suffix (firstPath n b choice)
        (secondPath choice m)) w = w.1.val := by
  cases choice <;> exact
    (KnowledgeStateFunction.extractAlong_append firstState secondState seam stmt₀
      (firstPath n b _) (secondPath _ m) w).trans rfl

-- Disposition KC-268.
example : compositeState.extractAlong stmt₀ truePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit) = 6 :=
  compositeState_extractAlong 7 true true 5 _

-- Disposition KC-271.
example : compositeState.extractAlong stmt₀ falsePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit) = 6 :=
  compositeState_extractAlong 7 false false 99 _

-- Disposition KC-274.
/-- info: 6 -/
#guard_msgs in
#eval compositeState.extractAlong stmt₀ truePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)

-- Disposition KC-276.
/-- info: 6 -/
#guard_msgs in
#eval compositeState.extractAlong stmt₀ falsePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)

-- Disposition KC-308.
/-- On the true path, the composite terminal witness of an output witness in `Fin 8 × Unit` keeps
its value. -/
example : (compositeState.terminalWitness stmt₀ truePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)).1.val = 6 := rfl

/-- At every composite transcript, the terminal witness carrier is the output witness carrier and
the terminal witness is the output witness. -/
theorem composite_terminalWitness (n : Nat) (b : Bool) (choice : Bool) (m : Nat)
    (w : Fin (n + 1) × Unit) :
    HEq (compositeState.terminalWitness stmt₀
      (PathAlong.append oracleSig firstProtocol suffix
        (firstPath n b choice) (secondPath choice m)) w) w := by
  cases choice <;> rfl

/-- The oracle suffix's terminal witness equals the supplied witness, on either challenge. -/
example (n : Nat) (b : Bool) (m : Nat) (w : Fin (n + 1) × Unit) :
    compositeState.terminalWitness stmt₀
      (PathAlong.append oracleSig firstProtocol suffix
        (firstPath n b false) (secondPath false m)) w = w := rfl

/-- The public suffix's terminal witness equals the supplied witness, on either challenge. -/
example (n : Nat) (b : Bool) (w : Fin (n + 1) × Unit) :
    compositeState.terminalWitness stmt₀
      (PathAlong.append oracleSig firstProtocol suffix
        (firstPath n b true) (secondPath true 0)) w = w := rfl

/-- The composite terminal state holds exactly when the composite accepts. -/
theorem composite_terminal_iff (n : Nat) (b : Bool) (choice : Bool) (m : Nat)
    (w : Fin (n + 1) × Unit) :
    compositeState.toFun stmt₀
        (completeSpine oracleSig
          (PathAlong.append oracleSig firstProtocol suffix (firstPath n b choice)
            (secondPath choice m)))
        (completeMoves oracleSig _)
        (compositeState.terminalWitness stmt₀
          (PathAlong.append oracleSig firstProtocol suffix (firstPath n b choice)
            (secondPath choice m)) w) ↔
      validOutput stmt₀
        (PathAlong.append oracleSig firstProtocol suffix (firstPath n b choice)
          (secondPath choice m)) w := by
  cases choice <;> exact
    (KnowledgeStateFunction.toFun_terminalWitness_append firstState secondState seam stmt₀
      (firstPath n b _) (secondPath _ m) w).trans (composed_validAcceptance_iff stmt₀
        (PathAlong.append oracleSig firstProtocol suffix
          (firstPath n b _) (secondPath _ m))).symm

-- Direct-family corollaries: the witness is given in the family at the completed transcript.
/-- The prefix protocol after its oracle message. -/
abbrev afterFirst : OracleProtocol := .liftBind (.challenge Bool) fun _ =>
  .liftBind (.message Bool) fun _ => .pure ⟨⟩

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

-- Disposition KC-068.
/-- The prefix verifier is round-by-round knowledge sound with error one. -/
theorem first_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundnessOfNodes.{0, 0, 0, 0, 0, 0, 0} firstVerifier impl
    (fun _ => True)
    (fun _ (_ : Nat) => False)
      (fun _ tr z (_ : MidWitness tr) => z.1 = true) firstDraw (fun _ => 1) :=
  ⟨firstState, fun _ _ a _ _ _ _ => by
    let : MeasurableSpace (Move oracleSig a) := ⊤
    exact evalDist_apply_le_one _ _⟩

-- Disposition KC-120, KC-131.
/-- Every suffix state function is locally bounded with error one. -/
theorem second_rbrKnowledgeSoundness (tr₁ : PathAlong oracleSig firstProtocol) :
    rbrKnowledgeSoundnessOfNodes.{0, 0, 0} oracleSig (suffix
    (projectPathAlong oracleSig firstProtocol
    tr₁))
      (fun _ => True) (relMid tr₁)
      (fun stmt tr₂ w => validOutput stmt (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)
        w)
      (secondDraw (projectPathAlong oracleSig firstProtocol tr₁)) (fun _ => 1) :=
  ⟨secondState tr₁, fun _ _ a _ _ _ _ => by
    let : MeasurableSpace (Move oracleSig a) := ⊤
    exact evalDist_apply_le_one _ _⟩

-- Disposition KC-135.
/-- The composite state function is locally bounded by the combined errors. -/
example : compositeState.LocallyBoundedOfNodes
    (combineDraw oracleSig firstProtocol suffix firstDraw secondDraw)
    (combineDraw (m := fun _ => ℝ≥0∞) oracleSig firstProtocol suffix (fun _ => 1)
      (fun _ _ => 1)) :=
  KnowledgeStateFunction.LocallyBoundedOfNodes.append seam
    (fun _ _ a _ _ _ _ => by
      let : MeasurableSpace (Move oracleSig a) := ⊤
      exact evalDist_apply_le_one _ _)
    (fun _ _ _ a _ _ _ _ => by
      let : MeasurableSpace (Move oracleSig a) := ⊤
      exact evalDist_apply_le_one _ _)
    (fun _ _ h => h)

-- Disposition KC-135, KC-303.
/-- The appended verifier is round-by-round knowledge sound with the combined errors. -/
theorem composed_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundnessOfNodes.{0, 0, 0, 0, 0, 0, 0} composed impl
    (fun _ => True) (fun
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
      (fun _ => MidWitness tr₁) (fun _ => True) (fun t _ => t = true) (fun t _ _ => t = true) := by
  rcases tr₁ with ⟨n, b, choice, ⟨⟩⟩
  cases choice
  · exact {
      Witness _ {_} sp _ := match sp with
        | .root _ => Fin (payload n + 1)
        | .down _ _ => Fin (payload n + 1) × Unit
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
    }
  · exact {
      Witness _ {_} sp _ := match sp with
        | .root _ => Fin (payload n + 1)
        | .down _ _ => Fin (payload n + 1) × Unit
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
    }

-- Disposition KC-135.
/-- The appended verifier is knowledge sound from a suffix stated over its own statement. -/
example :
    OracleVerifier.rbrKnowledgeSoundnessOfNodes.{0, 0, 0, 0, 0, 0, 0} composed impl
    (fun _ => True) (fun
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
  Witness n {_} _ _ := Fin (payload n + 1)
  toFun _ {_} _ _ _ := True
  extractRoot _ w := w
  extractStep _ {_ _} sp := nomatch sp
  extractLeaf _ _ _ w := w
  root _ _ _ _ := trivial
  send sp := nomatch sp
  leaf _ _ _ _ _ := trivial

/-- The standalone verifier theorem quantifies statement-indexed input and output witnesses. -/
theorem indexed_standalone : Verifier.rbrKnowledgeSoundnessOfNodes.{0, 0, 0} indexedVerifier impl
    (fun
    _ => True)
    (fun n (_ : Fin (n + 1)) => True) (fun n _ _ (w : Fin (n + 1)) => w.val ≤ n)
    indexedDraw (fun _ => 0) :=
  ⟨indexedCertificate, fun _ _ _ _ sp => nomatch sp⟩

/-- Verifier composition uses the suffix's standalone theorem at its own statement and witness
family. Both witness maps are identities in the carrier selected by the statement. -/
theorem indexed_composed :
    Verifier.rbrKnowledgeSoundnessOfNodes.{0, 0, 0}
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

-- Disposition KC-312.
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
      ``Interaction.Core.KnowledgeCompositionTests.composed_export_eq,
      ``Interaction.Core.KnowledgeCompositionTests.composite_terminalWitness,
      ``Interaction.Core.KnowledgeCompositionTests.composite_terminal_iff,
      ``Interaction.Core.KnowledgeCompositionTests.compositeState_extractAlong,
      ``Interaction.Core.KnowledgeCompositionTests.composed_rbrKnowledgeSoundness] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
