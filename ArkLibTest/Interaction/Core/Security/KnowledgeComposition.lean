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
state function has witness carrier `Fin (payload + 1)` after the oracle message, and each suffix
state function, indexed by the prefix transcript, has a carrier that reads the same payload.
Composition with `KnowledgeStateFunction.append` extracts along both challenge values, and the
security statements compose at the verifier level, with the prefix acceptance as the seam.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp MeasureTheory
open scoped ENNReal

namespace Interaction.Core.KnowledgeCompositionTests

/-- The carriers of no input oracles. -/
abbrev NoData : PEmpty.{1} → Type := fun i => i.elim

/-- No input oracles. -/
@[instance_reducible] def noInputs : OracleFamily PEmpty NoData := ⟨fun i => i.elim⟩

/-- The input data of `noInputs`. -/
def noData : ∀ i, NoData i := fun i => i.elim

/-- One exported scalar oracle. -/
@[instance_reducible] def exportFamily : OracleFamily PUnit (fun _ => Nat) :=
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

abbrev combined : OracleProtocol := firstProtocol.append suffix

/-- The prefix verifier returns the challenge from its view and exports the sent oracle. -/
def firstVerifier : OracleVerifier OracleSpec.emptySpec firstProtocol Unit Bool noInputs
    exportFamily where
  decide _ _ v := pure (show Bool from v.val.2.1)
  outputMap _ p _ := OracleMap.embedding (sumFamily noInputs (pathFamily firstProtocol p))
    (fun _ => .inr (.inl ⟨⟩))

/-- The suffix verifier accepts its input statement and passes the export through. -/
def secondVerifier : OracleVerifier OracleSpec.emptySpec secondProtocol Bool Bool exportFamily
    exportFamily where
  decide stmt _ _ := pure stmt
  outputMap _ q _ := OracleMap.embedding (sumFamily exportFamily (pathFamily secondProtocol q))
    (fun _ => .inl ⟨⟩)

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
        (sumData noData (payloads firstProtocol (firstPath n b))) ⟨⟩ = n := rfl

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
    firstVerifier.validAcceptance impl (fun z => z.1 = true) stmt tr ↔ bit tr.2.1 = true := by
  rcases tr with ⟨n, b, ⟨⟩⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change (∃ _ : Unit, 0 < 𝒟[(pure (some b) : ProbComp (Option Bool))]
    {v | ∃ t, v = some t ∧ t = true}) ↔ b = true
  cases b <;> simp

/-- The composite accepts with a true claim exactly when the challenge is true. -/
theorem composed_validAcceptance_iff (stmt : Stmt) (tr : PathAlong oracleSig combined) :
    composed.validAcceptance impl (fun z => z.1 = true) stmt tr ↔ bit tr.2.1 = true := by
  rcases tr with ⟨n, b, m, ⟨⟩⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change (∃ _ : Unit, 0 < 𝒟[(pure (some b) : ProbComp (Option Bool))]
    {v | ∃ t, v = some t ∧ t = true}) ↔ b = true
  cases b <;> simp

/-- The prefix valid output: acceptance with a true claim. -/
abbrev validMid (stmt : Stmt) (tr : PathAlong oracleSig firstProtocol) (_ : Nat) : Prop :=
  firstVerifier.validAcceptance impl (fun z => z.1 = true) stmt tr

/-- The composite valid output: acceptance with a true claim. -/
abbrev validOutput (stmt : Stmt) (tr : PathAlong oracleSig combined) (_ : Nat × Unit) : Prop :=
  composed.validAcceptance impl (fun z => z.1 = true) stmt tr

/-- The suffix input relation: the prefix challenge was true. -/
abbrev relMid (tr₁ : PathAlong oracleSig firstProtocol) (_ : Stmt) (_ : Nat) : Prop :=
  bit tr₁.2.1 = true

/-- The prefix state function. After the oracle message `n`, witnesses lie in `Fin (n + 1)`; the
state is false until the challenge, and then holds exactly when the challenge is true. -/
def firstState : KnowledgeStateFunction oracleSig firstProtocol Stmt Nat Nat (fun _ => True)
    (fun _ _ => False) validMid where
  Witness {_} sp history := match sp, history with
    | .root _, _ => Nat
    | .down _ _, history => Fin (payload history.1.1 + 1)
  toFun {_} sp history _ _ := match sp, history with
    | .root _, _ => False
    | .down _ (.root _), _ => False
    | .down _ (.down _ _), history => bit history.2.1.1 = true
  extractRoot _ w := w
  extractStep sp _ _ _ w := by
    cases sp with
    | root => exact w.val
    | down _ tail =>
      cases tail with
      | root => exact w
      | down _ tail => cases tail
  extractLeaf sp history _ w := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail
        exact ⟨w % (payload history.1.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
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
`Fin (n + 1)` for the prefix payload `n`, paired with a unit after the suffix message, and its
state holds exactly when the prefix challenge was true. -/
def secondState (tr₁ : PathAlong oracleSig firstProtocol) :
    KnowledgeStateFunction oracleSig (suffix (projectPathAlong oracleSig firstProtocol tr₁)) Stmt
      (Nat × Unit) Nat (fun _ => True) (relMid tr₁)
      (fun stmt tr₂ w => validOutput stmt (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)
        w) where
  Witness {_} sp _ := match sp with
    | .root _ => Fin (payload tr₁.1 + 1)
    | .down _ _ => Fin (payload tr₁.1 + 1) × Unit
  toFun _ _ _ _ := bit tr₁.2.1 = true
  extractRoot _ w := w.val
  extractStep sp _ _ _ w := by
    cases sp with
    | root => exact w.1
    | down _ tail => cases tail
  extractLeaf sp _ _ w := by
    cases sp with
    | down _ tail =>
      cases tail
      exact (⟨w.1 % (payload tr₁.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, ())
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
    (w : (secondState tr₁).Witness (.root _) ⟨⟩) (h : (secondState tr₁).toFun (.root _) ⟨⟩ stmt w) :
    validMid stmt tr₁ ((secondState tr₁).extractRoot stmt w) :=
  (firstVerifier_validAcceptance_iff stmt tr₁).2 h

/-- The composite state function. -/
def compositeState := KnowledgeStateFunction.append firstState secondState seam

/-- The input statement. -/
def stmt₀ : Stmt := ((), noData)

/-- The composite transcript with challenge `true`. -/
def truePath : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstProtocol suffix (firstPath 7 true) ⟨(5 : Nat), ⟨⟩⟩

/-- The composite transcript with challenge `false`. -/
def falsePath : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstProtocol suffix (firstPath 7 false) ⟨(99 : Nat), ⟨⟩⟩

-- KnowledgeComposition row 2, restated with `extractAlong`: the carrier after the message reads
-- the payload.
/-- Prefix extraction on payload `7` passes through `Fin 8`. -/
example : firstState.extractAlong stmt₀ (firstPath 7 true) 6 = 6 := rfl

/-- info: 6 -/
#guard_msgs in
#eval firstState.extractAlong stmt₀ (firstPath 7 true) 6

-- KnowledgeComposition rows 8 and 9, restated with `extractAlong_append`, for every payload,
-- challenge, suffix message and output witness.
/-- Composite extraction is suffix extraction followed by prefix extraction. -/
theorem compositeState_extractAlong (n : Nat) (b : Bool) (m w : Nat) :
    compositeState.extractAlong stmt₀
      (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) (w, ()) =
      w % (n + 1) := by
  rw [compositeState, KnowledgeStateFunction.extractAlong_append]
  exact Nat.mod_mod w (n + 1)

-- KnowledgeComposition row 8.
example : compositeState.extractAlong stmt₀ truePath (6, ()) = 6 :=
  compositeState_extractAlong 7 true 5 6

-- KnowledgeComposition row 9: the false challenge.
example : compositeState.extractAlong stmt₀ falsePath (6, ()) = 6 :=
  compositeState_extractAlong 7 false 99 6

-- KnowledgeComposition row 10.
/-- info: 6 -/
#guard_msgs in
#eval compositeState.extractAlong stmt₀ truePath (6, ())

-- KnowledgeComposition row 11.
/-- info: 6 -/
#guard_msgs in
#eval compositeState.extractAlong stmt₀ falsePath (6, ())

-- KnowledgeComposition row 12, restated with `toFun_terminalWitness_append` and the fixture iff
-- (R1): the terminal state of the composite is the suffix terminal state, and it holds exactly
-- when the composite accepts.
/-- The suffix terminal witness on the true path keeps the extracted value. -/
example : ((secondState (firstPath 7 true)).terminalWitness stmt₀ ⟨(5 : Nat), ⟨⟩⟩
    (6, ())).1.val = 6 := rfl

/-- The composite terminal state holds exactly when the composite accepts. -/
example (n : Nat) (b : Bool) (m : Nat) (w : Nat × Unit) :
    compositeState.toFun
        (completeSpine oracleSig
          (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩))
        (completeMoves oracleSig _) stmt₀
        (compositeState.terminalWitness stmt₀
          (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) w) ↔
      validOutput stmt₀
        (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩) w := by
  rw [compositeState, KnowledgeStateFunction.toFun_terminalWitness_append]
  exact (composed_validAcceptance_iff stmt₀
    (PathAlong.append oracleSig firstProtocol suffix (firstPath n b) ⟨m, ⟨⟩⟩)).symm

/-! ### Security -/

-- KnowledgeComposition fixture `firstCertificate`: the prefix at error one.
/-- The prefix verifier is round-by-round knowledge sound with error one. -/
theorem first_rbrKnowledgeSoundness :
    firstVerifier.rbrKnowledgeSoundness impl (fun _ => True) (fun _ (_ : Nat) => False)
      (fun z (_ : Nat) => z.1 = true) firstDraw (fun _ => 1) :=
  ⟨firstState, fun _ _ a _ _ _ _ => by
    let : MeasurableSpace (Move oracleSig a) := ⊤
    exact evalDist_apply_le_one _ _⟩

-- KnowledgeComposition fixtures `suffixCertificate` and `secondCertificate`: every suffix at
-- error one.
/-- Every suffix state function is locally bounded with error one. -/
theorem second_rbrKnowledgeSoundness (tr₁ : PathAlong oracleSig firstProtocol) :
    rbrKnowledgeSoundness oracleSig (suffix (projectPathAlong oracleSig firstProtocol tr₁))
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
    composed.rbrKnowledgeSoundness impl (fun _ => True) (fun _ (_ : Nat) => False)
      (fun z (_ : Nat × Unit) => z.1 = true)
      (combineDraw oracleSig firstProtocol suffix firstDraw secondDraw)
      (combineDraw (m := fun _ => ℝ≥0∞) oracleSig firstProtocol suffix (fun _ => 1)
        (fun _ _ => 1)) :=
  rbrKnowledgeSoundness_append oracleSig first_rbrKnowledgeSoundness second_rbrKnowledgeSoundness
    (fun _ _ h => h) (fun tr₁ stmt _ _ h => (firstVerifier_validAcceptance_iff stmt tr₁).2 h)

/-- The suffix state function over the suffix statement, a Boolean claim, after the prefix
transcript `tr₁`; its witness carriers read the prefix payload. -/
def suffixState (tr₁ : PathAlong oracleSig firstProtocol) :
    KnowledgeStateFunction oracleSig (suffix (projectPathAlong oracleSig firstProtocol tr₁)) Bool
      (Nat × Unit) Nat (fun _ => True) (fun t _ => t = true) (fun t _ _ => t = true) where
  Witness {_} sp _ := match sp with
    | .root _ => Fin (payload tr₁.1 + 1)
    | .down _ _ => Fin (payload tr₁.1 + 1) × Unit
  toFun _ _ t _ := t = true
  extractRoot _ w := w.val
  extractStep sp _ _ _ w := by
    cases sp with
    | root => exact w.1
    | down _ tail => cases tail
  extractLeaf sp _ _ w := by
    cases sp with
    | down _ tail =>
      cases tail
      exact (⟨w.1 % (payload tr₁.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, ())
  root _ _ _ h := h
  send _ _ _ _ _ _ h := h
  leaf _ _ _ _ h := h

-- KnowledgeComposition fixture `compositeCertificate` (`sequentialClosed`): the suffix statement
-- is the prefix challenge, a function of the prefix transcript.
/-- The appended verifier is knowledge sound from a suffix stated over its own statement. -/
example :
    composed.rbrKnowledgeSoundness impl (fun _ => True) (fun _ (_ : Nat) => False)
      (fun z (_ : Nat × Unit) => z.1 = true)
      (combineDraw oracleSig firstProtocol suffix firstDraw secondDraw)
      (combineDraw (m := fun _ => ℝ≥0∞) oracleSig firstProtocol suffix (fun _ => 1)
        (fun _ _ => 1)) :=
  rbrKnowledgeSoundness_append_of_mid oracleSig (fun _ tr₁ => bit tr₁.2.1)
    first_rbrKnowledgeSoundness
    (fun tr₁ => ⟨suffixState tr₁, fun _ _ a _ _ _ _ => by
      let : MeasurableSpace (Move oracleSig a) := ⊤
      exact evalDist_apply_le_one _ _⟩)
    (fun _ _ _ => trivial) (fun tr₁ stmt _ _ h => (firstVerifier_validAcceptance_iff stmt tr₁).2 h)
    (fun stmt tr₁ tr₂ _ h => (composed_validAcceptance_iff stmt
      (PathAlong.append oracleSig firstProtocol suffix tr₁ tr₂)).1 h)

-- KnowledgeComposition fixture `emptyExtractor`, restated on an `Empty` message.
/-- Empty message carriers and empty witnesses need no fabricated message or witness. -/
def emptyState : KnowledgeStateFunction plainSig
    (.liftBind (.message Empty) fun _ => .pure ⟨⟩ : Protocol.{0}) Unit Empty Empty
    (fun _ => True) (fun _ _ => False) (fun _ _ _ => True) where
  Witness _ _ := Empty
  toFun _ _ _ _ := False
  extractRoot _ w := w
  extractStep sp _ _ x _ := by
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
      ``Interaction.Core.KnowledgeCompositionTests.observed_eq,
      ``Interaction.Core.KnowledgeCompositionTests.compositeState_extractAlong,
      ``Interaction.Core.KnowledgeCompositionTests.composed_rbrKnowledgeSoundness] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
