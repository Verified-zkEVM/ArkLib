/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.RoundByRound
import ArkLibTest.Interaction.Core.Oracle

/-! Nonvacuous model examples and fixed-prefix bounds on a protocol with a challenge. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp MeasureTheory
open scoped ENNReal

universe v

namespace Interaction.Core.SecurityTests

@[instance_reducible] def problem : StatementProblem Bool where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ b _ := b = true
  rel_admissible _ _ _ _ := trivial

instance : ∀ b, MeasurableSpace (problem.Witness () b) := fun _ => ⊤

/-- A Boolean output is both the verdict and the prover's statement, with the unit witness. -/
def judgement : OutputJudgement Bool problem where
  context _ := ()
  verdict b := some b
  proverStatement b := b
  witness _ _ _ := ()

noncomputable def model : AdversaryModel Bool Bool where
  Adv _ := Unit
  outcome b _ := Measure.dirac b
  mass_le_one _ _ := by simp

example : completeness model problem problem judgement (fun _ _ => ()) 0 := by
  constructor
  · exact MeasurableSet.of_discrete
  intro b w h
  change b = true at h
  subst b
  simp [model, OutputJudgement.honest, judgement, problem]

example : soundness model problem problem (fun _ => ()) some 0 := by
  intro b _ h a
  have hb : b ≠ true := by
    intro hb
    exact h ⟨(), hb⟩
  simp [model, Problem.language, problem, hb]

noncomputable def extraction : ExtractionInterface model (problem.Witness ()) where
  Ext := Unit
  experiment _ b _ := Measure.dirac (b, some ())
  cost _ _ _ := 0

example : knowledgeSoundnessWith model problem problem judgement extraction () 0 := by
  intro b _ a
  constructor
  · simp [extraction, model]
  constructor
  · exact le_refl 0
  · simp [extraction, OutputJudgement.valid, judgement, problem]

/-- An extractor that returns no witness fails on the valid accepted input. -/
noncomputable def failedExtraction : ExtractionInterface model (problem.Witness ()) where
  Ext := Unit
  experiment _ b _ := Measure.dirac (b, none)
  cost _ _ _ := 0

example : ¬ knowledgeSoundnessWith model problem problem judgement failedExtraction () 0 := by
  intro h
  have bad := (h true trivial ()).2.2
  simp [failedExtraction, OutputJudgement.valid, judgement, problem] at bad

/-- Deleting the experiment's entire mass cannot satisfy observation preservation. -/
noncomputable def deletedExtraction : ExtractionInterface model (problem.Witness ()) where
  Ext := Unit
  experiment _ _ _ := 0
  cost _ _ _ := 0

example : ¬ knowledgeSoundnessWith model problem problem judgement deletedExtraction () 0 := by
  intro h
  have bad := congrArg (fun μ : Measure Bool => μ Set.univ) (h true trivial ()).1
  simp [deletedExtraction, model] at bad

abbrev zero : Protocol := .pure ⟨⟩
abbrev service : OracleSpec Nat := Nat →ₒ Nat

def loggedProver : Prover plainSig service zero (fun _ => Nat) := do
  let _ ← liftM (service.query 5)
  pure 7

/-- A verifier that queries the service at `6` and accepts the answer. -/
def loggedVerifier : Verifier service zero Unit (fun _ => Nat) where
  decide _ _ _ := do
    let n ← liftM (service.query 6)
    pure n

def loggedExtractor : Extractor.Straightline service zero (fun _ : Unit => Nat) (fun _ => Nat) :=
  fun _ _ out proverLog verifierLog => do
    let n ← liftM (service.query 9)
    pure (out + proverLog.length + verifierLog.length + n)

def logHandler : QueryImpl (service + challengeSpec plainSig zero) (StateM (List Nat))
  | .inl n => do
    modify (· ++ [n])
    pure n
  | .inr c => c.val.elim

run_cmd do
  let ((obs, extracted), trace) := (simulateQ logHandler
    (extractionGame loggedVerifier (fun _ n => n) loggedExtractor () loggedProver)).run []
  unless trace == [5, 6, 9] do throwError "logged extraction reordered stateful effects"
  unless obs.2.2 == some 6 && extracted == some 18 do
    throwError "logged extraction lost the output witness or participant logs"

/-- A terminal state changed by the prover must still be covered by the leaf obligation. -/
def readState : Verifier service zero Unit (fun _ => Bool) where
  decide _ _ _ := do
    let n ← liftM (service.query 0)
    pure (n == 1)

def stateImpl : QueryImpl service (StateT Nat ProbComp) := fun _ => get

example : readState.validAcceptance stateImpl () ⟨⟩ (· = true) := by
  refine ⟨1, ?_⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change 0 < 𝒟[(pure (some true) : ProbComp (Option Bool))] {v | ∃ t, v = some t ∧ t = true}
  simp

open Interaction.Core.OracleTests

def oracleProver : Prover oracleSig OracleSpec.emptySpec tree (fun _ => Nat) :=
  pure ⟨fun n => n + 5, pure 7⟩

def oracleExtractor : Extractor.OracleStraightline OracleSpec.emptySpec tree
    (fun _ : Unit × (∀ i, emptyFamily.Realization i) => Nat) (fun _ => Nat) :=
  fun _ _ out proveLog verifyLog => pure (out + proveLog.length + verifyLog.length)

def oracleHandler : QueryImpl (OracleSpec.emptySpec + challengeSpec oracleSig tree) Id
  | .inl i => i.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, i⟩, _⟩ => i.elim

run_cmd do
  let (obs, extracted) := simulateQ oracleHandler
    (queryDecision.extractionGame (fun _ n => n) oracleExtractor
      ((), fun i => i.elim) oracleProver)
  unless extracted == some 7 do throwError "oracle resource queries polluted ambient logs"
  match obs.2.2 with
  | none => throwError "logged oracle decision rejected"
  | some (n, data) =>
    unless n == 8 && data ⟨⟩ 3 == 8 do
      throwError "logged oracle decision disagrees with the materialized input"

-- The decision log records the message query before routing; its ambient part stays empty.
run_cmd do
  let z := simulateQ oracleHandler
    (queryDecision.runWithLog () (fun i => i.elim) oracleProver)
  unless z.2.2.length == 1 && z.2.2.fst.isEmpty do
    throwError "the decision log lost the message query or mixed it into the ambient log"

abbrev coin : Protocol := .liftBind (.challenge Bool) (fun _ => .pure ⟨⟩)

def draw : QueryImpl (challengeSpec plainSig coin) ProbComp
  | ⟨.inl _, _⟩ => (show ProbComp Bool from $ᵗ Bool)
  | ⟨.inr ⟨_, i⟩, _⟩ => i.elim

def state : StateFunction plainSig coin Bool (fun _ => True) (· = true)
    (fun stmt _ => stmt = true) where
  toFun _ _ stmt := stmt = true
  root _ _ h := h
  send _ _ _ _ h _ := h
  leaf _ _ _ h := h

example : rbrSoundness plainSig coin (fun _ => True) (· = true)
    (fun stmt _ => stmt = true) draw (fun _ => 0) := by
  refine ⟨state, ?_⟩
  intro stmt _ _ a next sp h history
  simp [state]

/-- Knowledge of a true Boolean statement is preserved at every prefix. -/
def knowledgeState : KnowledgeStateFunction plainSig coin Bool (fun _ _ => Unit) (fun _ => Unit)
    (fun _ => True)
    (fun stmt _ => stmt = true) (fun stmt _ _ => stmt = true) where
  Witness _ {_} _ _ := Unit
  toFun stmt {_} _ _ _ := stmt = true
  extractRoot _ _ := ()
  extractStep _ {_ _} _ _ _ _ := ()
  extractLeaf _ _ _ _ := ()
  root _ _ _ h := h
  send _ _ _ _ _ _ h := h
  leaf _ _ _ _ h := h

example : rbrKnowledgeSoundness.{0, 0, 0} plainSig coin (fun _ => True)
    (fun stmt (_ : Unit) => stmt = true) (fun stmt _ (_ : Unit) => stmt = true)
    draw (fun _ => 0) := by
  refine ⟨knowledgeState, ?_⟩
  intro stmt _ a next sp h history
  simp [knowledgeState]

/-- The same bound holds with the intermediate witnesses lifted to any universe `v`. -/
example : rbrKnowledgeSoundness.{0, 0, v} plainSig coin (fun _ => True)
    (fun stmt (_ : Unit) => stmt = true) (fun stmt _ (_ : Unit) => stmt = true)
    draw (fun _ => 0) := by
  apply rbrKnowledgeSoundness.lift.{0, 0, 0, 0, v}
  refine ⟨knowledgeState, ?_⟩
  intro stmt _ a next sp h history
  simp [knowledgeState]

/-- On zero rounds the promise `b = true` makes extraction immediate, while every input accepts. -/
def promisedState : KnowledgeStateFunction plainSig zero Bool (fun _ _ => Unit) (fun _ => Unit) (· =
    true)
    (fun b _ => b = true) (fun _ _ _ => True) where
  Witness _ {_} _ _ := Unit
  toFun _ {_} _ _ _ := True
  extractRoot _ _ := ()
  extractStep _ {_ _} _ _ _ _ := ()
  extractLeaf _ _ _ _ := ()
  root _ h _ _ := h
  send sp _ _ _ := nomatch sp
  leaf _ _ _ _ _ := trivial

/-- The promise excludes `false`, so its accepted runs need no witness. -/
example (err : ChallengeNode plainSig zero → ℝ≥0∞) :
    rbrKnowledgeSoundness.{0, 0, 0} plainSig zero (· = true) (fun b (_ : Unit) => b = true)
      (fun (_ : Bool) _ (_ : Unit) => True) (fun c => c.val.elim) err :=
  ⟨promisedState, fun _ _ _ _ sp => nomatch sp⟩

/-! ### A classical one-challenge protocol

The verifier reads a shared counter and accepts a true statement or a true challenge. The prover
reads the counter before and after the challenge, so the verifier's reading records both.
-/

abbrev counter : OracleSpec Unit := Unit →ₒ Nat

/-- A shared counter: each query returns the current value and increments it. -/
def tick : QueryImpl counter (StateT Nat ProbComp) := fun _ => do
  let n ← get
  set (n + 1)
  pure n

/-- Reads the counter, then accepts a true statement or a true challenge with that reading. -/
def coinVerifier : Verifier counter coin Bool (fun _ => Nat) where
  decide stmt _ v := OptionT.mk do
    let n ← liftM (counter.query ())
    pure (if (stmt || v.val.1) = true then some n else none)

theorem decide_run' (stmt : Bool) (p) (v) (st : Nat) :
    (simulateQ tick (coinVerifier.decide stmt p v).run).run' st =
      pure (if (stmt || v.val.1) = true then some st else none) := by
  rfl

@[instance_reducible] def boolProblem : StatementProblem Bool where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ b _ := b = true
  rel_admissible _ _ _ _ := trivial

@[instance_reducible] def anyOutput : PathProblem coin (fun _ => Nat) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ _ _ := True
  rel_admissible _ _ _ _ := trivial

theorem validAcceptance_iff {langOut : Nat → Prop} (hl : ∀ t, langOut t) (stmt : Bool)
    (tr : PathAlong plainSig coin) :
    coinVerifier.validAcceptance tick stmt tr langOut ↔
      (stmt || (tr.1 : Bool)) = true := by
  rcases tr with ⟨x, ⟨⟩⟩
  have key : ∀ st, (simulateQ tick (coinVerifier.decide stmt _
      (toPlainView coin ⟨x, ⟨⟩⟩)).run).run' st =
        pure (if (stmt || (x : Bool)) = true then some st else none) :=
    fun st => decide_run' stmt _ _ st
  simp only [Verifier.validAcceptance, key, evalDist_pure]
  cases stmt <;> cases x <;> simp [hl]

/-- The state is true at the root of a true statement and at a leaf with a true challenge. -/
def coinState : StateFunction plainSig coin Bool (boolProblem.admissible ())
    (boolProblem.language ()) (fun stmt tr => coinVerifier.validAcceptance tick stmt tr
      (anyOutput.language (projectPathAlong plainSig coin tr))) where
  toFun {_} sp history stmt := match sp, history with
    | .root _, _ => stmt = true
    | .down _ _, history => (stmt || (history.1.1 : Bool)) = true
  root _ _ h := ⟨(), h⟩
  send sp _ _ h := by
    cases sp with
    | root => exact nomatch h
    | down _ tail => cases tail
  leaf sp history stmt h := by
    cases sp with
    | down _ tail =>
      cases tail
      rcases history with ⟨⟨x, _⟩, ⟨⟩⟩
      rw [validAcceptance_iff (fun _ => ⟨(), trivial⟩)]
      exact h

/-- The only challenge node of the protocol. -/
def onlyChallenge : ChallengeNode plainSig coin := ⟨.inl ⟨⟩, rfl⟩

theorem sampleAt_root (h) : sampleAt plainSig draw (.root coin) h = ($ᵗ Bool : ProbComp Bool) :=
  LawfulFunctor.id_map _

theorem uniform_singleton (b : Bool) : 𝒟[($ᵗ Bool : ProbComp Bool)] {b} = 1 / 2 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

theorem uniform_true : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 1 / 2 := uniform_singleton true

/-- A false statement becomes true exactly when the challenge is true. -/
theorem coin_rbrSoundness :
    coinVerifier.rbrSoundness tick boolProblem anyOutput draw (fun _ => 1 / 2) := by
  refine ⟨coinState, ?_⟩
  intro stmt _ _ a next sp h history
  cases sp with
  | down _ tail => cases tail
  | root =>
    rw [sampleAt_root, ← uniform_true]
    refine measure_mono fun x hx => ?_
    obtain ⟨hstmt, hx⟩ := hx
    change ¬ stmt = true at hstmt
    change (stmt || (x : Bool)) = true at hx
    cases stmt
    · simpa using hx
    · exact absurd rfl hstmt

/-- No state function achieves an error below one half. -/
theorem coin_not_rbrSoundness (ε : ChallengeNode plainSig coin → ℝ≥0∞)
    (hε : ε onlyChallenge < 1 / 2) :
    ¬ coinVerifier.rbrSoundness tick boolProblem anyOutput draw ε := by
  rintro ⟨F, hF⟩
  have hroot : ¬ F.toFun (.root coin) ⟨⟩ false := fun h => by
    obtain ⟨_, h⟩ := F.root false trivial h
    exact Bool.false_ne_true h
  have hleaf : F.toFun (.down ⟨⟩ (.root _)) ⟨⟨true, rfl⟩, ⟨⟩⟩ false := by
    by_contra hc
    exact F.leaf _ _ false hc ((validAcceptance_iff (fun _ => ⟨(), trivial⟩) _ _).2 rfl)
  have bound := hF false trivial (fun ⟨_, h⟩ => Bool.false_ne_true h) _ _ (.root coin) rfl ⟨⟩
  erw [sampleAt_root] at bound
  refine absurd (lt_of_le_of_lt ?_ hε) (lt_irrefl _)
  refine le_trans ?_ bound
  rw [← uniform_true]
  refine measure_mono fun x hx => ?_
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨hroot, hleaf⟩

/-- The knowledge state tracks the soundness state; its leaf witness records the challenge read
from the transcript. -/
def coinKnowledge : KnowledgeStateFunction plainSig coin Bool (fun _ _ => Unit) (fun _ => Unit) (fun
    _ => True)
    (fun b _ => b = true) (fun stmt tr (_ : Unit) =>
      coinVerifier.validAcceptance tick stmt tr (fun _ => True)) where
  Witness _ {_} sp history := match sp, history with
    | .root _, _ => Unit
    | .down _ _, history => {b : Bool // b = history.1.1}
  toFun stmt {_} sp history _ := match sp, history with
    | .root _, _ => stmt = true
    | .down _ _, history => (stmt || (history.1.1 : Bool)) = true
  extractRoot _ _ := ()
  extractStep _ {_ _} sp _ _ _ := by
    cases sp with
    | root => exact ()
    | down _ tail => cases tail
  extractLeaf _ sp history _ := by
    cases sp with
    | down _ tail =>
      cases tail
      exact ⟨history.1.1, rfl⟩
  root _ _ _ h := h
  send sp _ _ h := by
    cases sp with
    | root => exact nomatch h
    | down _ tail => cases tail
  leaf sp history stmt _ h := by
    cases sp with
    | down _ tail =>
      cases tail
      rcases history with ⟨⟨x, _⟩, ⟨⟩⟩
      exact (validAcceptance_iff (fun _ => trivial) _ _).1 h

/-- Backwards extraction fails exactly when a false statement meets a true challenge. -/
theorem coin_rbrKnowledgeSoundness :
    Verifier.rbrKnowledgeSoundness.{0, 0, 0} coinVerifier tick (fun _ => True)
      (fun b (_ : Unit) => b = true)
      (fun _ _ (_ : Nat) (_ : Unit) => True) draw (fun _ => 1 / 2) := by
  refine ⟨coinKnowledge, ?_⟩
  intro stmt _ a next sp h history
  cases sp with
  | down _ tail => cases tail
  | root =>
    rw [sampleAt_root, ← uniform_true]
    refine measure_mono fun x hx => ?_
    obtain ⟨_, hstmt, hx⟩ := hx
    change ¬ stmt = true at hstmt
    change (stmt || (x : Bool)) = true at hx
    cases stmt
    · simpa using hx
    · exact absurd rfl hstmt

/-- No knowledge state function achieves an error below one half. -/
theorem coin_not_rbrKnowledgeSoundness (ε : ChallengeNode plainSig coin → ℝ≥0∞)
    (hε : ε onlyChallenge < 1 / 2) :
    ¬ Verifier.rbrKnowledgeSoundness.{0, 0, 0} coinVerifier tick (fun _ => True)
      (fun b (_ : Unit) => b = true)
      (fun _ _ (_ : Nat) (_ : Unit) => True) draw ε := by
  rintro ⟨F, hF⟩
  have hroot : ∀ w, ¬ F.toFun false (.root coin) ⟨⟩ w := fun w h =>
    Bool.false_ne_true (F.root false trivial w h)
  have hleaf := F.leaf (.down ⟨⟩ (.root _)) ⟨⟨true, rfl⟩, ⟨⟩⟩ false ()
    ((validAcceptance_iff (fun _ => trivial) _ _).2 rfl)
  have bound := hF false trivial _ _ (.root coin) rfl ⟨⟩
  erw [sampleAt_root] at bound
  refine absurd (lt_of_le_of_lt ?_ hε) (lt_irrefl _)
  refine le_trans ?_ bound
  rw [← uniform_true]
  refine measure_mono fun x hx => ?_
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨_, hroot _, hleaf⟩

/-! ### A transcript-dependent output witness

The prover sends `payload : Nat` and the verifier accepts when it equals the statement. The
output witness is an index `Fin (payload + 1)`, whose type depends on the message. The leaf
extractor keeps that carrier as the intermediate witness; its bound together with the acceptance
equality gives `w ≤ stmt`. Unrestricted `Nat` cannot support the same identity/value extraction
contract.
-/

/-- One prover message carrying a natural number. -/
abbrev payloadMsg : Protocol := .liftBind (.message Nat) (fun _ => .pure ⟨⟩)

/-- The payload of a completed transcript. -/
def payloadOf (tr : PathAlong plainSig payloadMsg) : Nat := tr.1

/-- The output witness carrier: an index bounded by the payload. -/
abbrev BoundedIndex (tr : PathAlong plainSig payloadMsg) : Type := Fin (payloadOf tr + 1)

/-- Accepts when the payload equals the statement, and outputs the payload. -/
def payloadVerifier : Verifier counter payloadMsg Nat (fun _ => Nat) where
  decide stmt _ v := OptionT.mk
    (pure (if payloadOf v.val = stmt then some (payloadOf v.val) else none))

theorem payload_validAcceptance_iff {langOut : Nat → Prop} (stmt : Nat)
    (tr : PathAlong plainSig payloadMsg) :
    payloadVerifier.validAcceptance tick stmt tr langOut ↔ payloadOf tr = stmt ∧ langOut stmt := by
  rcases tr with ⟨x, ⟨⟩⟩
  have key : ∀ st, (simulateQ tick (payloadVerifier.decide stmt _
      (toPlainView payloadMsg ⟨x, ⟨⟩⟩)).run).run' st =
        pure (if payloadOf ⟨x, ⟨⟩⟩ = stmt then some (payloadOf ⟨x, ⟨⟩⟩) else none) :=
    fun _ => rfl
  simp only [Verifier.validAcceptance, key, evalDist_pure]
  by_cases hx : payloadOf ⟨x, ⟨⟩⟩ = stmt <;> by_cases hl : langOut stmt <;> simp [hx, hl]

/-- The root witness is the input witness; at the leaf it is the output witness `Fin (payload + 1)`
itself, so leaf extraction is the identity. -/
def payloadKnowledge : KnowledgeStateFunction plainSig payloadMsg Nat (fun _ => BoundedIndex) (fun _
    => Nat)
    (fun _ => True) (fun stmt w => w ≤ stmt) (fun stmt tr (_ : BoundedIndex tr) =>
      payloadVerifier.validAcceptance tick stmt tr (fun _ => True)) where
  Witness _ {_} sp history := match sp, history with
    | .root _, _ => Nat
    | .down _ _, history => Fin ((show Nat from history.1.1) + 1)
  toFun stmt {_} sp history w := match sp, history, w with
    | .root _, _, w => w ≤ stmt
    | .down _ _, history, _ => (show Nat from history.1.1) = stmt
  extractRoot _ w := w
  extractStep _ {_ _} sp _ _ w := by
    cases sp with
    | root => exact Fin.val w
    | down _ tail => cases tail
  extractLeaf _ sp history w := by
    cases sp with
    | down _ tail =>
      cases tail
      exact w
  root _ _ _ h := h
  send sp _ _ _ x w h := by
    cases sp with
    | root =>
      change (show Nat from x) = _ at h
      subst h
      exact Nat.le_of_lt_succ w.isLt
    | down _ tail => cases tail
  leaf sp history stmt _ h := by
    cases sp with
    | down _ tail =>
      cases tail
      rcases history with ⟨⟨x, _⟩, ⟨⟩⟩
      exact ((payload_validAcceptance_iff _ _).1 h).1

/-- The move sending payload `n`. -/
def sendPayload (n : Nat) : TwoParty.Lens.Move plainSig (.message Nat) := n

/-- The complete cursor of the run sending payload `n`. -/
def payloadLeaf (n : Nat) : Cursor.Spine payloadMsg (.pure ⟨⟩) := .down (sendPayload n) (.root _)

/-- The full prefix of the run sending payload `n`. -/
def payloadHistory (n : Nat) : PrefixMoves plainSig (payloadLeaf n) := ⟨⟨sendPayload n, rfl⟩, ⟨⟩⟩

/-- Backwards extraction from the output witness `5 : Fin 8` at payload `7` returns `5`. -/
example : payloadKnowledge.extractRoot 7
    (payloadKnowledge.extractStep 7 (.root payloadMsg) ⟨⟩ (sendPayload 7)
      (payloadKnowledge.extractLeaf 7 (payloadLeaf 7) (payloadHistory 7) (5 : Fin 8))) = 5 :=
  rfl

/-- The leaf extractor passes the dependent output witness through unchanged. -/
example (w : Fin 8) :
    (payloadKnowledge.extractLeaf 7 (payloadLeaf 7) (payloadHistory 7) w : Fin 8) = w :=
  rfl

/-- The payload protocol has no challenge, so its knowledge state function has error zero under
every challenge implementation. -/
theorem payload_rbrKnowledgeSoundness
    (draw : QueryImpl (challengeSpec plainSig payloadMsg) ProbComp) :
    Verifier.rbrKnowledgeSoundness.{0, 0, 0} payloadVerifier tick (fun _ => True)
      (fun stmt (w : Nat) => w ≤ stmt)
      (fun _ tr (_ : Nat) (_ : BoundedIndex tr) => True) draw (fun _ => 0) := by
  refine ⟨payloadKnowledge, ?_⟩
  intro _ _ a next sp h _
  cases sp with
  | root => exact nomatch h
  | down _ tail => cases tail

/-- For every payload `n` and output witness `w : Fin (n + 1)`, backwards extraction returns
`w.val`. -/
theorem payloadKnowledge_extract (n : Nat) (w : Fin (n + 1)) :
    payloadKnowledge.extractRoot n
      (payloadKnowledge.extractStep n (.root payloadMsg) ⟨⟩ (sendPayload n)
        (payloadKnowledge.extractLeaf n (payloadLeaf n) (payloadHistory n) w)) = w.val :=
  rfl

/-! ### A transcript-dependent output witness in straight-line extraction

The prover sends `n` and outputs an index `w : Fin (n + 1)`. The game reads that output with the
identity `readOut` into the carrier `BoundedIndex`, and the extractor receives it at its own
transcript.
-/

/-- Sends `n` and outputs the index `w`, whose type depends on the message. -/
def payloadProver (n : Nat) (w : Fin (n + 1)) : Prover plainSig counter payloadMsg BoundedIndex :=
  pure ⟨sendPayload n, pure w⟩

/-- Returns the value of the transcript-indexed output witness. -/
def payloadExtractor :
    Extractor.Straightline counter payloadMsg (fun _ : Nat => Nat) BoundedIndex :=
  fun _ _ w _ _ => pure w.val

/-- Answers every ambient query with zero; the payload protocol has no challenge. -/
def payloadHandler : QueryImpl (counter + challengeSpec plainSig payloadMsg) Id
  | .inl _ => (0 : Nat)
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, i⟩, _⟩ => i.elim

/-- On the accepting run with payload `7`, the extractor receives every prover output
`w : Fin 8` itself and returns its value. -/
theorem payload_extractionGame (w : Fin 8) :
    simulateQ payloadHandler (extractionGame payloadVerifier (fun _ w => w) payloadExtractor 7
      (payloadProver 7 w)) = ((⟨⟨sendPayload 7, ⟨⟩⟩, w, some 7⟩, some w.val) :
        Observation plainSig payloadMsg BoundedIndex (fun _ => Nat) × Option Nat) :=
  rfl

run_cmd do
  let (obs, extracted) := simulateQ payloadHandler
    (extractionGame payloadVerifier (fun _ w => w) payloadExtractor 7 (payloadProver 7 5))
  unless obs.2.2 == some 7 && extracted == some 5 do
    throwError "the accepting payload run lost the dependent output witness"

/-- Reads the counter before the challenge and again after it, and outputs the second reading. -/
def countingProver : Prover plainSig counter coin (fun _ => Nat) := do
  let _ ← liftM (counter.query ())
  pure fun _ => liftM (counter.query ())

/-- The observation of a run with challenge `b`. -/
def coinObs (stmt b : Bool) : Observation plainSig coin (fun _ => Nat) (fun _ => Nat) :=
  ⟨⟨b, ⟨⟩⟩, 1, if (stmt || b) = true then some 2 else none⟩

theorem experiment_counting (stmt : Bool) :
    experiment (pure 0) tick draw (coinVerifier.run stmt countingProver) =
      (($ᵗ Bool : ProbComp Bool) >>= fun b => pure (coinObs stmt b)) := by
  rfl

/-- Every set of observations of the coin protocol is measurable. -/
instance : MeasurableSpace (Observation plainSig coin (fun _ => Nat) (fun _ => Nat)) := ⊤

/-- The observations of the coin protocol form a discrete measurable space. -/
instance : DiscreteMeasurableSpace (Observation plainSig coin (fun _ => Nat) (fun _ => Nat)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable (PathAlong plainSig coin) :=
  Function.Injective.countable (β := Bool) (f := fun tr => tr.1) fun
    | ⟨_, ⟨⟩⟩, ⟨_, ⟨⟩⟩, rfl => rfl

/-- The classical model of the coin verifier, with fresh challenges and a shared counter. -/
noncomputable abbrev coinModel :=
  coinVerifier.classicalModel (Out := fun _ => Nat) (pure 0) tick draw

/-- The outcome of the counting prover is the uniform challenge bit mapped through `coinObs`. -/
theorem outcome_counting (stmt : Bool)
    (S : Set (Observation plainSig coin (fun _ => Nat) (fun _ => Nat))) :
    coinModel.outcome stmt countingProver S =
      𝒟[($ᵗ Bool : ProbComp Bool)] (coinObs stmt ⁻¹' S) := by
  change 𝒟[experiment (pure 0) tick draw (coinVerifier.run stmt countingProver)] S = _
  rw [experiment_counting, LawfulMonad.bind_pure_comp, evalDist_map _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]

/-- On a false statement, half of the mass is a returned rejection. -/
example : coinModel.outcome false countingProver
    {obs | obs.2.2 = none} = 1 / 2 := by
  rw [outcome_counting, ← uniform_singleton false]
  congr 1
  ext b
  cases b
  · exact iff_of_true rfl rfl
  · exact iff_of_false (fun h => Option.some_ne_none _ h) Bool.noConfusion

/-- The other half accepts, after the prover's two readings and the verifier's third. -/
example : coinModel.outcome false countingProver
    {obs | obs.2.2 = some 2} = 1 / 2 := by
  rw [outcome_counting, ← uniform_true]
  congr 1
  ext b
  cases b
  · refine iff_of_false (fun h => ?_) Bool.noConfusion
    change (none : Option Nat) = some 2 at h
    cases h
  · exact iff_of_true rfl rfl

/-- No mass is missing: rejection is an observation of the run. -/
example : coinModel.outcome false countingProver
    Set.univ = 1 := by
  rw [outcome_counting, Set.preimage_univ]
  simp

/-- A true statement or a true challenge bit witnesses the input. -/
@[instance_reducible] def coinInput : StatementProblem Bool where
  Witness _ _ := Bool × Nat
  admissible _ _ := True
  rel _ b w := (b || w.1) = true
  rel_admissible _ _ _ _ := trivial

instance : ∀ b, MeasurableSpace (coinInput.Witness () b) := fun _ => ⊤

instance : ∀ b, DiscreteMeasurableSpace (coinInput.Witness () b) :=
  fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : ∀ b, Countable (coinInput.Witness () b) := fun _ =>
  inferInstanceAs (Countable (Bool × Nat))

/-- Judge a coin observation against `anyOutput`: the prover's output is its claimed statement,
and every accepted claim has the unit witness. -/
def coinJudgement :
    OutputJudgement (Observation plainSig coin (fun _ => Nat) (fun _ => Nat)) anyOutput :=
  .ofObservation anyOutput (fun _ n => n) (fun _ _ _ => ())

/-- Reads the challenge from the transcript and the sizes of both participant logs. -/
def coinLoggedExtractor :
    Extractor.Straightline counter coin (coinInput.Witness ()) (fun _ => Nat) :=
  fun _ tr _ proveLog verifyLog => pure (tr.1, proveLog.length + verifyLog.length)

/-- Reads the challenge and the prover output from the transcript alone. -/
def coinTranscriptExtractor :
    Extractor.TranscriptOnly counter coin (coinInput.Witness ()) (fun _ => Nat) :=
  fun _ tr out => pure (tr.1, out)

theorem accepted_of_mem_support (stmt : Bool)
    (adv : Prover plainSig counter coin (fun _ => Nat))
    {obs : Observation plainSig coin (fun _ => Nat) (fun _ => Nat)}
    (h : obs ∈ support (coinVerifier.run stmt adv))
    {t : Nat} (ht : obs.2.2 = some t) : (stmt || (obs.1.1 : Bool)) = true := by
  have hv := Verifier.verdict_mem_support_run coinVerifier stmt adv h
  rw [ht] at hv
  change some t ∈ support ((liftM (counter.query ()) : OracleComp counter Nat) >>= fun n =>
    pure (if (stmt || (obs.1.1 : Bool)) = true then some n else none)) at hv
  by_contra hc
  simp [hc] at hv

/-- An extractor that returns the transcript's challenge bit never misses a witness. -/
theorem bad_eq_zero (E : Extractor.Straightline counter coin (coinInput.Witness ()) (fun _ => Nat))
    (hE : ∀ stmt tr out proveLog verifyLog, ∀ w ∈ support (E stmt tr out proveLog verifyLog).run,
      ∃ n, w = some ((tr.1 : Bool), n))
    (stmt : Bool) (adv : Prover plainSig counter coin (fun _ => Nat)) :
    (classicalStraightline (coinInput.Witness ()) coinVerifier (pure 0) tick draw
      (fun _ n => n)).experiment E stmt adv
      {z | coinJudgement.valid z.1 ∧ ∀ wit ∈ z.2, ¬ coinInput.rel () stmt wit} = 0 := by
  refine evalDist.apply_eq_zero_of_disjoint_support _ (Set.to_countable _).measurableSet ?_
  rintro z hz ⟨⟨t, ht, -⟩, hbad⟩
  change z.1.2.2 = some t at ht
  simp only [experiment, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, rfl, hz⟩ := hz
  obtain ⟨hrun, -, hext⟩ := mem_support_extractionGame coinVerifier (fun _ n => n) E stmt adv
    (support_simulateQ_run'_subset _ _ _ hz)
  have hacc := accepted_of_mem_support stmt adv hrun ht
  obtain ⟨proveLog, verifyLog, hw⟩ := hext (by rw [ht]; exact Option.some_ne_none t)
  obtain ⟨n, hn⟩ := hE _ _ _ _ _ _ hw
  exact hbad _ hn hacc

/-- The logged extractor certifies classical knowledge soundness with zero error. -/
example : knowledgeSoundnessWith coinModel coinInput anyOutput coinJudgement
    (classicalStraightline (coinInput.Witness ()) coinVerifier (pure 0) tick draw
      (fun _ n => n)) coinLoggedExtractor 0 := fun stmt _ adv =>
  ⟨classicalStraightline_marginal _ _ _ _ _ _ _ _ _, le_refl _,
    (bad_eq_zero coinLoggedExtractor (fun _ _ _ _ _ _ hw => ⟨_, hw⟩) stmt adv).le⟩

/-- The transcript-only extractor certifies the same bound without either log. -/
example : knowledgeSoundnessWith coinModel coinInput anyOutput coinJudgement
    (classicalTranscriptOnly (coinInput.Witness ()) coinVerifier (pure 0) tick draw
      (fun _ n => n)) coinTranscriptExtractor 0 := fun stmt _ adv =>
  ⟨classicalTranscriptOnly_marginal _ _ _ _ _ _ _ _ _, le_refl _,
    (bad_eq_zero coinTranscriptExtractor.withLogs (fun _ _ _ _ _ _ hw => ⟨_, hw⟩) stmt adv).le⟩

/-- Records ambient queries and challenges in order, answering every challenge with `b`. -/
def traceHandler (b : Bool) :
    QueryImpl (counter + challengeSpec plainSig coin) (StateM (List String × Nat))
  | .inl _ => do
    let (trace, n) ← get
    set (trace ++ ["ambient"], n + 1)
    pure n
  | .inr ⟨.inl _, _⟩ => (show StateM _ Bool from do
    modify fun (trace, n) => (trace ++ ["challenge"], n)
    pure b)
  | .inr ⟨.inr ⟨_, i⟩, _⟩ => i.elim

run_cmd do
  let ((obs, extracted), trace, _) := (simulateQ (traceHandler true)
    (extractionGame coinVerifier (fun _ n => n) coinLoggedExtractor false countingProver)).run
      ([], 0)
  unless trace == ["ambient", "challenge", "ambient", "ambient"] do
    throwError "the challenge was not drawn between the prover's two ambient queries"
  unless obs.2.1 == 1 && obs.2.2 == some 2 &&
      extracted.map (fun (w : Bool × Nat) => w) == some (true, 3) do
    throwError "the accepting branch lost the shared state or a participant log"
  let ((obs, extracted), _) := (simulateQ (traceHandler false)
    (extractionGame coinVerifier (fun _ n => n) coinLoggedExtractor false countingProver)).run
      ([], 0)
  unless obs.2.2 == none && extracted.isNone do
    throwError "the rejecting branch accepted or extracted"

end Interaction.Core.SecurityTests

run_cmd do
  for decl in [``Interaction.Core.completeness, ``Interaction.Core.soundness,
      ``Interaction.Core.knowledgeSoundnessWith, ``Interaction.Core.classicalStraightline,
      ``Interaction.Core.classicalTranscriptOnly, ``Interaction.Core.Verifier.runWithLog_fst,
      ``Interaction.Core.OracleVerifier.classicalStraightline, ``Interaction.Core.rbrSoundness,
      ``Interaction.Core.rbrKnowledgeSoundness, ``Interaction.Core.Verifier.verdict_mem_support_run,
      ``Interaction.Core.mem_support_extractionGame,
      ``Interaction.Core.map_run_withLogging_addLift_fst,
      ``Interaction.Core.OracleVerifier.runWithLog_fst,
      ``Interaction.Core.classicalStraightline_marginal,
      ``Interaction.Core.classicalTranscriptOnly_marginal,
      ``Interaction.Core.SecurityTests.coin_rbrSoundness,
      ``Interaction.Core.SecurityTests.coin_not_rbrSoundness,
      ``Interaction.Core.SecurityTests.coin_rbrKnowledgeSoundness,
      ``Interaction.Core.SecurityTests.coin_not_rbrKnowledgeSoundness,
      ``Interaction.Core.SecurityTests.payload_rbrKnowledgeSoundness,
      ``Interaction.Core.SecurityTests.payloadKnowledge_extract,
      ``Interaction.Core.SecurityTests.payload_extractionGame,
      ``Interaction.Core.SecurityTests.bad_eq_zero] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
