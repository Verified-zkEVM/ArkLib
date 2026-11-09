import ArkLib.Interaction.Core.Security.RoundByRound
import ArkLibTest.Interaction.Core.Oracle

/-! Nonvacuous model examples and fixed-prefix bounds on a protocol with a challenge. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp MeasureTheory
open scoped ENNReal

namespace Interaction.Core.SecurityTests

@[instance_reducible] def problem : StatementProblem Bool where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ b _ := b = true
  rel_admissible _ _ _ _ := trivial

instance : ∀ b, MeasurableSpace (problem.Witness () b) := fun _ => ⊤

def judgement : OutputJudgement Bool Bool problem where
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

example : soundness model problem problem some 0 := by
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

def loggedVerifier : Verifier service zero Unit Nat where
  decide _ _ _ := do
    let n ← liftM (service.query 6)
    pure n

def loggedExtractor : Extractor.Straightline service zero (fun _ : Unit => Nat) Nat :=
  fun _ out _ proverLog verifierLog => do
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
def readState : Verifier service zero Unit Bool where
  decide _ _ _ := do
    let n ← liftM (service.query 0)
    pure (n == 1)

def stateImpl : QueryImpl service (StateT Nat ProbComp) := fun _ => get

example : readState.validAcceptance stateImpl (· = true) () ⟨⟩ := by
  refine ⟨1, ?_⟩
  let : MeasurableSpace (Option Bool) := ⊤
  change 0 < 𝒟[(pure (some true) : ProbComp (Option Bool))] {v | ∃ t, v = some t ∧ t = true}
  simp

open Interaction.Core.OracleTests

def oracleProver : Prover oracleSig OracleSpec.emptySpec tree (fun _ => Nat) :=
  pure ⟨fun n => n + 5, pure 7⟩

def oracleExtractor : Extractor.OracleStraightline OracleSpec.emptySpec tree
    (fun _ : Unit × (∀ i, emptyFamily.{0, 0, 0}.Realization i) => Nat) Nat :=
  fun _ out _ proveLog verifyLog => pure (out + proveLog.length + verifyLog.length)

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

def knowledgeState : KnowledgeStateFunction plainSig coin Bool Unit Unit
    (fun stmt _ => stmt = true) (fun stmt _ _ => stmt = true) where
  Witness _ := Unit
  toFun _ _ stmt _ := stmt = true
  extractRoot _ _ := ()
  extractStep _ _ _ _ _ := ()
  extractLeaf _ _ _ _ := ()
  root _ _ h := h
  send _ _ _ _ _ _ h := h
  leaf _ _ _ _ h := h

example : rbrKnowledgeSoundness plainSig coin (fun _ => True)
    (fun stmt (_ : Unit) => stmt = true) (fun stmt _ (_ : Unit) => stmt = true)
    draw (fun _ => 0) := by
  refine ⟨knowledgeState, ?_⟩
  intro stmt _ a next sp h history
  simp [knowledgeState]

end Interaction.Core.SecurityTests

run_cmd do
  for decl in [``Interaction.Core.completeness, ``Interaction.Core.soundness,
      ``Interaction.Core.knowledgeSoundnessWith, ``Interaction.Core.classicalStraightline,
      ``Interaction.Core.classicalTranscriptOnly, ``Interaction.Core.Verifier.runWithLog_fst,
      ``Interaction.Core.OracleVerifier.classicalStraightline, ``Interaction.Core.rbrSoundness,
      ``Interaction.Core.rbrKnowledgeSoundness] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
