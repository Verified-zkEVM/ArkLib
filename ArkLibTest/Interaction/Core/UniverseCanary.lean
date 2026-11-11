/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Composition
import ArkLib.Interaction.Core.Security.Knowledge
import ArkLib.Interaction.Core.Security.KnowledgeComposition

/-!
# Components that are not run outputs live in their own universes

Ambient oracle indices, input oracle indices, output oracle indices, input and output oracle
query types, input statements and input witnesses each take their own universe. The instances
below put an oracle index in `Type 1` with responses in `Type 0`, input oracle queries in
`Type 1`, output oracle queries in `Type 2`, an input statement in `Type 2` and an input witness
in `Type 1`, while moves, run outputs and oracle responses stay in `Type 0`. They typecheck
against `Verifier`, `OracleVerifier`, `Reduction`, both appends, the oracle routing laws, oracle
runs, the classical security and extraction models and round-by-round knowledge state functions,
whose intermediate witnesses lie in their own universe. A run returns the output oracle data
`∀ j, B p j`, so the run's output index is in `Type 0`.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp MeasureTheory

universe v

namespace Interaction.Core.UniverseCanaryTests

/-- Ambient oracles indexed by types, answering in `Bool`: the index lies in `Type 1`. -/
abbrev bigAmbient : OracleSpec.{1, 0} Type := Type →ₒ Bool

/-- An ambient oracle with an index in `Type 0`, which a prover can query. -/
abbrev smallAmbient : OracleSpec.{0, 0} Unit := Unit →ₒ Bool

/-- A natural number answers the unit query with itself. -/
@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := read

/-- Input oracles indexed by types (`Type 1`) with natural-number data (`Type 0`). -/
@[instance_reducible]
def bigInputs : OracleFamily.{1, 0, 0} Type (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- The protocol with no rounds. -/
abbrev done : Protocol := .pure ⟨⟩

/-- The oracle protocol with no rounds. -/
abbrev oracleDone : OracleProtocol := .pure ⟨⟩

/-! ### Plain verifiers and reductions -/

/-- A plain verifier with an ambient index in `Type 1` and an input statement in `Type 2`. -/
def plainVerifier : Verifier bigAmbient done (Type 1) (fun _ => Bool) where
  decide _ _ _ := liftM (bigAmbient.query Nat)

/-- A suffix whose input statement is the prefix's `Bool` output. -/
def plainSuffix : Verifier bigAmbient done Bool (fun _ => Bool) where
  decide b _ _ := pure (!b)

/-- Plain append with the large ambient index and input statement. -/
def plainAppend : Verifier bigAmbient (done.append (fun _ => done)) (Type 1) (fun _ => Bool) :=
  plainVerifier.append (fun _ => plainSuffix)

/-- A reduction with an input statement in `Type 2` and an input witness in `Type 1`. The ambient
index stays in `Type 0`, because the prover runs in `OracleComp smallAmbient`. -/
def reduction : Reduction smallAmbient done (Type 1) Type (fun _ => Unit) (fun _ => PUnit) where
  prover _ _ := pure ⟨⟩
  verifier := { decide := fun _ _ _ => pure () }

/-! ### Oracle verifiers -/

/-- An oracle verifier whose ambient, input and output indices lie in `Type 1` and whose input
statement lies in `Type 2`. It queries the input oracle at index `Nat`. -/
def oracleVerifier : OracleVerifier bigAmbient oracleDone (Type 1) (fun _ => Nat) bigInputs
    (fun _ => bigInputs) where
  decide _ p _ := by
    cases p
    exact liftM ((bigAmbient + (pathResources bigInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨Nat, ()⟩)))
  outputMap _ _ _ := OracleMap.fst _ _

/-- A suffix whose middle oracle family is indexed by types. -/
def oracleSuffix : OracleVerifier bigAmbient oracleDone Nat (fun _ => Nat) bigInputs
    (fun _ => bigInputs) where
  decide n _ _ := pure (n + 1)
  outputMap _ _ _ := OracleMap.fst _ _

/-- The composite output map ignores the intermediate statement, so any certificate holds. -/
def oracleCompatible :
    OracleVerifier.OutputCompatibility oracleVerifier (fun _ => oracleSuffix) where
  outputMap stmt p v :=
    (oracleSuffix.outputMap 0 (Path.split oracleDone (fun _ => oracleDone) p).2
      (View.split oracleDone (fun _ => oracleDone) p v).2).comp
      (OracleVerifier.suffixRoute oracleVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Oracle append with large ambient, input, middle and output indices. -/
def oracleAppend := oracleVerifier.append (fun _ => oracleSuffix) oracleCompatible

/-- The oracle routing law at large indices. -/
theorem oracleAppend_decideWith (stmt : Type 1)
    (p : Path (oracleDone.append (fun _ => oracleDone)))
    (v : View (oracleDone.append (fun _ => oracleDone)) p)
    (data : (pathResources bigInputs (oracleDone.append (fun _ => oracleDone)) p).Data) :
    oracleAppend.decideWith stmt p v data =
      oracleVerifier.decideWith stmt (Path.split oracleDone (fun _ => oracleDone) p).1
          (View.split oracleDone (fun _ => oracleDone) p v).1
          ((OracleVerifier.prefixRoute (inputs := bigInputs) p).f data) >>= fun
        | none => pure none
        | some mid => oracleSuffix.decideWith mid
            (Path.split oracleDone (fun _ => oracleDone) p).2
            (View.split oracleDone (fun _ => oracleDone) p v).2
            ((OracleVerifier.suffixRoute oracleVerifier stmt p v).f data) :=
  OracleVerifier.append_decideWith _ _ _ _ _ _ _

/-- Routing through an oracle map with a large input index agrees with materialized data. -/
theorem embedding_simulate_eq (x : Type → Nat) {α : Type}
    (program : OracleComp (bigInputs.reindex (fun X : Type => X)).spec α) :
    simulateQ (bigInputs.behaviorOfRealizations x)
        (simulateQ (OracleMap.embedding bigInputs (fun X : Type => X)).impl program) =
      simulateQ ((bigInputs.reindex (fun X : Type => X)).behaviorOfRealizations
        ((OracleMap.embedding bigInputs (fun X : Type => X)).f x)) program :=
  OracleMap.simulate_eq (OracleMap.embedding bigInputs (fun X : Type => X)) x program

/-! ### An oracle run with a large input index -/

/-- One natural-number output oracle with an index in `Type 0`, as a run requires. -/
@[instance_reducible]
def smallOutputs : OracleFamily.{0, 0, 0} Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- An oracle verifier that a prover can run against. Its ambient index and output index are in
`Type 0`, while its input oracle index and input statement stay in `Type 1` and `Type 2`. -/
def runnable : OracleVerifier smallAmbient oracleDone (Type 1) (fun _ => Nat) bigInputs
    (fun _ => smallOutputs) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathResources bigInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨Bool, ()⟩)))
  outputMap _ _ _ := (OracleMap.embedding bigInputs (fun _ : Unit => Bool)).comp
    (OracleMap.fst _ _)

/-- The ambient oracle answers `true`; the protocol has no challenges. -/
def handler : QueryImpl (smallAmbient + challengeSpec oracleSig oracleDone) Id
  | .inl _ => true
  | .inr c => c.val.elim

/-- The prover of the protocol with no rounds. -/
def idle : Prover oracleSig smallAmbient oracleDone (fun _ => PUnit) := pure ⟨⟩

/-- The run on input data that is `3` at every type. -/
def observation := simulateQ handler (runnable.run (Type 0) (fun _ => 3) idle)

/-- The run answers the input query at index `Bool` from the data, and the output oracle at `()`
is the input oracle at `Bool`. -/
example : observation.2.2.map (fun out => (out.1, out.2 ())) = some (3, 3) := rfl

/-! ### Input and output query types in their own universes -/

/-- A natural number answers every query `X : Type` with itself. The query type `Type` lies in
`Type 1`, while the data and the responses lie in `Type 0`. -/
@[reducible]
def typeQueries : OracleInterface.{0, 1} Nat where
  Query := Type
  toOC.spec := Type →ₒ Nat
  toOC.impl _ := read

/-- A natural number answers every query `X : Type 1` with itself; the query type lies in
`Type 2`. -/
@[reducible]
def bigTypeQueries : OracleInterface.{0, 2} Nat where
  Query := Type 1
  toOC.spec := Type 1 →ₒ Nat
  toOC.impl _ := read

/-- One input oracle whose queries are types, with natural-number data and responses. -/
@[instance_reducible]
def typeQueryInputs : OracleFamily.{0, 0, 1} Unit (fun _ => Nat) := ⟨fun _ => typeQueries⟩

/-- One oracle whose queries lie in `Type 1`, a query universe different from the inputs'. -/
@[instance_reducible]
def bigQueryOracles : OracleFamily.{0, 0, 2} Unit (fun _ => Nat) := ⟨fun _ => bigTypeQueries⟩

/-- The output oracle answers each query by asking the input oracle at `Nat`. -/
def forwardQueries (p : Path oracleDone) :
    OracleMap (pathResources typeQueryInputs oracleDone p) (Resources.ofFamily bigQueryOracles)
    where
  f x _ := x.1 ()
  impl _ := liftM ((pathResources typeQueryInputs oracleDone p).spec.query (.inl ⟨(), Nat⟩))
  law _ _ := rfl

/-- An oracle verifier whose input queries lie in `Type 1` and whose output queries lie in
`Type 2`, while its moves, its result and all oracle responses lie in `Type 0`. It queries its
input at the type `Bool`. -/
def typeQueryVerifier : OracleVerifier smallAmbient oracleDone Unit (fun _ => Nat)
    typeQueryInputs (fun _ => bigQueryOracles) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathResources typeQueryInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨(), Bool⟩)))
  outputMap _ p _ := forwardQueries p

/-- The run answers the input query at the type `Bool` from the data `5`, and the output oracle
answers a query in `Type 1` with the same value. -/
example :
    (simulateQ handler (typeQueryVerifier.run () (fun _ => 5) idle)).2.2.map
      (fun out => (out.1, bigQueryOracles.behaviorOfRealizations out.2 ⟨(), Type⟩)) =
      some ((5, 5) : Nat × Nat) := rfl

/-- A suffix whose input oracle has queries in `Type 2` and whose output oracle has queries in
`Type 0`. It adds one to its input statement after querying its input at the type `Type`. -/
def typeQuerySuffix : OracleVerifier smallAmbient oracleDone Nat (fun _ => Nat)
    bigQueryOracles (fun _ => smallOutputs) where
  decide n p _ := by
    cases p
    exact (fun m => n + m) <$> liftM
      ((smallAmbient + (pathResources bigQueryOracles oracleDone ⟨⟩).spec).query
        (.inr (.inl ⟨(), Type⟩)))
  outputMap _ p _ :=
    { f := fun x _ => x.1 ()
      impl := fun _ => liftM
        ((pathResources bigQueryOracles oracleDone p).spec.query (.inl ⟨(), Type⟩))
      law := fun _ _ => rfl }

/-- The composite output map ignores the intermediate statement, so any certificate holds. -/
def typeQueryCompatible :
    OracleVerifier.OutputCompatibility typeQueryVerifier (fun _ => typeQuerySuffix) where
  outputMap stmt p v :=
    (typeQuerySuffix.outputMap 0 (Path.split oracleDone (fun _ => oracleDone) p).2
      (View.split oracleDone (fun _ => oracleDone) p v).2).comp
      (OracleVerifier.suffixRoute typeQueryVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Oracle append whose input, middle and output query types lie in three different universes. -/
def typeQueryAppend := typeQueryVerifier.append (fun _ => typeQuerySuffix) typeQueryCompatible

/-- The oracle routing law when the input, middle and output query universes differ. -/
theorem typeQueryAppend_decideWith (stmt : Unit)
    (p : Path (oracleDone.append (fun _ => oracleDone)))
    (v : View (oracleDone.append (fun _ => oracleDone)) p)
    (data : (pathResources typeQueryInputs (oracleDone.append (fun _ => oracleDone)) p).Data) :
    typeQueryAppend.decideWith stmt p v data =
      typeQueryVerifier.decideWith stmt (Path.split oracleDone (fun _ => oracleDone) p).1
          (View.split oracleDone (fun _ => oracleDone) p v).1
          ((OracleVerifier.prefixRoute (inputs := typeQueryInputs) p).f data) >>= fun
        | none => pure none
        | some mid => typeQuerySuffix.decideWith mid
            (Path.split oracleDone (fun _ => oracleDone) p).2
            (View.split oracleDone (fun _ => oracleDone) p v).2
            ((OracleVerifier.suffixRoute typeQueryVerifier stmt p v).f data) :=
  OracleVerifier.append_decideWith _ _ _ _ _ _ _

/-! ### Security models with large inputs -/

/-- Observations of `runnable` and `typeQueryVerifier` are small, so every set of them may be
declared measurable. -/
instance : MeasurableSpace (Observation oracleSig oracleDone (fun _ => PUnit)
    (OracleVerifier.Output (fun _ => Nat) (fun _ (_ : Unit) => Nat))) := ⊤

/-- The ambient oracle of the security experiments answers `true` and keeps no state. -/
def ambientTrue : QueryImpl smallAmbient (StateT Unit ProbComp) := fun _ => pure true

/-- The protocol with no rounds samples no challenges. -/
def noChallenges : QueryImpl (challengeSpec oracleSig oracleDone) ProbComp := fun c => c.val.elim

/-- The classical model of `runnable`. Its statements pair an input statement in `Type 2` with
input data indexed by `Type`, while its observations stay in `Type 0`. -/
noncomputable def runnableModel :
    AdversaryModel ((Type 1) × (Type → Nat))
      (Observation oracleSig oracleDone (fun _ => PUnit)
        (OracleVerifier.Output (fun _ => Nat) (fun _ (_ : Unit) => Nat))) :=
  runnable.classicalModel (pure ()) ambientTrue noChallenges

/-- The classical model of `typeQueryVerifier`, whose input queries lie in `Type 1` and whose
output queries lie in `Type 2`. -/
noncomputable def typeQueryModel :
    AdversaryModel (Unit × (Unit → Nat))
      (Observation oracleSig oracleDone (fun _ => PUnit)
        (OracleVerifier.Output (fun _ => Nat) (fun _ (_ : Unit) => Nat))) :=
  typeQueryVerifier.classicalModel (pure ()) ambientTrue noChallenges

/-- Every classical model is sound with error one; the statement typechecks for `runnable`. -/
example (input : StatementProblem ((Type 1) × (Type → Nat)))
    (output : PathProblem oracleDone
      (OracleVerifier.Output (fun _ => Nat) (fun _ (_ : Unit) => Nat))) :
    soundness runnableModel input output (fun obs => projectPathAlong oracleSig oracleDone obs.1)
      (fun obs => obs.2.2) 1 :=
  fun _ _ _ _ => le_trans (measure_mono (Set.subset_univ _)) (runnableModel.mass_le_one _ _)

/-- The trivial output problem: every claim holds with the unit witness. -/
def anyOutput : PathProblem done (fun _ => Unit) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ _ _ := True
  rel_admissible _ _ _ _ := trivial

/-- The ambient oracle of the plain experiments answers `true` and keeps no state. -/
def plainAmbientTrue : QueryImpl smallAmbient (StateT Unit ProbComp) := fun _ => pure true

/-- The plain protocol with no rounds samples no challenges. -/
def noPlainChallenges : QueryImpl (challengeSpec plainSig done) ProbComp := fun c => c.val.elim

/-- The reduction with an input statement in `Type 2` and an input witness in `Type 1` has an
exported completeness statement, which holds with error one. -/
example (input : StatementProblem (Type 1)) (witness : ∀ stmt, input.Witness () stmt → Type) :
    reduction.completeness (pure ()) plainAmbientTrue noPlainChallenges input anyOutput
      (fun _ _ => ()) (fun _ _ _ => ()) witness 1 :=
  ⟨MeasurableSpace.measurableSet_top, fun _ _ _ => by simp⟩

/-- The soundness statement of the reduction's verifier, whose input statement lies in `Type 2`,
typechecks against the plain classical model. -/
example (input : StatementProblem (Type 1)) : Prop :=
  reduction.verifier.soundness (pure ()) plainAmbientTrue noPlainChallenges input anyOutput 0

/-! ### Extraction models with large input indices and large query types -/

/-- An extractor that ignores its inputs and returns `7`. -/
def sevenExtractor {S : Type v} :
    Extractor.OracleStraightline smallAmbient oracleDone (fun _ : S => Nat) (fun _ => PUnit) :=
  fun _ _ _ _ _ => pure 7

/-- The extraction game of `runnable`, whose input index lies in `Type 1`, accepts on data `3` and
extracts `7`; the ambient decision log is empty because the decision queries only its input. -/
example :
    (simulateQ handler (runnable.extractionGame (fun _ o => o) sevenExtractor
      ((Type 0), fun _ => 3) idle)).2 = some 7 := rfl

/-- The ambient-log run of `typeQueryVerifier`, whose input queries lie in `Type 1`, keeps the
run's observation and two empty ambient logs. -/
example :
    (simulateQ handler (typeQueryVerifier.runWithAmbientLog () (fun _ => 5) idle)).2.2.isEmpty =
      true := rfl

/-- The classical straight-line extraction model of `runnable`. -/
noncomputable def runnableExtraction :=
  runnable.classicalStraightline (Out := fun _ => PUnit) (Wout := fun _ => PUnit)
    (fun _ => Nat) (pure ()) ambientTrue noChallenges (fun _ o => o)

/-- Straight-line extraction for `runnable` preserves the run's observation law. -/
example (E : Extractor.OracleStraightline smallAmbient oracleDone
      (fun _ : (Type 1) × (Type → Nat) => Nat) (fun _ => PUnit))
    (stmt : (Type 1) × (Type → Nat)) (adv : Prover oracleSig smallAmbient oracleDone
      (fun _ => PUnit)) :
    (runnableExtraction.experiment E stmt adv).map Prod.fst = runnableModel.outcome stmt adv :=
  runnable.classicalStraightline_marginal _ _ _ _ _ E stmt adv

/-- The classical transcript-only extraction model of `typeQueryVerifier`, whose input queries
lie in `Type 1` and whose output queries lie in `Type 2`. -/
noncomputable def typeQueryExtraction :=
  typeQueryVerifier.classicalTranscriptOnly (Out := fun _ => PUnit) (Wout := fun _ => PUnit)
    (fun _ => Nat) (pure ()) ambientTrue noChallenges (fun _ o => o)

/-- Transcript-only extraction for `typeQueryVerifier` preserves the run's observation law. -/
example (E : Extractor.OracleTranscriptOnly smallAmbient oracleDone
      (fun _ : Unit × (Unit → Nat) => Nat) (fun _ => PUnit))
    (stmt : Unit × (Unit → Nat)) (adv : Prover oracleSig smallAmbient oracleDone
      (fun _ => PUnit)) :
    (typeQueryExtraction.experiment E stmt adv).map Prod.fst = typeQueryModel.outcome stmt adv :=
  typeQueryVerifier.classicalTranscriptOnly_marginal _ _ _ _ _ E stmt adv

/-! ### Knowledge state functions with large intermediate witnesses -/

/-- A knowledge state function on a protocol with no rounds whose intermediate witnesses are
types, in `Type 1`, while its input witness is the unit, in `Type 0`. The root extractor maps a
type to the unit. -/
def typeCertificate {P : PFunctor.{1, 0}} (l : PFunctor.Lens P TwoParty.Lens.rolePoly)
    {S : Type v} (validOutput : S → PathAlong l (.pure ⟨⟩ : FreeM P PUnit) → Unit → Prop) :
    KnowledgeStateFunction.{v, 0, 1} l (.pure ⟨⟩) S (fun _ _ => Unit) (fun _ => Unit)
    (fun _ => True)
      (fun _ _ => True) validOutput where
  Witness _ {_} _ _ := Type
  toFun _ {_} _ _ _ := True
  extractRoot _ _ := ()
  extractStep _ {_ _} sp := nomatch sp
  extractLeaf _ _ _ _ := Unit
  root _ _ _ _ := trivial
  send sp _ _ _ := nomatch sp
  leaf _ _ _ _ _ := trivial

/-- Round-by-round knowledge with intermediate witnesses in `Type 1`, a small input witness and an
input statement in `Type 2`. -/
example : rbrKnowledgeSoundness.{2, 0, 1} plainSig done (fun (_ : Type 1) => True)
    (fun _ (_ : Unit) => True) (fun _ _ (_ : Unit) => True) (fun c => c.val.elim) (fun _ => 0) :=
  ⟨typeCertificate plainSig _, fun _ _ _ _ sp => nomatch sp⟩

/-- The plain verifier wrapper at the same unequal universes. -/
example : Verifier.rbrKnowledgeSoundness.{2, 0, 1} reduction.verifier plainAmbientTrue
    (fun _ => True) (fun _ (_ : Unit) => True) (fun _ _ _ (_ : Unit) => True) noPlainChallenges
    (fun _ => 0) :=
  ⟨typeCertificate plainSig _, fun _ _ _ _ sp => nomatch sp⟩

/-- The oracle verifier wrapper for `runnable`, with intermediate witnesses in `Type 1`, a small
input witness, an input statement in `Type 2` and an input index in `Type 1`. -/
example : OracleVerifier.rbrKnowledgeSoundness.{2, 0, 1, 1, 0, 0} runnable ambientTrue
    (fun _ => True) (fun _ (_ : Unit) => True) (fun _ _ _ (_ : Unit) => True) noChallenges
    (fun _ => 0) :=
  ⟨typeCertificate oracleSig _, fun _ _ _ _ sp => nomatch sp⟩

/-- Statement-dependent finite witnesses at three independent universes. -/
def indexedLargeCertificate : KnowledgeStateFunction.{2, 2, 1} plainSig done
    (Type 1 × Nat) (fun stmt _ => Fin (stmt.2 + 1))
    (fun stmt => ULift.{2} (Fin (stmt.2 + 1))) (fun _ => True) (fun _ _ => True)
    (fun _ _ _ => True) where
  Witness stmt {_} _ _ := ULift.{1} (Fin (stmt.2 + 1))
  toFun _ {_} _ _ _ := True
  extractRoot _ w := ⟨w.down⟩
  extractStep _ {_ _} sp := nomatch sp
  extractLeaf _ _ _ w := ⟨w⟩
  root _ _ _ _ := trivial
  send sp := nomatch sp
  leaf _ _ _ _ _ := trivial

/-- The suffix extracts a small finite input witness from a large intermediate witness. -/
def indexedSmallCertificate : KnowledgeStateFunction.{2, 0, 1} plainSig done
    (Type 1 × Nat) (fun stmt _ => Fin (stmt.2 + 1))
    (fun stmt => Fin (stmt.2 + 1)) (fun _ => True) (fun _ _ => True)
    (fun _ _ _ => True) where
  Witness stmt {_} _ _ := ULift.{1} (Fin (stmt.2 + 1))
  toFun _ {_} _ _ _ := True
  extractRoot _ w := w.down
  extractStep _ {_ _} sp := nomatch sp
  extractLeaf _ _ _ w := ⟨w⟩
  root _ _ _ _ := trivial
  send sp := nomatch sp
  leaf _ _ _ _ _ := trivial

/-- Composition keeps the large statement-indexed input carrier and small seam carrier. -/
example (stmt : Type 1 × Nat) (w : Fin (stmt.2 + 1)) :
    (KnowledgeStateFunction.append (s₂ := fun _ => done)
      (W := fun stmt _ => Fin (stmt.2 + 1)) (validOutput := fun _ _ _ => True)
      (admissible₂ := fun _ _ => True) (relMid := fun _ _ _ => True)
      indexedLargeCertificate (fun _ =>
    indexedSmallCertificate)
      (fun _ _ _ _ => trivial)).extractAlong stmt ⟨⟩ w = ULift.up w := rfl

/-- Lifting preserves statement-dependent witnesses and the root extraction map. -/
example (stmt : Type 1 × Nat) (w : Fin (stmt.2 + 1)) :
    (indexedLargeCertificate.lift.{2, 2, 1, 3}).extractRoot stmt ⟨⟨w⟩⟩ = ULift.up w := rfl

/-- Lifting a bound retains the same dependent input and output carriers at a larger universe. -/
example : rbrKnowledgeSoundness.{2, 2, 3} plainSig done
    (fun (_ : Type 1 × Nat) => True)
    (fun stmt (_ : ULift.{2} (Fin (stmt.2 + 1))) => True)
    (fun stmt _ (_ : Fin (stmt.2 + 1)) => True) noPlainChallenges (fun _ => 0) :=
  rbrKnowledgeSoundness.lift.{2, 2, 1, 3} plainSig
    ⟨indexedLargeCertificate, fun _ _ _ _ sp => nomatch sp⟩

end Interaction.Core.UniverseCanaryTests
