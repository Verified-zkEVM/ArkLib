/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture
import ArkLibTest.Interaction.Core.Support
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import VCVio.OracleComp.EvalDist.AnswerMeasure

/-! Access certificates for the hidden-bit composition of
`ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture`. The prefix exports its input oracle and its
decision makes one dummy request. The suffix decision reads the export as a pad and reveals the
hidden bit. Oracle access is typing. The export is a map over the prefix bundle, which on the
only prefix path consists of the inputs alone. The suffix decision routed by `suffixRoute` queries
only the reveal request and the input oracle of the composed bundle. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec
open Interaction.Core.HiddenBitFixture

namespace Interaction.Core.HiddenBitAccessTests

/-- The only path of the prefix. -/
abbrev firstPath : Path bitFirst := ⟨⟨⟩, ⟨⟩⟩

/-- The path of the composition on which the prover guesses `guess`. -/
abbrev combinedPath (guess : Bool) : Path bitCombined := ⟨⟨⟩, guess, ⟨⟩⟩

/-- The export returned by the prefix. -/
abbrev exportMap (v : View bitFirst firstPath) := bitPrefix.outputMap () firstPath v

-- RuntimeQueryBounds 2, restated: node names are removed. The export's only query is the input
-- oracle `.inl ()` of the prefix bundle.
example (v : View bitFirst firstPath) :
    (exportMap v).impl ⟨(), ()⟩ = liftM (firstBundle.spec.query (.inl ⟨(), ()⟩)) := rfl

-- RuntimeQueryBounds 1, access part, restated: the export is typed over the prefix bundle.
-- On the only prefix path this bundle has no oracle message, and the export reads the inputs
-- alone. Its query is the input oracle. The cost part is in `QueryCost.lean`.
example : IsEmpty (OracleMessageIndex bitFirst firstPath) := inferInstanceAs (IsEmpty PEmpty)

/-- The prefix export queries only its input oracle. -/
theorem export_access (v : View bitFirst firstPath) :
    AllQueriesSatisfy ((exportMap v).impl ⟨(), ()⟩) (fun q => q = .inl ⟨(), ()⟩) :=
  (allQueriesSatisfy_query_iff (spec := firstBundle.spec) (.inl ⟨(), ()⟩) _).mpr rfl

-- RuntimeQueryBounds 3, restated: the prefix output map is the embedding of the input oracle, and
-- the prefix decision makes the dummy request and accepts.
example (v : View bitFirst firstPath) :
    exportMap v = OracleMap.fst _ _ := rfl

example (v : View bitFirst firstPath) : (bitPrefix.decide () firstPath v).run = (do
    let _ : Bool ← liftM ((bitAmbient + firstBundle.spec).query (.inl false))
    pure (some ())) := rfl

/-- The suffix decision reads the pad from the export, reveals the hidden bit and claims
`hidden ^^ pad`. -/
theorem suffix_decide (guess : Bool) (v : View bitSecond ⟨guess, ⟨⟩⟩) :
    (bitSuffix.decide () ⟨guess, ⟨⟩⟩ v).run = (do
      let pad : Bool ← liftM ((bitAmbient + (secondBundle guess).spec).query
        (.inr (.inl ⟨(), ()⟩)))
      let hidden : Bool ← liftM ((bitAmbient + (secondBundle guess).spec).query (.inl true))
      pure (some (hidden ^^ pad))) := rfl

-- RuntimeQueryBounds 4, restated: the suffix decision unfolds to the pad and reveal queries
-- (`suffix_decide`), and the suffix output data is `guess ^^ pad`, with the pad read from the
-- export.
example (guess : Bool) (v : View bitSecond ⟨guess, ⟨⟩⟩)
    (x : (secondBundle guess).Data) :
    (bitSuffix.outputMap () ⟨guess, ⟨⟩⟩ v).f x () = (guess ^^ (show Bool from x.1 ())) :=
  rfl

/-- The suffix may request only the reveal, and may query only the export oracle. -/
abbrev suffixAllowed (p : Path bitSecond) :
    (bitAmbient + (pathBundle bits bitSecond p).spec).Domain → Prop
  | .inl request => request = true
  | .inr q => q = .inl ⟨(), ()⟩

-- RuntimeQueryBounds 5, restated: the ambient permission is kept. The suffix's bundle queries
-- go to the export oracle, and the suffix bundle has no other oracle on any path.
/-- The suffix decision queries only its export oracle and the reveal request. -/
theorem suffix_access (p : Path bitSecond) (v : View bitSecond p) :
    AllQueriesSatisfy (bitSuffix.decide () p v).run (suffixAllowed p) := by
  rcases p with ⟨guess, ⟨⟩⟩
  rw [suffix_decide]
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨rfl, fun _ =>
    (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨rfl, fun _ => allQueriesSatisfy_pure _ _⟩⟩

example (guess : Bool) : IsEmpty (OracleMessageIndex bitSecond ⟨guess, ⟨⟩⟩) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The suffix route of the composition, with ambient requests kept. -/
abbrev routeSuffix (p : Path bitCombined) (v : View bitCombined p) :=
  (OracleVerifier.suffixRoute bitPrefix () p v).withAmbient bitAmbient

/-- The suffix decision with its bundle queries routed into the composed bundle. -/
def routedSuffix (p : Path bitCombined) (v : View bitCombined p) :
    OracleComp (bitAmbient + (pathBundle bits bitCombined p).spec) (Option Bool) :=
  simulateQ (routeSuffix p v)
    (bitSuffix.decide () (Path.split bitFirst (fun _ => bitSecond) p).2
      (View.split bitFirst (fun _ => bitSecond) p v).2).run

/-- The routed export query is the input-oracle query of the composed bundle. -/
theorem routeSuffix_export (guess : Bool) (v : View bitCombined (combinedPath guess)) :
    routeSuffix (combinedPath guess) v (.inr (.inl ⟨(), ()⟩)) =
      liftM ((bitAmbient + (pathBundle bits bitCombined
        (combinedPath guess)).spec).query (.inr (.inl ⟨(), ()⟩))) := rfl

/-- The raw permissions: only the reveal request, and only the input oracle. -/
abbrev rawAllowed (p : Path bitCombined) :
    (bitAmbient + (pathBundle bits bitCombined p).spec).Domain → Prop
  | .inl request => request = true
  | .inr q => q = .inl ⟨(), ()⟩

-- RuntimeQueryBounds 8, restated: on every composed path and view, the routed suffix decision
-- satisfies the raw permissions. The ambient permission is kept, and the export query becomes the
-- input-oracle query.
/-- The routed suffix decision queries only the input oracle and the reveal request. -/
theorem routed_suffix_access (p : Path bitCombined) (v : View bitCombined p) :
    AllQueriesSatisfy (routedSuffix p v) (rawAllowed p) := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  refine (suffix_access _ _).simulateQ fun q allowed => ?_
  rcases q with request | (⟨i, q⟩ | ⟨i, q⟩)
  · exact (allQueriesSatisfy_query_iff _ _).mpr allowed
  · cases i
    cases q
    exact (routeSuffix_export guess v).symm ▸
      (allQueriesSatisfy_query_iff (spec := bitAmbient +
        (pathBundle bits bitCombined (combinedPath guess)).spec)
        (.inr (.inl ⟨(), ()⟩)) _).mpr rfl
  · exact i.elim

/-- The outcome of the hidden-bit protocol, including the materialized output oracle. -/
abbrev BitObservation := Outcome oracleSig bitCombined.{0} (fun _ => Nat)
  (OracleVerifier.Output (fun _ => Bool) (fun _ (_ : Unit) => Bool))

/-- Compare the actual output-oracle answer with the accepted target bit. -/
def answers (observation : BitObservation) : Option (Bool × Bool) :=
  observation.2.2.map fun claim => (claim.2 (), claim.1)

/-- The fixed guess and the actual target bit are both kept by the runtime execution. -/
theorem guess_answers (guess : Bool) (secret : Nat) :
    (fun result => answers result.output) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => some (guess, hidden)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  calc
    _ = (fun hidden => some (guess ^^ false, hidden ^^ false)) <$>
        (coinSpec.query () : OracleComp coinSpec Bool) := by kernel_rfl
    _ = _ := by simp only [Bool.xor_false]

/-- A prover querying the hidden bit returns that bit as both output answer and target. -/
theorem informed_answers (secret : Nat) :
    (fun result => answers result.output) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
    (fun hidden => some (hidden, hidden)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  calc
    _ = (fun hidden => some (hidden ^^ false, hidden ^^ false)) <$>
        (coinSpec.query () : OracleComp coinSpec Bool) := by kernel_rfl
    _ = _ := by simp only [Bool.xor_false]

open MeasureTheory in
/-- Every fixed guess matches the accepted output-oracle answer with probability one half. -/
theorem guess_success (guess : Bool) (secret : Nat) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret))}[
      (answers result.output).map (fun pair => pair.1 = pair.2) = some True] =
      (2 : ENNReal)⁻¹ := by
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{let pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (guess_answers guess secret)
  simp only [prEvent_map] at mass
  refine mass.trans ?_
  simp only [Option.map_some, Option.some.injEq]
  rw [prEvent_eq_evalDist_of_discrete,
    OracleComp.evalDist_liftM_query_apply (spec := coinSpec) () MeasurableSet.of_discrete]
  have event : {hidden : Bool | (guess = hidden) = True} = {guess} := by
    ext hidden
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, eq_iff_iff, true_iff, eq_comm]
  rw [event, OracleSpec.UniformAnswerMeasure.toMeasure_singleton]
  rfl

/-- The query-informed prover's actual output-oracle answer matches the target with probability
one; bundle access alone does not imply the fixed-guess half bound. -/
theorem informed_success (secret : Nat) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (informedProver secret))}[
      (answers result.output).map (fun pair => pair.1 = pair.2) = some True] = 1 := by
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{let pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (informed_answers secret)
  simp only [prEvent_map] at mass
  refine mass.trans ?_
  simp only [Option.map_some, eq_self, prEvent_true_eq_evalDist_apply_univ,
    OracleComp.evalDist_apply_univ_eq_one]

end Interaction.Core.HiddenBitAccessTests
