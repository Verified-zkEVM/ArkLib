/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Cost
import ArkLibTest.Interaction.Oracle.HiddenSendRun
import ArkLibTest.Interaction.Oracle.RoutedAccess
import ArkLibTest.Interaction.Oracle.HiddenBitAccess
import VCVio.OracleComp.QueryTracking.CostModel.Simulation
import ArkLibTest.Interaction.Support

/-! Weighted query cost of routed decisions and query counts of logged runs. A cost bound of a
decision transfers through its route with VCVio's `WorstCaseCostBound.simulateQ` once every routed
query is bounded by its source charge. Query profiles are `QueryLog.countQ`, additive over
appended logs. -/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

universe wJ

/-! ## The doubled export: `RoutedAccess.lean`

The prefix exports twice its message, reading the prefix oracle twice. The suffix decision reads
the export and its own oracle. Ambient queries cost 1 throughout. -/

namespace Interaction.QueryCostTests
open Interaction.RoutedAccessTests

/-- Raw charges on the composed bundle: 1 for the prefix oracle, 3 for the suffix oracle. -/
def rawCost : CostModel (ambient + rawBundle.spec) Nat := ⟨fun q => match q with
  | .inl _ => 1
  | .inr (.inl ⟨i, _⟩) => i.elim
  | .inr (.inr ⟨.inl _, _⟩) => 1
  | .inr (.inr ⟨.inr _, _⟩) => 3⟩

/-- Source charges on the suffix bundle: 2 for the export, 3 for the suffix's own oracle. -/
def sourceCost : CostModel (ambient + suffixBundle.spec) Nat := ⟨fun q => match q with
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 3⟩

-- QueryBounds 1, restated: the route is `suffixRoute` of `OracleVerifier.append`, with ambient
-- queries kept. Each routed query costs at most its source charge. The export expands to two
-- prefix-oracle queries of cost 1, and the fresh query is the suffix-oracle query of cost 3.
/-- Routing each suffix query costs at most its assigned source charge. -/
theorem route_cost (v : View combined combinedPath) (q : (ambient + suffixBundle.spec).Domain) :
    WorstCaseCostBound (route v q) rawCost (sourceCost.queryCost q) := by
  rcases q with n | (⟨⟨⟩, q⟩ | ⟨⟨⟩ | i, q⟩)
  · exact worstCaseCostBound_query (.inl n) rawCost
  · cases q
    change WorstCaseCostBound (do
      let left : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
      let right : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
      pure (left + right)) rawCost 2
    refine WorstCaseCostBound.bind (A := 1) (B := 1)
      (worstCaseCostBound_query _ rawCost) fun _ => ?_
    refine WorstCaseCostBound.bind (A := 1) (B := 0)
      (worstCaseCostBound_query _ rawCost) fun _ => ?_
    exact (worstCaseCostBound_pure _ _ _).mpr le_rfl
  · cases q
    exact worstCaseCostBound_query (.inr suffixSlot) rawCost
  · exact i.elim

-- QueryBounds 2, restated: the suffix decision program, over the ambient oracle and the suffix
-- bundle, has weighted cost at most 5.
/-- The suffix decision has weighted query cost at most five. -/
theorem program_cost : WorstCaseCostBound suffixProgram sourceCost 5 := by
  refine WorstCaseCostBound.bind (A := 2) (B := 3)
    (worstCaseCostBound_query (.inr (.inl ⟨(), ()⟩)) sourceCost) fun _ => ?_
  refine WorstCaseCostBound.bind (A := 3) (B := 0)
    (worstCaseCostBound_query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)) sourceCost) fun _ => ?_
  exact (worstCaseCostBound_pure _ _ _).mpr le_rfl

-- QueryBounds 3, restated: the routed suffix decision has raw cost at most 5.
/-- The routed suffix decision has weighted query cost at most five. -/
theorem routed_cost (v : View combined combinedPath) :
    WorstCaseCostBound (routedSuffix v) rawCost 5 :=
  program_cost.simulateQ (route v) (route_cost v)

/-- The routed program is available at the produced decision entry and costs at most five. -/
theorem routed_available_and_cost (a b : Nat) (v : View combined combinedPath) :
    AllQueriesSatisfy (routedSuffix v) (decisionAllowed a b) ∧
      WorstCaseCostBound (routedSuffix v) rawCost 5 :=
  ⟨routed_available a b v, routed_cost v⟩

example (v : View combined combinedPath) :
    ∃ program : OracleComp (ambient + rawBundle.spec) Nat,
      program = routedSuffix v ∧ WorstCaseCostBound program rawCost 5 :=
  ⟨routedSuffix v, rfl, routed_cost v⟩

/-- The routed export query reads the prefix oracle twice. -/
theorem route_export (v : View combined combinedPath) :
    route v (.inr (.inl ⟨(), ()⟩)) = (do
      let left : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
      let right : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
      pure (left + right)) := rfl

/-- The routed fresh query is the suffix-oracle query. -/
theorem route_fresh (v : View combined combinedPath) :
    route v (.inr (.inr ⟨.inl ⟨⟩, ()⟩)) =
      (liftM ((ambient + rawBundle.spec).query (.inr suffixSlot)) :
        OracleComp (ambient + rawBundle.spec) Nat) := rfl

/-- The routed suffix decision reads the prefix oracle twice, then the suffix oracle. -/
theorem routedSuffix_eq (v : View combined combinedPath) : routedSuffix v = (do
    let left : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
    let right : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
    let fresh : Nat ← liftM ((ambient + rawBundle.spec).query (.inr suffixSlot))
    pure (left + right + fresh)) := by
  kernel_rfl

-- QueryBounds 17: the routed suffix decision has a completed path of raw cost 5. Since the
-- shared prefix oracle is charged twice, 4 is not a bound.
example (v : View combined combinedPath) : ¬ WorstCaseCostBound (routedSuffix v) rawCost 4 := by
  intro certificate
  have last := mem_support_costDist_query_bind (.inr suffixSlot)
    (fun fresh : Nat => pure (0 + 0 + fresh)) (0 : Nat) rawCost (0, 1)
    (by rw [costDist_pure, mem_support_pure_iff])
  have middle := mem_support_costDist_query_bind (.inr prefixSlot) (fun right : Nat => do
      let fresh : Nat ← liftM ((ambient + rawBundle.spec).query (.inr suffixSlot))
      pure (0 + right + fresh)) (0 : Nat) rawCost _ last
  have member := mem_support_costDist_query_bind (.inr prefixSlot) (fun left : Nat => do
      let right : Nat ← liftM ((ambient + rawBundle.spec).query (.inr prefixSlot))
      let fresh : Nat ← liftM ((ambient + rawBundle.spec).query (.inr suffixSlot))
      pure (left + right + fresh)) (0 : Nat) rawCost _ middle
  rw [routedSuffix_eq] at certificate
  exact absurd ((worstCaseCostBound_iff_support_bound _ _ _).1 certificate _ member) (by decide)

end Interaction.QueryCostTests

/-! ## The hidden-bit composition: `HiddenBitAccess.lean`

A reveal request costs 3 and a dummy request 1; each input or export query costs 2; the runtime's
import, one coin, costs 1. -/

namespace Interaction.QueryCostTests
open Interaction.HiddenBitFixture Interaction.HiddenBitAccessTests

/-- Charges on the prefix bundle: 2 per input query. -/
def inputCost : CostModel firstBundle.spec Nat := ⟨fun _ => 2⟩

/-- Ambient charges: 3 for a reveal, 1 for a dummy request. -/
def ambientCost : CostModel bitAmbient Nat := ⟨fun request => if request then 3 else 1⟩

/-- The runtime's import charge. -/
def importCost : CostModel coinSpec Nat := ⟨fun _ => 1⟩

/-- Suffix charges: ambient charges, and 2 per export query. -/
def suffixCost (p : Path bitSecond) :
    CostModel (bitAmbient + (pathBundle bits bitSecond p).spec) Nat :=
  ⟨fun q => match q with
    | .inl request => ambientCost.queryCost request
    | .inr _ => 2⟩

/-- Raw charges on the composed bundle: ambient charges, and 2 per input query. -/
def bitRawCost (p : Path bitCombined) :
    CostModel (bitAmbient + (pathBundle bits bitCombined p).spec) Nat :=
  ⟨fun q => match q with
    | .inl request => ambientCost.queryCost request
    | .inr _ => 2⟩

-- RuntimeQueryBounds 1, cost part, restated: the export, a map over the prefix bundle, costs at
-- most 2.
example (v : View bitFirst firstPath) :
    WorstCaseCostBound ((exportMap v).impl ⟨(), ()⟩) inputCost 2 :=
  worstCaseCostBound_query (spec := firstBundle.spec) (.inl ⟨(), ()⟩) inputCost

-- RuntimeQueryBounds 6: on every suffix path and view, the suffix decision costs at most
-- 5: the export query 2 and the reveal 3.
/-- Every suffix decision has weighted query cost at most five. -/
theorem suffix_budget (p : Path bitSecond) (v : View bitSecond p) :
    WorstCaseCostBound (bitSuffix.decide () p v).run (suffixCost p) 5 := by
  rcases p with ⟨guess, ⟨⟩⟩
  rw [suffix_decide]
  refine WorstCaseCostBound.bind (A := 2) (B := 3)
    (worstCaseCostBound_query (.inr (.inl ⟨(), ()⟩)) (suffixCost _)) fun _ => ?_
  refine WorstCaseCostBound.bind (A := 3) (B := 0)
    (worstCaseCostBound_query (.inl true) (suffixCost _)) fun _ => ?_
  exact (worstCaseCostBound_pure _ _ _).mpr le_rfl

-- RuntimeQueryBounds 7, restated: the route is `suffixRoute … withAmbient`. On every composed
-- path and view, the routed suffix decision costs at most 5.
/-- Routing preserves the suffix decision's weighted cost bound of five. -/
theorem routed_suffix_budget (p : Path bitCombined) (v : View bitCombined p) :
    WorstCaseCostBound (routedSuffix p v) (bitRawCost p) 5 := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  refine OracleMap.withAmbient_worstCaseCost
    (In := pathBundle bits bitCombined (combinedPath guess)) (Out := secondBundle guess)
    (OracleVerifier.suffixRoute bitPrefix () (combinedPath guess) v)
    (suffix_budget.{0} _ (View.split bitFirst (fun _ => bitSecond) _ v).2) (fun _ => le_rfl) ?_
  rintro (⟨i, q⟩ | ⟨i, q⟩)
  · cases i
    cases q
    exact worstCaseCostBound_query
      (spec := (pathBundle bits bitCombined (combinedPath guess)).spec) (.inl ⟨(), ()⟩) _
  · exact i.elim

-- RuntimeQueryBounds 11: the runtime setup samples the hidden bit once.
/-- Runtime setup makes exactly one coin query and costs at most one. -/
theorem setup_budget : WorstCaseCostBound bitRuntime.setup importCost 1 :=
  WorstCaseCostBound.bind (A := 1) (B := 0) (worstCaseCostBound_query () importCost)
    fun _ => (worstCaseCostBound_pure _ _ _).mpr le_rfl

/-- The runtime history of the composed run with the guess prover, split by
`OracleVerifier.run_append`. -/
theorem guess_history (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  unfold bitVerifier
  rw [OracleVerifier.run_append]
  kernel_rfl

-- RuntimeQueryBounds 15, restated: the whole runtime execution of the composed run makes one
-- import query, for every guess and secret. The proof reflects the cost through the observed
-- history, as in the old-layer row.
/-- The composed runtime execution makes at most one import query. -/
theorem import_budget (guess : Bool) (secret : Nat) :
    WorstCaseCostBound (bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)))
      importCost 1 := by
  refine (worstCaseCostBound_map_iff _
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) importCost 1).mp ?_
  rw [guess_history]
  exact (worstCaseCostBound_map_iff _ _ importCost 1).mpr (worstCaseCostBound_query () importCost)

/-- The fixed guessing prover has the certified export, source and routed cost bounds and one
import query. The same run has the charged runtime history and success probability one half. -/
theorem fixed_resource_bounds (guess : Bool) (secret : Nat) :
    (∀ v : View bitFirst firstPath,
      (bitPrefix.decide () firstPath v).run = (do
        let _ : Bool ← liftM ((bitAmbient + firstBundle.spec).query (.inl false))
        pure (some ())) ∧
      exportMap v = OracleMap.fst _ _ ∧
      AllQueriesSatisfy ((exportMap v).impl ⟨(), ()⟩) (fun q => q = .inl ⟨(), ()⟩) ∧
      WorstCaseCostBound ((exportMap v).impl ⟨(), ()⟩) inputCost 2) ∧
    (∀ (p : Path bitCombined) (v : View bitCombined p),
      AllQueriesSatisfy (routedSuffix p v) (rawAllowed p) ∧
      WorstCaseCostBound (routedSuffix p v) (bitRawCost p) 5) ∧
    WorstCaseCostBound (bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)))
      importCost 1 ∧
    ((fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
      (fun hidden => ((hidden, 2),
        ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull), 4))
        <$> (coinSpec.query () : OracleComp coinSpec Bool)) ∧
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret))}[
      (answers result.output).map (fun pair => pair.1 = pair.2) = some True] ≤
      (2 : ENNReal)⁻¹ := by
  refine ⟨?_, ?_, import_budget guess secret, guess_history guess secret,
    (guess_success guess secret).le⟩
  · intro v
    exact ⟨rfl, rfl, export_access v,
      worstCaseCostBound_query (spec := firstBundle.spec) (.inl ⟨(), ()⟩) inputCost⟩
  · intro p v
    exact ⟨routed_suffix_access p v, routed_suffix_budget p v⟩

/-- The query-informed prover has chronological ambient charge seven and success one. Its
reveal precedes the passive prefix decision's dummy request. -/
theorem informed_cost_does_not_give_half (secret : Nat) :
    ((fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
      (fun hidden => ((hidden, 3),
        ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] :
          QueryLog bitFull), 7)) <$> (coinSpec.query () : OracleComp coinSpec Bool)) ∧
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (informedProver secret))}[
      (answers result.output).map (fun pair => pair.1 = pair.2) = some True] = 1 := by
  refine ⟨?_, informed_success secret⟩
  unfold bitVerifier
  rw [OracleVerifier.run_append]
  kernel_rfl

end Interaction.QueryCostTests

/-! ## Query profiles: `HiddenSendRun.lean` -/

namespace Interaction.QueryCostTests
open Interaction.HiddenSendRunTests

-- The full-log runner keeps input indices and input query types in `Type`; output query types
-- remain independent. See implementation note 18 in the interaction rebuild design notes.
/-- The prover's ambient log of the logged run, with arbitrary output query universe. -/
def proverLog.{qJ} (payload hidden : Nat) (bit : Bool) : QueryLog HiddenSendRunTests.ambient :=
  ((simulateQ (logger bit) ((verifier.{0, 0, 0, qJ} true).runWithLog () noData
    (prover payload hidden))).run []).1.2.1

-- PhasedRun 3, restated: per-move profiles are removed, and the query profile is
-- `QueryLog.countQ`. For every oracle message, private output and challenge, the prover's ambient
-- log is the two setup queries followed by the queries 1, 4 and 5. Query 9 therefore counts twice:
-- `2 + 0` over the two segments.
/-- The prover log contains the two setup queries followed by its three interaction queries. -/
theorem proverLog_eq (payload hidden : Nat) (bit : Bool) :
    proverLog.{wJ} payload hidden bit = [⟨9, ()⟩, ⟨9, ()⟩] ++ [⟨1, ()⟩, ⟨4, ()⟩, ⟨5, ()⟩] := by
  kernel_rfl

example (payload hidden : Nat) (bit : Bool) :
    (proverLog.{wJ} payload hidden bit).countQ (· = 9) = 2 := by
  rw [proverLog_eq, QueryLog.countQ_append]
  rfl

end Interaction.QueryCostTests
