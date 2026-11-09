/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibTest.Interaction.Core.Oracle.PhasedRun
import ArkLibTest.Interaction.Core.Oracle.QueryBounds
import ArkLibTest.Interaction.Core.Oracle.RuntimeQueryBounds
import VCVio.OracleComp.QueryTracking.CostModel.Simulation

/-! Weighted query cost of routed decisions and query counts of logged runs. A cost bound of a
decision transfers through its route with VCVio's `WorstCaseCostBound.simulateQ` once every routed
query is bounded by its source charge. Query profiles are `QueryLog.countQ`, additive over
appended logs. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

/-! ## The doubled export: `QueryBounds.lean`

The prefix exports twice its message, reading the prefix slot twice; the suffix decision reads the
export and its own slot. Ambient queries cost 1 throughout. -/

namespace Interaction.Core.QueryCostTests
open Interaction.Core.QueryBoundsTests

/-- Raw charges on the composed resources: 1 for the prefix slot, 3 for the suffix slot. -/
def rawCost : CostModel (ambient + rawResources.spec) Nat := ⟨fun q => match q with
  | .inl _ => 1
  | .inr ⟨.inl i, _⟩ => i.elim
  | .inr ⟨.inr (.inl _), _⟩ => 1
  | .inr ⟨.inr (.inr _), _⟩ => 3⟩

/-- Source charges on the suffix resources: 2 for the export, 3 for the suffix's own slot. -/
def sourceCost : CostModel (ambient + suffixResources.spec) Nat := ⟨fun q => match q with
  | .inl _ => 1
  | .inr ⟨.inl _, _⟩ => 2
  | .inr ⟨.inr _, _⟩ => 3⟩

-- QueryBounds 1, restated: the route is `suffixRoute` of `OracleVerifier.append`, with ambient
-- queries kept. Each routed query costs at most its source charge: the export expands to two
-- prefix-slot queries of cost 1, and the fresh query is the suffix-slot query of cost 3.
theorem route_cost (v : View combined combinedPath) (q : (ambient + suffixResources.spec).Domain) :
    WorstCaseCostBound (route v q) rawCost (sourceCost.queryCost q) := by
  rcases q with n | ⟨⟨⟩ | ⟨⟩ | i, q⟩
  · exact worstCaseCostBound_query (.inl n) rawCost
  · cases q
    change WorstCaseCostBound (do
      let left : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
      let right : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
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
-- resources, has weighted cost at most 5.
theorem program_cost : WorstCaseCostBound suffixProgram sourceCost 5 := by
  refine WorstCaseCostBound.bind (A := 2) (B := 3)
    (worstCaseCostBound_query (.inr ⟨.inl (), ()⟩) sourceCost) fun _ => ?_
  refine WorstCaseCostBound.bind (A := 3) (B := 0)
    (worstCaseCostBound_query (.inr ⟨.inr (.inl ⟨⟩), ()⟩) sourceCost) fun _ => ?_
  exact (worstCaseCostBound_pure _ _ _).mpr le_rfl

-- QueryBounds 3, restated: the routed suffix decision has raw cost at most 5.
theorem routed_cost (v : View combined combinedPath) :
    WorstCaseCostBound (routedSuffix v) rawCost 5 :=
  program_cost.simulateQ (route v) (route_cost v)

-- QueryBounds 13, restated: availability is the typing of the routed program over the composed
-- resources (`QueryBounds.lean`, row 4), and the cost part is row 3.
example (v : View combined combinedPath) :
    ∃ program : OracleComp (ambient + rawResources.spec) Nat,
      program = routedSuffix v ∧ WorstCaseCostBound program rawCost 5 :=
  ⟨routedSuffix v, rfl, routed_cost v⟩

/-- The routed export query reads the prefix slot twice. -/
theorem route_export (v : View combined combinedPath) :
    route v (.inr ⟨.inl (), ()⟩) = (do
      let left : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
      let right : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
      pure (left + right)) := rfl

/-- The routed fresh query is the suffix-slot query. -/
theorem route_fresh (v : View combined combinedPath) :
    route v (.inr ⟨.inr (.inl ⟨⟩), ()⟩) =
      (liftM ((ambient + rawResources.spec).query (.inr suffixSlot)) :
        OracleComp (ambient + rawResources.spec) Nat) := rfl

/-- The routed suffix decision reads the prefix slot twice, then the suffix slot. -/
theorem routedSuffix_eq (v : View combined combinedPath) : routedSuffix v = (do
    let left : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
    let right : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
    let fresh : Nat ← liftM ((ambient + rawResources.spec).query (.inr suffixSlot))
    pure (left + right + fresh)) := by
  kernel_rfl

-- QueryBounds 17: the routed suffix decision has a completed path of raw cost 5, since the
-- shared prefix slot is charged twice, so 4 is not a bound.
example (v : View combined combinedPath) : ¬ WorstCaseCostBound (routedSuffix v) rawCost 4 := by
  intro certificate
  have last := mem_support_costDist_query_bind (.inr suffixSlot)
    (fun fresh : Nat => pure (0 + 0 + fresh)) (0 : Nat) rawCost (0, 1)
    (by rw [costDist_pure, mem_support_pure_iff])
  have middle := mem_support_costDist_query_bind (.inr prefixSlot) (fun right : Nat => do
      let fresh : Nat ← liftM ((ambient + rawResources.spec).query (.inr suffixSlot))
      pure (0 + right + fresh)) (0 : Nat) rawCost _ last
  have member := mem_support_costDist_query_bind (.inr prefixSlot) (fun left : Nat => do
      let right : Nat ← liftM ((ambient + rawResources.spec).query (.inr prefixSlot))
      let fresh : Nat ← liftM ((ambient + rawResources.spec).query (.inr suffixSlot))
      pure (left + right + fresh)) (0 : Nat) rawCost _ middle
  rw [routedSuffix_eq] at certificate
  exact absurd (certificate _ member) (by decide)

end Interaction.Core.QueryCostTests

/-! ## The hidden-bit composition: `RuntimeQueryBounds.lean`

A reveal request costs 3 and a dummy request 1; each input or export query costs 2; the runtime's
import, one coin, costs 1. -/

namespace Interaction.Core.QueryCostTests
open Interaction.Core.LoggedExecutionTests Interaction.Core.RuntimeQueryBoundsTests

/-- Charges on the prefix resources: 2 per input query. -/
def inputCost : CostModel firstResources.spec Nat := ⟨fun _ => 2⟩

/-- Ambient charges: 3 for a reveal, 1 for a dummy request. -/
def ambientCost : CostModel bitAmbient Nat := ⟨fun request => if request then 3 else 1⟩

/-- The runtime's import charge. -/
def importCost : CostModel coinSpec Nat := ⟨fun _ => 1⟩

/-- Suffix charges: ambient charges, and 2 per export query. -/
def suffixCost (p : Path bitSecond) :
    CostModel (bitAmbient + (sumFamily bits (pathFamily bitSecond p)).spec) Nat :=
  ⟨fun q => match q with
    | .inl request => ambientCost.queryCost request
    | .inr _ => 2⟩

/-- Raw charges on the composed resources: ambient charges, and 2 per input query. -/
def bitRawCost (p : Path bitCombined) :
    CostModel (bitAmbient + (sumFamily bits (pathFamily bitCombined p)).spec) Nat :=
  ⟨fun q => match q with
    | .inl request => ambientCost.queryCost request
    | .inr _ => 2⟩

-- RuntimeQueryBounds 1, cost part, restated: the export, a map over the prefix resources, costs
-- at most 2.
example (v : View bitFirst firstPath) :
    WorstCaseCostBound ((exportMap v).impl ⟨(), ()⟩) inputCost 2 :=
  worstCaseCostBound_query (spec := firstResources.spec) ⟨.inl (), ()⟩ inputCost

-- RuntimeQueryBounds 6: on every suffix path and view, the suffix decision costs at most
-- 5: the export query 2 and the reveal 3.
theorem suffix_budget (p : Path bitSecond) (v : View bitSecond p) :
    WorstCaseCostBound (bitSuffix.decide () p v).run (suffixCost p) 5 := by
  rcases p with ⟨guess, ⟨⟩⟩
  rw [suffix_decide]
  refine WorstCaseCostBound.bind (A := 2) (B := 3)
    (worstCaseCostBound_query (.inr ⟨.inl (), ()⟩) (suffixCost _)) fun _ => ?_
  refine WorstCaseCostBound.bind (A := 3) (B := 0)
    (worstCaseCostBound_query (.inl true) (suffixCost _)) fun _ => ?_
  exact (worstCaseCostBound_pure _ _ _).mpr le_rfl

-- RuntimeQueryBounds 7, restated: the route is `suffixRoute … withAmbient`. On every composed
-- path and view, the routed suffix decision costs at most 5.
theorem routed_suffix_budget (p : Path bitCombined) (v : View bitCombined p) :
    WorstCaseCostBound (routedSuffix p v) (bitRawCost p) 5 := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  refine (suffix_budget _ _).simulateQ _ fun q => ?_
  rcases q with request | ⟨i | i, q⟩
  · exact worstCaseCostBound_query (.inl request) (bitRawCost _)
  · cases i
    cases q
    exact (routeSuffix_export guess v).symm ▸
      worstCaseCostBound_query (.inr ⟨.inl (), ()⟩) (bitRawCost (combinedPath guess))
  · exact i.elim

-- RuntimeQueryBounds 11: the runtime setup samples the hidden bit once.
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
-- import query, for every guess and secret. The proof reflects the cost through the history
-- observation, as in the frozen row.
theorem import_budget (guess : Bool) (secret : Nat) :
    WorstCaseCostBound (bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)))
      importCost 1 := by
  refine (worstCaseCostBound_map_iff _
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) importCost 1).mp ?_
  rw [guess_history]
  exact (worstCaseCostBound_map_iff _ _ importCost 1).mpr (worstCaseCostBound_query () importCost)

end Interaction.Core.QueryCostTests

/-! ## Query profiles: `PhasedRun.lean` -/

namespace Interaction.Core.QueryCostTests
open Interaction.Core.PhasedRunTests

/-- The prover's ambient log of the logged run. -/
def proverLog (payload hidden : Nat) (bit : Bool) : QueryLog PhasedRunTests.ambient :=
  ((simulateQ (logger bit) ((verifier true).runWithLog () noData
    (prover payload hidden))).run []).1.2.1

-- PhasedRun 3, restated: phases are retired (D6), and the query profile is `QueryLog.countQ`. For
-- every payload, private output and challenge, the prover's ambient log is the two setup queries
-- followed by the queries 1, 4 and 5, so query 9 counts twice: `2 + 0` over the two segments.
theorem proverLog_eq (payload hidden : Nat) (bit : Bool) :
    proverLog payload hidden bit = [⟨9, ()⟩, ⟨9, ()⟩] ++ [⟨1, ()⟩, ⟨4, ()⟩, ⟨5, ()⟩] := by
  kernel_rfl

example (payload hidden : Nat) (bit : Bool) :
    (proverLog payload hidden bit).countQ (· = 9) = 2 := by
  rw [proverLog_eq, QueryLog.countQ_append]
  rfl

end Interaction.Core.QueryCostTests
