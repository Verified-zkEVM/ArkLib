/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun

/-!
# Query cost after changing a returned value

A pure map changes neither the random-oracle queries nor their distinct-key charge.
-/

@[expose] public section

open OracleSpec MeasureTheory

namespace OracleComp

/-- Mapping a returned value preserves the ordered oracle log and final cache. -/
theorem randomOracleLoggedRun_mapResult {D A B : Type} {R : D → Type}
    [DecidableEq D] [∀ d, SampleableType (R d)]
    (program : OracleComp (unifSpec + ofFn R) A)
    (f : A → B) (cache : (ofFn R).QueryCache) :
    randomOracleLoggedRun (f <$> program) cache =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun program cache := by
  simp [randomOracleLoggedRun, simulateQ_map, StateT.run_map]

/-- Applying a pure function to the result preserves the expected weighted distinct-key cost.
The returned value may itself represent failure; its executed queries are still counted. -/
theorem expectedFreshQueryCharge_map {D A B : Type} {R : D → Type}
    [DecidableEq D] [∀ d, SampleableType (R d)]
    (program : OracleComp (unifSpec + ofFn R) A)
    (f : A → B) (weight : D → ENNReal) :
    expectedFreshQueryCharge (f <$> program) weight =
      expectedFreshQueryCharge program weight := by
  let : MeasurableSpace ((A × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  let : MeasurableSpace ((B × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  unfold expectedFreshQueryCharge
  rw [randomOracleLoggedRun_mapResult, lintegral_evalDist_map_of_discrete]

end OracleComp
