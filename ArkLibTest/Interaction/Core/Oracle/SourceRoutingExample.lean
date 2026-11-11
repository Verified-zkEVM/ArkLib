/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Cost
import ArkLibTest.Interaction.Core.Oracle.Routing

/-!
# The worst-case cost of one exported oracle query

The routing tests' prefix output map `RoutingTests.exportMap` exports `input false + sent.1`.
`RoutingTests.exportMap_raw_trace` shows that one exported query makes exactly two resource
queries. Here the same map gets a worst-case cost bound: at unit cost per resource query, one
exported query costs at most two, and a query charged two units stays within two units after
routing through the map.
-/

open Interaction.Core OracleComp
open Interaction.Core.RoutingTests (prefixResources exported exportMap)

namespace Interaction.Core.SourceRoutingExampleTests

/-- Each query costs one unit. -/
def unitCost {ι : Type} (spec : OracleSpec ι) : CostModel spec Nat := ⟨fun _ => 1⟩

/-- Every query to the exported oracle is charged two units. -/
def exportCost : CostModel (OracleSpec.emptySpec + exported.spec) Nat :=
  ⟨fun | .inl q => q.elim | .inr _ => 2⟩

/-- The exported query's implementation makes two unit-cost queries. -/
theorem exportMap_cost (q : exported.spec.Domain) :
    WorstCaseCostBound (exportMap.impl q) (unitCost prefixResources.spec) 2 := by
  exact (worstCaseCostBound_query _ _).bind fun _ => (worstCaseCostBound_query _ _).bind
    fun _ => (worstCaseCostBound_pure _ _ (0 : Nat)).mpr le_rfl

-- A use of `OracleMap.withAmbient_worstCaseCost`: one exported query, charged two units, routed
-- through `exportMap` costs at most two unit-cost queries to the prefix resources.
example : WorstCaseCostBound
    (simulateQ (exportMap.withAmbient OracleSpec.emptySpec)
      (liftM ((OracleSpec.emptySpec + exported.spec).query (.inr ⟨⟨⟩, ()⟩)) :
        OracleComp (OracleSpec.emptySpec + exported.spec) Nat))
    (unitCost _) 2 := by
  have hquery : WorstCaseCostBound
      (liftM ((OracleSpec.emptySpec + exported.spec).query (.inr ⟨⟨⟩, ()⟩)) :
        OracleComp (OracleSpec.emptySpec + exported.spec) Nat) exportCost 2 :=
    worstCaseCostBound_query (.inr ⟨⟨⟩, ()⟩) exportCost
  exact OracleMap.withAmbient_worstCaseCost
    (In := prefixResources) (Out := Resources.ofFamily exported)
    (ambient := OracleSpec.emptySpec) (sourceCost := exportCost) (targetCost := unitCost _)
    exportMap hquery (fun q => q.elim) exportMap_cost

end Interaction.Core.SourceRoutingExampleTests

run_cmd do
  for decl in [``Interaction.Core.OracleMap.withAmbient_worstCaseCost] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
