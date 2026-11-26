/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Cost
import ArkLibTest.Interaction.Oracle.Routing

/-!
# The worst-case cost of one exported oracle query

The routing tests' prefix output map `RoutingTests.exportMap` exports `input false + sent.1`.
`RoutingTests.exportMap_raw_trace` shows that one exported query makes exactly two bundle
queries. Here the same map gets a worst-case cost bound. At unit cost per bundle query, one
exported query costs at most two, and a query charged two units stays within two units after
routing through the map. A second program also makes an ambient query, which the target charges
less than the source. A last example shows that the bound covers completed paths only.
-/

open Interaction OracleComp
open Interaction.RoutingTests (prefixBundle exported exportMap)

namespace Interaction.ExportCostTests

/-- Each query costs one unit. -/
def unitCost {ι : Type} (spec : OracleSpec ι) : CostModel spec Nat := ⟨fun _ => 1⟩

/-- Every query to the exported oracle is charged two units. -/
def exportCost : CostModel (OracleSpec.emptySpec + exported.spec) Nat :=
  ⟨fun | .inl q => q.elim | .inr _ => 2⟩

/-- The exported query's implementation makes two unit-cost queries. -/
theorem exportMap_cost (q : exported.spec.Domain) :
    WorstCaseCostBound (exportMap.impl q) (unitCost prefixBundle.spec) 2 := by
  exact (worstCaseCostBound_query _ _).bind fun _ => (worstCaseCostBound_query _ _).bind
    fun _ => (worstCaseCostBound_pure _ _ (0 : Nat)).mpr le_rfl

-- A use of `OracleMap.withAmbient_worstCaseCost`: one exported query, charged two units, routed
-- through `exportMap` costs at most two unit-cost queries to the prefix bundle.
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
    (In := prefixBundle) (Out := exported)
    (ambient := OracleSpec.emptySpec) (sourceCost := exportCost) (targetCost := unitCost _)
    exportMap hquery (fun q => q.elim) exportMap_cost

/-- A nonempty ambient interface with one natural-number query. -/
abbrev amb : OracleSpec Unit := Unit →ₒ Nat

/-- The source charges an ambient query three units and an exported query two. -/
def srcCost : CostModel (amb + exported.spec) Nat := ⟨fun | .inl _ => 3 | .inr _ => 2⟩

/-- The target charges every query one unit, so ambient queries become cheaper. -/
def tgtCost : CostModel (amb + prefixBundle.spec) Nat := ⟨fun | .inl _ => 1 | .inr _ => 1⟩

/-- One ambient query followed by one exported query. -/
def prog : OracleComp (amb + exported.spec) Nat := do
  let _ ← liftM ((amb + exported.spec).query (.inl ()))
  liftM ((amb + exported.spec).query (.inr ⟨⟨⟩, ()⟩))

/-- At the source prices, `prog` costs at most three plus two. -/
theorem prog_cost : WorstCaseCostBound prog srcCost (3 + 2) := by
  unfold prog
  exact (worstCaseCostBound_query (.inl ()) srcCost).bind fun _ =>
    worstCaseCostBound_query (.inr ⟨⟨⟩, ()⟩) srcCost

-- The ambient hypothesis of `OracleMap.withAmbient_worstCaseCost` with a nonempty ambient
-- interface: the ambient query costs one unit after routing instead of three.
example : WorstCaseCostBound (simulateQ (exportMap.withAmbient amb) prog) tgtCost (3 + 2) :=
  OracleMap.withAmbient_worstCaseCost (In := prefixBundle) (Out := exported)
    exportMap prog_cost (fun _ => (by decide : (1 : Nat) ≤ 3)) exportMap_cost

-- `WorstCaseCostBound` bounds completed paths only. A query with an empty response type ends no
-- completed path, so a program that makes one, charged one unit, satisfies the bound zero.
example : WorstCaseCostBound ((Unit →ₒ Empty).query () : OracleComp (Unit →ₒ Empty) Empty)
    (⟨fun _ => (1 : Nat)⟩ : CostModel (Unit →ₒ Empty) Nat) 0 := by
  rw [worstCaseCostBound_iff_support_bound]
  intro z hz
  exact z.1.elim

end Interaction.ExportCostTests

run_cmd do
  for decl in [``Interaction.OracleMap.withAmbient_worstCaseCost] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
