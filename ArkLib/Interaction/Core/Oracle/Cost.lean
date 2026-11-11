/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Composition
public import VCVio.OracleComp.QueryTracking.CostModel.Simulation

/-!
# Weighted cost of routed oracle programs

Routing a decision through an oracle map with `OracleMap.withAmbient` keeps every ambient query
and replaces every resource query by the map's implementing program over the input resources. A
weighted bound on the routed program follows from a bound on the original program when each
ambient query costs no more after routing and each implementing program fits the charge of the
resource query it implements. This is VCVio's `WorstCaseCostBound.simulateQ` for the handler
`OracleMap.withAmbient`.

Query multiplicities of a recorded run are counted with VCVio's `QueryLog.countQ`, which adds
over appended logs (`QueryLog.countQ_append`).
-/

@[expose] public section

universe dX dY

namespace Interaction.Core
open OracleComp OracleSpec Oracle

/-- A weighted bound on a decision over the output resources transfers to the same decision routed
through an oracle map. Ambient queries are charged at most their original cost, and the program
implementing each output query, charged at the target cost of the input queries it makes, fits
the original charge of that output query. -/
theorem OracleMap.withAmbient_worstCaseCost {ι α ω : Type} {ambient : OracleSpec ι}
    {In : Resources.{0, 0, dX}} {Out : Resources.{0, 0, dY}}
    [AddCommMonoid ω] [Preorder ω] [IsOrderedAddMonoid ω]
    (route : OracleMap In Out) {program : OracleComp (ambient + Out.spec) α}
    {sourceCost : CostModel (ambient + Out.spec) ω}
    {targetCost : CostModel (ambient + In.spec) ω} {budget : ω}
    (hprogram : WorstCaseCostBound program sourceCost budget)
    (hambient : ∀ q, targetCost.queryCost (.inl q) ≤ sourceCost.queryCost (.inl q))
    (hroute : ∀ q, WorstCaseCostBound (route.impl q)
      ⟨fun r => targetCost.queryCost (.inr r)⟩ (sourceCost.queryCost (.inr q))) :
    WorstCaseCostBound (simulateQ (route.withAmbient ambient) program) targetCost budget := by
  refine hprogram.simulateQ _ fun q => ?_
  rcases q with q | q
  · change WorstCaseCostBound
      (liftM ((ambient + In.spec).query (.inl q)) : OracleComp (ambient + In.spec) _) targetCost _
    rw [worstCaseCostBound_iff_support_bound]
    intro z hz
    exact ((worstCaseCostBound_iff_support_bound _ _ _).mp
      (worstCaseCostBound_query (.inl q) targetCost) z hz).trans (hambient q)
  · exact (hroute q).simulateQ _ fun r => worstCaseCostBound_query (.inr r) targetCost

end Interaction.Core
