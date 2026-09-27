/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Query substitution preserves access and weighted budgets

An allowed-query condition transfers through substitution when each allowed query's actual route
satisfies the target condition. A query's charge pays for its entire routing program, including
repeated calls. Cost bounds concern complete execution paths; access is a separate requirement.
-/

@[expose] public section

open OracleComp OracleSpec

namespace OracleComp

/-- Instrumenting ordinary bind retains both actions and adds their actual costs. -/
theorem costDist_bind {ι A B : Type} {spec : OracleSpec ι}
    (first : OracleComp spec A) (next : A → OracleComp spec B) (cm : CostModel spec Nat) :
    costDist (first >>= next) cm = (do
      let left ← costDist first cm
      let right ← costDist (next left.1) cm
      return (right.1, left.2 * right.2)) := by
  simp only [costDist, instrumentedRun, simulateQ_bind, WriterT.run_bind]
  apply bind_congr
  intro left
  rw [map_eq_bind_pure_comp]
  rfl

/-- A raw query incurs precisely the model's charge for that query tag. -/
theorem costDist_query {ι : Type} {spec : OracleSpec ι}
    (query : spec.Domain) (cm : CostModel spec Nat) :
    costDist (liftM (spec.query query)) cm = (do
      let response ← liftM (spec.query query)
      return (response, cm.queryCost query)) := by
  simp only [costDist, instrumentedRun, simulateQ_query, QueryImpl.withAddCost_apply]
  rfl

@[simp] theorem costDist_pure {ι A : Type} {spec : OracleSpec ι}
    (value : A) (cm : CostModel spec Nat) :
    costDist (pure value) cm = pure (value, 1) := by
  simp only [costDist, instrumentedRun, simulateQ_pure, WriterT.run_pure]

/-- Observing the result leaves every accumulated query cost unchanged. -/
theorem costDist_map {ι A B : Type} {spec : OracleSpec ι}
    (program : OracleComp spec A) (f : A → B) (cm : CostModel spec Nat) :
    costDist (f <$> program) cm =
      (fun result => (f result.1, result.2)) <$> costDist program cm := by
  simp [costDist, instrumentedRun, simulateQ_map, WriterT.run_map]

/-- A pure result observation preserves and reflects a complete-path cost bound. -/
theorem worstCaseCostBound_map_iff {ι A B : Type} {spec : OracleSpec ι}
    (program : OracleComp spec A) (f : A → B) (cm : CostModel spec Nat) (budget : Nat) :
    WorstCaseCostBound (f <$> program) cm budget ↔ WorstCaseCostBound program cm budget := by
  simp only [worstCaseCostBound_iff_support_bound, costDist_map, support_map, Set.mem_image]
  constructor
  · intro h result member
    exact h (f result.1, result.2) ⟨result, member, rfl⟩
  · intro h result member
    obtain ⟨original, member, rfl⟩ := member
    exact h original member

/-- Every continuation path can be preceded by a raw query with the same chosen response. -/
theorem mem_support_costDist_query_bind {ι A : Type} {spec : OracleSpec ι}
    (query : spec.Domain) (next : spec.Range query → OracleComp spec A)
    (response : spec.Range query) (cm : CostModel spec Nat)
    (result : A × Multiplicative Nat) (member : result ∈ support (costDist (next response) cm)) :
    (result.1, Multiplicative.ofAdd (cm.queryCost query) * result.2) ∈
      support (costDist (liftM (spec.query query) >>= next) cm) := by
  rw [costDist_bind, costDist_query]
  simp only [bind_assoc, pure_bind]
  apply (mem_support_bind_iff _ _ _).mpr
  refine ⟨response, ?_, ?_⟩
  · simp
  · apply (mem_support_bind_iff _ _ _).mpr
    exact ⟨result, member, by simp only [mem_support_pure_iff]; rfl⟩

/-- Every complete routed path has a source path whose charged cost bounds the actual raw cost. -/
theorem mem_support_costDist_simulateQ {ι κ A : Type}
    {source : OracleSpec ι} {target : OracleSpec κ}
    (route : QueryImpl source (OracleComp target)) (program : OracleComp source A)
    (sourceCost : CostModel source Nat) (targetCost : CostModel target Nat)
    (hstep : ∀ query, WorstCaseCostBound (route query) targetCost (sourceCost.queryCost query))
    (result : A × Multiplicative Nat)
    (member : result ∈ support (costDist (simulateQ route program) targetCost)) :
    ∃ sourceResult ∈ support (costDist program sourceCost),
      Multiplicative.toAdd result.2 ≤ Multiplicative.toAdd sourceResult.2 := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
    rw [simulateQ_pure, costDist_pure, mem_support_pure_iff] at member
    subst result
    exact ⟨(value, 1), by simp, le_rfl⟩
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, costDist_bind] at member
    rcases (mem_support_bind_iff _ _ _).mp member with ⟨step, stepMember, restMember⟩
    rcases (mem_support_bind_iff _ _ _).mp restMember with ⟨tail, tailMember, finalMember⟩
    rw [mem_support_pure_iff] at finalMember
    subst result
    obtain ⟨sourceResult, sourceMember, htail⟩ := ih step.1 tail tailMember
    refine ⟨(sourceResult.1, Multiplicative.ofAdd (sourceCost.queryCost query) * sourceResult.2),
      mem_support_costDist_query_bind query next step.1 sourceCost sourceResult sourceMember, ?_⟩
    have hcost := hstep query step stepMember
    change Multiplicative.toAdd step.2 + Multiplicative.toAdd tail.2 ≤
      sourceCost.queryCost query + Multiplicative.toAdd sourceResult.2
    exact Nat.add_le_add hcost htail

/-- Substitution charges every actual raw route query against its source-query budget.
The premise and conclusion use the same route, including branches that issue several queries. -/
theorem worstCaseCostBound_simulateQ {ι κ A : Type}
    {source : OracleSpec ι} {target : OracleSpec κ}
    (route : QueryImpl source (OracleComp target)) (program : OracleComp source A)
    (sourceCost : CostModel source Nat) (targetCost : CostModel target Nat) (budget : Nat)
    (hprogram : WorstCaseCostBound program sourceCost budget)
    (hstep : ∀ query, WorstCaseCostBound (route query) targetCost (sourceCost.queryCost query)) :
    WorstCaseCostBound (simulateQ route program) targetCost budget := by
  intro result member
  obtain ⟨sourceResult, sourceMember, hcost⟩ :=
    mem_support_costDist_simulateQ route program sourceCost targetCost hstep result member
  exact hcost.trans (hprogram sourceResult sourceMember)

/-- The same concrete cost model composes sequential prefix and suffix budgets. -/
theorem worstCaseCostBound_bind {ι A B : Type} {spec : OracleSpec ι}
    (first : OracleComp spec A) (next : A → OracleComp spec B) (cm : CostModel spec Nat)
    (prefixBudget suffixBudget : Nat)
    (hfirst : WorstCaseCostBound first cm prefixBudget)
    (hnext : ∀ value, WorstCaseCostBound (next value) cm suffixBudget) :
    WorstCaseCostBound (first >>= next) cm (prefixBudget + suffixBudget) := by
  unfold WorstCaseCostBound instrumentedRun
  rw [simulateQ_bind]
  exact AddWriterT.pathwiseCostAtMost_bind hfirst hnext

/-- Every completed path of a raw query has the exact designated cost. -/
theorem worstCaseCostBound_query {ι : Type} {spec : OracleSpec ι}
    (query : spec.Domain) (cm : CostModel spec Nat) :
    WorstCaseCostBound (liftM (spec.query query)) cm (cm.queryCost query) := by
  intro result member
  change result ∈ support (costDist (liftM (spec.query query)) cm) at member
  rw [costDist_query] at member
  rcases (mem_support_bind_iff _ _ _).mp member with ⟨response, _, member⟩
  rw [mem_support_pure_iff] at member
  subst result
  exact le_rfl

end OracleComp

namespace OracleComp

/-- Availability follows the exact query programs substituted by the same route. -/
theorem allQueriesSatisfy_simulateQ {ι κ A : Type}
    {source : OracleSpec ι} {target : OracleSpec κ}
    (route : QueryImpl source (OracleComp target)) (program : OracleComp source A)
    (sourceAllowed : ι → Prop) (targetAllowed : κ → Prop)
    (hprogram : AllQueriesSatisfy program sourceAllowed)
    (hstep : ∀ query, sourceAllowed query → AllQueriesSatisfy (route query) targetAllowed) :
    AllQueriesSatisfy (simulateQ route program) targetAllowed := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    simp only [simulateQ_pure, allQueriesSatisfy_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hprogram
    rw [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (hstep query hprogram.1)
      (fun response => ih response (hprogram.2 response))

end OracleComp
