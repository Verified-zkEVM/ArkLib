/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Complete-path costs with determined responses

When a deterministic handler gives the only inhabitant of every response type, the free
instrumented computation has exactly one execution path: the handler's. Its worst-case cost bound
is then the cost recorded by running that handler once. Certified instruction sets, whose response
types are singleton subtypes, have this property. Without it, a worst-case bound still bounds the
cost recorded by any deterministic handler, since that execution is one path.

These are generic VCVio cost laws, candidates for upstreaming next to `WorstCaseCostBound`.
-/

@[expose] public section

open OracleSpec

namespace OracleComp

variable {ι ω A : Type} {spec : OracleSpec ι} [AddCommMonoid ω]

/-- A deterministic handler's execution, with its recorded cost, is one path of the instrumented
computation. -/
theorem run_withAddCost_mem_support_costDist (answer : QueryImpl spec Id)
    (oa : OracleComp spec A) (cm : CostModel spec ω) :
    (simulateQ (answer.withAddCost cm.queryCost) oa).run ∈ support (costDist oa cm) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp [costDist, instrumentedRun]
    rfl
  | query_bind t k ih =>
    rw [costDist_query_bind]
    simp only [support_bind, support_liftM_query, Set.mem_iUnion, Set.mem_univ, support_map,
      Set.mem_image, exists_true_left]
    refine ⟨answer t, _, ih (answer t), ?_⟩
    simp [simulateQ_bind, simulateQ_query, QueryImpl.withAddCost_apply, WriterT.run_bind]
    rfl

/-- A worst-case cost bound bounds the cost recorded by any deterministic handler. -/
theorem _root_.WorstCaseCostBound.runAdd_withAddCost_le [Preorder ω] {oa : OracleComp spec A}
    {cm : CostModel spec ω} {B : ω} (h : WorstCaseCostBound oa cm B)
    (answer : QueryImpl spec Id) :
    (simulateQ (answer.withAddCost cm.queryCost) oa).runAdd.2 ≤ B :=
  (worstCaseCostBound_iff_support_bound oa cm B).mp h _
    (run_withAddCost_mem_support_costDist answer oa cm)

/-- If every response equals the handler's answer, the instrumented computation has the handler's
execution as its only path. -/
theorem support_costDist_of_forall_eq_answer (answer : QueryImpl spec Id)
    (hanswer : ∀ t (u : spec.Range t), u = answer t) (oa : OracleComp spec A)
    (cm : CostModel spec ω) :
    support (costDist oa cm) = {(simulateQ (answer.withAddCost cm.queryCost) oa).run} := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp [costDist, instrumentedRun]
    rfl
  | query_bind t k ih =>
    rw [costDist_query_bind]
    ext z
    simp only [support_bind, support_liftM_query, Set.mem_iUnion, Set.mem_univ, support_map,
      Set.mem_image, exists_true_left, ih, Set.mem_singleton_iff]
    have hrun : (simulateQ (answer.withAddCost cm.queryCost)
        (liftM (OracleSpec.query t) >>= k)).run =
        ((simulateQ (answer.withAddCost cm.queryCost) (k (answer t))).run.1,
          Multiplicative.ofAdd (cm.queryCost t + Multiplicative.toAdd
            (simulateQ (answer.withAddCost cm.queryCost) (k (answer t))).run.2)) := by
      simp [simulateQ_bind, simulateQ_query, QueryImpl.withAddCost_apply, WriterT.run_bind]
      rfl
    rw [hrun]
    constructor
    · rintro ⟨u, _, rfl, rfl⟩
      rw [← hanswer t u]
    · rintro rfl
      exact ⟨answer t, _, rfl, rfl⟩

/-- If every response equals the handler's answer, a worst-case cost bound is exactly a bound on
the cost of the handler's execution. -/
theorem worstCaseCostBound_iff_of_forall_eq_answer [Preorder ω] (answer : QueryImpl spec Id)
    (hanswer : ∀ t (u : spec.Range t), u = answer t) (oa : OracleComp spec A)
    (cm : CostModel spec ω) (B : ω) :
    WorstCaseCostBound oa cm B ↔
      (simulateQ (answer.withAddCost cm.queryCost) oa).runAdd.2 ≤ B := by
  rw [worstCaseCostBound_iff_support_bound, support_costDist_of_forall_eq_answer answer hanswer]
  simp [AddWriterT.runAdd]
  rfl

end OracleComp
