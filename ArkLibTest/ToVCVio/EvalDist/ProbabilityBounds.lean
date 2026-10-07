/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ToVCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.ProbComp

/-!
# Candidate-list union bound acceptance tests

The bounds apply to any computation, not only to uniform sampling. An empty set makes the event
impossible. A candidate whose event is certain is excluded by the predicate, so with no index
satisfying it the one-index bound holds at `ε = 0`. Tight instances over uniform challenges are in
`ArkLibTest/ProofSystem/RingSwitching/Packing/Batching.lean`.
-/

open scoped ENNReal

/-- The union bound over the empty set: no index has its event. -/
example {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α ι : Type} (mx : m α) (event : ι → α → Prop) :
    Pr{let x ← mx}[∃ i ∈ (∅ : Finset ι), event i x] ≤ 0 := by
  simpa using prEvent_exists_finset_le_card_mul ∅ mx event (ε := 1)
    fun _ h => absurd h (Finset.notMem_empty _)

/-- The only valid candidate `0` is correct, and its event is certain under a deterministic
computation; excluding it leaves probability `0`. -/
example : Pr{let x ← (pure 1 : ProbComp ℕ)}[∃ i : ℕ, (i = 0 ∧ i ≠ 0) ∧ x = 1] ≤ 0 :=
  prEvent_exists_and_le_of_subsingleton _ (fun i => i = 0 ∧ i ≠ 0) (fun _ x => x = 1)
    (fun _ h => absurd h.1 h.2) fun _ ha _ hb => ha.1.trans hb.1.symm

/-- Without the exclusion the same correct candidate has its event with probability `1`. -/
example : Pr{let x ← (pure 1 : ProbComp ℕ)}[∃ i : ℕ, i = 0 ∧ x = 1] = 1 := by
  simp
