/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core

/-!
# Generic finite-target probability accounting

This module contains the experiment-independent counting layer behind the
finite-target collision bounds in Lemma 5.8.  It deliberately has no sponge,
trace, or simulator assumptions: callers supply the atom bound and this file
accounts for finite partitions and finite covers.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

/-- **GENERIC — disjoint refinement bound.** Splitting a predicate `P` by an `A`-valued readout
`X` gives a disjoint refinement, so the split probabilities sum to at most `Pr[P]`. -/
lemma sum_probEvent_and_eq_le {γ A : Type} [Fintype A]
    (exp : ProbComp γ) (P : γ → Prop) (X : γ → A) :
    ∑ a : A, Pr[ fun g => P g ∧ X g = a | exp] ≤ Pr[ fun g => P g | exp] := by
  classical
  simp_rw [probEvent_eq_tsum_indicator]
  rw [← Summable.tsum_finsetSum (fun a _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum (fun g => le_of_eq ?_)
  by_cases hP : P g
  · rw [Set.indicator_of_mem (show g ∈ {g' | P g'} from hP), Finset.sum_eq_single (X g)]
    · exact Set.indicator_of_mem (show g ∈ {g' | P g' ∧ X g' = X g} from ⟨hP, rfl⟩) _
    · intro b _ hb
      exact Set.indicator_of_notMem (fun h => hb h.2.symm) _
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [Set.indicator_of_notMem (show g ∉ {g' | P g'} from hP),
      Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (fun h => hP h.1) _)]

/-- **Disjoint-target sum bound (generic probability).** For a `ProbComp` and any `Option`-valued
readout `X`, the probabilities of the disjoint events `X = some c` sum (over all `c` in a `Fintype`)
to `≤ 1` — the `some c` events are a sub-family of the full `Option`-partition, which sums to
`Pr[True] ≤ 1` by `sum_probEvent_and_eq_le`. -/
lemma sum_probEvent_eq_some_le_one {α β : Type} [Fintype β]
    (exp : ProbComp α) (X : α → Option β) :
    ∑ c : β, Pr[ fun a => X a = some c | exp] ≤ 1 := by
  calc
    ∑ c : β, Pr[ fun a => X a = some c | exp]
        ≤ ∑ o : Option β, Pr[ fun a => X a = o | exp] := by
          rw [Fintype.sum_option]
          exact le_add_self
    _ = ∑ o : Option β, Pr[ fun a => True ∧ X a = o | exp] := by
      simp only [true_and]
    _ ≤ Pr[ fun _ => True | exp] := sum_probEvent_and_eq_le exp (fun _ => True) X
    _ ≤ 1 := probEvent_le_one

/-- **GENERIC — bind-stable relative bound.**
If every continuation of a probabilistic bind satisfies a relative bound
`Pr[A] ≤ Pr[B] / D`, then the whole bind satisfies the same relative bound.  This is the
probability-algebra step used to peel the initial `k_g ← 𝒟_Σ` sample and, more generally, to
thread Lemma-5.8 freshness contracts through monadic decompositions. -/
lemma probEvent_bind_rel_div_le {α β : Type}
    (mx : ProbComp α) (my : α → ProbComp β) (A B : β → Prop) (D : ℝ≥0∞)
    (h : ∀ x ∈ support mx, Pr[ A | my x] ≤ Pr[ B | my x] / D) :
    Pr[ A | mx >>= my] ≤ Pr[ B | mx >>= my] / D := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  rw [div_eq_mul_inv]
  calc
    ∑' x : α, Pr[= x | mx] * Pr[A | my x]
        ≤ ∑' x : α, Pr[= x | mx] * (Pr[B | my x] / D) := by
          refine ENNReal.tsum_le_tsum ?_
          intro x
          by_cases hx : x ∈ support mx
          · exact mul_le_mul' le_rfl (h x hx)
          · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = ∑' x : α, (Pr[= x | mx] * Pr[B | my x]) * D⁻¹ := by
          refine tsum_congr ?_
          intro x
          rw [div_eq_mul_inv, mul_assoc]
    _ = (∑' x : α, Pr[= x | mx] * Pr[B | my x]) * D⁻¹ := by
          rw [ENNReal.tsum_mul_right]

/-- **GENERIC — finite-cover union bound.**
If every occurrence of `A` has a witness in the finite index set `I`, and each witnessed event
has the stated weight, then `A` has at most the sum of those weights.  This packages the
cover-then-union-bound pattern used by the functional-conflict and finite-target arguments. -/
lemma probEvent_finite_cover_le_sum {α ι : Type} [DecidableEq ι]
    (exp : ProbComp α) (I : Finset ι) (A : α → Prop) (event : ι → α → Prop)
    (weight : ι → ℝ≥0∞)
    (hcover : ∀ a, A a → ∃ i ∈ I, event i a)
    (hbound : ∀ i ∈ I, Pr[ event i | exp] ≤ weight i) :
    Pr[ A | exp] ≤ ∑ i ∈ I, weight i := by
  calc
    Pr[ A | exp] ≤ Pr[ fun a => ∃ i ∈ I, event i a | exp] := by
      apply probEvent_mono
      intro a _ hA
      exact hcover a hA
    _ ≤ ∑ i ∈ I, Pr[ event i | exp] :=
      probEvent_exists_finset_le_sum I exp event
    _ ≤ ∑ i ∈ I, weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound i hi

end BadEventDS

end DuplexSpongeFS
