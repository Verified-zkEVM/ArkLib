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

end BadEventDS

end DuplexSpongeFS
