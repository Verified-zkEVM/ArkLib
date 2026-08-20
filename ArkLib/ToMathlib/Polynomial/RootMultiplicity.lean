/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Algebra.Polynomial.Roots

/-!
# Additional polynomial root-multiplicity lemmas

## Main statements

* `Polynomial.sum_rootMultiplicity_le_natDegree` — root multiplicities summed over a finite
  set are bounded by the degree.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

namespace Polynomial

/-- The sum of the root multiplicities of a polynomial over a finite set of points is at most
its natural degree. -/
lemma sum_rootMultiplicity_le_natDegree {F : Type*} [Field F]
    {W : Polynomial F} (S : Finset F) :
    ∑ a ∈ S, W.rootMultiplicity a ≤ W.natDegree := by
  classical
  have hle : (∑ a ∈ S, Multiset.replicate (W.rootMultiplicity a) a) ≤ W.roots := by
    rw [Multiset.le_iff_count]
    intro b
    rw [Multiset.count_sum', Polynomial.count_roots]
    calc ∑ a ∈ S, Multiset.count b (Multiset.replicate (W.rootMultiplicity a) a)
        = ∑ a ∈ S, (if a = b then W.rootMultiplicity a else 0) :=
          Finset.sum_congr rfl fun a _ => by rw [Multiset.count_replicate]
      _ ≤ W.rootMultiplicity b := by
          rw [Finset.sum_ite_eq' S b]
          split <;> simp
  have hcard := Multiset.card_le_card hle
  rw [Multiset.card_sum] at hcard
  simp only [Multiset.card_replicate] at hcard
  exact hcard.trans (Polynomial.card_roots' W)

end Polynomial
