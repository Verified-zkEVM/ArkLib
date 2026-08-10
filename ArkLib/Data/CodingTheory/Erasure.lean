/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Erasure-decoding uniqueness

This file supplies the metric fact used by erasure decoders: below the minimum-distance
threshold, at most one codeword is consistent with a partially erased word. The underlying
exceptional-coordinate theorem is the more general
`Code.eq_of_disagreementCols_subset_of_card_lt_minDist` in `Basic/Distance.lean`; the result
here packages it for `Option`-valued observations.

ABF26 Definition 6.4 and Lemma 6.5 additionally concern a deterministic erasure-correction
algorithm and its `O((s · n)³)` running time. ArkLib currently has no cost model in which to
state that content. Merely existentially quantifying over an unrestricted mathematical
function would make “supports erasure correction” true of every code, so this module does not
introduce such a predicate or claim to formalize the algorithmic result.

## Main statements

* `CodingTheory.eq_of_consistent_with_erased` — uniqueness of the codeword consistent with a
  lightly-erased word.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26] (§6.2: Definition 6.4, Lemma 6.5)
* [Guruswami, V., Rudra, A., and Sudan, M., *Essential Coding Theory*][codingtheory]
    (Proposition 1.4.2(4): a code of minimum distance `d` corrects exactly `d − 1` erasures;
    Exercise 5.3 for the Gaussian-elimination running time, which is out of scope here)
* [Bordage, S., Chiesa, A., Guan, Z., and Manzur, I., *All Polynomial Generators Preserve
    Distance with Mutual Correlated Agreement*][BCGM25] (Definition 3.7,
    `LinearCode.projectedWord` — see the generalization note on
    `eq_of_consistent_with_erased`)
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- **Uniqueness pigeonhole for erasure decoding (ABF26 L6.5 core).** Two
codewords consistent with the same partially-erased word `f`, with strictly
fewer than `minDist C` erasures, are equal: they can disagree only on erased
coordinates, so their Hamming distance is below the code's minimum distance.

This is the `Option`-valued corollary of
`Code.eq_of_disagreementCols_subset_of_card_lt_minDist`; it does not duplicate the underlying
minimum-distance argument. -/
theorem eq_of_consistent_with_erased [DecidableEq F] {C : Set (ι → F)}
    {f : ι → Option F} {u v : ι → F} (hu : u ∈ C) (hv : v ∈ C)
    (hfu : ∀ i, f i = some (u i) ∨ f i = none)
    (hfv : ∀ i, f i = some (v i) ∨ f i = none)
    (hcard : (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) :
    u = v := by
  -- `u` and `v` agree wherever `f` is not erased.
  have hsub : disagreementCols u v ⊆ Finset.univ.filter (fun i ↦ f i = none) := by
    intro i hi
    rw [mem_disagreementCols] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hfu i with h1 | h1
    · rcases hfv i with h2 | h2
      · exact absurd (Option.some.inj (h1.symm.trans h2)) hi
      · exact h2
    · exact h1
  exact Code.eq_of_disagreementCols_subset_of_card_lt_minDist hu hv _ hsub hcard

end CodingTheory
