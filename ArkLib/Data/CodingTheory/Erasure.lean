/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Erasure-decoding uniqueness

The metric fact underlying erasure decoding: fewer than `minDist C` erasures leave at most one
codeword consistent with the observed word. Equivalently, a code of minimum distance `d`
corrects `d - 1` erasures.

The observations are modelled as an `Option`-valued word, `none` marking an erasure. This
file packages the general exceptional-coordinate theorem
`Code.eq_of_disagreementCols_subset_of_card_lt_minDist` for that shape; the correction
*algorithm* and its cost are out of scope, ArkLib having no cost model to state them in.

## Main statements

* `CodingTheory.eq_of_consistent_with_erased`

## References

* [Guruswami, V., Rudra, A., and Sudan, M., *Essential Coding Theory*][codingtheory]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- Two codewords consistent with the same partially-erased word `f`, where fewer than
`minDist C` coordinates are erased, are equal: they can disagree only on erased coordinates,
so their Hamming distance is below the minimum distance. -/
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
