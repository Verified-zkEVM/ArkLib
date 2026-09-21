/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
public import ArkLib.Data.Probability.Instances

/-!
# Probability of exceptional shared-level tensor challenges

`ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement` counts the challenge
tuples at which a height-`h` binary tensor fold is exceptional: given a full-set level witness
with count `e`, at most `h * e * |F| ^ (h - 1)` of the `|F| ^ h` tuples are bad. This file divides
by `|F| ^ h`. When the `h` level challenges are drawn independently and uniformly from `F`, the
fold is exceptional with probability at most `h * e / |F|`, and outside this event every codeword
with `a` agreements with the folded word is the fold of codeword leaves with the same common
agreement set.

Probabilities are written with the `Pr_{let r ←$ᵖ S}[…]` notation and bounded by
`ENNReal.ofReal (B / |S|)`, the form used by
`CoreDefinitions.mcaError_le_of_exists_exceptional_set`.

## Main statements

* `TensorMCA.tensorFoldFamilyBad_probability_le`: the bound `h * e / |F|` for a family of leaf
  arrays folded with shared challenges.
* `TensorMCA.tensorFoldBad_probability_le`: the same bound for a single leaf array.
* `TensorMCA.prob_not_hasFullTensorDecomposition_le`: the probability that the fold has no full
  tensor decomposition is at most `h * e / |F|`.
* `TensorMCA.tensorFoldBad_probability_height_three`: the height-three instance `3 * e / |F|`.

## References

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ProximityGenerator/BinaryTensorFoldProbability.lean`:

* `tensorFoldBad_probability_le` is ported with the field weakened to a finite ring and the
  coordinate and alphabet types in arbitrary universes. Its proof is the special case
  `β = Unit` of the new family statement `tensorFoldFamilyBad_probability_le`.
* `tensorFoldBad_probability_height_three` is ported unchanged.
* `prob_not_hasFullTensorDecomposition_le` is new; it states the conclusion the source obtains by
  combining the probability bound with `hasFullTensorDecomposition_of_not_mem_bad`.
-/

@[expose] public section

namespace TensorMCA

open CoreDefinitions
open scoped ProbabilityTheory

variable {ι A : Type*} {F : Type} [Ring F] [Fintype F] [AddCommMonoid A] [Module F A]
  [Fintype ι] [DecidableEq ι] [DecidableEq A] {C : ModuleCode ι F A} {a e : ℕ}

/-- **Uniform challenges for a family fold.** If the `h` level challenges of a family fold are
drawn independently and uniformly from `F`, the levelwise good event fails with probability at
most `h * e / |F|`.

This is `tensorFoldFamilyBad_card_le` divided by `|F| ^ h`. At height `0` both sides are `0`,
since the bad set is empty; for `h ≥ 1` the factor `|F| ^ (h - 1) / |F| ^ h` is `1 / |F|`. -/
theorem tensorFoldFamilyBad_probability_le (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    {β : Type} [Fintype β] (u : β → (Fin h → Bool) → ι → A) :
    Pr_{let r ←$ᵖ (Fin h → F)}[r ∈ tensorFoldFamilyBad hlevel u] ≤
      ENNReal.ofReal ((h * e : ℕ) / (Fintype.card F : ℝ)) := by
  classical
  rw [Probability.prob_uniform_eq_ofReal]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow]
  apply ENNReal.ofReal_le_ofReal
  have hcard : ((tensorFoldFamilyBad hlevel u).card : ℝ) ≤
      ((h * e : ℕ) : ℝ) * (Fintype.card F : ℝ) ^ (h - 1) := by
    exact_mod_cast tensorFoldFamilyBad_card_le hlevel u
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have hzero : (tensorFoldFamilyBad hlevel u).card = 0 := by
      simpa using tensorFoldFamilyBad_card_le hlevel u
    simp [hzero]
  · have hpow : (Fintype.card F : ℝ) ^ h =
        (Fintype.card F : ℝ) ^ (h - 1) * Fintype.card F := by
      rw [← pow_succ, Nat.sub_add_cancel hh]
    calc
      _ ≤ (((h * e : ℕ) : ℝ) * (Fintype.card F : ℝ) ^ (h - 1)) / (Fintype.card F : ℝ) ^ h :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = ((h * e : ℕ) : ℝ) / Fintype.card F := by
        rw [hpow]
        field_simp

/-- **Uniform challenges for a single fold.** A height-`h` fold of one leaf array, with a full-set
level witness of count `e` and independent uniform level challenges, is exceptional with
probability at most `h * e / |F|`. Outside this event,
`hasFullTensorDecomposition_of_not_mem_bad` applies. -/
theorem tensorFoldBad_probability_le (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    (u : (Fin h → Bool) → ι → A) :
    Pr_{let r ←$ᵖ (Fin h → F)}[r ∈ tensorFoldBad hlevel u] ≤
      ENNReal.ofReal ((h * e : ℕ) / (Fintype.card F : ℝ)) :=
  tensorFoldFamilyBad_probability_le hlevel _

/-- **The decomposition holds with high probability.** With independent uniform level
challenges, the probability that some codeword with `a` agreements with the folded word is not
the fold of codeword leaves with the same common agreement set is at most `h * e / |F|`. -/
theorem prob_not_hasFullTensorDecomposition_le (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    (u : (Fin h → Bool) → ι → A) :
    Pr_{let r ←$ᵖ (Fin h → F)}[¬ HasFullTensorDecomposition C a r u] ≤
      ENNReal.ofReal ((h * e : ℕ) / (Fintype.card F : ℝ)) :=
  (Probability.Pr_le_Pr_of_implies _ _ (fun r ↦ r ∈ tensorFoldBad hlevel u)
    fun r hr ↦ by_contra fun hmem ↦ hr (hasFullTensorDecomposition_of_not_mem_bad hlevel r u hmem)
    ).trans (tensorFoldBad_probability_le hlevel u)

/-- **Height three.** Three shared challenge levels cost at most three level exceptional counts:
the fold is exceptional with probability at most `3 * e / |F|`. -/
theorem tensorFoldBad_probability_height_three (hlevel : FullSetLevelWitness C a e)
    (u : (Fin 3 → Bool) → ι → A) :
    Pr_{let r ←$ᵖ (Fin 3 → F)}[r ∈ tensorFoldBad hlevel u] ≤
      ENNReal.ofReal ((3 * e : ℕ) / (Fintype.card F : ℝ)) :=
  tensorFoldBad_probability_le hlevel u

end TensorMCA
