/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Hamming ball volume

The number of words of `Σ^n`, with `|Σ| = q`, within absolute Hamming distance `⌊δ * n⌋` of a
fixed centre:

  `Vol_q(δ, n) = ∑ i ∈ range (⌊δ * n⌋ + 1), (n choose i) * (q-1) ^ i` .

## Main definitions

* `CodingTheory.hammingBallVolume`

## Main statements

* `CodingTheory.hammingBallVolume_zero_radius` — `Vol_q(0, n) = 1`.
* `CodingTheory.card_filter_hammingDist_eq` — the shell count
  `#{x | Δ(y, x) = i} = (n choose i) * (q - 1) ^ i`.
* `CodingTheory.hammingBallVolume_eq_ncard_hammingBall` — the volume is the cardinality of
  `Code.hammingBall`, for any centre.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace CodingTheory

/-- The volume of the Hamming ball of relative radius `δ` over an alphabet of size `q` and
block length `n`:

  `Vol_q(δ, n) = ∑ i ∈ range (⌊δ * n⌋ + 1), (n choose i) * (q-1) ^ i` .

This counts the words within absolute Hamming distance `⌊δ * n⌋` of a fixed centre, and is
independent of the centre (`hammingBallVolume_eq_ncard_hammingBall`).

Noncomputable because `Nat.floor` on `ℝ` is. The intended domain is `0 < δ < 1` and `q ≥ 2`;
outside it the formula is a total extension, with the floor clamping to `0` for `δ ≤ 0`. -/
noncomputable def hammingBallVolume (q : ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i

/-- A Hamming ball of zero radius contains exactly one word, its centre. -/
@[simp]
lemma hammingBallVolume_zero_radius (q n : ℕ) : hammingBallVolume q 0 n = 1 := by
  simp [hammingBallVolume]

/-- The number of words at Hamming distance exactly `i` from a fixed `y` is
`(n choose i) * (q - 1) ^ i`, where `n = |ι|` and `q = |F|`, independent of `y`.

The proof splits the words by their disagreement set `S = {j | x j ≠ y j}`, an `i`-element
subset of `ι`, on which each coordinate ranges over `F \ {y j}`. -/
lemma card_filter_hammingDist_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Fintype F] [DecidableEq F] (y : ι → F) (i : ℕ) :
    (Finset.univ.filter (fun x : ι → F ↦ hammingDist y x = i)).card
      = Nat.choose (Fintype.card ι) i * (Fintype.card F - 1) ^ i := by
  classical
  -- Disagreement set of `x` from `y`. By `hammingDist` def, `(dis x).card = hammingDist y x`.
  let dis : (ι → F) → Finset ι := fun x ↦ Finset.univ.filter (fun j ↦ y j ≠ x j)
  have h_dis_card : ∀ x, (dis x).card = hammingDist y x := fun _ ↦ rfl
  -- Step 1: split LHS by the disagreement set.
  rw [Finset.card_eq_sum_card_fiberwise (f := dis)
      (t := Finset.univ.powersetCard i)
      (H := by
        intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ,
          true_and, h_dis_card, hx])]
  -- Step 2: each fiber `{x | dis x = S}` has `(Fintype.card F - 1) ^ i` words.
  have h_fiber : ∀ S ∈ Finset.univ.powersetCard i,
      ((Finset.univ.filter (fun x : ι → F ↦ hammingDist y x = i)).filter
          (fun x ↦ dis x = S)).card = (Fintype.card F - 1) ^ i := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    -- Drop the outer "hammingDist y x = i" filter (implied by `dis x = S`).
    have h_simp : (Finset.univ.filter (fun x : ι → F ↦ hammingDist y x = i)).filter
        (fun x ↦ dis x = S) = Finset.univ.filter (fun x : ι → F ↦ dis x = S) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro h_dis
      rw [← h_dis_card, h_dis, hS.2]
    rw [h_simp]
    -- Build a bijection: `{x | dis x = S} ≃ (j : ι) → (if j ∈ S then F\{y j} else {y j})`.
    have h_set_eq : Finset.univ.filter (fun x : ι → F ↦ dis x = S) =
        ((Finset.univ : Finset ι).pi
          (fun j ↦ if j ∈ S then ({y j}ᶜ : Finset F) else ({y j} : Finset F))).image
        (fun f j ↦ f j (Finset.mem_univ j)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_pi]
      constructor
      · intro h_dis_eq
        refine ⟨fun j _ ↦ x j, ?_, rfl⟩
        intro j _
        by_cases hj : j ∈ S
        · simp only [if_pos hj, Finset.mem_compl, Finset.mem_singleton]
          have : j ∈ dis x := by rw [h_dis_eq]; exact hj
          simp only [dis, Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact fun heq ↦ this heq.symm
        · simp only [if_neg hj, Finset.mem_singleton]
          have : j ∉ dis x := by rw [h_dis_eq]; exact hj
          simp only [dis, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
          exact this.symm
      · rintro ⟨f, hf_mem, rfl⟩
        ext j
        simp only [dis, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfj := hf_mem j trivial
        by_cases hj : j ∈ S
        · rw [if_pos hj] at hfj
          simp only [Finset.mem_compl, Finset.mem_singleton] at hfj
          simp only [hj, iff_true]
          exact fun heq ↦ hfj heq.symm
        · rw [if_neg hj] at hfj
          simp only [Finset.mem_singleton] at hfj
          simp only [hj, iff_false, not_not]
          exact hfj.symm
    rw [h_set_eq, Finset.card_image_of_injective _ (by
        intro f g hfg
        ext j hj
        exact congrFun hfg j), Finset.card_pi]
    -- Replace each factor by `if j ∈ S then |F|-1 else 1`.
    have h_prod_eq : (∏ j ∈ (Finset.univ : Finset ι),
          ((if j ∈ S then ({y j}ᶜ : Finset F) else ({y j} : Finset F)).card)) =
        ∏ j ∈ (Finset.univ : Finset ι),
          (if j ∈ S then (Fintype.card F - 1) else 1) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · rw [if_pos hj, if_pos hj, Finset.card_compl, Finset.card_singleton]
      · rw [if_neg hj, if_neg hj, Finset.card_singleton]
    rw [h_prod_eq, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    -- `(univ.filter (· ∈ S)).card = S.card = i`.
    rw [Finset.filter_univ_mem]; exact congrArg _ hS.2
  rw [Finset.sum_congr rfl h_fiber, Finset.sum_const, smul_eq_mul,
      Finset.card_powersetCard, Finset.card_univ]

open Classical in
/-- The volume is the cardinality of `Code.hammingBall y ⌊δ * n⌋`, for every centre `y`:
partition the ball by exact distance and apply `card_filter_hammingDist_eq`.

No `DecidableEq` hypothesis is exposed, `Code.hammingBall` carrying its decidability data
under `open Classical in`. -/
theorem hammingBallVolume_eq_ncard_hammingBall
    {ι : Type*} [Fintype ι] {F : Type*} [Fintype F] (δ : ℝ) (y : ι → F) :
    hammingBallVolume (Fintype.card F) δ (Fintype.card ι)
      = (Code.hammingBall y (⌊δ * Fintype.card ι⌋₊)).ncard := by
  classical
  set r : ℕ := ⌊δ * Fintype.card ι⌋₊
  -- Step 1: convert RHS ncard → Finset.card with explicit filter.
  have h_rhs :
      (Code.hammingBall y r).ncard
        = (Finset.univ.filter (fun x : ι → F ↦ hammingDist y x ≤ r)).card := by
    have h_finite : (Code.hammingBall y r).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ h_finite]
    apply Finset.card_bij (fun x _ ↦ x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Set.Finite.mem_toFinset, Code.hammingBall, Set.mem_setOf_eq] at hx
      convert hx using 2
    · intros; assumption
    · intro x hx
      refine ⟨x, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Set.Finite.mem_toFinset, Code.hammingBall, Set.mem_setOf_eq]
      convert hx using 2
  -- Step 2: partition by exact distance.
  have h_partition :
      (Finset.univ.filter (fun x : ι → F ↦ hammingDist y x ≤ r)).card
        = ∑ i ∈ Finset.range (r + 1),
            (Finset.univ.filter (fun x : ι → F ↦ hammingDist y x = i)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_univ, true_and]
      refine ⟨fun h ↦ ⟨hammingDist y x, by omega, rfl⟩,
              fun ⟨i, hi, hd⟩ ↦ ?_⟩
      omega
    · -- disjointness
      intro a _ b _ hab
      simp only [Finset.disjoint_filter, Finset.mem_univ, true_implies]
      intro _ hxa hxb
      exact hab (hxa.symm.trans hxb)
  -- Combine.
  rw [h_rhs, h_partition]
  unfold hammingBallVolume
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  exact (card_filter_hammingDist_eq y i).symm

end CodingTheory
