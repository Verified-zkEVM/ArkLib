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

ABF26 Definition 2.4: the volume of a Hamming ball.

  `Vol_q(δ, n) := ∑_{i=0}^{⌊δ · n⌋} (n choose i) · (q-1)^i`

Counts the number of words in `Σ^n` (with `|Σ| = q`) within absolute Hamming
distance `⌊δ · n⌋` of any fixed center. Independent of the choice of center.

Used in:

- ABF26 Lemma 3.7 (Elias lower bound for `|Λ(C, δ)|`).
- ABF26 Corollary 3.8 (volume-based lower bound).

This file also provides the bridge between the volume function and the existing
`hammingBall` set in `ListDecodability.lean`.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace CodingTheory

/-- **ABF26 Definition 2.4.** Volume of the Hamming ball of relative radius `δ` over
an alphabet of size `q` and block length `n`:

  `Vol_q(δ, n) := ∑_{i=0}^{⌊δ · n⌋} (n choose i) · (q-1)^i`.

Counts the number of words in `Σ^n` (with `|Σ| = q`) within absolute Hamming distance
`⌊δ · n⌋` of any fixed center. Independent of the choice of center.

Used in `ABF26-L3.7` (Elias lower bound) and `ABF26-C3.8` (volume-based lower bound).

Noncomputable because the floor `⌊δ · n⌋₊` over `ℝ` is noncomputable (Mathlib's
`Nat.floor` on `ℝ` depends on a `noncomputable` `linearOrder` instance). -/
noncomputable def hammingBallVolume (q : ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i

/-- Boundary case: a Hamming ball of zero radius contains exactly one word
(the center itself). The single summand `i = 0` contributes
`(n choose 0) · (q-1)^0 = 1`. -/
@[simp]
lemma hammingBallVolume_zero_radius (q n : ℕ) : hammingBallVolume q 0 n = 1 := by
  simp [hammingBallVolume]

/-- **Key combinatorial identity.** The number of vectors `x : ι → F` at Hamming
distance exactly `i` from a fixed `y` is `C(n, i) · (q-1)^i`, where `n = |ι|` and
`q = |F|`. Independent of `y`.

Proof via an explicit bijection: `x` corresponds to the pair `(S, f)` where
`S := {j | x j ≠ y j}` (an `i`-element subset of `ι`) and `f : S → F` is the
restriction of `x` to `S` (each value forced into `F \ {y j}`). Counting:
`Σ S ∈ powersetCard i univ, ∏ j ∈ S, (|F| - 1) = C(n, i) · (q-1)^i`. -/
lemma card_filter_hammingDist_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F] (y : ι → F) (i : ℕ) :
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

/-- **Bridge to `hammingBall`.** The volume function counts the cardinality of the
existing `hammingBall` (set of words within radius `⌊δ·n⌋` of any fixed center). The
identity collapses to the standard combinatorial fact
`#{x ∈ F^n : Δ(x, y) ≤ r} = ∑_{i ≤ r} C(n, i) · (q-1)^i` independent of `y`.

This links the ArkLib `ListDecodability.hammingBall` (set-form, used elsewhere in the
list-decoding development) to ABF26 Definition 2.4's `Vol_q(δ, n)` (cardinality form).

Proof: partition `hammingBall y r` by exact distance via `card_filter_hammingDist_eq`,
then sum. -/
theorem hammingBallVolume_eq_ncard_hammingBall
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F] (δ : ℝ) (y : ι → F) :
    hammingBallVolume (Fintype.card F) δ (Fintype.card ι)
      = (ListDecodable.hammingBall (F := F) y (⌊δ * Fintype.card ι⌋₊)).ncard := by
  set r : ℕ := ⌊δ * Fintype.card ι⌋₊
  -- Step 1: convert RHS ncard → Finset.card with explicit filter.
  have h_rhs :
      (ListDecodable.hammingBall (F := F) y r).ncard
        = (Finset.univ.filter (fun x : ι → F ↦ hammingDist y x ≤ r)).card := by
    have h_finite : (ListDecodable.hammingBall (F := F) y r).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ h_finite]
    apply Finset.card_bij (fun x _ ↦ x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Set.Finite.mem_toFinset, ListDecodable.hammingBall, Set.mem_setOf_eq] at hx
      convert hx using 2
    · intros; assumption
    · intro x hx
      refine ⟨x, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Set.Finite.mem_toFinset, ListDecodable.hammingBall, Set.mem_setOf_eq]
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
