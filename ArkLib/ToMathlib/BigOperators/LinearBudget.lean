/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite linear-budget arithmetic

Suppose each index `i` of a finite set carries a charge `x i` bounded by `c * h i + e * a i`,
where `h i` and `a i` are the index's shares of two budgets. If the shares of the first budget,
together with a separate nonnegative amount `r`, total at most `H`, and the shares of the second
budget total at most `B`, then `r` plus all charges is at most `c * H + e * B`, provided
`1 ≤ c` and `0 ≤ e`. The amount `r` is charged at rate one, so it costs no more than it would at
rate `c`.

Exceptional-set counts in mutual correlated agreement arguments are aggregated this way: every
irreducible factor of an interpolating polynomial contributes a count bounded linearly by its
height and root degree, the content contributes its height, and heights and root degrees add up
over the factorization.

For a finite set of columns with natural-number weights, `slotSurplusHeight` chooses a height from
the total weight and the difference between the number of columns and the row budget. The slot
sum at this height is strictly larger than the row budget times the number of coefficient slots
per row.

## Main statements

* `Finset.add_sum_le_mul_add_mul_of_le`: the aggregated bound in an ordered semiring.
* `Finset.sum_tsub_add_sum_eq_card_mul` and `Finset.slotSurplusHeight`: exact finite slot counts
  and their canonical height.
* `Finset.rows_mul_slotSurplusHeight_add_one_lt_sum_tsub`: the strict slot-surplus bound.
-/

@[expose] public section

namespace Finset

open scoped BigOperators

/-- If each charge satisfies `x i ≤ c * h i + e * a i`, the shares `h i` together with `r` total
at most `H`, and the shares `a i` total at most `B`, then `r + ∑ i ∈ s, x i ≤ c * H + e * B`.

The hypothesis `1 ≤ c` lets the amount `r`, charged at rate one, be absorbed at rate `c`; it also
gives `0 ≤ c`, which is needed to scale the first budget. The hypothesis `0 ≤ r` is needed as
well: with `s = ∅`, `r = H = -1`, `c = 2` and `e = B = 0` the conclusion reads `-1 ≤ -2`. The
hypothesis `0 ≤ e` is needed to scale the second budget. -/
theorem add_sum_le_mul_add_mul_of_le {ι R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (s : Finset ι) {x h a : ι → R} {r c e H B : R}
    (hr : 0 ≤ r) (hc : 1 ≤ c) (he : 0 ≤ e)
    (hx : ∀ i ∈ s, x i ≤ c * h i + e * a i)
    (hH : r + ∑ i ∈ s, h i ≤ H) (hB : ∑ i ∈ s, a i ≤ B) :
    r + ∑ i ∈ s, x i ≤ c * H + e * B :=
  calc
    r + ∑ i ∈ s, x i ≤ c * r + ∑ i ∈ s, (c * h i + e * a i) :=
      add_le_add (le_mul_of_one_le_left hr hc) (sum_le_sum hx)
    _ = c * (r + ∑ i ∈ s, h i) + e * ∑ i ∈ s, a i := by
      rw [sum_add_distrib, mul_add, mul_sum, mul_sum, add_assoc]
    _ ≤ c * H + e * B :=
      add_le_add (mul_le_mul_of_nonneg_left hH (zero_le_one.trans hc))
        (mul_le_mul_of_nonneg_left hB he)

/-- At height `h`, the coefficient slots for weights `w i` together with the weights themselves
form a rectangle whenever every weight is at most `h + 1`. -/
theorem sum_tsub_add_sum_eq_card_mul {ι : Type*} (s : Finset ι) (w : ι → ℕ) (h : ℕ)
    (hw : ∀ i ∈ s, w i ≤ h + 1) :
    (s.sum fun i ↦ h + 1 - w i) + s.sum w = s.card * (h + 1) := by
  rw [← Finset.sum_add_distrib]
  calc
    s.sum (fun i ↦ (h + 1 - w i) + w i) = s.sum fun _ ↦ h + 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.sub_add_cancel (hw i hi)]
    _ = s.card * (h + 1) := by simp

/-- The least height at least `floor` whose product with the support surplus exceeds its total
weight, using the positive part `card - rows` as the divisor. -/
def slotSurplusHeight {ι : Type*} (s : Finset ι) (w : ι → ℕ) (floor rows : ℕ) : ℕ :=
  max floor (s.sum w / (s.card - rows))

/-- If `rows` is below the number of columns and every weight is at most `floor`, then
`slotSurplusHeight` gives strictly more coefficient slots than rows. -/
theorem rows_mul_slotSurplusHeight_add_one_lt_sum_tsub {ι : Type*} (s : Finset ι)
    (w : ι → ℕ) (floor rows : ℕ) (hrows : rows < s.card)
    (hw : ∀ i ∈ s, w i ≤ floor) :
    rows * (slotSurplusHeight s w floor rows + 1) <
      s.sum (fun i ↦ slotSurplusHeight s w floor rows + 1 - w i) := by
  let N := s.card
  let W := s.sum w
  let gap := N - rows
  let H := slotSurplusHeight s w floor rows
  have hgap : 0 < gap := by simpa [gap, N] using Nat.sub_pos_of_lt hrows
  have hfloor : W < (W / gap + 1) * gap :=
    (Nat.div_lt_iff_lt_mul hgap).mp (Nat.lt_succ_self (W / gap))
  have hfloor_le : W / gap ≤ H := by simp [H, slotSurplusHeight, W, gap, N]
  have hweight : W < gap * (H + 1) := by
    calc
      W < (W / gap + 1) * gap := hfloor
      _ ≤ (H + 1) * gap := Nat.mul_le_mul_right gap (Nat.add_le_add_right hfloor_le 1)
      _ = gap * (H + 1) := Nat.mul_comm _ _
  have hslots : (s.sum fun i ↦ H + 1 - w i) + W = N * (H + 1) := by
    simpa [N, W] using
      (sum_tsub_add_sum_eq_card_mul s w H fun i hi =>
        (hw i hi).trans (show floor ≤ H + 1 by
          dsimp [H, slotSurplusHeight]
          exact Nat.le_trans (le_max_left _ _) (Nat.le_add_right H 1)))
  have hdecomp : N * (H + 1) = rows * (H + 1) + gap * (H + 1) := by
    rw [← Nat.add_mul]
    congr 1
    exact (Nat.add_sub_of_le hrows.le).symm
  change rows * (H + 1) < s.sum fun i ↦ H + 1 - w i
  omega

end Finset
