/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension

/-!
# Acceptance cases for the dimension of weighted-support spaces

These cases check eligibility of a concrete exponent through its coordinates, compute the
staircase lower bound `5` on a dimension with two higher-jet tuples, evaluate the cubic lower bound
at one tuple, and derive the source's `card_weightedSupportSlot_le`, stated for the dependent slot
type, from `sum_count_le_card_weightedSupportExponents`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative Finset

/-! ### Coordinates -/

/-- For `d = 2`, `D = 2`, `W = 1`, `L = 4`, the exponent `X Y₂` has higher-jet weight `1 ≤ 1`
and coarse weight `1 + 2 * 1 = 3 < 4`. -/
example : WeightedSupportEligible 2 2 1 4
    ((jetExponentCoordinatesEquiv (d := 2) (by norm_num)).symm (1, 0, 0, fun _ => 1)) :=
  (weightedSupportEligible_coordinates_iff (by norm_num) 1 0 0 _).mpr ⟨by decide, by norm_num⟩

/-- The same exponent is not eligible at `L = 3`: the cutoff is strict. -/
example : ¬ WeightedSupportEligible 2 2 1 3
    ((jetExponentCoordinatesEquiv (d := 2) (by norm_num)).symm (1, 0, 0, fun _ => 1)) := by
  rw [weightedSupportEligible_coordinates_iff (by norm_num)]
  norm_num

/-! ### Concrete lower bounds -/

/-- For `d = 2`, `D = 1`, `W = 1`, `L = 2` the higher-jet tuples are `c = 0` and `c = 1`. They
contribute `count 1 2 = 4` (the triples of sum at most `1`) and `count 1 1 = 1` (the triple
`(0, 0, 0)` with `Y₂`), so the dimension is at least `5`. -/
example : 5 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 2 1 2 one_pos) := by
  refine le_trans (le_of_eq ?_) (sum_count_le_finrank_weightedSupportSpace ℚ (d := 2) (W := 1)
    (L := 2) (by norm_num) one_pos)
  have hs : natWeightedSimplex (fun i : Fin (2 - 1) => i.val + 1) 1 = {fun _ => 0, fun _ => 1} := by
    decide
  have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by exact_mod_cast Nat.ceil_natCast 1
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  rw [hs, sum_pair (by decide)]
  norm_num [CubicStaircase.count, h1, h2, Finset.sum_range_succ]

/-- The cubic lower bound at `d = 1`, `D = 1`, `W = 0`, `L = 3`: the only higher-jet tuple is
empty and contributes `3 ^ 3 / 6 = 9 / 2`, so the dimension is at least `5`. -/
example : 5 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 3 one_pos) := by
  have h := weightedSupport_dimension_ge_cubic_sum ℚ (d := 1) (W := 0) (L := 3) (by norm_num)
    one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by decide
  rw [hs, sum_singleton] at h
  norm_num at h
  have h4 : (4 : ℝ) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 3 one_pos) := by linarith
  exact_mod_cast h4

/-! ### The source-shaped slot count -/

/-- The source's `card_weightedSupportSlot_le` with `card_weightedSupportSlot_eq`: its dependent
slot type `WeightedSupportSlot D d W L` is the sigma type below, and its cardinality is at most
the number of eligible exponents. -/
example {D d W : ℕ} {L : ℝ} (hd : 0 < d) (hD : 0 < D) :
    Fintype.card (Σ c : ↥(natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W),
        CubicStaircase.Slot D (L / D - ((∑ i, c.val i : ℕ) : ℝ))) ≤
      #(weightedSupportExponents D d W L hD) := by
  rw [Fintype.card_sigma]
  simp only [CubicStaircase.card_slot]
  rw [Finset.sum_coe_sort (natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W)
    (fun c => CubicStaircase.count D (L / D - ((∑ i, c i : ℕ) : ℝ)))]
  exact sum_count_le_card_weightedSupportExponents hd hD
