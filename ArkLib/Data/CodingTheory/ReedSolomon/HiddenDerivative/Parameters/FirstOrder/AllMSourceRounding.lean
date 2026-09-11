/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateRounding

/-! # Exact source rounding for arbitrary first-order derivative caps -/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

private def allMSourceLinearSum (x : ℝ) : ℝ := x * (x - 1) / 2

private def allMSourceSquareSum (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem allMSource_sum_range_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = allMSourceLinearSum n := by
  induction n with
  | zero => simp [allMSourceLinearSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [allMSourceLinearSum]
      push_cast
      ring

private theorem allMSource_sum_range_sq_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = allMSourceSquareSum n := by
  induction n with
  | zero => simp [allMSourceSquareSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [allMSourceSquareSum]
      push_cast
      ring

private def allMSourceRoundingModel (z u c v : ℝ) : ℝ :=
  (z + v) * u * (u - v) / 2 - u * (u - v) * (2 * u - v) / 6 +
    u * ((z + v) * (c - u) - (c * (c - v) - u * (u - v)) / 2)

private theorem allMSourceRoundingModel_ge
    {z u c v beta : ℝ}
    (hz1 : 1 ≤ z) (hbz : beta ≤ z) (hbu : beta ≤ u) (hub : u ≤ beta + v)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hzc : z + v ≤ c) (hcz : c ≤ z + 2 * v) :
    beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      allMSourceRoundingModel z u c v := by
  have hconcave : allMSourceRoundingModel z u (z + v) v ≤
      allMSourceRoundingModel z u c v := by
    have hid : allMSourceRoundingModel z u c v -
        allMSourceRoundingModel z u (z + v) v =
          u / 2 * (c - (z + v)) * (z + 2 * v - c) := by
      unfold allMSourceRoundingModel
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hleft : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      allMSourceRoundingModel z u (z + v) v := by
    have hquad : 0 ≤
        (u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2 := by
      nlinarith [sq_nonneg ((u - z) + (beta - z)), sq_nonneg (u - z),
        sq_nonneg (beta - z)]
    have hbase : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
        u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6 := by
      have hid :
          (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) -
              (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) =
            (u - beta) / 6 *
              ((u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2) := by ring
      have hfac : 0 ≤ (u - beta) / 6 :=
        div_nonneg (sub_nonneg.mpr hbu) (by norm_num)
      nlinarith [mul_nonneg hfac hquad]
    have huz : u ≤ z + v := hub.trans (by
      simpa only [add_comm] using add_le_add_right hbz v)
    have hbracket : 0 ≤ z - u / 2 + v / 3 := by nlinarith
    have hround : 0 ≤ v * u * (z - u / 2 + v / 3) := by positivity
    have hid : allMSourceRoundingModel z u (z + v) v =
        (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) +
          v * u * (z - u / 2 + v / 3) := by
      unfold allMSourceRoundingModel
      ring
    rw [hid]
    linarith
  exact hleft.trans hconcave

private def allMSourceLowerCount (R a : ℝ) (m M L : ℕ) : ℝ :=
  ∑ t ∈ Finset.range L, (min t M : ℕ) * (m * a - R * t)

private theorem allMSourceLowerCount_normalized_eq_model
    {R z : ℝ} {m M L : ℕ} (hm : 0 < m) (hML : M ≤ L) :
    allMSourceLowerCount R (R * (z + (m : ℝ)⁻¹)) m M L / (m : ℝ) ^ 3 =
      R * allMSourceRoundingModel z ((M : ℝ) / m) ((L : ℝ) / m)
        ((m : ℝ)⁻¹) := by
  have hsplit :
      allMSourceLowerCount R (R * (z + (m : ℝ)⁻¹)) m M L =
        (R * (z + (m : ℝ)⁻¹)) * m * allMSourceLinearSum M -
          R * allMSourceSquareSum M +
          M * ((R * (z + (m : ℝ)⁻¹)) * m * (L - M) -
            R * (allMSourceLinearSum L - allMSourceLinearSum M)) := by
    rw [allMSourceLowerCount, ← Finset.sum_range_add_sum_Ico _ hML]
    have hfirst :
        (∑ t ∈ Finset.range M,
            (min t M : ℕ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) =
          (R * (z + (m : ℝ)⁻¹)) * m * allMSourceLinearSum M -
            R * allMSourceSquareSum M := by
      calc
        _ = ∑ t ∈ Finset.range M,
            ((t : ℝ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_left (Finset.mem_range.mp ht).le]
        _ = ∑ t ∈ Finset.range M,
            ((R * (z + (m : ℝ)⁻¹)) * m * (t : ℝ) - R * (t : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            allMSource_sum_range_cast, allMSource_sum_range_sq_cast]
    have htail :
        (∑ t ∈ Finset.Ico M L,
            (min t M : ℕ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) =
          M * ((R * (z + (m : ℝ)⁻¹)) * m * (L - M) -
            R * (allMSourceLinearSum L - allMSourceLinearSum M)) := by
      calc
        _ = ∑ t ∈ Finset.Ico M L,
            ((M : ℝ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_right (Finset.mem_Ico.mp ht).1]
        _ = _ := by
          have hsum (q : ℕ) :
              (∑ t ∈ Finset.range q,
                ((m : ℝ) * (R * (z + (m : ℝ)⁻¹)) - R * t)) =
                q * (m * (R * (z + (m : ℝ)⁻¹))) -
                  R * allMSourceLinearSum q := by
            induction q with
            | zero => simp [allMSourceLinearSum]
            | succ q ih =>
                rw [Finset.sum_range_succ, ih]
                simp only [allMSourceLinearSum]
                push_cast
                ring
          rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hML, hsum, hsum]
          ring
    exact congrArg₂ (fun x y : ℝ ↦ x + y) hfirst htail
  rw [hsplit]
  simp only [allMSourceLinearSum, allMSourceSquareSum, allMSourceRoundingModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]

private theorem allM_shiftedSourceLowerCount_eq
    {R a : ℝ} {m M L : ℕ} (hm : 0 < m) :
    allMSourceLowerCount R (a + R / m) m (M + 1) (L + 2) =
      ∑ t ∈ Finset.range (L + 1),
        (min t M + 1 : ℕ) * (m * a - R * t) := by
  rw [allMSourceLowerCount, Finset.sum_range_succ']
  rw [show min 0 (M + 1) = 0 by omega]
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro t _
  rw [show min (t + 1) (M + 1) = min t M + 1 by omega]
  push_cast
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

/-- Rounded source count dominates its continuous density for every nonnegative derivative ratio
below the coefficient cutoff. -/
theorem firstOrderSourceDensity_mul_cube_le_rateSourceCount
    {R a beta : ℝ} {m : ℕ}
    (hR : 0 < R) (hRa : R ≤ a) (hbeta0 : 0 ≤ beta) (hbeta : beta < a / R)
    (hm : 0 < m) :
    (m : ℝ) ^ 3 * firstOrderSourceDensity R a beta ≤
      firstOrderRateSourceCount R a m (Nat.floor (beta * m)) (Nat.ceil (m * a / R)) := by
  let M := ⌊beta * m⌋₊
  let mu := ⌈m * a / R⌉₊
  let L := ⌊m * a / R⌋₊
  let z := a / R
  let u : ℝ := (M + 1 : ℕ) / m
  let c : ℝ := (L + 2 : ℕ) / m
  let v : ℝ := (m : ℝ)⁻¹
  let Q : ℝ := ∑ t ∈ Finset.range (L + 1),
    (min t M + 1 : ℕ) * (m * a - R * t)
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmCube : 0 < (m : ℝ) ^ 3 := pow_pos hmReal 3
  have ha0 : 0 < a := hR.trans_le hRa
  have hMReal : (M : ℝ) ≤ beta * m := by
    dsimp only [M]
    exact Nat.floor_le (mul_nonneg hbeta0 (Nat.cast_nonneg _))
  have hMlt : beta * m < (M : ℝ) + 1 := by
    dsimp only [M]
    exact Nat.lt_floor_add_one _
  have hmulCutoff : beta * m ≤ m * a / R := by
    calc
      beta * (m : ℝ) ≤ (a / R) * m :=
        mul_le_mul_of_nonneg_right hbeta.le (Nat.cast_nonneg m)
      _ = (m : ℝ) * a / R := by ring
  have hML : M ≤ L := by
    dsimp only [M, L]
    exact Nat.floor_le_floor hmulCutoff
  have hcutoff0 : 0 ≤ (m : ℝ) * a / R := by positivity
  have hLReal : (L : ℝ) ≤ m * a / R := by
    dsimp only [L]
    exact Nat.floor_le hcutoff0
  have hLlt : (m : ℝ) * a / R < (L : ℝ) + 1 := by
    dsimp only [L]
    exact Nat.lt_floor_add_one _
  have hLmu : L ≤ mu := by
    dsimp only [mu, L]
    exact_mod_cast hLReal.trans (Nat.le_ceil _)
  have hQle : Q ≤ firstOrderRateSourceCount R a m M mu := by
    change Q ≤ ∑ t ∈ Finset.range (mu + 1),
      (min t M + 1 : ℕ) * max (m * a - R * t) 0
    dsimp only [Q]
    calc
      (∑ t ∈ Finset.range (L + 1),
          (min t M + 1 : ℕ) * (m * a - R * t)) =
          ∑ t ∈ Finset.range (L + 1),
            (min t M + 1 : ℕ) * max (m * a - R * t) 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [max_eq_left]
        have htL : (t : ℝ) ≤ L := by
          have htNat : t < L + 1 := Finset.mem_range.mp ht
          exact_mod_cast (show t ≤ L by omega)
        have htCutoff := htL.trans hLReal
        have := mul_le_mul_of_nonneg_left htCutoff hR.le
        field_simp [ne_of_gt hR] at this ⊢
        nlinarith
      _ ≤ ∑ t ∈ Finset.range (mu + 1),
            (min t M + 1 : ℕ) * max (m * a - R * t) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.add_le_add_right hLmu 1)
        · intro t _ _
          positivity
  have hshift : allMSourceLowerCount R (a + R / m) m (M + 1) (L + 2) = Q :=
    allM_shiftedSourceLowerCount_eq hm
  have harg : R * (z + (m : ℝ)⁻¹) = a + R / m := by
    dsimp only [z]
    field_simp [ne_of_gt hR, ne_of_gt hmReal]
  have hnormalized : Q / (m : ℝ) ^ 3 =
      R * allMSourceRoundingModel z u c v := by
    have h := allMSourceLowerCount_normalized_eq_model
      (R := R) (z := z) (m := m) (M := M + 1) (L := L + 2) hm (by omega)
    rw [harg, hshift] at h
    exact h
  have hz1 : 1 ≤ z := by
    dsimp only [z]
    exact (le_div_iff₀ hR).2 (by simpa only [one_mul] using hRa)
  have hbz : beta ≤ z := hbeta.le
  have hbu : beta ≤ u := by
    dsimp only [u]
    exact (le_div_iff₀ hmReal).2 (by norm_num at hMlt ⊢; linarith)
  have hub : u ≤ beta + v := by
    dsimp only [u, v]
    rw [show beta + (m : ℝ)⁻¹ = (beta * m + 1) / m by
      field_simp [ne_of_gt hmReal]]
    exact (div_le_div_iff_of_pos_right hmReal).2 (by norm_num; linarith)
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp only [v]
    rw [inv_le_one₀ hmReal]
    exact_mod_cast hm
  have hzc : z + v ≤ c := by
    dsimp only [z, v, c]
    apply (le_div_iff₀ hmReal).2
    have : (m : ℝ) * (a / R + (m : ℝ)⁻¹) = m * a / R + 1 := by
      field_simp [ne_of_gt hmReal]
    rw [mul_comm, this]
    push_cast
    linarith
  have hcz : c ≤ z + 2 * v := by
    dsimp only [z, v, c]
    apply (div_le_iff₀ hmReal).2
    have : (m : ℝ) * (a / R + 2 * (m : ℝ)⁻¹) = m * a / R + 2 := by
      field_simp [ne_of_gt hmReal]
    rw [mul_comm, this]
    push_cast
    linarith
  have hmodel := allMSourceRoundingModel_ge hz1 hbz hbu hub hu0 hv0 hv1 hzc hcz
  have hdensity : firstOrderSourceDensity R a beta =
      R * (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) := by
    unfold firstOrderSourceDensity
    dsimp only [z]
    field_simp [ne_of_gt hR]
  have hdensityNorm : firstOrderSourceDensity R a beta ≤ Q / (m : ℝ) ^ 3 := by
    rw [hdensity, hnormalized]
    exact mul_le_mul_of_nonneg_left hmodel hR.le
  have hdensityQ : (m : ℝ) ^ 3 * firstOrderSourceDensity R a beta ≤ Q := by
    have := (le_div_iff₀ hmCube).mp hdensityNorm
    nlinarith
  change (m : ℝ) ^ 3 * firstOrderSourceDensity R a beta ≤
    firstOrderRateSourceCount R a m M mu
  exact hdensityQ.trans hQle

end

end ReedSolomon.HiddenDerivative
