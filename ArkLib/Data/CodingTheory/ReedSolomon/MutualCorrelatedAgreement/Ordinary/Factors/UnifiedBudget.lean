/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.FactorBounds
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# One characteristic-free ordinary transfer budget

The positive-part correction extends the sharp ordinary factor comparison beyond the range where
the separable factor degree is at most the message degree. It agrees with the sharp coefficient
through root degree `2 * D + 1` and remains valid for every Frobenius factor.
-/

@[expose] public section

namespace ReedSolomon

open scoped BigOperators

/-- The unified coefficient of challenge height in the ordinary joint-image degree. -/
def ordinaryPsi (D B : ℕ) : ℕ :=
  1 + (2 * D - 1) * (2 * B - 1) + 2 * (B - 2 * D - 1)

/-- Up to root degree `2D+1`, the unified coefficient is exactly the sharp coefficient. -/
theorem ordinaryPsi_eq_sharp {D B : ℕ} (hB : B ≤ 2 * D + 1) :
    ordinaryPsi D B = 1 + (2 * D - 1) * (2 * B - 1) := by
  unfold ordinaryPsi
  omega

/-- The unified coefficient is monotone in the original root-degree budget. -/
theorem ordinaryPsi_mono (D : ℕ) {B C : ℕ} (hBC : B ≤ C) :
    ordinaryPsi D B ≤ ordinaryPsi D C := by
  unfold ordinaryPsi
  apply Nat.add_le_add
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left (2 * D - 1)
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hBC) 1)) 1
  · exact Nat.mul_le_mul_left 2
      (Nat.sub_le_sub_right (Nat.sub_le_sub_right hBC (2 * D)) 1)

/-- The unified coefficient retains the earlier coarse `4DB` envelope. -/
theorem ordinaryPsi_le_four_mul {D B : ℕ} (hD : 1 ≤ D) (hB : 1 ≤ B) :
    ordinaryPsi D B ≤ 4 * D * B := by
  unfold ordinaryPsi
  have hDsub : 2 * D - 1 + 1 = 2 * D := Nat.sub_add_cancel (by omega)
  have hBsub : 2 * B - 1 + 1 = 2 * B := Nat.sub_add_cancel (by omega)
  by_cases hsmall : B ≤ 2 * D + 1
  · have hzero : B - 2 * D - 1 = 0 := by omega
    rw [hzero]
    nlinarith
  · have hlarge : 2 * D + 1 < B := Nat.lt_of_not_ge hsmall
    have hsub : B - 2 * D - 1 + (2 * D + 1) = B := by omega
    nlinarith

/-- The positive-part correction absorbs the degree loss of every inseparable pullback, including
the case where the separable factor degree exceeds `D`. -/
theorem ordinaryFrobenius_unified_factor {D s b : ℕ}
    (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    1 + (2 * D * s - 1) * (2 * b - 1) ≤ ordinaryPsi D (s * b) := by
  unfold ordinaryPsi
  by_cases hbD : b ≤ D
  · exact (Nat.add_le_add_left (ordinaryFrobenius_sharp_factor hbD hs hb) 1).trans
      (Nat.le_add_right _ _)
  have hDb : D < b := Nat.lt_of_not_ge hbD
  rcases eq_or_lt_of_le hs with rfl | hsTwo
  · simp
  have htailPos : 2 * D + 1 ≤ s * b := by nlinarith
  have hDs : 1 ≤ 2 * D * s := by nlinarith
  have hbTwo : 1 ≤ 2 * b := by omega
  have hDTwo : 1 ≤ 2 * D := by omega
  have hsbTwo : 1 ≤ 2 * (s * b) := by nlinarith
  have hsZ : (0 : ℤ) ≤ (s : ℤ) - 2 := by omega
  have hDZ : (0 : ℤ) ≤ D := by positivity
  have hbZ : (0 : ℤ) ≤ (b : ℤ) - D - 1 := by omega
  have htailZ :
      (2 : ℤ) * ((s : ℤ) - 1) * ((b : ℤ) - D) ≤
        2 * ((s : ℤ) * b - 2 * D - 1) := by
    nlinarith [mul_nonneg hDZ hsZ]
  have htailCast : ((s * b - 2 * D - 1 : ℕ) : ℤ) =
      (s : ℤ) * b - 2 * D - 1 := by omega
  zify [hDs, hbTwo, hDTwo, hsbTwo, htailPos]
  rw [htailCast] at *
  nlinarith [ordinaryFrobenius_sharp_difference (D : ℤ) (s : ℤ) (b : ℤ), htailZ]

/-- The ordinary Frobenius image degree satisfies the unified bound without assuming `b ≤ D`. -/
theorem ordinaryFrobeniusMixedDegree_le_unified {D s b : ℕ} (h : ℕ)
    (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ordinaryFrobeniusMixedDegree D h s b ≤ s * b + h * ordinaryPsi D (s * b) := by
  rw [ordinaryFrobeniusMixedDegree_eq D h s b hb]
  have hcoefficient := ordinaryFrobenius_unified_factor hD hs hb
  nlinarith

/-- The free-retention all-characteristic ordinary MCA budget at a supplied incidence ratio.
The retention threshold `L` affects the joint-incidence ratio upstream and appears here in the
exact accidental-agreement term. -/
def ordinaryUnifiedPowerFactorRawAt
    (theta : ℚ) (n D ell B H L : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
    (ell * ((n - L) * B) : ℕ)

/-- The manuscript's free-retention ordinary polynomial-curve budget. -/
def ordinaryUnifiedPowerFactorAt (n D ell B H A L : ℕ) : ℚ :=
  ordinaryUnifiedPowerFactorRawAt
    (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) n D ell B H L

/-- Exact ordinary free-retention budget including the separate root-degree-zero height branch. -/
def ordinaryUnifiedPowerFactorAtOrHeight (n D ell B H A L : ℕ) : ℚ :=
  if B = 0 then H else ordinaryUnifiedPowerFactorAt n D ell B H A L

@[simp]
theorem ordinaryUnifiedPowerFactorAtOrHeight_zero (n D ell H A L : ℕ) :
    ordinaryUnifiedPowerFactorAtOrHeight n D ell 0 H A L = H := by
  simp [ordinaryUnifiedPowerFactorAtOrHeight]

theorem ordinaryUnifiedPowerFactorAtOrHeight_of_pos
    (n D ell B H A L : ℕ) (hB : 0 < B) :
    ordinaryUnifiedPowerFactorAtOrHeight n D ell B H A L =
      ordinaryUnifiedPowerFactorAt n D ell B H A L := by
  simp [ordinaryUnifiedPowerFactorAtOrHeight, Nat.ne_of_gt hB]

/-- The former fixed-split budget is the free-retention budget at `L = D + 1`. -/
theorem ordinaryUnifiedPowerFactorRawAt_succ_eq
    (theta : ℚ) (n D ell B H : ℕ) :
    ordinaryUnifiedPowerFactorRawAt theta n D ell B H (D + 1) =
      ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
        (ell * ((n - D - 1) * B) : ℕ) := by
  unfold ordinaryUnifiedPowerFactorRawAt
  have hn : n - (D + 1) = n - D - 1 := by omega
  rw [hn]

/-- The unified all-characteristic ordinary MCA budget for the compatibility threshold
`L = D + 1`. This is the original integral form of the manuscript's `E_ord^(ell)`. -/
def ordinaryUnifiedPowerFactorRaw (theta : ℚ) (n D ell B H : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
    (ell * ((n - D - 1) * B) : ℕ)

/-- Named compatibility of the free-retention formula with the former fixed split. -/
theorem ordinaryUnifiedPowerFactorAt_succ_eq
    (n D ell B H A : ℕ) (hDA : D + 1 ≤ A) (hAn : A ≤ n) :
    ordinaryUnifiedPowerFactorAt n D ell B H A (D + 1) =
      ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell B H := by
  have hn : n - (D + 1) + 1 = n - D := by omega
  have hA : A - (D + 1) + 1 = A - D := by omega
  unfold ordinaryUnifiedPowerFactorAt
  rw [hn, hA, ordinaryUnifiedPowerFactorRawAt_succ_eq]
  rfl

/-- Content plus all distinct positive-root factors fits the free-retention curve budget. -/
theorem ordinaryUnifiedPowerFactorRawAt_sum_le {I : Type*} (S : Finset I)
    (degree height : I → ℕ) (theta : ℚ) (n D ell B H L contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hdegree : ∑ i ∈ S, degree i ≤ B)
    (hheight : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) +
        ∑ i ∈ S, ordinaryUnifiedPowerFactorRawAt theta n D ell
          (degree i) (height i) L ≤
      ordinaryUnifiedPowerFactorRawAt theta n D ell B H L := by
  let c : ℚ := (2 * B - 1 : ℕ) + theta * ordinaryPsi D B
  let e : ℚ := theta * ell + ell * (n - L : ℕ)
  have hc : 1 ≤ c := by
    have hnat : 1 ≤ 2 * B - 1 := by omega
    have hcast : (1 : ℚ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast hnat
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hterm (i : I) (hi : i ∈ S) :
      ordinaryUnifiedPowerFactorRawAt theta n D ell (degree i) (height i) L ≤
        c * height i + e * degree i := by
    have hiB : degree i ≤ B :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans hdegree
    have hlinear : 2 * degree i - 1 ≤ 2 * B - 1 :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hiB) 1
    have hpsi := ordinaryPsi_mono D hiB
    have hfirstQ : (((2 * degree i - 1) * height i : ℕ) : ℚ) ≤
        (2 * B - 1 : ℕ) * height i := by
      exact_mod_cast Nat.mul_le_mul_right (height i) hlinear
    have hpsiQ : ((height i * ordinaryPsi D (degree i) : ℕ) : ℚ) ≤
        height i * ordinaryPsi D B := by
      exact_mod_cast Nat.mul_le_mul_left (height i) hpsi
    unfold ordinaryUnifiedPowerFactorRawAt
    dsimp [c, e]
    push_cast
    push_cast at hfirstQ hpsiQ
    nlinarith [mul_nonneg htheta (sub_nonneg.mpr hpsiQ)]
  have hsum := Finset.sum_le_sum hterm
  have hcontent : (contentHeight : ℚ) ≤ c * contentHeight := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg contentHeight)
  have hheightQ : (contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ) ≤ H := by
    exact_mod_cast hheight
  have hdegreeQ : (∑ i ∈ S, (degree i : ℚ)) ≤ B := by exact_mod_cast hdegree
  calc
    (contentHeight : ℚ) +
        ∑ i ∈ S, ordinaryUnifiedPowerFactorRawAt theta n D ell
          (degree i) (height i) L ≤
      c * contentHeight + ∑ i ∈ S, (c * height i + e * degree i) :=
        add_le_add hcontent hsum
    _ = c * ((contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ)) +
        e * ∑ i ∈ S, (degree i : ℚ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ c * H + e * B := add_le_add (mul_le_mul_of_nonneg_left hheightQ hc0)
      (mul_le_mul_of_nonneg_left hdegreeQ he0)
    _ = ordinaryUnifiedPowerFactorRawAt theta n D ell B H L := by
      dsimp [c, e, ordinaryUnifiedPowerFactorRawAt]
      push_cast
      ring

/-- Content plus all distinct positive-root factors fits the unified curve budget. The proof uses
only additive root degrees and heights, so this is shared by the Johnson and first-order tails. -/
theorem ordinaryUnifiedPowerFactorRaw_sum_le {I : Type*} (S : Finset I)
    (degree height : I → ℕ) (theta : ℚ) (n D ell B H contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hdegree : ∑ i ∈ S, degree i ≤ B)
    (hheight : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) +
        ∑ i ∈ S, ordinaryUnifiedPowerFactorRaw theta n D ell (degree i) (height i) ≤
      ordinaryUnifiedPowerFactorRaw theta n D ell B H := by
  let c : ℚ := (2 * B - 1 : ℕ) + theta * ordinaryPsi D B
  let e : ℚ := theta * ell + ell * (n - D - 1 : ℕ)
  have hc : 1 ≤ c := by
    have hnat : 1 ≤ 2 * B - 1 := by omega
    have hcast : (1 : ℚ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast hnat
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hterm (i : I) (hi : i ∈ S) :
      ordinaryUnifiedPowerFactorRaw theta n D ell (degree i) (height i) ≤
        c * height i + e * degree i := by
    have hiB : degree i ≤ B :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans hdegree
    have hlinear : 2 * degree i - 1 ≤ 2 * B - 1 :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hiB) 1
    have hpsi := ordinaryPsi_mono D hiB
    have hfirstQ : (((2 * degree i - 1) * height i : ℕ) : ℚ) ≤
        (2 * B - 1 : ℕ) * height i := by
      exact_mod_cast Nat.mul_le_mul_right (height i) hlinear
    have hpsiQ : ((height i * ordinaryPsi D (degree i) : ℕ) : ℚ) ≤
        height i * ordinaryPsi D B := by
      exact_mod_cast Nat.mul_le_mul_left (height i) hpsi
    unfold ordinaryUnifiedPowerFactorRaw
    dsimp [c, e]
    push_cast
    push_cast at hfirstQ hpsiQ
    nlinarith [mul_nonneg htheta (sub_nonneg.mpr hpsiQ)]
  have hsum := Finset.sum_le_sum hterm
  have hcontent : (contentHeight : ℚ) ≤ c * contentHeight := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg contentHeight)
  have hheightQ : (contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ) ≤ H := by
    exact_mod_cast hheight
  have hdegreeQ : (∑ i ∈ S, (degree i : ℚ)) ≤ B := by exact_mod_cast hdegree
  calc
    (contentHeight : ℚ) +
        ∑ i ∈ S, ordinaryUnifiedPowerFactorRaw theta n D ell (degree i) (height i) ≤
      c * contentHeight + ∑ i ∈ S, (c * height i + e * degree i) :=
        add_le_add hcontent hsum
    _ = c * ((contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ)) +
        e * ∑ i ∈ S, (degree i : ℚ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ c * H + e * B := add_le_add (mul_le_mul_of_nonneg_left hheightQ hc0)
      (mul_le_mul_of_nonneg_left hdegreeQ he0)
    _ = ordinaryUnifiedPowerFactorRaw theta n D ell B H := by
      dsimp [c, e, ordinaryUnifiedPowerFactorRaw]
      push_cast
      ring

end ReedSolomon
