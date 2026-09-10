/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.RateParameters
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.SharpCountingBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
/-!
# Scalar first-order exceptional-set constants

The separant schedule charges every total degree at most once. The full square
sum therefore bounds both the joint images and the generic fibers.
-/

@[expose] public section

namespace ReedSolomon

open HiddenDerivative
open scoped BigOperators

/-- The rate-first exceptional constant for a received line. -/
noncomputable def firstOrderRateExceptionalConstant (δ : ℝ) (μ h : ℕ) : ℝ :=
  h + 24 * h * firstOrderRateSquareSum μ / δ ^ 2 + 4 * firstOrderRateSquareSum μ / δ

/-- The tight Taylor total degree is at most the uniform linear bound. -/
theorem firstOrderRate_taylor_total_le {K j : ℕ} (hK : 2 ≤ K) (hj : 0 < j) :
    firstOrderTaylorTotalCap j (2 * K - 3) ≤ 2 * K * j := by
  unfold firstOrderTaylorTotalCap
  have hτ : 2 * K - 3 ≤ 2 * K := Nat.sub_le _ _
  have hj' : j - 1 + 1 = j := by omega
  nlinarith

/-- One regular first-order fiber is charged by its squared total degree. -/
theorem firstOrderRate_fiberStage_le {K j r : ℕ}
    (hK : 2 ≤ K) (hj : 0 < j) (hrj : r ≤ j) :
    firstOrderCurveFiberStageOne K j r (2 * K - 3) ≤ 2 * K * j ^ 2 := by
  have h := firstOrderCurveFiberStageOne_le_full (K := K) (τ := 2 * K - 3) hrj
  exact h.trans (by
    have hh := Nat.mul_le_mul_left j (firstOrderRate_taylor_total_le hK hj)
    nlinarith only [hh])

/-- One joint first-order image is charged by `12hK²j²`. -/
theorem firstOrderRate_jointStage_le {K j r h : ℕ}
    (hK : 2 ≤ K) (hj : 0 < j) (hrj : r ≤ j) (hh : 0 < h) :
    firstOrderCurveJointStageOne K 1 h j r (2 * K - 3) ≤ 12 * h * K ^ 2 * j ^ 2 := by
  let b := firstOrderTaylorTotalCap j (2 * K - 3)
  let c := firstOrderTaylorDerivativeCap K j r (2 * K - 3)
  have hcb : c ≤ b := min_le_left _ _
  have harea : 2 * b * c - c ^ 2 ≤ b ^ 2 := by
    have hs : c ^ 2 ≤ 2 * b * c := by nlinarith
    have he := Nat.sub_add_cancel hs
    nlinarith [sq_nonneg ((b : ℤ) - c)]
  have hfiber : j * c + r * (b - c) ≤ j * b := by
    have h := firstOrderCurveFiberStageOne_le_full (K := K) (τ := 2 * K - 3) hrj
    exact h
  have hb : b ≤ 2 * K * j := firstOrderRate_taylor_total_le hK hj
  have ha : 1 + (2 * K - 3) * h ≤ 2 * K * h := by
    have ht : 2 * K - 3 + 3 = 2 * K := by omega
    nlinarith
  unfold firstOrderCurveJointStageOne AffineHilbert.mixedDerivativeImageDegree
  change h * (2 * b * c - c ^ 2) + 2 * (1 + (2 * K - 3) * h) *
    (j * c + r * (b - c)) ≤ _
  calc
    _ ≤ h * b ^ 2 + 2 * (1 + (2 * K - 3) * h) * (j * b) := by gcongr
    _ ≤ h * (2 * K * j) ^ 2 + 2 * (2 * K * h) * (j * (2 * K * j)) := by gcongr
    _ = _ := by ring

/-- Padding the order-zero part and adding the complementary order-one part counts each
degree once. -/
private theorem sum_complementary_schedule_le (μ T : ℕ) (hT : T ≤ μ)
    (f g w : ℕ → ℕ) (hf : ∀ t < T, f t ≤ w t)
    (hg : ∀ t < μ, T ≤ t → g t ≤ w t) :
    (∑ t ∈ Finset.range T, f t) +
      (∑ t ∈ Finset.range μ, if T ≤ t then g t else 0) ≤ ∑ t ∈ Finset.range μ, w t := by
  have hpad : ∑ t ∈ Finset.range T, f t =
      ∑ t ∈ Finset.range μ, if t < T then f t else 0 := by
    calc
      _ = ∑ t ∈ Finset.range T, if t < T then f t else 0 :=
        Finset.sum_congr rfl (fun t ht ↦ by simp [Finset.mem_range.mp ht])
      _ = _ := Finset.sum_subset (Finset.range_mono hT) (fun t _ ht ↦ by
        simp only [Finset.mem_range, not_lt] at ht
        simp [not_lt.mpr ht])
  rw [hpad, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : t < T
  · simpa [h, not_le.mpr h] using hf t h
  · simpa [h, le_of_not_gt h] using hg t (Finset.mem_range.mp ht) (le_of_not_gt h)

/-- The two fiber schedules together have the full square-sum bound. -/
theorem firstOrderRate_fiberSum_le {K μ M : ℕ} (hK : 2 ≤ K) :
    firstOrderCurveFiberZero μ M + firstOrderCurveFiberOne K μ M (2 * K - 3) ≤
      2 * K * firstOrderRateSquareSum μ := by
  unfold firstOrderCurveFiberZero firstOrderCurveFiberOne
  have h := sum_complementary_schedule_le μ (μ - min M μ) (Nat.sub_le _ _)
    (fun t ↦ t + 1)
    (fun t ↦ firstOrderCurveFiberStageOne K (t + 1) (t + 1 - (μ - min M μ)) (2 * K - 3))
    (fun t ↦ 2 * K * (t + 1) ^ 2)
    (fun t _ ↦ by nlinarith)
    (fun t _ _ ↦ firstOrderRate_fiberStage_le hK (by omega) (Nat.sub_le _ _))
  apply h.trans_eq
  rw [← Finset.mul_sum, firstOrderRateSquareSum, Finset.sum_range_succ']
  simp

/-- The two joint schedules together have the full square-sum bound. -/
theorem firstOrderRate_jointSum_le {K μ M h : ℕ} (hK : 2 ≤ K) (hh : 0 < h) :
    firstOrderCurveJointZero K μ M 1 h (2 * K - 3) +
      firstOrderCurveJointOne K μ M 1 h (2 * K - 3) ≤
        12 * h * K ^ 2 * firstOrderRateSquareSum μ := by
  unfold firstOrderCurveJointZero firstOrderCurveJointOne
  have hbound := sum_complementary_schedule_le μ (μ - min M μ) (Nat.sub_le _ _)
    (fun t ↦ h * (1 + (2 * K - 3) * t) + (t + 1) * (1 + (2 * K - 3) * h))
    (fun t ↦ firstOrderCurveJointStageOne K 1 h (t + 1)
      (t + 1 - (μ - min M μ)) (2 * K - 3))
    (fun t ↦ 12 * h * K ^ 2 * (t + 1) ^ 2)
    (fun t _ ↦ by
      have ht : 2 * K - 3 + 3 = 2 * K := by omega
      have hb : 1 + (2 * K - 3) * t ≤ 2 * K * (t + 1) := by nlinarith
      have ha : 1 + (2 * K - 3) * h ≤ 2 * K * h := by nlinarith
      have hprod := Nat.mul_le_mul_left h hb
      have hprod' := Nat.mul_le_mul_left (t + 1) ha
      calc
        _ ≤ h * (2 * K * (t + 1)) + (t + 1) * (2 * K * h) :=
          Nat.add_le_add hprod hprod'
        _ = 4 * h * K * (t + 1) := by ring
        _ ≤ (4 * h * K * (t + 1)) * (3 * K * (t + 1)) :=
          Nat.le_mul_of_pos_right _ (by positivity)
        _ = 12 * h * K ^ 2 * (t + 1) ^ 2 := by ring)
    (fun t _ _ ↦ firstOrderRate_jointStage_le hK (by omega) (Nat.sub_le _ _) hh)
  apply hbound.trans_eq
  rw [← Finset.mul_sum, firstOrderRateSquareSum, Finset.sum_range_succ']
  simp

/-- The exact cap-sensitive curve envelope is bounded by the advertised rate-first scalar
constant at the midpoint split. -/
theorem firstOrderCurveBound_le_rateExceptionalConstant
    (δ : ℝ) (n K k A μ M h : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hK : 2 ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (hh : 0 < h) :
    let L := correlatedMidpoint δ n k
    ((firstOrderCurveBound n K k L A μ M 1 h
      (τ := 2 * K - 3)
      (η := ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ)) : ℚ) : ℝ) ≤
        firstOrderRateExceptionalConstant δ μ h * n ^ 2 := by
  dsimp only
  let L := correlatedMidpoint δ n k
  let l1 : ℝ := (n - L + 1 : ℕ) / (A - L + 1 : ℕ)
  let l2 : ℝ := (n - k + 1 : ℕ) / (L - k + 1 : ℕ)
  let eta : ℝ := (n - k + 1 : ℕ) / (A - k + 1 : ℕ)
  let J0 : ℝ := firstOrderCurveJointZero K μ M 1 h (2 * K - 3)
  let J1 : ℝ := firstOrderCurveJointOne K μ M 1 h (2 * K - 3)
  let F0 : ℝ := firstOrderCurveFiberZero μ M
  let F1 : ℝ := firstOrderCurveFiberOne K μ M (2 * K - 3)
  let S : ℝ := firstOrderRateSquareSum μ
  have hmid := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have hratios := correlatedMidpoint_ratios_le_two_div δ n k A hδ hn hk hgap hAn
  have hkA : k ≤ A := hmid.1.trans hmid.2.1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdirect : eta ≤ 1 / δ := by
    dsimp [eta]
    have hden : (0 : ℝ) < (A - k + 1 : ℕ) := by positivity
    apply (div_le_iff₀ hden).mpr
    have hnum : ((n - k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega)
    have hgap' : δ * (n : ℝ) ≤ (A - k + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_sub hkA, Nat.cast_one]
      linarith
    have hs := mul_le_mul_of_nonneg_left hgap' (by positivity : 0 ≤ 1 / δ)
    have heq : (1 / δ) * (δ * n) = (n : ℝ) := by field_simp
    rw [heq] at hs
    exact hnum.trans hs
  have hjoint := firstOrderRate_jointSum_le (K := K) (μ := μ) (M := M) (h := h) hK hh
  have hfiber := firstOrderRate_fiberSum_le (K := K) (μ := μ) (M := M) hK
  have hl1 : l1 ≤ 2 / δ := by simpa [l1, L] using hratios.1
  have hl2 : l2 ≤ 2 / δ := by simpa [l2, L] using hratios.2
  have hL1one : (1 : ℝ) ≤ l1 := by
    dsimp [l1]
    apply (le_div_iff₀ (by positivity)).mpr
    push_cast
    have hsub : ((A - L : ℕ) : ℝ) ≤ (n - L : ℕ) := by exact_mod_cast (by omega)
    linarith
  have hL2one : (1 : ℝ) ≤ l2 := by
    dsimp [l2]
    apply (le_div_iff₀ (by positivity)).mpr
    push_cast
    have hsub : ((L - k : ℕ) : ℝ) ≤ (n - k : ℕ) := by exact_mod_cast (by omega)
    linarith
  have hetaOne : (1 : ℝ) ≤ eta := by
    dsimp [eta]
    apply (le_div_iff₀ (by positivity)).mpr
    push_cast
    have hsub : ((A - k : ℕ) : ℝ) ≤ (n - k : ℕ) := by exact_mod_cast (by omega)
    linarith
  have hjointR : J0 + J1 ≤ 12 * h * K ^ 2 * S := by
    dsimp [J0, J1, S]
    exact_mod_cast hjoint
  have hfiberR : F0 + F1 ≤ 2 * K * S := by
    dsimp [F0, F1, S]
    exact_mod_cast hfiber
  have hl1nonneg : 0 ≤ l1 := by dsimp [l1]; positivity
  have hl2nonneg : 0 ≤ l2 := by dsimp [l2]; positivity
  have hetanonneg : 0 ≤ eta := by dsimp [eta]; positivity
  have hJ0nonneg : 0 ≤ J0 := by dsimp [J0]; positivity
  have hJ1nonneg : 0 ≤ J1 := by dsimp [J1]; positivity
  have hF0nonneg : 0 ≤ F0 := by dsimp [F0]; positivity
  have hF1nonneg : 0 ≤ F1 := by dsimp [F1]; positivity
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hjointBound : l1 * J0 + l1 * eta * J1 ≤ 24 * h * n ^ 2 * S / δ ^ 2 := by
    calc
      l1 * J0 + l1 * eta * J1 ≤ l1 * eta * (J0 + J1) := by
        nlinarith [mul_nonneg hl1nonneg
          (mul_nonneg (sub_nonneg.mpr hetaOne) hJ0nonneg)]
      _ ≤ (2 / δ) * (1 / δ) * (12 * h * K ^ 2 * S) := by gcongr
      _ ≤ (2 / δ) * (1 / δ) * (12 * h * n ^ 2 * S) := by
        gcongr
      _ = 24 * h * n ^ 2 * S / δ ^ 2 := by field_simp; ring
  have hfiberInner : F0 + l2 * F1 ≤ l2 * (F0 + F1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL2one) hF0nonneg]
  have hfiberBound : ((n - L : ℕ) : ℝ) * (F0 + l2 * F1) ≤
      4 * n ^ 2 * S / δ := by
    calc
      ((n - L : ℕ) : ℝ) * (F0 + l2 * F1) ≤
          (n : ℝ) * (l2 * (F0 + F1)) := by
        gcongr
        exact_mod_cast Nat.sub_le n L
      _ ≤ n * ((2 / δ) * (2 * K * S)) := by gcongr
      _ ≤ n * ((2 / δ) * (2 * n * S)) := by
        gcongr
      _ = 4 * n ^ 2 * S / δ := by field_simp; ring
  have hheight : (h : ℝ) ≤ h * n ^ 2 := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have htotal : (h : ℝ) + l1 * J0 + l1 * eta * J1 +
      ((n - L : ℕ) : ℝ) * (F0 + l2 * F1) ≤
        firstOrderRateExceptionalConstant δ μ h * n ^ 2 := by
    calc
      _ = (h : ℝ) + (l1 * J0 + l1 * eta * J1) +
          ((n - L : ℕ) : ℝ) * (F0 + l2 * F1) := by ring
      _ ≤ h * n ^ 2 + 24 * h * n ^ 2 * S / δ ^ 2 + 4 * n ^ 2 * S / δ :=
        add_le_add (add_le_add hheight hjointBound) hfiberBound
      _ = firstOrderRateExceptionalConstant δ μ h * n ^ 2 := by
        dsimp [firstOrderRateExceptionalConstant, S]
        ring
  rw [firstOrderCurveBound]
  push_cast
  simpa only [L, l1, l2, eta, J0, J1, F0, F1, Nat.cast_add, Nat.cast_one,
    one_mul] using htotal

end ReedSolomon
