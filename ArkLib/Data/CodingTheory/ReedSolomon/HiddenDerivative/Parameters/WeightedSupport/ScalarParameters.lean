/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Scalar prerequisites for the no-band weighted support

This file records the dimension-free part of the prescribed parameter choice. The exponential
order uses `ξ = 27 / 10`. Its size makes the finite simplex estimates available, while the
harmonic lower bound and the clipped rate parameter imply `g * H ≥ ξ`. These statements are
kept separate from the later simplex distribution and rank comparison.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

noncomputable section

/-- The exponential constant in the prescribed no-band support. -/
def xi : ℝ := 27 / 10

/-- The fixed support tilt. -/
def theta : ℝ := 3 / 8

/-- The residual fraction `1 - theta`. -/
def residualFraction : ℝ := 5 / 8

@[simp] theorem xi_pos : 0 < xi := by norm_num [xi]

@[simp] theorem theta_pos : 0 < theta := by norm_num [theta]

/-- A degree-eighteen Taylor polynomial certifies the finite threshold used by all moment and
rounding estimates. -/
theorem exp_fifty_four_fifths_gt : (48000 : ℝ) < Real.exp (54 / 5) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 54 / 5) 19
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The prescribed exponential order supplies the finite threshold, logarithmic lower bound,
and harmonic lower bound required by the no-band proof. -/
theorem prescribed_order_lower (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) :
    let d := Nat.ceil (Real.exp (xi / δ))
    48000 ≤ d ∧ xi / δ ≤ Real.log d ∧
      xi / δ ≤ (harmonic (d - 1) : ℝ) := by
  let d := Nat.ceil (Real.exp (xi / δ))
  have hceil : Real.exp (xi / δ) ≤ (d : ℝ) := Nat.le_ceil _
  have hdp : (0 : ℝ) < d := (Real.exp_pos _).trans_le hceil
  have hlog := Real.log_le_log (Real.exp_pos _) hceil
  rw [Real.log_exp] at hlog
  have he : (54 / 5 : ℝ) ≤ xi / δ := by
    apply (le_div_iff₀ hδ).mpr
    norm_num [xi] at hδmax ⊢
    nlinarith
  have hexp := Real.exp_le_exp.mpr he
  have hd : 48000 ≤ d := by
    exact_mod_cast ((exp_fifty_four_fifths_gt.trans_le (hexp.trans hceil)).le)
  have hh := log_add_one_le_harmonic (d - 1)
  have heq : d - 1 + 1 = d := by omega
  rw [heq] at hh
  exact ⟨hd, hlog, hlog.trans hh⟩

/-- The clipped gap is positive and at most one throughout the permitted rate interval. -/
theorem clippedGap_mem_unit (δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) :
    0 < min 1 (δ / ρ) ∧ min 1 (δ / ρ) ≤ 1 := by
  exact ⟨lt_min (by norm_num) (div_pos hδ hρ), min_le_left _ _⟩

/-- The clipped gap and harmonic number retain the full exponential constant `ξ`. -/
theorem clippedGap_mul_harmonic_ge_xi (δ ρ H : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ) (hH : xi / δ ≤ H) :
    xi ≤ min 1 (δ / ρ) * H := by
  have hδone : δ ≤ 1 := hδmax.trans (by norm_num)
  have hHpos : 0 < H := (div_pos xi_pos hδ).trans_le hH
  have hδH : xi ≤ δ * H := by
    have h := mul_le_mul_of_nonneg_right hH hδ.le
    simpa [div_mul_cancel₀ _ hδ.ne', mul_comm] using h
  by_cases hlow : ρ ≤ δ
  · rw [min_eq_left ((le_div_iff₀ hρ).mpr (by simpa using hlow))]
    have hxi_le_H : xi ≤ H := by
      have hxidiv : xi ≤ xi / δ := by
        apply (le_div_iff₀ hδ).mpr
        nlinarith [xi_pos]
      exact hxidiv.trans hH
    simpa using hxi_le_H
  · have hhigh : δ < ρ := lt_of_not_ge hlow
    rw [min_eq_right ((div_le_one hρ).mpr hhigh.le)]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hρ).mpr
    have hρone : ρ ≤ 1 := hρmax.trans (sub_le_self 1 hδ.le)
    have hxiρ : xi * ρ ≤ xi := by
      simpa using mul_le_mul_of_nonneg_left hρone xi_pos.le
    exact hxiρ.trans hδH

/-- The tilted-to-clipped ratio is at most `1 / δ`, in both rate branches. -/
theorem one_add_theta_mul_clippedGap_div_le (δ ρ : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ) :
    (1 + theta * min 1 (δ / ρ)) / min 1 (δ / ρ) ≤ 1 / δ := by
  by_cases hlow : ρ ≤ δ
  · rw [min_eq_left ((le_div_iff₀ hρ).mpr (by simpa using hlow))]
    norm_num [theta]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  · have hhigh : δ < ρ := lt_of_not_ge hlow
    rw [min_eq_right ((div_le_one hρ).mpr hhigh.le)]
    have hρδ : ρ + theta * δ ≤ 1 := by
      norm_num [theta] at hρmax ⊢
      nlinarith
    calc
      (1 + theta * (δ / ρ)) / (δ / ρ) = (ρ + theta * δ) / δ := by
        field_simp
      _ ≤ 1 / δ := div_le_div_of_nonneg_right hρδ hδ.le

/-- Any radius already bounded by `a/(gH)` is at most `1/ξ = 10/27`. The geometric
floor-radius lemma supplies the first premise in the capacity construction. -/
theorem normalizedRadius_le_ten_twentySeven (δ ρ H s : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ) (hH : xi / δ ≤ H)
    (hs : s ≤ (1 + theta * min 1 (δ / ρ)) /
      (min 1 (δ / ρ) * H)) :
    s ≤ 10 / 27 := by
  let g := min 1 (δ / ρ)
  have hg := (clippedGap_mem_unit δ ρ hδ hρ).1
  have hHpos : 0 < H := (div_pos xi_pos hδ).trans_le hH
  have ha := one_add_theta_mul_clippedGap_div_le δ ρ hδ hδmax hρ hρmax
  have hquot : (1 + theta * g) / (g * H) ≤ (1 / δ) / H := by
    calc
      (1 + theta * g) / (g * H) = ((1 + theta * g) / g) / H := by
        field_simp
      _ ≤ (1 / δ) / H := div_le_div_of_nonneg_right ha hHpos.le
  have hlast : (1 / δ) / H ≤ 10 / 27 := by
    have hx' : (27 / 10 : ℝ) ≤ δ * H := by
      have hx := (div_le_iff₀ hδ).mp (show (27 / 10 : ℝ) / δ ≤ H by
        simpa [xi] using hH)
      simpa [mul_comm] using hx
    rw [div_div]
    apply (div_le_iff₀ (mul_pos hδ hHpos)).mpr
    nlinarith
  exact hs.trans (hquot.trans hlast)

/-- The harmonic square is small enough for the finite centered-moment estimates. -/
theorem harmonic_square_bound (d H : ℝ) (hd : 10000 ≤ d) (hH0 : 0 ≤ H)
    (hH : H ≤ Real.log d + 3 / 5) : H ^ 2 ≤ d / 100 := by
  have h := hH.trans (Real.log_add_three_fifths_le_sqrt_div_ten d hd)
  have hs := Real.sq_sqrt (show 0 ≤ d by linarith)
  nlinarith [Real.sqrt_nonneg d]

/-- At the prescribed finite threshold, the logarithmic harmonic estimate is a small explicit
multiple of `sqrt d`. This sharper form supplies the `0.002` centering loss. -/
theorem log_add_three_fifths_le_nineteen_over_365_sqrt (d : ℝ) (hd : 48000 ≤ d) :
    Real.log d + 3 / 5 ≤ (19 / 365) * Real.sqrt d := by
  have hdpos : 0 < d := by linarith
  have hsqrtd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hsqrt48000 : (219 : ℝ) < Real.sqrt 48000 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hexp2 : Real.exp 2 < 48000 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hdomain0 : Real.exp 2 ≤ (48000 : ℝ) := hexp2.le
  have hdomain : Real.exp 2 ≤ d := hdomain0.trans hd
  have hanti := Real.log_div_sqrt_antitoneOn hdomain0 hdomain hd
  have hlog48000 : Real.log 48000 < (54 / 5 : ℝ) := by
    have h := Real.strictMonoOn_log (by norm_num : (0 : ℝ) < 48000)
      (Real.exp_pos (54 / 5)) exp_fifty_four_fifths_gt
    simpa using h
  have hbase : Real.log 48000 / Real.sqrt 48000 < (54 / 5 : ℝ) / 219 := by
    exact (div_lt_div_of_pos_right hlog48000 (Real.sqrt_pos.2 (by norm_num))).trans_le
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrt48000.le)
  have hlogratio : Real.log d / Real.sqrt d < (54 / 5 : ℝ) / 219 :=
    hanti.trans_lt hbase
  have hconst : (3 / 5 : ℝ) / Real.sqrt d < (3 / 5) / 219 := by
    exact div_lt_div_of_pos_left (by norm_num) (by norm_num) (hsqrt48000.trans_le
      (Real.sqrt_le_sqrt hd))
  have hratio : (Real.log d + 3 / 5) / Real.sqrt d ≤ 19 / 365 := by
    rw [add_div]
    norm_num at hlogratio hconst ⊢
    linarith
  exact (div_le_iff₀ hsqrtd).mp (by simpa [mul_comm] using hratio)

/-- The same sharp square-root estimate applies to any harmonic upper bound. -/
theorem harmonic_le_nineteen_over_365_sqrt (d H : ℝ) (hd : 48000 ≤ d)
    (hH : H ≤ Real.log d + 3 / 5) :
    H ≤ (19 / 365) * Real.sqrt d :=
  hH.trans (log_add_three_fifths_le_nineteen_over_365_sqrt d hd)

end
end ReedSolomon.HiddenDerivative.WeightedSupportParameters
