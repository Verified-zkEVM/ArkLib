/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants

/-!
# Polynomial envelopes of the first-order constants

If the rate satisfies `D ≤ ρ n` and the agreement threshold satisfies `a n ≤ A` with `ρ < a`,
then the agreement-incidence ratio is at most `1 / (a - ρ)`, independently of the block length.
Given a common bound `C ≥ 1` on the agreement-incidence ratio, and bounds `μ ≤ C q`,
`h ≤ C q²` and `T ≤ C q³` in terms of `q ≥ 1`, the closed list constant is at most
`3 C² n q³` and the closed exception constant is at most `45 C⁴ n² q⁵`.

## Main statements

* `agreementIncidenceRatio_le_one_div_sub`: the rate bound on the agreement-incidence ratio.
* `firstOrderListConstant_le_cubic`: the cubic bound on the list constant.
* `firstOrderExceptionConstant_le_quintic`: the quintic bound on the exception constant.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- For `D ≤ ρ n`, `a n ≤ A` and `ρ < a`, the agreement-incidence ratio is at
most `1 / (a - ρ)`. -/
theorem agreementIncidenceRatio_le_one_div_sub {n D A : ℕ} {ρ a : ℝ}
    (hD : (D : ℝ) ≤ ρ * n) (hA : a * n ≤ A) (hρa : ρ < a) :
    agreementIncidenceRatio n D A ≤ 1 / (a - ρ) := by
  by_cases hDn : n ≤ D
  · simp only [agreementIncidenceRatio, Nat.sub_eq_zero_of_le hDn, Nat.cast_zero, zero_div]
    positivity
  have hDn : D ≤ n := (Nat.lt_of_not_ge hDn).le
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDA : D < A := by
    exact_mod_cast (hD.trans_lt (mul_lt_mul_of_pos_right hρa hn)).trans_le hA
  have hden : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hDA
  unfold agreementIncidenceRatio
  rw [div_le_div_iff₀ hden (sub_pos.mpr hρa), Nat.cast_sub hDn, Nat.cast_sub hDA.le]
  have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  nlinarith

private theorem monomial_le_of_exponent_le {C N q : ℝ} (hC : 1 ≤ C) (hN : 1 ≤ N) (hq : 1 ≤ q)
    {r s t : ℕ} (hr : r ≤ 4) (hs : s ≤ 2) (ht : t ≤ 5) :
    C ^ r * N ^ s * q ^ t ≤ C ^ 4 * N ^ 2 * q ^ 5 := by
  gcongr

/-- For `1 ≤ C`, `1 ≤ q`, `1 ≤ n`, `D ≤ n`, `θ ≤ C`, `μ ≤ C q` and `T ≤ C q³` for the
staircase `T` at `M`, the closed list constant is at most `3 C² n q³`. -/
theorem firstOrderListConstant_le_cubic {C q θ : ℝ} {n D μ M : ℕ} (hC : 1 ≤ C) (hq : 1 ≤ q)
    (hn : 1 ≤ n) (hD : D ≤ n) (hθ : θ ≤ C) (hμ : (μ : ℝ) ≤ C * q)
    (hT : stageStaircase μ M ≤ C * q ^ 3) :
    firstOrderListConstant θ D μ M ≤ 3 * C ^ 2 * n * q ^ 3 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hD
  have hsub : ((μ - M : ℕ) : ℝ) ≤ μ := by exact_mod_cast Nat.sub_le μ M
  have hT0 := stageStaircase_nonneg μ M
  have hq3 : q ≤ q ^ 3 := le_self_pow₀ hq (by norm_num)
  have hC2 : C ≤ C ^ 2 := le_self_pow₀ hC (by norm_num)
  calc
    firstOrderListConstant θ D μ M ≤ 2 * n * C * (C * q ^ 3) + C * q := by
      unfold firstOrderListConstant
      by_cases hθ0 : 0 ≤ θ
      · gcongr
        exact hsub.trans hμ
      · have hterm : 2 * (D : ℝ) * θ * stageStaircase μ M ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hθ0)) hT0
        have hbound : 0 ≤ 2 * (n : ℝ) * C * (C * q ^ 3) := by positivity
        linarith [hsub.trans hμ]
    _ ≤ 2 * n * C * (C * q ^ 3) + C ^ 2 * n * q ^ 3 := by
      refine add_le_add_right ?_ (2 * (n : ℝ) * C * (C * q ^ 3))
      calc
        C * q ≤ C ^ 2 * q ^ 3 := by gcongr
        _ = C ^ 2 * 1 * q ^ 3 := by ring
        _ ≤ C ^ 2 * n * q ^ 3 := by gcongr
    _ = 3 * C ^ 2 * n * q ^ 3 := by ring

/-- For `1 ≤ C`, `1 ≤ q`, `1 ≤ n`, `D ≤ n`, `0 ≤ θ ≤ C`, `μ ≤ C q`, `h ≤ C q²` and `T ≤ C q³`
for the staircase `T` at `M`, the closed exception constant is at most `45 C⁴ n² q⁵`. -/
theorem firstOrderExceptionConstant_le_quintic {C q θ : ℝ} {n D h μ M : ℕ} (hC : 1 ≤ C)
    (hq : 1 ≤ q) (hn : 1 ≤ n) (hD : D ≤ n) (hθ0 : 0 ≤ θ) (hθ : θ ≤ C)
    (hμ : (μ : ℝ) ≤ C * q) (hh : (h : ℝ) ≤ C * q ^ 2) (hT : stageStaircase μ M ≤ C * q ^ 3) :
    firstOrderExceptionConstant θ n D h μ M ≤ 45 * C ^ 4 * n ^ 2 * q ^ 5 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hD
  have hT0 := stageStaircase_nonneg μ M
  have hsub : ((n - D - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le (n - D) 1).trans (Nat.sub_le n D)
  have hμ' : ((2 * μ - 1 : ℕ) : ℝ) ≤ 2 * (C * q) := by
    calc
      ((2 * μ - 1 : ℕ) : ℝ) ≤ 2 * (μ : ℝ) := by exact_mod_cast Nat.sub_le (2 * μ) 1
      _ ≤ 2 * (C * q) := by gcongr
  calc
    firstOrderExceptionConstant θ n D h μ M ≤
        2 * (C * q) * (C * q ^ 2) +
        C * (C * q ^ 2 + C * q + 4 * n * (C * q) * (C * q ^ 2)) +
        n * (C * q) + (24 * n ^ 2 * (C * q ^ 2) + 8 * n) * C ^ 2 * (C * q ^ 3) +
        4 * n * n * C * (C * q ^ 3) := by
      unfold firstOrderExceptionConstant ordinaryTailCharge
      split_ifs with hμ
      · subst μ
        gcongr
        have hfactor : 1 ≤ 2 * (C * q) := by nlinarith
        have hh0 := hh.trans (le_mul_of_one_le_left (by positivity) hfactor)
        have hr1 : 0 ≤ C * (C * q ^ 2 + C * q + 4 * (n : ℝ) * (C * q) * (C * q ^ 2)) := by
          positivity
        have hr2 : 0 ≤ (n : ℝ) * (C * q) := by positivity
        linarith only [hh0, hr1, hr2]
      · gcongr
    _ = 2 * (C ^ 2 * (n : ℝ) ^ 0 * q ^ 3) + (C ^ 2 * (n : ℝ) ^ 0 * q ^ 2) +
        (C ^ 2 * (n : ℝ) ^ 0 * q ^ 1) + 4 * (C ^ 3 * (n : ℝ) ^ 1 * q ^ 3) +
        (C ^ 1 * (n : ℝ) ^ 1 * q ^ 1) + 24 * (C ^ 4 * (n : ℝ) ^ 2 * q ^ 5) +
        8 * (C ^ 3 * (n : ℝ) ^ 1 * q ^ 3) + 4 * (C ^ 2 * (n : ℝ) ^ 2 * q ^ 3) := by ring
    _ ≤ 45 * C ^ 4 * n ^ 2 * q ^ 5 := by
      have := monomial_le_of_exponent_le hC hN hq (r := 2) (s := 0) (t := 3) (by norm_num)
        (by norm_num) (by norm_num)
      have := monomial_le_of_exponent_le hC hN hq (r := 2) (s := 0) (t := 2) (by norm_num)
        (by norm_num) (by norm_num)
      have := monomial_le_of_exponent_le hC hN hq (r := 2) (s := 0) (t := 1) (by norm_num)
        (by norm_num) (by norm_num)
      have := monomial_le_of_exponent_le hC hN hq (r := 3) (s := 1) (t := 3) (by norm_num)
        (by norm_num) (by norm_num)
      have := monomial_le_of_exponent_le hC hN hq (r := 1) (s := 1) (t := 1) (by norm_num)
        (by norm_num) (by norm_num)
      have := monomial_le_of_exponent_le hC hN hq (r := 2) (s := 2) (t := 3) (by norm_num)
        (by norm_num) (by norm_num)
      linarith

end ReedSolomon.HiddenDerivative
