/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Parameters

/-!
# The fixed-rate exponent of the partition gate

The logarithmic gate isolates the leading constant
`R log(40/(9R))`. Every positive addition to that exponent eventually
gives a strict gate as the gap decreases to zero.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- The leading order exponent at a fixed rate. -/
def ratePartitionExponent (R : ℝ) : ℝ := R * Real.log (40 / (9 * R))

/-- The logarithm of the limiting ratio, with all positivity assumptions discharged. -/
theorem log_ratePartitionGamma {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hd : 0 < d) :
    Real.log (ratePartitionGamma R a d) =
      Real.log ((27 / 20 : ℝ) * R) + Real.log ((d : ℝ) + 1) -
        R / a * (Real.log 6 + Real.log d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [ratePartitionGamma, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity : (27 / 20 : ℝ) * R ≠ 0) (by positivity),
    Real.log_rpow (by positivity), Real.log_mul (by norm_num) hd'.ne']

/-- A lower bound for the logarithmic gate drops only the positive `log(1+1/d)` term. -/
theorem ratePartitionGamma_gt_one_of_log_bound {R δ : ℝ} {d : ℕ}
    (hR : 0 < R) (hδ : 0 < δ) (hd : 0 < d)
    (hgate : 0 < (R + δ) * Real.log ((27 / 20 : ℝ) * R) +
      δ * Real.log d - R * Real.log 6) :
    1 < ratePartitionGamma R (R + δ) d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < R + δ := by positivity
  have hlogd : Real.log (d : ℝ) ≤ Real.log ((d : ℝ) + 1) :=
    Real.log_le_log hd' (by linarith)
  have hlog : 0 < Real.log (ratePartitionGamma R (R + δ) d) := by
    rw [log_ratePartitionGamma hR hd]
    have h := mul_le_mul_of_nonneg_left hlogd ha.le
    have heq : (R + δ) *
        (Real.log ((27 / 20 : ℝ) * R) + Real.log ((d : ℝ) + 1) -
          R / (R + δ) * (Real.log 6 + Real.log d)) =
        (R + δ) * (Real.log ((27 / 20 : ℝ) * R) + Real.log ((d : ℝ) + 1)) -
          R * (Real.log 6 + Real.log d) := by field_simp
    nlinarith
  exact (Real.log_pos_iff (by unfold ratePartitionGamma; positivity)).mp hlog

/-- The fixed-rate exponent is the difference of the two logarithmic constants. -/
theorem ratePartitionExponent_eq {R : ℝ} (hR : 0 < R) :
    ratePartitionExponent R =
      R * (Real.log 6 - Real.log ((27 / 20 : ℝ) * R)) := by
  have hquot : (40 : ℝ) / (9 * R) = 6 / ((27 / 20 : ℝ) * R) := by field_simp; ring
  rw [ratePartitionExponent, hquot, Real.log_div (by norm_num) (by positivity)]

/-- Any positive exponent margin supplies a gate once its lower-order logarithmic term is small. -/
theorem ratePartitionGamma_gt_one_of_exponent_margin {R δ ε : ℝ} {d : ℕ}
    (hR : 0 < R) (hδ : 0 < δ) (hd : 0 < d)
    (horder : ratePartitionExponent R + ε ≤ δ * Real.log d)
    (hmargin : 0 < ε + δ * Real.log ((27 / 20 : ℝ) * R)) :
    1 < ratePartitionGamma R (R + δ) d := by
  apply ratePartitionGamma_gt_one_of_log_bound hR hδ hd
  rw [ratePartitionExponent_eq hR] at horder
  nlinarith

/-- The leading fixed-rate exponent is strictly positive throughout the code-rate interval. -/
theorem ratePartitionExponent_pos {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    0 < ratePartitionExponent R := by
  apply mul_pos hR
  apply Real.log_pos
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * R)).mpr
  nlinarith

/-- Every positive exponent margin eventually gives an admissible strict partition gate. -/
theorem ratePartition_fixedRate_eventually {R ε : ℝ}
    (hR : 0 < R) (hRone : R < 1) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      let d := ⌈Real.exp ((ratePartitionExponent R + ε) / δ)⌉₊
      R + δ < 1 ∧ 500 ≤ d ∧ 1 < ratePartitionGamma R (R + δ) d := by
  let C := ratePartitionExponent R + ε
  let B := Real.log ((27 / 20 : ℝ) * R)
  have hC : 0 < C := add_pos (ratePartitionExponent_pos hR hRone) hε
  have hlog : 0 < Real.log 500 := Real.log_pos (by norm_num)
  let δ₀ := min ((1 - R) / 2)
    (min (ε / (2 * (|B| + 1))) (C / (Real.log 500 + 1)))
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hsmall
  have h₁ : δ < (1 - R) / 2 := hsmall.trans_le (min_le_left _ _)
  have h₂ : δ < ε / (2 * (|B| + 1)) :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ : δ < C / (Real.log 500 + 1) :=
    hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let d := ⌈Real.exp (C / δ)⌉₊
  have hexp : 0 < Real.exp (C / δ) := Real.exp_pos _
  have hd : 0 < d := Nat.lt_ceil.mpr (by simpa using hexp)
  have hlogd : C / δ ≤ Real.log (d : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log hexp (Nat.le_ceil (Real.exp (C / δ)))
  have horder : C ≤ δ * Real.log d := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hlogd
  have h500 : 500 ≤ d := by
    have h₃' := (lt_div_iff₀ (by positivity : 0 < Real.log 500 + 1)).mp h₃
    have hlogbound : Real.log 500 ≤ C / δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith
    have he : (500 : ℝ) ≤ Real.exp (C / δ) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 500)]
      exact Real.exp_le_exp.mpr hlogbound
    exact_mod_cast he.trans (Nat.le_ceil (Real.exp (C / δ)))
  have hmargin : 0 < ε + δ * B := by
    have h₂' := (lt_div_iff₀ (by positivity : 0 < 2 * (|B| + 1))).mp h₂
    have hb := mul_le_mul_of_nonneg_left (neg_abs_le B) hδ.le
    nlinarith [abs_nonneg B]
  exact ⟨by linarith, h500,
    ratePartitionGamma_gt_one_of_exponent_margin hR hδ hd horder hmargin⟩

end ReedSolomon.HiddenDerivative
