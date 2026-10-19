/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
public import ArkLib.ToMathlib.Algebra.Order.Floor.RelativeError
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rounding loss at a closed-form multiplicity

The finite partition ratio of `FiniteRatio.lean` factors exactly as its limit times
`exp(-loss)`, where, with `λ₀ = (R/a) log(6d)` the limiting inverse radius,

```text
loss = (λ - λ₀) + λ d (d + 1) / (2m) + log(1 + (d + 1) λ / m).
```

The three terms are the floor error of the weight budget, the enlargement of the simplex and the
rounded contact factor. At the closed-form multiplicity `m = ⌈C d² log(6d)⌉₊` with
`K = C d³ > 1` and `0 < R ≤ a`, the weight budget satisfies `W ≥ (1 - 1/K) m a d / (R log(6d))`,
so `λ ≤ λ₀ K / (K - 1)`, and the loss is at most

```text
(log(6d) + d (d + 1) (d + 2) / 2) / (C d³ - 1).
```

Hence the finite ratio is at least its limit times `exp` of minus this bound. The bound is below
`1/1000` for `C = 1000` and `d ≥ 6`, and below `1677/10⁶` for `C = 300` and `d ≥ 500`.

## Main definitions

* `closedMultiplicity C d = ⌈C d² log(6d)⌉₊`.
* `partitionRoundingLoss`: the logarithmic loss above.
* `closedMultiplicityLoss C d`: the displayed bound on the loss.

## Main statements

* `partitionFiniteRatio_eq_mul_exp_neg_roundingLoss`: the exact factorization, with no
  hypotheses.
* `partitionWeightBudget_closedMultiplicity_pos`, `partitionInverseRadius_closedMultiplicity_le`:
  the weight budget is positive and `λ ≤ λ₀ K / (K - 1)`.
* `partitionRoundingLoss_closedMultiplicity_le`: the loss is at most `closedMultiplicityLoss`.
* `partitionFiniteRatio_closedMultiplicity_ge`, `partitionFiniteRatio_closedMultiplicity_gt`:
  the resulting lower bounds on the finite ratio.
* `closedMultiplicityLoss_thousand_lt`, `closedMultiplicityLoss_three_hundred_lt`: the two
  numerical loss bounds.
* `add_two_le_closedMultiplicity`: `d + 2 ≤ ⌈C d² log(6d)⌉₊` for `C ≥ 3` and `d ≥ 1`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The closed-form multiplicity `⌈C d² log(6d)⌉₊` at scale `C` and derivative order `d`. -/
def closedMultiplicity (scale : ℝ) (order : ℕ) : ℕ :=
  ⌈scale * (order : ℝ) ^ 2 * Real.log (6 * order)⌉₊

/-- The logarithmic rounding loss
`(λ - λ₀) + λ d (d + 1) / (2m) + log(1 + (d + 1) λ / m)` of the finite partition ratio, where
`λ` is `partitionInverseRadius` and `λ₀ = (R/a) log(6d)`. -/
def partitionRoundingLoss (rate agreement : ℝ) (order multiplicity : ℕ) : ℝ :=
  let lambda := partitionInverseRadius rate agreement order multiplicity
  lambda - rate / agreement * Real.log (6 * order) +
    lambda * ((order : ℝ) * (order + 1) / (2 * multiplicity)) +
      Real.log (1 + (order + 1) * lambda / multiplicity)

/-- The bound `(log(6d) + d (d + 1) (d + 2) / 2) / (C d³ - 1)` on the rounding loss at the
closed-form multiplicity `closedMultiplicity C d`. -/
def closedMultiplicityLoss (scale : ℝ) (order : ℕ) : ℝ :=
  (Real.log (6 * order) + (order : ℝ) * (order + 1) * (order + 2) / 2) /
    (scale * (order : ℝ) ^ 3 - 1)

/-- The finite ratio is its limit `(27/20) R (d + 1) exp(-(R/a) log(6d))` times
`exp(-partitionRoundingLoss R a d m)`, for all inputs. -/
theorem partitionFiniteRatio_eq_mul_exp_neg_roundingLoss (rate agreement : ℝ)
    (order multiplicity : ℕ) :
    partitionFiniteRatio rate agreement order multiplicity =
      (27 / 20 : ℝ) * rate * (order + 1) *
          Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) *
        Real.exp (-partitionRoundingLoss rate agreement order multiplicity) := by
  have hlambda := partitionInverseRadius_nonneg rate agreement order multiplicity
  have hdenominator : 0 < 1 + ((order : ℝ) + 1) *
      partitionInverseRadius rate agreement order multiplicity / multiplicity := by positivity
  simp only [partitionFiniteRatio, partitionRoundingLoss]
  rw [mul_assoc _ (Real.exp _), ← Real.exp_add]
  rw [show -(rate / agreement * Real.log (6 * (order : ℝ))) +
      -(partitionInverseRadius rate agreement order multiplicity -
          rate / agreement * Real.log (6 * (order : ℝ)) +
        partitionInverseRadius rate agreement order multiplicity *
          ((order : ℝ) * (order + 1) / (2 * multiplicity)) +
        Real.log (1 + (order + 1) *
          partitionInverseRadius rate agreement order multiplicity / multiplicity)) =
      -partitionInverseRadius rate agreement order multiplicity *
          (1 + (order : ℝ) * (order + 1) / (2 * multiplicity)) -
        Real.log (1 + (order + 1) *
          partitionInverseRadius rate agreement order multiplicity / multiplicity) by ring]
  rw [Real.exp_sub, Real.exp_log hdenominator, mul_div_assoc]

/-- The basic estimates at the closed-form multiplicity `m = ⌈C d² log(6d)⌉₊` with
`K = C d³ > 1` and `0 < R ≤ a`: `0 < d`, `0 < log(6d)`, `C d² log(6d) ≤ m`, and the unrounded
weight budget `m a d / (R log(6d))` is at least `K`. -/
private theorem closedMultiplicity_estimates {rate agreement scale : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hle : rate ≤ agreement) (hscale : 1 < scale * (order : ℝ) ^ 3) :
    (0 : ℝ) < order ∧ 0 < Real.log (6 * (order : ℝ)) ∧
      scale * (order : ℝ) ^ 2 * Real.log (6 * order) ≤ closedMultiplicity scale order ∧
      scale * (order : ℝ) ^ 3 ≤ (closedMultiplicity scale order : ℝ) * agreement * order /
        (rate * Real.log (6 * (order : ℝ))) := by
  have horder : (0 : ℝ) < order := by
    rcases Nat.eq_zero_or_pos order with h | h
    · subst h; norm_num at hscale
    · exact_mod_cast h
  have hlog : 0 < Real.log (6 * (order : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ order := by exact_mod_cast Nat.cast_pos.mp horder
    linarith)
  have hm : scale * (order : ℝ) ^ 2 * Real.log (6 * order) ≤ closedMultiplicity scale order :=
    Nat.le_ceil _
  refine ⟨horder, hlog, hm, ?_⟩
  rw [le_div_iff₀ (mul_pos hrate hlog)]
  have h₁ := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (order : ℝ) * rate)
  have h₂ := mul_le_mul_of_nonneg_left hle
    (by positivity : 0 ≤ (closedMultiplicity scale order : ℝ) * order)
  nlinarith

/-- At the closed-form multiplicity with `C d³ > 1` and `0 < R ≤ a`, the weight budget is
positive. -/
theorem partitionWeightBudget_closedMultiplicity_pos {rate agreement scale : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hle : rate ≤ agreement) (hscale : 1 < scale * (order : ℝ) ^ 3) :
    0 < partitionWeightBudget rate agreement order (closedMultiplicity scale order) := by
  obtain ⟨-, -, -, hbudget⟩ := closedMultiplicity_estimates hrate hle hscale
  exact Nat.floor_pos.mpr (by linarith)

/-- At the closed-form multiplicity with `K = C d³ > 1` and `0 < R ≤ a`, the inverse radius is
at most `λ₀ K / (K - 1)`, where `λ₀ = (R/a) log(6d)`. -/
theorem partitionInverseRadius_closedMultiplicity_le {rate agreement scale : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hle : rate ≤ agreement) (hscale : 1 < scale * (order : ℝ) ^ 3) :
    partitionInverseRadius rate agreement order (closedMultiplicity scale order) ≤
      rate / agreement * Real.log (6 * (order : ℝ)) *
        (scale * (order : ℝ) ^ 3 / (scale * (order : ℝ) ^ 3 - 1)) := by
  obtain ⟨horder, hlog, -, hbudget⟩ := closedMultiplicity_estimates hrate hle hscale
  have hagreement : 0 < agreement := hrate.trans_le hle
  set m := closedMultiplicity scale order
  set X := (m : ℝ) * agreement * order / (rate * Real.log (6 * (order : ℝ)))
  have hcancel : (order : ℝ) * m = rate / agreement * Real.log (6 * (order : ℝ)) * X := by
    have hlog' : Real.log ((order : ℝ) * 6) ≠ 0 := by rw [mul_comm]; exact hlog.ne'
    simp only [X]
    field_simp
  rw [partitionInverseRadius_eq, hcancel, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (Nat.div_floor_le_div_sub_one hscale hbudget) (by positivity)

/-- At the closed-form multiplicity with `C d³ > 1` and `0 < R ≤ a`, the rounding loss is at
most `closedMultiplicityLoss C d`. -/
theorem partitionRoundingLoss_closedMultiplicity_le {rate agreement scale : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hle : rate ≤ agreement) (hscale : 1 < scale * (order : ℝ) ^ 3) :
    partitionRoundingLoss rate agreement order (closedMultiplicity scale order) ≤
      closedMultiplicityLoss scale order := by
  obtain ⟨horder, hlog, hm, -⟩ := closedMultiplicity_estimates hrate hle hscale
  have hagreement : 0 < agreement := hrate.trans_le hle
  have hlambda := partitionInverseRadius_closedMultiplicity_le hrate hle hscale
  set m := closedMultiplicity scale order
  set lambda := partitionInverseRadius rate agreement order m
  set lambda₀ := rate / agreement * Real.log (6 * (order : ℝ))
  set L := Real.log (6 * (order : ℝ))
  set K := scale * (order : ℝ) ^ 3
  have hK : 0 < K - 1 := by linarith
  have hlambdaNonneg : 0 ≤ lambda := partitionInverseRadius_nonneg _ _ _ _
  have hmPos : (0 : ℝ) < m := lt_of_lt_of_le (by nlinarith) hm
  have hlambda₀ : lambda₀ ≤ L := by
    simp only [lambda₀]
    rw [div_mul_eq_mul_div, div_le_iff₀ hagreement]
    nlinarith
  -- `λ (K - 1) ≤ λ₀ K`
  have hlambdaK : lambda * (K - 1) ≤ lambda₀ * K := by
    rwa [← mul_div_assoc, le_div_iff₀ hK] at hlambda
  -- `λ (K - 1) ≤ d m`
  have hlambdaM : lambda * (K - 1) ≤ order * m := by
    have hLK : lambda₀ * K ≤ L * K := mul_le_mul_of_nonneg_right hlambda₀ (by linarith)
    have hKm : L * K ≤ order * m := by
      have := mul_le_mul_of_nonneg_left hm horder.le
      simp only [K, L]
      nlinarith
    linarith
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 1 + ((order : ℝ) + 1) * lambda / m by positivity)
  have hsplit : lambda * ((order : ℝ) * (order + 1) / (2 * m)) + (order + 1) * lambda / m =
      lambda * (K - 1) / m * ((order + 1) * (order + 2) / 2) / (K - 1) := by
    field_simp
  have hsecond : lambda * (K - 1) / m * ((order + 1) * (order + 2) / 2) / (K - 1) ≤
      (order : ℝ) * (order + 1) * (order + 2) / 2 / (K - 1) := by
    apply div_le_div_of_nonneg_right _ hK.le
    have : lambda * (K - 1) / m ≤ order := by
      rw [div_le_iff₀ hmPos]
      exact hlambdaM
    calc lambda * (K - 1) / m * ((order + 1) * (order + 2) / 2)
        ≤ order * ((order + 1) * (order + 2) / 2) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (order : ℝ) * (order + 1) * (order + 2) / 2 := by ring
  have hfirst : lambda - lambda₀ ≤ L / (K - 1) := by
    rw [le_div_iff₀ hK]
    nlinarith
  have hloss : partitionRoundingLoss rate agreement order m =
      lambda - lambda₀ + lambda * ((order : ℝ) * (order + 1) / (2 * m)) +
        Real.log (1 + (order + 1) * lambda / m) := rfl
  rw [hloss, closedMultiplicityLoss, add_div]
  linarith

/-- At the closed-form multiplicity with `C d³ > 1` and `0 < R ≤ a`, the finite ratio is at
least its limit `(27/20) R (d + 1) exp(-(R/a) log(6d))` times
`exp(-closedMultiplicityLoss C d)`. -/
theorem partitionFiniteRatio_closedMultiplicity_ge {rate agreement scale : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hle : rate ≤ agreement) (hscale : 1 < scale * (order : ℝ) ^ 3) :
    (27 / 20 : ℝ) * rate * (order + 1) *
          Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) *
        Real.exp (-closedMultiplicityLoss scale order) ≤
      partitionFiniteRatio rate agreement order (closedMultiplicity scale order) := by
  rw [partitionFiniteRatio_eq_mul_exp_neg_roundingLoss]
  gcongr
  exact partitionRoundingLoss_closedMultiplicity_le hrate hle hscale

/-- If `closedMultiplicityLoss C d < η`, then at the closed-form multiplicity with `C d³ > 1`
and `0 < R ≤ a` the finite ratio exceeds its limit `(27/20) R (d + 1) exp(-(R/a) log(6d))` times
`exp(-η)`. -/
theorem partitionFiniteRatio_closedMultiplicity_gt {rate agreement scale η : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hle : rate ≤ agreement) (hscale : 1 < scale * (order : ℝ) ^ 3)
    (hloss : closedMultiplicityLoss scale order < η) :
    (27 / 20 : ℝ) * rate * (order + 1) *
          Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) * Real.exp (-η) <
      partitionFiniteRatio rate agreement order (closedMultiplicity scale order) := by
  refine lt_of_lt_of_le ?_ (partitionFiniteRatio_closedMultiplicity_ge hrate hle hscale)
  gcongr

/-- For `C = 1000` and `d ≥ 6`, the rounding-loss bound is below `1/1000`. -/
theorem closedMultiplicityLoss_thousand_lt {order : ℕ} (horder : 6 ≤ order) :
    closedMultiplicityLoss 1000 order < 1 / 1000 := by
  have hd : (6 : ℝ) ≤ order := by exact_mod_cast horder
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 * order by positivity)
  have hcube : (6 : ℝ) ^ 3 ≤ (order : ℝ) ^ 3 := by gcongr
  rw [closedMultiplicityLoss, div_lt_iff₀ (by nlinarith)]
  have h₁ : 0 ≤ ((order : ℝ) - 6) * (order : ℝ) := by nlinarith
  have h₂ : 0 ≤ ((order : ℝ) - 6) * (order : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- For `C = 300` and `d ≥ 500`, the rounding-loss bound is below `1677/10⁶`. -/
theorem closedMultiplicityLoss_three_hundred_lt {order : ℕ} (horder : 500 ≤ order) :
    closedMultiplicityLoss 300 order < 1677 / 1000000 := by
  have hd : (500 : ℝ) ≤ order := by exact_mod_cast horder
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 * order by positivity)
  have hcube : (500 : ℝ) ^ 3 ≤ (order : ℝ) ^ 3 := by gcongr
  rw [closedMultiplicityLoss, div_lt_iff₀ (by nlinarith)]
  have h₁ : 0 ≤ ((order : ℝ) - 500) * (order : ℝ) := by nlinarith
  have h₂ : 0 ≤ ((order : ℝ) - 500) * (order : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- For `C ≥ 3` and `d ≥ 1`, the closed-form multiplicity is at least `d + 2`. -/
theorem add_two_le_closedMultiplicity {scale : ℝ} {order : ℕ} (hscale : 3 ≤ scale)
    (horder : 1 ≤ order) : order + 2 ≤ closedMultiplicity scale order := by
  have hd : (1 : ℝ) ≤ order := by exact_mod_cast horder
  have hlog : 1 < Real.log (6 * (order : ℝ)) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr (Real.exp_one_lt_three.trans (by linarith))
  have hm : scale * (order : ℝ) ^ 2 * Real.log (6 * order) ≤ closedMultiplicity scale order :=
    Nat.le_ceil _
  have hsq : 3 * (order : ℝ) ^ 2 ≤ scale * (order : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hscale (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hlog.le (by positivity : 0 ≤ scale * (order : ℝ) ^ 2)
  exact_mod_cast (show (order : ℝ) + 2 ≤ closedMultiplicity scale order by nlinarith)

end ReedSolomon.HiddenDerivative.RatePartition
