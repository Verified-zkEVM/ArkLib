/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds

/-!
# Finite Johnson parameter acceptance tests

The recipe at `n = 4`, `D = 1`, `η = 1/4`, `A = 3` computed in full, the closed bounds applied to
it, cases showing that the remaining hypotheses are needed, and the source-shaped statements
derived from the generalized ones.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### A concrete parameter set: `n = 4`, `D = 1`, `η = 1/4`, `A = 3` -/

private theorem test_rho : johnsonRhoMinus 4 1 = 1 / 4 := by
  norm_num [johnsonRhoMinus]

private theorem test_sqrt : √(johnsonRhoMinus 4 1) = 1 / 2 := by
  rw [test_rho, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `ρ₋ = 1/4`, so the agreement fraction is `1/2 + 1/4 = 3/4`. -/
private theorem test_agreement : johnsonAgreement 4 1 (1 / 4) = 3 / 4 := by
  rw [johnsonAgreement, test_sqrt]
  norm_num

/-- `⌈(1/2) / (1/2)⌉₊ = 1`, so the floor `3` is active: `m = 3`. -/
private theorem test_M : johnsonM 4 1 (1 / 4) = 3 := by
  rw [johnsonM, test_sqrt]
  norm_num

private theorem test_T : johnsonT 4 1 (1 / 4) = 7 / 2 := by
  rw [johnsonT, test_M]
  norm_num

/-- `μ = ⌈(7/2) / (1/2)⌉₊ - 1 = 6`. -/
private theorem test_Mu : johnsonMu 4 1 (1 / 4) = 6 := by
  rw [johnsonMu, test_T, test_sqrt]
  norm_num

/-- `h = ⌈(49/4) / (3/4)⌉₊ - 1 = ⌈49/3⌉₊ - 1 = 16`. -/
private theorem test_H : johnsonH 4 1 (1 / 4) = 16 := by
  have hceil : ⌈(7 / 2 : ℝ) ^ 2 / (3 * (1 / 4))⌉₊ = 17 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [johnsonH, test_T, test_rho, hceil]

/-- `θ = (4 - 1) / (3 - 1) = 3/2`. -/
private theorem test_theta : johnsonTheta 4 1 3 = 3 / 2 := by
  norm_num [johnsonTheta]

/-- `E₀ = 11 · 16 + (3/2)(16 + 6 + 384) + 2 · 6 = 797`. -/
private theorem test_E0 : johnsonE0 4 1 3 (1 / 4) = 797 := by
  simp only [johnsonE0, test_Mu, test_H, test_theta]
  norm_num

/-- The threshold `(3/4) · 4 = 3 ≤ A` holds with equality. -/
private theorem test_threshold : johnsonAgreement 4 1 (1 / 4) * (4 : ℕ) ≤ (3 : ℕ) := by
  rw [test_agreement]
  norm_num

/-- The closed bound gives `797 < (8/3) · 4 · (7/2)³ / (1/4) = 5488/3`. -/
example : johnsonE0 4 1 3 (1 / 4) < 5488 / 3 := by
  have h := johnsonE0_lt_closed (n := 4) (D := 1) (A := 3) (eta := 1 / 4)
    le_rfl (by norm_num) (by norm_num) test_threshold
  rw [test_T, test_rho] at h
  linarith

/-- `μ < t / √ρ₋` is `6 < 7`, and `h < t² / (3ρ₋)` is `16 < 49/3`. -/
example : (johnsonMu 4 1 (1 / 4) : ℝ) < 7 ∧ (johnsonH 4 1 (1 / 4) : ℝ) < 49 / 3 := by
  have h1 := johnsonMu_lt (n := 4) (D := 1) (eta := 1 / 4) le_rfl (by norm_num)
  have h2 := johnsonH_lt (n := 4) (D := 1) (eta := 1 / 4) le_rfl (by norm_num)
  rw [test_T, test_sqrt] at h1
  rw [test_T, test_rho] at h2
  constructor <;> [linarith; linarith]

/-- The incidence ratio `3/2` is below `(1 + 1/2) / (1/2) = 3`. -/
example : johnsonTheta 4 1 3 ≤ 3 := by
  have h := johnsonTheta_le_sqrt_envelope (n := 4) (D := 1) (A := 3) (eta := 1 / 4)
    le_rfl (by norm_num) (by norm_num) test_threshold
  rw [test_sqrt] at h
  linarith

/-- The BCHKS comparison holds at the concrete parameters. -/
example : johnsonE0 4 1 3 (1 / 4) < johnsonBCHKS 4 1 (1 / 4) :=
  johnsonE0_lt_BCHKS le_rfl (by norm_num) (by norm_num) (by rw [test_agreement]; norm_num)
    test_threshold

/-! ### The remaining hypotheses are needed -/

/-- `1 ≤ D` is needed in `johnsonMu_lt`: at `D = 0` both sides are `0`. -/
example : ¬ (johnsonMu 4 0 (1 / 4) : ℝ) < johnsonT 4 0 (1 / 4) / √(johnsonRhoMinus 4 0) := by
  simp [johnsonMu, johnsonRhoMinus]

/-- `D ≤ n - 2` is needed in `johnson_inv_length_le_min`: at `n = 3`, `D = 2` the second
restriction reads `1/3 ≤ 1/6`. -/
example : ¬ (1 : ℝ) / (3 : ℕ) ≤ min (√(johnsonRhoMinus 3 2) ^ 2)
    ((1 - √(johnsonRhoMinus 3 2) ^ 2) / 2) := by
  rw [Real.sq_sqrt (by norm_num [johnsonRhoMinus])]
  norm_num [johnsonRhoMinus]

/-- `0 < η` is needed in `johnson_half_gap`: at `η = -1` the right side is `-3`. -/
example : ¬ √(johnsonRhoMinus 4 1) / 2 ≤ johnsonM 4 1 (-1) * (-1) := by
  have hM : johnsonM 4 1 (-1) = 3 := by
    rw [johnsonM, test_sqrt]
    norm_num
  rw [hM, test_sqrt]
  norm_num

/-! ### Source-shaped statements -/

/-- The source form of `johnsonMu_lt`, with the guard `D ≤ n - 2`. -/
example {n D : ℕ} {eta : ℝ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    (johnsonMu n D eta : ℝ) < johnsonT n D eta / √(johnsonRhoMinus n D) :=
  johnsonMu_lt hD (by omega)

/-- The source form of `johnson_half_gap`, with its unused guards. -/
example {n D : ℕ} {eta : ℝ} (_hD : 1 ≤ D) (_hDn : D ≤ n - 2) (heta : 0 < eta) :
    √(johnsonRhoMinus n D) / 2 ≤ johnsonM n D eta * eta :=
  johnson_half_gap n D heta

/-- The source form of `johnsonE0_lt_closed`, with the unused hypotheses
`johnsonAgreement n D eta ≤ 1` and `A ≤ n`. -/
example {n D A : ℕ} {eta : ℝ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (_ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (_hAn : A ≤ n) :
    johnsonE0 n D A eta <
      (8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D :=
  johnsonE0_lt_closed hD hDn heta hthreshold

/-- The source form of `johnsonE0_le_BCHKS`, with the unused hypothesis `A ≤ n`. -/
example {n D A : ℕ} {eta : ℝ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (_hAn : A ≤ n) :
    johnsonE0 n D A eta ≤ johnsonBCHKS n D eta :=
  johnsonE0_le_BCHKS hD hDn heta ha hthreshold

end ReedSolomon.HiddenDerivative
