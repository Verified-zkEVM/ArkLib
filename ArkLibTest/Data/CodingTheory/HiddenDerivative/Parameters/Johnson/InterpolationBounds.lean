/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.InterpolationBounds

/-!
# Johnson interpolation count acceptance tests

The instance `n = 4`, `D = 1`, `η = 1` computed in full, the source-shaped statement under the
source guard `D ≤ n - 2`, and a case showing that `1 ≤ D` is needed in `johnsonMu_add_one`.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### `n = 4`, `D = 1`, `η = 1`: `√ρ₋ = 1/2`, `m = 3`, `t = 7/2` -/

private theorem sqrt_rho_4_1 : √(johnsonRhoMinus 4 1) = 1 / 2 := by
  rw [johnsonRhoMinus, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

private theorem johnsonM_4_1_1 : johnsonM 4 1 1 = 3 := by
  rw [johnsonM, sqrt_rho_4_1]
  have : ⌈(1 / 2 : ℝ) / (2 * 1)⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  rw [this]; rfl

private theorem johnsonT_4_1_1 : johnsonT 4 1 1 = 7 / 2 := by
  rw [johnsonT, johnsonM_4_1_1]; norm_num

/-- `X = ⌈(7/2) · 4 · (1/2)⌉₊ = 7`. -/
theorem johnsonXCutoff_4_1_1 : johnsonXCutoff 4 1 1 = 7 := by
  rw [johnsonXCutoff, johnsonT_4_1_1, sqrt_rho_4_1]
  norm_num

/-- `μ = ⌈(7/2) / (1/2)⌉₊ - 1 = 6`. -/
theorem johnsonMu_4_1_1 : johnsonMu 4 1 1 = 6 := by
  rw [johnsonMu, johnsonT_4_1_1, sqrt_rho_4_1]
  norm_num

/-- `h = ⌈(49/4) / (3/4)⌉₊ - 1 = ⌈49/3⌉₊ - 1 = 16`. -/
theorem johnsonH_4_1_1 : johnsonH 4 1 1 = 16 := by
  rw [johnsonH, johnsonT_4_1_1, johnsonRhoMinus]
  have : ⌈(7 / 2 : ℝ) ^ 2 / (3 * ((1 : ℕ) / (4 : ℕ) : ℝ))⌉₊ = 17 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  rw [this]

/-- The concrete slot counts: `4 · (3·17 + 2·16 + 1·15) = 392` constraints against
`∑_{j ≤ 6} (7 - j)(17 - j) = 420` source coefficients. -/
theorem slot_counts_4_1_1 :
    johnsonRowSlotCount 4 3 16 = 392 ∧ johnsonSourceSlotCount 7 1 6 16 = 420 := by
  decide

/-- The surplus theorem at this instance, matched against the computed counts. -/
example : johnsonRowSlotCount 4 3 16 < johnsonSourceSlotCount 7 1 6 16 := by
  have h := johnson_interpolation_slot_surplus (n := 4) (D := 1) (eta := 1) le_rfl (by norm_num)
  rwa [johnsonM_4_1_1, johnsonH_4_1_1, johnsonXCutoff_4_1_1, johnsonMu_4_1_1] at h

/-- `D μ < X` at this instance is `6 < 7`: the top slice has exactly one `x`-degree. -/
example : 1 * johnsonMu 4 1 1 < johnsonXCutoff 4 1 1 :=
  johnson_D_mul_mu_lt_XCutoff le_rfl (by norm_num)

/-- `X ≤ m A` at the smallest admissible threshold `A = ⌈(1/2 + 1) · 4⌉ = 6`: `7 ≤ 18`. -/
example : johnsonXCutoff 4 1 1 ≤ johnsonM 4 1 1 * 6 :=
  johnsonXCutoff_le_mul_agreement one_pos (by
    rw [johnsonAgreement, sqrt_rho_4_1]; norm_num)

/-! ### Source-shaped statement -/

/-- The source statement, with guard `D ≤ n - 2`, follows from the weakened guard `D < n`. -/
example {n D : ℕ} {eta : ℝ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    johnsonRowSlotCount n (johnsonM n D eta) (johnsonH n D eta) <
      johnsonSourceSlotCount (johnsonXCutoff n D eta) D
        (johnsonMu n D eta) (johnsonH n D eta) :=
  johnson_interpolation_slot_surplus hD (by omega)

/-! ### Necessity -/

/-- `1 ≤ D` is needed in `johnsonMu_add_one`: at `D = 0` the ceiling is `⌈t / 0⌉₊ = 0`, while
`μ + 1 = 1`. -/
example : johnsonMu 4 0 1 + 1 ≠ ⌈johnsonT 4 0 1 / √(johnsonRhoMinus 4 0)⌉₊ := by
  simp [johnsonMu, johnsonRhoMinus]

end ReedSolomon.HiddenDerivative
