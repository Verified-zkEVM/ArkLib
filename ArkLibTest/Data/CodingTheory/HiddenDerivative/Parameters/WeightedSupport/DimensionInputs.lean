/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs

/-!
# Acceptance cases for the rounding inputs of the weighted dimension estimate

An instance of `prescribed_dimension_inputs` at the smallest admitted order `d = 3`, and the
source's statement, with `48000 ≤ d` and the gap written as `min 1 (δ / ρ)`, derived from the
general one.
-/

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- At `d = 3`, `δ = 1 / 4`, `ρ = 1 / 2` and `H = ξ / δ = 54 / 5`: here `g = 1 / 2`,
`a = 19 / 16`, `m = ⌈9720⌉₊`, and the five rounding inputs hold. -/
example :
    let g := rateGap (1 / 4) (1 / 2)
    let a := 1 + theta * g
    let m := ⌈100 * ((3 : ℕ) : ℝ) ^ 2 * (54 / 5)⌉₊
    let W := ⌊a * (3 : ℕ) * m / (54 / 5)⌋₊
    0 < m ∧ 0 < W ∧
      (W : ℝ) * (54 / 5) / (3 : ℕ) ≤ (1 + 3 * g / 8) * m ∧
      (W : ℝ) / (((3 : ℕ) : ℝ) * (g * m)) ≤ 10 / 27 ∧
      (999 / 1000) * (a / (g * (54 / 5))) ^ 2 ≤ ((W : ℝ) / (((3 : ℕ) : ℝ) * (g * m))) ^ 2 :=
  prescribed_dimension_inputs (1 / 4) (1 / 2) (54 / 5) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num [xi])

/-- The source's `prescribed_dimension_inputs`, with `48000 ≤ d`. -/
example (δ ρ H : ℝ) (d : ℕ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ)
    (hd : 48000 ≤ d) (hHlo : xi / δ ≤ H) :
    let g := min 1 (δ / ρ)
    let a := 1 + theta * g
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    0 < m ∧ 0 < W ∧
      (W : ℝ) * H / d ≤ (1 + 3 * g / 8) * m ∧
      (W : ℝ) / ((d : ℝ) * (g * m)) ≤ 10 / 27 ∧
      (999 / 1000) * (a / (g * H)) ^ 2 ≤
        ((W : ℝ) / ((d : ℝ) * (g * m))) ^ 2 :=
  prescribed_dimension_inputs δ ρ H d hδ hδmax hρ hρmax (by omega) hHlo
