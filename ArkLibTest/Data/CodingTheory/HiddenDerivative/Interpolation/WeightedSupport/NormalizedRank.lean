/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.NormalizedRank
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Acceptance cases for the volume-normalized weighted local rank

A concrete instance of the scalar conversion, the case showing that its hypothesis `0 < c` is
needed for strictness, and `normalized_rank_lt_of_rounding_bounds` and
`finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error` specialized to
`c = 448 / 625`, `b = 3 / 5`, `K = 37 / 20`, `a = 1 + 3 g / 8`, `L = m D (1 + g)` and
`48000 ≤ d`.
-/

open Finset ReedSolomon.HiddenDerivative

/-- `g = c = E = a = H = κ = d = m = 1`, `b = 1`, `e = 0`, `ρ = 2`, `K = 3`, `X = 1`: the
normalized bound is `R = 2 exp 1`, and the conversion gives `2 exp 1 < 1 · 1 · 2 · 3 = 6`. -/
example : 2 * Real.exp 1 < 6 := by
  have h := normalized_rank_lt_of_rounding_bounds (2 * Real.exp 1) 1 1 1 1 1 0 2 3 1 1 1 1 1
    one_pos one_pos le_rfl le_rfl zero_le_one one_pos one_pos one_pos one_pos
    (by simp) (by norm_num) (by simpa using Real.exp_one_lt_d9.trans (by norm_num))
    (by norm_num) (by norm_num; ring_nf; exact le_rfl)
  norm_num at h
  exact h

/-- The hypothesis `0 < c` is needed for strictness: with `c = E = R = 0` every other hypothesis
holds at the parameters above, but the conclusion `0 < 0` fails. -/
example : (0 : ℝ) ≤ 1 * 0 * Real.exp 1 * (1 / (1 * 1 ^ 2) + 1 / (1 * 1)) ∧
    ¬ ((0 : ℝ) < 1 * 0 * 2 * 3 * 1 ^ 2 / 1 ^ 2 * (1 : ℝ) ^ (1 / (1 : ℝ)) / 1) := by
  norm_num

/-- `normalized_rank_lt_of_rounding_bounds` at `c = 448 / 625`, `b = 3 / 5`,
`e = 1 / 100`, `ρ = 101 / 100`, `K = 37 / 20`, and natural `d`, `m`. -/
example (R g Ee a H E κ : ℝ) (d m : ℕ)
    (hg : 0 < g) (hEe : Ee ≤ 448 / 625)
    (ha : 1 ≤ a) (hH : 0 < H) (hd : 0 < d) (hm : 0 < m) (hκ : 0 < κ)
    (hHlog : H ≤ Real.log d + 3 / 5) (hE : E ≤ H / a + 1 / 100)
    (hrec : 1 / κ ^ 2 + (d : ℝ) / (m * κ) ≤ 101 / 100 * (1 / (H / a) ^ 2))
    (hR : R ≤ g * Ee * Real.exp E * (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ))) :
    R < g * (448 / 625) * (101 / 100) * (37 / 20) *
      a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d :=
  normalized_rank_lt_of_rounding_bounds R g Ee (448 / 625) a (3 / 5) (1 / 100) (101 / 100)
    (37 / 20) H E κ d m hg (by norm_num) hEe ha (by norm_num) hH (by exact_mod_cast hd)
    (by exact_mod_cast hm) hκ hHlog hE (by norm_num; exact Real.exp_sixtyOne_div_hundred_lt)
    hrec hR

/-- `finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error` at
`a = 1 + 3 g / 8`, `L = m D (1 + g)` (so `L / D = m (1 + g)`), `c = 448 / 625`, `b = 3 / 5`,
`K = 37 / 20` and `48000 ≤ d`. -/
example {F : Type*} [Field F] (g H : ℝ) (d D : ℕ)
    (hg : 0 < g) (hH : 0 < H) (hd : 48000 ≤ d) (hD : 0 < D)
    (hHlog : H ≤ Real.log d + 3 / 5)
    (hgap :
      let a := 1 + 3 * g / 8
      let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
      let W := ⌊a * d * m / H⌋₊
      ∀ r ∈ range m,
        (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d <
          (m : ℝ) * (1 + g) + (d - 1 : ℕ))
    (herror :
      let a := 1 + 3 * g / 8
      let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
      let W := ⌊a * d * m / H⌋₊
      ∀ r ∈ range m,
        (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
            (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d +
            ((((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
                (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
              (4 * ((m : ℝ) * (1 + g) + (d - 1 : ℕ) -
                (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d)) + 1 ≤
          g * m * (448 / 625))
    (center received : F) :
    let a := 1 + 3 * g / 8
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊a * d * m / H⌋₊
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD center received)) : ℝ) / (V * m ^ 3) <
      g * (448 / 625) * (101 / 100) * (37 / 20) *
        a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  intro a m W V
  have hDR : (D : ℝ) ≠ 0 := by positivity
  have hLD : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by field_simp
  have ha : 1 ≤ a := by
    have : 0 ≤ 3 * g / 8 := by positivity
    simp only [a]
    linarith
  exact finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error
    d D ((m : ℝ) * D * (1 + g)) g (448 / 625) a (3 / 5) (37 / 20) H (by omega) hD hg
    (by norm_num) ha (by norm_num) hH hHlog
    (by norm_num; exact Real.exp_sixtyOne_div_hundred_lt)
    (by rw [hLD]; exact hgap) (by rw [hLD]; exact herror) center received
