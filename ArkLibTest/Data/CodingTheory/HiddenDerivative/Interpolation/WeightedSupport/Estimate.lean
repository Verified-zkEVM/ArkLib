/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Estimate

/-!
# Acceptance cases for the integral lower bounds on the weighted support dimension

The source's forms of `weighted_dimension_integral` (with pointwise simplex hypotheses and
`0 ≤ g * m`) and of `weighted_dimension_probability` (an integral against the uniform probability
measure on the simplex, with `0 < W` and `0 < g * m`), derived from the general statements; a
concrete bound at `d = 1`, where the simplex is a single point; and the case `W = 0`, which the
source excluded.
-/

open MeasureTheory Set ReedSolomon.HiddenDerivative
open scoped ProbabilityTheory

/-! ### Source-shaped statements -/

/-- The source's `weighted_dimension_integral`, with the pointwise hypotheses `hu` and `hW` in
place of `T ⊆ weightedSimplex _ W` and the unused hypothesis `0 ≤ g * m`. -/
example (F : Type*) [Field F] (d D W : ℕ) (hd : 0 < d) (hD : 0 < D) (g m μ : ℝ)
    (T : Set (Fin (d - 1) → ℝ)) (hT : MeasurableSet T) (z : (Fin (d - 1) → ℝ) → ℝ)
    (hu : ∀ u ∈ T, ∀ i, 0 ≤ u i) (hW : ∀ u ∈ T, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W)
    (hμhi : μ ≤ (1 + 3 * g / 8) * m) (_hgm0 : 0 ≤ g * m)
    (hZ : ∀ u ∈ T, (∑ i, u i) - μ = z u * (g * m))
    (hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3) T volume) :
    (D : ℝ) / 6 * (∫ u in T, (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3) ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) :=
  weighted_dimension_integral F hd hD g m μ hT (fun u hu' => mem_weightedSimplex.mpr
    ⟨hu u hu', hW u hu'⟩) z hμhi hZ hint

/-- The source's `weighted_dimension_probability`, as an integral against the uniform probability
measure on the simplex, with the unused hypotheses `0 < W` and `0 < g * m`. -/
example (F : Type*) [Field F] (d D W : ℕ) (hd : 0 < d) (hD : 0 < D) (_hW : 0 < W) (g m : ℝ)
    (_ht : 0 < g * m) (hμ : W * (harmonic (d - 1) : ℝ) / d ≤ (1 + 3 * g / 8) * m) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    V * D / 6 * (g * m) ^ 3 *
      (∫ u, (max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3
        ∂volume[|weightedSimplex (fun i : Fin (d - 1) ↦ (i : ℝ) + 1) W]) ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) := by
  intro V
  rw [ProbabilityTheory.cond, ← setAverage_eq']
  exact weighted_dimension_probability F hd hD g m hμ

/-! ### Concrete and boundary cases -/

/-- At `d = 1` there are no higher jets: the simplex is the single point of `Fin 0 → ℝ`, the
normalized radius is `0`, and the bound reads `D / 6 * (g * m) ^ 3 * (5 / 8) ^ 3 ≤ dimension`.
At `D = 1`, `g = 1`, `m = 8` this is `125 / 6 ≤ dimension`, so the space at the cutoff `16` has
dimension at least `21`. -/
example : 21 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 5 16 one_pos) := by
  have h := weighted_dimension_probability ℚ (d := 1) (D := 1) (W := 5) (by norm_num) one_pos 1 8
    (by norm_num [harmonic])
  have hS : weightedSimplex (fun i : Fin (1 - 1) ↦ (i : ℝ) + 1) (5 : ℕ) = univ := by
    ext u
    simp [mem_weightedSimplex]
  have havg : ⨍ u in weightedSimplex (fun i : Fin (1 - 1) ↦ (i : ℝ) + 1) (5 : ℕ),
      (max (5 / 8 - normalizedRadius (5 : ℕ) (1 * 8) u) 0) ^ 3 = (5 / 8 : ℝ) ^ 3 := by
    rw [hS, Measure.restrict_univ]
    simp [normalizedRadius]
    norm_num
  rw [havg, show (8 : ℝ) * ((1 : ℕ) : ℝ) * (1 + 1) = 16 by norm_num] at h
  norm_num at h
  have h20 : (20 : ℝ) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 5 16 one_pos) := by
    linarith
  exact_mod_cast h20

/-- The case `W = 0`, excluded by the source: the simplex in `Fin (d - 1) → ℝ` is the point `0`,
and the bound still holds for every `d`. -/
example (d D : ℕ) (hd : 0 < d) (hD : 0 < D) (g m : ℝ) (hm : 0 ≤ (1 + 3 * g / 8) * m) :
    ((0 : ℕ) : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 * D / 6 * (g * m) ^ 3 *
        ⨍ u in weightedSimplex (fun i : Fin (d - 1) ↦ (i : ℝ) + 1) (0 : ℕ),
          (max (5 / 8 - normalizedRadius (0 : ℕ) (g * m) u) 0) ^ 3 ≤
      Module.finrank ℚ (weightedSupportSpace ℚ D d 0 (m * D * (1 + g)) hD) :=
  weighted_dimension_probability ℚ hd hD g m (by simpa using hm)
