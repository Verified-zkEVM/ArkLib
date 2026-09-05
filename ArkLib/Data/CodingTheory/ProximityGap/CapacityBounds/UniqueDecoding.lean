/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.UniqueDecoding.Internal

/-!
# Reed--Solomon CA in the unique-decoding range

This module proves the BCHKS25 correlated-agreement bound between one third of the minimum
distance and the finite-length half-distance boundary. The interpolation and collision-counting
machinery is isolated in `UniqueDecoding.Internal`; this module retains the final probability
calculation and the source-facing theorem.

## Main result

- `rs_epsCa_le_in_unique_decoding_range` is [BCHKS25, Theorem 1.3].

## References

- [BCHKS25] Theorem 1.3.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap
open UniqueDecoding.Internal

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped NNReal ProbabilityTheory in
omit [DecidableEq ι] in
private theorem rs_fold_probability_le_bound_of_not_joint_proximity
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_ud : (δ_fld : ℝ) ≤
      (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
      / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int)
    (u : Fin 2 → ι → F)
    (hjoint : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int) :
    Pr_{let z ← $ᵖ F}[
      δᵣ(u 0 + z • u 1, ReedSolomon.code domain k) ≤ δ_fld] ≤
      ENNReal.ofReal
        (max
          ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
            ((δ_fld : ℝ) *
              (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
              Fintype.card F))
          ((δ_int : ℝ) /
            (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))) := by
  classical
  let good := ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ_fld
  let T₁ : ℝ :=
    (1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
      ((δ_fld : ℝ) *
        (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)))
  let T₂ : ℝ := (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ))
  have hcard : (good.card : ℝ) ≤ max T₁ T₂ := by
    simpa [good, T₁, T₂] using
      rs_good_coeffs_card_le_max_threshold_of_not_joint_proximity
        domain k δ_fld δ_int u h_ud h_dmin h_lt hjoint
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  change (good.card : ℝ) / Fintype.card F ≤
    max
      ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
        ((δ_fld : ℝ) *
          (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
          Fintype.card F))
      ((δ_int : ℝ) /
        (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
  calc
    (good.card : ℝ) / Fintype.card F ≤
        max T₁ T₂ / Fintype.card F :=
      div_le_div_of_nonneg_right hcard hq.le
    _ = max (T₁ / Fintype.card F) (T₂ / Fintype.card F) := by
      symm
      exact max_div_div_right hq.le T₁ T₂
    _ = max
        ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
          ((δ_fld : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
            Fintype.card F))
        ((δ_int : ℝ) /
          (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F)) := by
      apply congrArg₂ max
      · simp only [T₁]
        rw [div_div]
      · simp only [T₂]
        rw [div_div]

open scoped NNReal in
open scoped ProbabilityTheory in
omit [DecidableEq ι] in
/-- Bounds Reed--Solomon CA error when `δ_fld` lies between one third of the minimum
distance and the finite-length unique-decoding radius, and `δ_fld < δ_int`. -/
theorem rs_epsCa_le_in_unique_decoding_range
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (_h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (_h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (_h_lt : δ_fld < δ_int) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / ((δ_int - δ_fld) * Fintype.card F))
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
      ENNReal.ofReal bound := by
  classical
  dsimp
  unfold epsCa
  refine iSup_le fun u => ?_
  by_cases hj : Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int
  · rw [if_pos hj]
    exact zero_le
  · rw [if_neg hj]
    exact rs_fold_probability_le_bound_of_not_joint_proximity
      domain k δ_fld δ_int _h_ud _h_dmin _h_lt u hj

end ReedSolomon

end CodingTheory
