/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Analysis.Simplex.VolumeIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The weighted-simplex diagonal change of variables

The map `u_i ↦ (i+1)u_i` identifies the weighted simplex with the ordinary simplex.
This file records its determinant and the resulting set-integral Jacobian.  It is the shared
change-of-variables route for both weighted volumes and moments.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace SimplexIntegration

/-- The positive integer weight on the `i`-th coordinate. -/
def coordinateWeight {n : ℕ} (i : Fin n) : ℝ := i.val + 1

/-- The weighted simplex `Σ_i (i+1)u_i ≤ W` in the nonnegative orthant. -/
def weightedSimplex (n : ℕ) (W : ℝ) : Set (Fin n → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, coordinateWeight i * u i ≤ W}

/-- The diagonal map from weighted coordinates to ordinary simplex coordinates. -/
noncomputable def weightedToStandard (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' (Matrix.diagonal coordinateWeight)

@[simp]
theorem weightedToStandard_apply {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    weightedToStandard n u i = coordinateWeight i * u i := by
  classical
  simp [weightedToStandard, Matrix.toLin'_apply, Matrix.mulVec, coordinateWeight]

/-- The inverse diagonal map. -/
noncomputable def standardToWeighted {n : ℕ} (t : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ t i / coordinateWeight i

@[simp]
theorem weightedToStandard_standardToWeighted {n : ℕ} (t : Fin n → ℝ) :
    weightedToStandard n (standardToWeighted t) = t := by
  funext i
  rw [weightedToStandard_apply]
  change coordinateWeight i * (t i / coordinateWeight i) = t i
  have hw : coordinateWeight i ≠ 0 := by
    unfold coordinateWeight
    positivity
  field_simp

@[simp]
theorem standardToWeighted_weightedToStandard {n : ℕ} (u : Fin n → ℝ) :
    standardToWeighted (weightedToStandard n u) = u := by
  funext i
  change weightedToStandard n u i / coordinateWeight i = u i
  rw [weightedToStandard_apply]
  have hw : coordinateWeight i ≠ 0 := by
    unfold coordinateWeight
    positivity
  field_simp

/-- The diagonal linear equivalence underlying the weighted change of variables. -/
noncomputable def weightedStandardLinearEquiv (n : ℕ) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toLinearMap := weightedToStandard n
  invFun := standardToWeighted
  left_inv := standardToWeighted_weightedToStandard
  right_inv := weightedToStandard_standardToWeighted

theorem weightedSimplex_eq_preimage (n : ℕ) (W : ℝ) :
    weightedSimplex n W = weightedToStandard n ⁻¹' standardSimplex n W := by
  ext u
  simp only [weightedSimplex, standardSimplex, Set.mem_ofPred_eq, Set.mem_preimage,
    weightedToStandard_apply]
  constructor
  · rintro ⟨hu, hsum⟩
    refine ⟨fun i ↦ mul_nonneg ?_ (hu i), hsum⟩
    unfold coordinateWeight
    positivity
  · rintro ⟨hu, hsum⟩
    refine ⟨fun i ↦ ?_, hsum⟩
    apply nonneg_of_mul_nonneg_right (hu i)
    unfold coordinateWeight
    positivity

theorem weightedSimplex_eq_image (n : ℕ) (W : ℝ) :
    weightedSimplex n W = standardToWeighted '' standardSimplex n W := by
  rw [weightedSimplex_eq_preimage]
  ext u
  constructor
  · intro hu
    refine ⟨weightedToStandard n u, hu, ?_⟩
    exact standardToWeighted_weightedToStandard u
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

/-- Weighted simplices are compact; this is the compactness input used by all moment
integrability proofs. -/
theorem isCompact_weightedSimplex (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    IsCompact (weightedSimplex n W) := by
  rw [weightedSimplex_eq_image]
  apply (isCompact_standardSimplex n hW).image
  change Continuous (weightedStandardLinearEquiv n).symm
  exact LinearMap.continuous_on_pi (weightedStandardLinearEquiv n).symm.toLinearMap

/-- A continuous function is integrable on a weighted simplex. -/
theorem Continuous.integrableOn_weightedSimplex {n : ℕ} {W : ℝ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hW : 0 ≤ W) :
    IntegrableOn f (weightedSimplex n W) :=
  hf.continuousOn.integrableOn_compact (isCompact_weightedSimplex n hW)

/-- A function continuous on a weighted simplex is integrable there. -/
theorem ContinuousOn.integrableOn_weightedSimplex {n : ℕ} {W : ℝ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (weightedSimplex n W)) (hW : 0 ≤ W) :
    IntegrableOn f (weightedSimplex n W) :=
  hf.integrableOn_compact (isCompact_weightedSimplex n hW)

theorem weightedToStandard_det (n : ℕ) :
    LinearMap.det (weightedToStandard n) = (n.factorial : ℝ) := by
  classical
  rw [weightedToStandard, LinearMap.det_toLin', Matrix.det_diagonal]
  calc
    (∏ i : Fin n, coordinateWeight i) =
        ∏ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) := by
          rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) n]
          apply Finset.prod_congr rfl
          intro i _
          simp only [coordinateWeight, Nat.cast_add, Nat.cast_one]
    _ = (n.factorial : ℝ) := by
      norm_cast
      exact (Nat.factorial_eq_prod_range_add_one n).symm

private noncomputable def weightedStandardMeasurableEquiv (n : ℕ) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toEquiv := weightedStandardLinearEquiv n
  measurable_toFun := (LinearMap.continuous_on_pi (weightedToStandard n)).measurable
  measurable_invFun :=
    (LinearMap.continuous_on_pi (weightedStandardLinearEquiv n).symm.toLinearMap).measurable

/-- Exact weighted-to-standard set-integral substitution.  The factor `1 / n!` is the
Jacobian of `t_i ↦ t_i/(i+1)`. -/
theorem integral_weightedSimplex_eq_standardSimplex (n : ℕ) (W : ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ u in weightedSimplex n W, f u) =
      (1 / n.factorial) *
        ∫ t in standardSimplex n W, f (standardToWeighted t) := by
  let e := weightedStandardMeasurableEquiv n
  have hdet : LinearMap.det (weightedToStandard n) ≠ 0 := by
    rw [weightedToStandard_det]
    exact_mod_cast Nat.factorial_ne_zero n
  have hmap : Measure.map e volume =
      ENNReal.ofReal |((n.factorial : ℝ))⁻¹| • volume := by
    change Measure.map (weightedToStandard n) volume = _
    rw [← weightedToStandard_det]
    exact Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have hchange := setIntegral_map_equiv (μ := volume) e (f ∘ e.symm)
    (standardSimplex n W)
  rw [hmap, Measure.restrict_smul, integral_smul_measure] at hchange
  have hpre : e ⁻¹' standardSimplex n W = weightedSimplex n W := by
    change weightedToStandard n ⁻¹' standardSimplex n W = weightedSimplex n W
    exact (weightedSimplex_eq_preimage n W).symm
  rw [hpre] at hchange
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] at hchange
  have hinv : ∀ t, e.symm t = standardToWeighted t := by
    intro t
    rfl
  have hfun : (fun t ↦ f (e.symm t)) = fun t ↦ f (standardToWeighted t) := by
    funext t
    rw [hinv]
  rw [hfun] at hchange
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos] at hchange
  · rw [one_div]
    change (∫ u in weightedSimplex n W, f u) =
      (n.factorial : ℝ)⁻¹ *
        ∫ t in standardSimplex n W, f (standardToWeighted t)
    change (n.factorial : ℝ)⁻¹ *
      (∫ t in standardSimplex n W, f (standardToWeighted t)) =
        ∫ u in weightedSimplex n W, f u at hchange
    exact hchange.symm
  · positivity

/-- The weighted simplex has volume `W ^ n / (n!)²`: one factorial comes from the
ordinary simplex, and one from the diagonal Jacobian. -/
theorem volume_weightedSimplex (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    volume.real (weightedSimplex n W) = W ^ n / (n.factorial : ℝ) ^ 2 := by
  have h := integral_weightedSimplex_eq_standardSimplex n W (fun _ ↦ 1)
  rw [show (∫ _ in weightedSimplex n W, (1 : ℝ)) =
      volume.real (weightedSimplex n W) by
        simp [weightedSimplex_eq_preimage],
    show (∫ _ in standardSimplex n W, (1 : ℝ)) =
      volume.real (standardSimplex n W) by
        simp,
    volume_standardSimplex n hW] at h
  rw [h]
  field_simp

end SimplexIntegration
