/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.OrderedSimplex
public import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Maximum-coordinate moments for the rate-partition simplex

The maximum below ranges over the `d` genuine simplex coordinates.  The implicit slack
coordinate is deliberately excluded.  Sorting the genuine coordinates decomposes the ordinary
simplex into `d!` chambers, and the determinant-one cumulative map identifies one chamber with
the weighted simplex having weights `1, ..., d`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- Maximum of the `d` genuine coordinates; the slack coordinate is not included. -/
noncomputable def simplexMaximum (d : ℕ) [NeZero d] (x : Fin d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

theorem continuous_simplexMaximum (d : ℕ) [NeZero d] :
    Continuous (simplexMaximum d) := by
  unfold simplexMaximum
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun _ _ ↦ continuous_apply _

theorem simplexMaximum_le_iff {d : ℕ} [NeZero d] {x : Fin d → ℝ} {a : ℝ} :
    simplexMaximum d x ≤ a ↔ ∀ i, x i ≤ a := by
  simp [simplexMaximum, Finset.sup'_le_iff]

theorem le_simplexMaximum {d : ℕ} [NeZero d] (x : Fin d → ℝ) (i : Fin d) :
    x i ≤ simplexMaximum d x := by
  exact Finset.le_sup' x (Finset.mem_univ i)

theorem simplexMaximum_eq_zero_of_antitone {d : ℕ} [NeZero d]
    {x : Fin d → ℝ} (hx : Antitone x) :
    simplexMaximum d x = x 0 := by
  apply le_antisymm
  · rw [simplexMaximum_le_iff]
    intro i
    exact hx (Fin.zero_le i)
  · exact le_simplexMaximum x 0

theorem simplexMaximum_permute {d : ℕ} [NeZero d] (σ : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) :
    simplexMaximum d (permuteCoordinates σ x) = simplexMaximum d x := by
  apply le_antisymm <;> rw [simplexMaximum_le_iff] <;> intro i
  · rw [permuteCoordinates_apply]
    exact le_simplexMaximum x (σ i)
  · calc
      x i = permuteCoordinates σ x (σ.symm i) := by simp
      _ ≤ simplexMaximum d (permuteCoordinates σ x) :=
        le_simplexMaximum (permuteCoordinates σ x) (σ.symm i)

/-- Uniform expectation of a test function of the genuine-coordinate maximum. -/
noncomputable def simplexMaximumExpectation (d : ℕ) [NeZero d] (W : ℝ)
    (f : ℝ → ℝ) : ℝ :=
  ⨍ x in SimplexIntegration.standardSimplex d W, f (simplexMaximum d x)

private theorem integral_permutationChamber_maximum {d : ℕ} [NeZero d]
    {W : ℝ} (hW : 0 ≤ W) (f : ℝ → ℝ) (_hf : Continuous f)
    (σ : Equiv.Perm (Fin d)) :
    (∫ x in permutationChamber W σ, f (simplexMaximum d x)) =
      ∫ v in orderedSimplex d W, f (v 0) := by
  have hchange := setIntegral_map_equiv (μ := volume) (permuteCoordinates σ)
    (fun v : Fin d → ℝ ↦ f (v 0)) (orderedSimplex d W)
  rw [permuteCoordinates_map_volume,
    ← permutationChamber_eq_preimage_ordered W σ] at hchange
  calc
    (∫ x in permutationChamber W σ, f (simplexMaximum d x)) =
        ∫ x in permutationChamber W σ, f (permuteCoordinates σ x 0) := by
      apply setIntegral_congr_fun (isCompact_permutationChamber hW σ).isClosed.measurableSet
      intro x hx
      change f (simplexMaximum d x) = f (permuteCoordinates σ x 0)
      have hanti : Antitone (permuteCoordinates σ x) := by
        intro i j hij
        have h := hx.2 hij
        change x (σ j) ≤ x (σ i) at h
        rw [permuteCoordinates_apply, permuteCoordinates_apply]
        exact h
      congr 1
      calc
        simplexMaximum d x = simplexMaximum d (permuteCoordinates σ x) :=
          (simplexMaximum_permute σ x).symm
        _ = permuteCoordinates σ x 0 := simplexMaximum_eq_zero_of_antitone hanti
    _ = ∫ v in orderedSimplex d W, f (v 0) := hchange.symm

/-- Sorting the genuine coordinates gives `d!` equal chambers. -/
theorem integral_standardSimplex_maximum {d : ℕ} [NeZero d]
    {W : ℝ} (hW : 0 ≤ W) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in SimplexIntegration.standardSimplex d W, f (simplexMaximum d x)) =
      d.factorial * ∫ v in orderedSimplex d W, f (v 0) := by
  have hint : IntegrableOn (fun x : Fin d → ℝ ↦ f (simplexMaximum d x))
      (SimplexIntegration.standardSimplex d W) :=
    (hf.comp (continuous_simplexMaximum d)).continuousOn.integrableOn_compact
      (SimplexIntegration.isCompact_standardSimplex d hW)
  rw [← iUnion_permutationChamber W] at hint ⊢
  rw [integral_iUnion_ae
    (fun σ ↦ (isCompact_permutationChamber hW σ).isClosed.measurableSet.nullMeasurableSet)
    (permutationChamber_pairwise_ae_disjoint W) hint, tsum_fintype]
  simp_rw [integral_permutationChamber_maximum hW f hf]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- The normalized maximum law equals the weighted-radius law, for every positive radius. -/
theorem simplexMaximumExpectation_eq_weightedRadius {d : ℕ} [NeZero d]
    {W : ℝ} (hW : 0 < W) (f : ℝ → ℝ) (hf : Continuous f) :
    simplexMaximumExpectation d W f =
      SimplexIntegration.weightedSimplexExpectation d W
        (fun u ↦ f (SimplexIntegration.weightedRadius u)) := by
  rw [simplexMaximumExpectation, SimplexIntegration.weightedSimplexExpectation,
    setAverage_eq, setAverage_eq, integral_standardSimplex_maximum hW.le f hf]
  have hsource := integral_weightedSimplex_comp_cumulative d W (fun v ↦ f (v 0))
  simp only [cumulativeCoordinates_zero_eq_weightedRadius] at hsource
  rw [hsource]
  rw [SimplexIntegration.volume_standardSimplex d hW.le,
    SimplexIntegration.volume_weightedSimplex d hW.le]
  have hfac : (d.factorial : ℝ) ≠ 0 := by positivity
  have hpow : (W ^ d : ℝ) ≠ 0 := pow_ne_zero _ hW.ne'
  field_simp
  ring

/-- Dilation of every coordinate by a nonzero scalar, as a linear equivalence. -/
private noncomputable def simplexScaleLinearEquiv (d : ℕ) (W : ℝ) (hW : W ≠ 0) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) where
  toLinearMap := W • LinearMap.id
  invFun x := W⁻¹ • x
  left_inv x := by
    ext i
    simp [hW]
  right_inv x := by
    ext i
    simp [hW]

@[simp]
private theorem simplexScaleLinearEquiv_apply {d : ℕ} {W : ℝ} (hW : W ≠ 0)
    (x : Fin d → ℝ) :
    simplexScaleLinearEquiv d W hW x = W • x := by
  rfl

private theorem simplexScaleLinearEquiv_det {d : ℕ} {W : ℝ} (hW : W ≠ 0) :
    LinearMap.det (simplexScaleLinearEquiv d W hW).toLinearMap = W ^ d := by
  rw [show (simplexScaleLinearEquiv d W hW).toLinearMap = W • LinearMap.id by rfl,
    LinearMap.det_smul, LinearMap.det_id, mul_one]
  congr 1
  simp

private noncomputable def simplexScaleMeasurableEquiv (d : ℕ) (W : ℝ) (hW : W ≠ 0) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) where
  toEquiv := simplexScaleLinearEquiv d W hW
  measurable_toFun :=
    (LinearMap.continuous_on_pi (simplexScaleLinearEquiv d W hW).toLinearMap).measurable
  measurable_invFun :=
    (LinearMap.continuous_on_pi (simplexScaleLinearEquiv d W hW).symm.toLinearMap).measurable

private theorem simplexScale_preimage_weightedSimplex {d : ℕ} {W : ℝ} (hW : 0 < W) :
    simplexScaleMeasurableEquiv d W hW.ne' ⁻¹'
        SimplexIntegration.weightedSimplex d W =
      SimplexIntegration.weightedSimplex d 1 := by
  ext x
  simp only [Set.mem_preimage, SimplexIntegration.weightedSimplex, Set.mem_ofPred_eq]
  change ((∀ i, 0 ≤ W * x i) ∧
      ∑ i, SimplexIntegration.coordinateWeight i * (W * x i) ≤ W) ↔
    (∀ i, 0 ≤ x i) ∧ ∑ i, SimplexIntegration.coordinateWeight i * x i ≤ 1
  constructor
  · rintro ⟨hx, hsum⟩
    constructor
    · intro i
      exact nonneg_of_mul_nonneg_right (hx i) hW
    · have hs : W * (∑ i, SimplexIntegration.coordinateWeight i * x i) ≤ W * 1 := by
        calc
          W * (∑ i, SimplexIntegration.coordinateWeight i * x i) =
              ∑ i, SimplexIntegration.coordinateWeight i * (W * x i) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ ≤ W := hsum
          _ = W * 1 := by ring
      exact (mul_le_mul_iff_of_pos_left hW).mp hs
  · rintro ⟨hx, hsum⟩
    constructor
    · intro i
      exact mul_nonneg hW.le (hx i)
    · calc
        ∑ i, SimplexIntegration.coordinateWeight i * (W * x i) =
            W * ∑ i, SimplexIntegration.coordinateWeight i * x i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ W * 1 := mul_le_mul_of_nonneg_left hsum hW.le
        _ = W := mul_one W

private theorem weightedRadius_scale {d : ℕ} (W : ℝ) (x : Fin d → ℝ) :
    SimplexIntegration.weightedRadius (W • x) =
      W * SimplexIntegration.weightedRadius x := by
  simp [SimplexIntegration.weightedRadius, Finset.mul_sum]

/-- Normalized weighted-simplex expectations are invariant under positive dilation. -/
theorem weightedSimplexExpectation_scale {d : ℕ} {W : ℝ} (hW : 0 < W)
    (f : ℝ → ℝ) :
    SimplexIntegration.weightedSimplexExpectation d W
        (fun u ↦ f (SimplexIntegration.weightedRadius u / W)) =
      SimplexIntegration.weightedSimplexExpectation d 1
        (fun u ↦ f (SimplexIntegration.weightedRadius u)) := by
  let e := simplexScaleMeasurableEquiv d W hW.ne'
  have hdet : LinearMap.det (simplexScaleLinearEquiv d W hW.ne').toLinearMap ≠ 0 := by
    rw [simplexScaleLinearEquiv_det hW.ne']
    exact pow_ne_zero _ hW.ne'
  have hmap : Measure.map e volume = ENNReal.ofReal ((W ^ d)⁻¹) • volume := by
    change Measure.map (simplexScaleLinearEquiv d W hW.ne') volume = _
    have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
    rw [simplexScaleLinearEquiv_det hW.ne',
      abs_of_pos (inv_pos.mpr (pow_pos hW d))] at h
    exact h
  have hchange := setIntegral_map_equiv (μ := volume) e
    (fun u ↦ f (SimplexIntegration.weightedRadius u / W))
    (SimplexIntegration.weightedSimplex d W)
  rw [hmap, Measure.restrict_smul, integral_smul_measure,
    simplexScale_preimage_weightedSimplex hW] at hchange
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hW.le d))] at hchange
  have hcomp : (fun x ↦ f (SimplexIntegration.weightedRadius (e x) / W)) =
      fun x ↦ f (SimplexIntegration.weightedRadius x) := by
    funext x
    change f (SimplexIntegration.weightedRadius (W • x) / W) = _
    rw [weightedRadius_scale]
    field_simp
  rw [hcomp] at hchange
  rw [SimplexIntegration.weightedSimplexExpectation,
    SimplexIntegration.weightedSimplexExpectation, setAverage_eq, setAverage_eq,
    SimplexIntegration.volume_weightedSimplex d hW.le,
    SimplexIntegration.volume_weightedSimplex d zero_le_one]
  have hpow : (W ^ d : ℝ) ≠ 0 := pow_ne_zero _ hW.ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by positivity
  simp only [one_pow, one_div]
  rw [← hchange]
  field_simp
  ring

/-- Exact first moment of the genuine-coordinate maximum (slack excluded). -/
theorem simplexMaximumExpectation_id {d : ℕ} [NeZero d] {W : ℝ} (hW : 0 < W) :
    simplexMaximumExpectation d W id =
      W * SimplexIntegration.harmonicPowerSum d 1 / (d + 1) := by
  rw [simplexMaximumExpectation_eq_weightedRadius hW id continuous_id]
  simpa using SimplexIntegration.weightedSimplexExpectation_radius d hW

/-- Exact second moment of the genuine-coordinate maximum (slack excluded). -/
theorem simplexMaximumExpectation_sq {d : ℕ} [NeZero d] {W : ℝ} (hW : 0 < W) :
    simplexMaximumExpectation d W (fun x ↦ x ^ 2) =
      W ^ 2 * (SimplexIntegration.harmonicPowerSum d 1 ^ 2 +
        SimplexIntegration.harmonicPowerSum d 2) / ((d + 1) * (d + 2)) := by
  rw [simplexMaximumExpectation_eq_weightedRadius hW (fun x ↦ x ^ 2) (continuous_id.pow 2)]
  simpa using SimplexIntegration.weightedSimplexExpectation_radius_sq d hW

private def coordinateSpike {d : ℕ} (i : Fin d) (y : ℝ) : Fin d → ℝ :=
  Pi.single i y

private theorem sum_coordinateSpike {d : ℕ} (i : Fin d) (y : ℝ) :
    ∑ j, coordinateSpike i y j = y := by
  classical
  simp [coordinateSpike]

private theorem add_coordinateSpike_preimage {d : ℕ} (i : Fin d) {W y : ℝ}
    (hy : 0 ≤ y) :
    (fun x : Fin d → ℝ ↦ x + coordinateSpike i y) ⁻¹'
        {x | x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i} =
      SimplexIntegration.standardSimplex d (W - y) := by
  classical
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, SimplexIntegration.standardSimplex,
    Pi.add_apply]
  rw [Finset.sum_add_distrib, sum_coordinateSpike]
  constructor
  · rintro ⟨⟨hnonneg, hsum⟩, hycoord⟩
    refine ⟨fun j ↦ ?_, by linarith⟩
    by_cases hji : j = i
    · subst j
      simpa [coordinateSpike] using hycoord
    · simpa [coordinateSpike, hji] using hnonneg j
  · rintro ⟨hnonneg, hsum⟩
    refine ⟨⟨fun j ↦ ?_, by linarith⟩, ?_⟩
    · by_cases hji : j = i
      · subst j
        simpa [coordinateSpike] using add_nonneg (hnonneg i) hy
      · simpa [coordinateSpike, hji] using hnonneg j
    · simpa [coordinateSpike] using add_le_add_right (hnonneg i) y

/-- A coordinate of a uniform simplex has the exact beta tail `(W-y)^d/d!`. -/
theorem volume_standardSimplex_coordinate_ge {d : ℕ} (i : Fin d) {W y : ℝ}
    (hy : 0 ≤ y) (hyW : y ≤ W) :
    volume.real {x : Fin d → ℝ |
        x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i} =
      (W - y) ^ d / d.factorial := by
  let e : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
    MeasurableEquiv.addRight (coordinateSpike i y)
  have hmap : Measure.map e volume = volume := by
    simpa [e] using (map_add_right_eq_self volume (coordinateSpike i y))
  have hmeas : MeasurableSet {x : Fin d → ℝ |
      x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i} :=
    (SimplexIntegration.isClosed_standardSimplex d W).measurableSet.inter
      (measurableSet_le measurable_const (measurable_pi_apply i))
  have hmeasure : volume {x : Fin d → ℝ |
      x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i} =
      volume (SimplexIntegration.standardSimplex d (W - y)) := by
    calc
      volume {x : Fin d → ℝ |
          x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i} =
          Measure.map e volume {x : Fin d → ℝ |
            x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i} := by rw [hmap]
      _ = volume (e ⁻¹' {x : Fin d → ℝ |
          x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i}) :=
        Measure.map_apply e.measurable hmeas
      _ = volume (SimplexIntegration.standardSimplex d (W - y)) := by
        change volume ((fun x : Fin d → ℝ ↦ x + coordinateSpike i y) ⁻¹'
          {x | x ∈ SimplexIntegration.standardSimplex d W ∧ y ≤ x i}) = _
        rw [add_coordinateSpike_preimage i hy]
  rw [measureReal_def, hmeasure, ← measureReal_def,
    SimplexIntegration.volume_standardSimplex d (sub_nonneg.mpr hyW)]

/-- The centered maximum variable used in the rate-first moment estimate. -/
noncomputable def centeredSimplexMaximum (d : ℕ) [NeZero d] (x : Fin d → ℝ) : ℝ :=
  d * simplexMaximum d x - Real.log d

/-- Union-bound tail estimate for the actual `d` genuine coordinates. -/
theorem volume_centeredSimplexMaximum_gt {d : ℕ} [NeZero d]
    (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    volume.real {x : Fin d → ℝ |
        x ∈ SimplexIntegration.standardSimplex d 1 ∧ t < centeredSimplexMaximum d x} ≤
      Real.exp (-t) / d.factorial := by
  let y : ℝ := (Real.log d + t) / d
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hy : 0 ≤ y := div_nonneg (add_nonneg hlog ht) hdR.le
  by_cases hy1 : y ≤ 1
  · have hsubset : {x : Fin d → ℝ |
        x ∈ SimplexIntegration.standardSimplex d 1 ∧ t < centeredSimplexMaximum d x} ⊆
        ⋃ i : Fin d, {x : Fin d → ℝ |
          x ∈ SimplexIntegration.standardSimplex d 1 ∧ y ≤ x i} := by
      rintro x ⟨hx, htail⟩
      have hymax : y < simplexMaximum d x := by
        dsimp only [centeredSimplexMaximum] at htail
        dsimp only [y]
        apply (div_lt_iff₀ hdR).2
        linarith
      rw [simplexMaximum] at hymax
      obtain ⟨i, _, hi⟩ := (Finset.lt_sup'_iff Finset.univ_nonempty).1 hymax
      exact Set.mem_iUnion.2 ⟨i, hx, hi.le⟩
    have hunion : (⋃ i : Fin d, {x : Fin d → ℝ |
        x ∈ SimplexIntegration.standardSimplex d 1 ∧ y ≤ x i}) ⊆
        SimplexIntegration.standardSimplex d 1 := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hi.1
    calc
      volume.real {x : Fin d → ℝ |
          x ∈ SimplexIntegration.standardSimplex d 1 ∧ t < centeredSimplexMaximum d x} ≤
          volume.real (⋃ i : Fin d, {x : Fin d → ℝ |
            x ∈ SimplexIntegration.standardSimplex d 1 ∧ y ≤ x i}) :=
        measureReal_mono hsubset (measure_ne_top_of_subset hunion
          (SimplexIntegration.isCompact_standardSimplex d zero_le_one).measure_lt_top.ne)
      _ ≤ ∑ i : Fin d, volume.real {x : Fin d → ℝ |
          x ∈ SimplexIntegration.standardSimplex d 1 ∧ y ≤ x i} :=
        measureReal_iUnion_fintype_le _
      _ = d * ((1 - y) ^ d / d.factorial) := by
        simp_rw [volume_standardSimplex_coordinate_ge _ hy hy1]
        simp
      _ ≤ Real.exp (-t) / d.factorial := by
        have hpow := Real.one_sub_div_pow_le_exp_neg
          (n := d) (t := Real.log d + t) (by
            dsimp only [y] at hy1
            apply (div_le_one hdR).mp
            simpa using hy1)
        have hexp : (d : ℝ) * Real.exp (-(Real.log d + t)) = Real.exp (-t) := by
          rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hdR]
          field_simp
        dsimp only [y]
        calc
          (d : ℝ) * ((1 - (Real.log d + t) / d) ^ d / d.factorial) =
              (d * (1 - (Real.log d + t) / d) ^ d) / d.factorial := by ring
          _ ≤ (d * Real.exp (-(Real.log d + t))) / d.factorial := by
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hdR.le) (by positivity)
          _ = Real.exp (-t) / d.factorial := by rw [hexp]
  · have hempty : {x : Fin d → ℝ |
        x ∈ SimplexIntegration.standardSimplex d 1 ∧ t < centeredSimplexMaximum d x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx, htail⟩
      have hmax_le : simplexMaximum d x ≤ 1 := by
        rw [simplexMaximum_le_iff]
        intro i
        exact (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans hx.2
      have hymax : y < simplexMaximum d x := by
        dsimp only [centeredSimplexMaximum] at htail
        dsimp only [y]
        apply (div_lt_iff₀ hdR).2
        linarith
      exact hy1 (hymax.le.trans hmax_le)
    rw [hempty, measureReal_empty]
    positivity

/-- Positive part of the upper centered-maximum tail beyond `log 6`. -/
noncomputable def centeredMaximumUpperTail (d : ℕ) [NeZero d] (x : Fin d → ℝ) : ℝ :=
  max (centeredSimplexMaximum d x - Real.log 6) 0

theorem continuous_centeredMaximumUpperTail (d : ℕ) [NeZero d] :
    Continuous (centeredMaximumUpperTail d) := by
  unfold centeredMaximumUpperTail centeredSimplexMaximum
  exact (((continuous_const.mul (continuous_simplexMaximum d)).sub continuous_const).sub
    continuous_const).max continuous_const

private theorem integral_exp_neg_sqrt :
    (∫ t : ℝ in Ioi 0, Real.exp (-Real.sqrt t)) = 2 := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_exp_neg_rpow (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num [Real.Gamma_nat_eq_factorial]

private theorem integrableOn_exp_neg_sqrt :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-Real.sqrt t)) (Ioi 0) := by
  simpa only [Real.sqrt_eq_rpow, Real.rpow_zero, one_mul] using
    (integrableOn_rpow_mul_exp_neg_rpow
      (p := (1 / 2 : ℝ)) (s := (0 : ℝ)) (by norm_num) (by norm_num))

/-- The discarded upper-tail square contributes at most `1/3` to normalized expectation. -/
theorem simplexMaximumExpectation_upperTail_sq_le {d : ℕ} [NeZero d] (hd : 1 ≤ d) :
    simplexMaximumExpectation d 1
      (fun m ↦ max (d * m - Real.log d - Real.log 6) 0 ^ 2) ≤ 1 / 3 := by
  let S := SimplexIntegration.standardSimplex d 1
  let F : (Fin d → ℝ) → ℝ := fun x ↦ centeredMaximumUpperTail d x ^ 2
  let μ : Measure (Fin d → ℝ) := volume.restrict S
  have hFint : Integrable F μ := by
    change IntegrableOn F S volume
    exact (continuous_centeredMaximumUpperTail d).pow 2 |>.continuousOn.integrableOn_compact
      (SimplexIntegration.isCompact_standardSimplex d zero_le_one)
  have hlayer := hFint.integral_eq_integral_meas_lt (ae_of_all _ fun x ↦ sq_nonneg _)
  have htail : ∀ t ∈ Ioi (0 : ℝ), μ.real {x | t < F x} ≤
      Real.exp (-(Real.log 6 + Real.sqrt t)) / d.factorial := by
    intro t ht
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have ht0 : 0 ≤ t := ht.le
    have hsqrt_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hset : {x : Fin d → ℝ | t < F x} ∩ S ⊆
        {x : Fin d → ℝ | x ∈ SimplexIntegration.standardSimplex d 1 ∧
          Real.log 6 + Real.sqrt t < centeredSimplexMaximum d x} := by
      rintro x ⟨hFx, hxS⟩
      refine ⟨hxS, ?_⟩
      have hroot : Real.sqrt t < centeredMaximumUpperTail d x := by
        dsimp only [F] at hFx
        change t < centeredMaximumUpperTail d x ^ 2 at hFx
        have hnonneg : 0 ≤ centeredMaximumUpperTail d x :=
          le_max_right _ _
        nlinarith
      unfold centeredMaximumUpperTail at hroot
      have hpos : 0 < centeredSimplexMaximum d x - Real.log 6 := by
        rcases (lt_max_iff.mp hroot) with h | h
        · linarith
        · exact (not_lt_of_ge (Real.sqrt_nonneg t) h).elim
      rw [max_eq_left hpos.le] at hroot
      linarith
    have hmeas : NullMeasurableSet {x : Fin d → ℝ | t < F x} μ := by
      apply MeasurableSet.nullMeasurableSet
      exact measurableSet_lt measurable_const
        ((continuous_centeredMaximumUpperTail d).pow 2).measurable
    rw [measureReal_restrict_apply₀ hmeas]
    exact (measureReal_mono hset
      (measure_ne_top_of_subset (by intro x hx; exact hx.1)
        (SimplexIntegration.isCompact_standardSimplex d zero_le_one).measure_lt_top.ne)).trans
      (volume_centeredSimplexMaximum_gt hd
        (add_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg t)))
  have hmajorant : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-(Real.log 6 + Real.sqrt t)) / d.factorial) (Ioi 0) := by
    change Integrable (fun t : ℝ ↦ Real.exp (-(Real.log 6 + Real.sqrt t)) / d.factorial)
      (volume.restrict (Ioi 0))
    convert integrableOn_exp_neg_sqrt.const_mul
      (Real.exp (-Real.log 6) / d.factorial) using 1
    ext t
    simp only [neg_add, Real.exp_add, div_eq_mul_inv]
    ring
  have hraw : (∫ x in S, F x) ≤ 1 / (3 * d.factorial) := by
    rw [show (∫ x in S, F x) = ∫ x, F x ∂μ by rfl, hlayer]
    calc
      (∫ t : ℝ in Ioi 0, μ.real {x | t < F x}) ≤
          ∫ t : ℝ in Ioi 0,
            Real.exp (-(Real.log 6 + Real.sqrt t)) / d.factorial := by
        exact integral_mono_of_nonneg (ae_of_all _ fun _ ↦ measureReal_nonneg)
          hmajorant (ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ htail))
      _ = 1 / (3 * d.factorial) := by
        calc
          (∫ t : ℝ in Ioi 0,
              Real.exp (-(Real.log 6 + Real.sqrt t)) / d.factorial) =
              (Real.exp (-Real.log 6) / d.factorial) *
                ∫ t : ℝ in Ioi 0, Real.exp (-Real.sqrt t) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _
            change Real.exp (-(Real.log 6 + Real.sqrt t)) / d.factorial =
              (Real.exp (-Real.log 6) / d.factorial) * Real.exp (-Real.sqrt t)
            rw [neg_add, Real.exp_add]
            ring
          _ = 1 / (3 * d.factorial) := by
            rw [integral_exp_neg_sqrt, Real.exp_neg,
              Real.exp_log (by norm_num : (0 : ℝ) < 6)]
            field_simp
            ring
  rw [simplexMaximumExpectation, setAverage_eq,
    SimplexIntegration.volume_standardSimplex d zero_le_one]
  simp only [one_pow, one_div]
  have hfac : (0 : ℝ) < d.factorial := by positivity
  calc
    (d.factorial : ℝ)⁻¹⁻¹ • ∫ x in S, F x = d.factorial * ∫ x in S, F x := by
      simp
    _ ≤ d.factorial * (1 / (3 * d.factorial)) :=
      mul_le_mul_of_nonneg_left hraw hfac.le
    _ = (3 : ℝ)⁻¹ := by field_simp

theorem log_six_gt : (179 / 100 : ℝ) < Real.log 6 := by
  have hlog : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hlog]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem log_five_hundred_lt : Real.log 500 < (311 / 50 : ℝ) := by
  have hlog : Real.log (500 : ℝ) = 2 * Real.log 2 + 3 * Real.log 5 := by
    calc
      Real.log (500 : ℝ) = Real.log ((2 : ℝ) ^ 2 * (5 : ℝ) ^ 3) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log ((5 : ℝ) ^ 3) := by
        rw [Real.log_mul] <;> positivity
      _ = 2 * Real.log 2 + 3 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  rw [hlog]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem harmonic_sub_log_lt {d : ℕ} (hd : 200 ≤ d) :
    (harmonic d : ℝ) - Real.log d < 29 / 50 := by
  have hlog : Real.log (200 : ℝ) = 3 * Real.log 2 + 2 * Real.log 5 := by
    calc
      Real.log (200 : ℝ) = Real.log ((2 : ℝ) ^ 3 * (5 : ℝ) ^ 2) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul] <;> positivity
      _ = 3 * Real.log 2 + 2 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  have hbase : Real.eulerMascheroniSeq' 200 < (29 / 50 : ℝ) := by
    rw [Real.eulerMascheroniSeq']
    norm_num only [OfNat.ofNat_ne_zero, ↓reduceIte]
    rw [hlog]
    have htwo := Real.log_two_gt_d9
    have hfive := Real.log_five_gt_d9
    norm_num [harmonic, Finset.sum_range_succ] at *
    linarith
  have hmono := (Real.strictAnti_eulerMascheroniSeq'.antitone hd).trans_lt hbase
  have hd0 : d ≠ 0 := by omega
  simpa only [Real.eulerMascheroniSeq', hd0, ↓reduceIte] using hmono

theorem harmonicPowerSum_two_gt {d : ℕ} (hd : 500 ≤ d) :
    (41 / 25 : ℝ) < SimplexIntegration.harmonicPowerSum d 2 := by
  rw [SimplexIntegration.harmonicPowerSum_eq_range]
  have hbase : (41 / 25 : ℝ) <
      ∑ i ∈ Finset.range 500, (1 / (i + 1 : ℝ)) ^ 2 := by
    norm_num [Finset.sum_range_succ]
  exact hbase.trans_le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd)
    (fun _ _ _ ↦ sq_nonneg _))

private noncomputable def momentErrorPolynomial (x : ℝ) : ℝ :=
  x ^ 2 - 63 / 50 * x + 2408 / 625

private noncomputable def momentErrorRatio (x : ℝ) : ℝ :=
  momentErrorPolynomial (Real.log x) / x

private theorem momentErrorRatio_antitone :
    AntitoneOn momentErrorRatio (Ici (500 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (500 : ℝ))
  · intro x hx
    have hxne : x ≠ 0 := by simp only [mem_Ici] at hx; linarith
    have hlog := Real.continuousAt_log hxne
    unfold momentErrorRatio momentErrorPolynomial
    exact ((((hlog.pow 2).sub (continuousAt_const.mul hlog)).add continuousAt_const).div
      continuousAt_id hxne).continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by simp only [interior_Ici, mem_Ioi] at hx; linarith
    have hlog := Real.hasDerivAt_log hxpos.ne'
    unfold momentErrorRatio momentErrorPolynomial
    exact ((((hlog.pow 2).sub (hlog.const_mul (63 / 50))).add_const (2408 / 625)).div
      (hasDerivAt_id x) hxpos.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    have hxpos : 0 < x := by simp only [interior_Ici, mem_Ioi] at hx; linarith
    have hnum := (((Real.hasDerivAt_log hxpos.ne').pow 2).sub
      ((Real.hasDerivAt_log hxpos.ne').const_mul (63 / 50))).add_const (2408 / 625)
    have hderiv' := hnum.div (hasDerivAt_id x) hxpos.ne'
    unfold momentErrorRatio momentErrorPolynomial
    change deriv (((fun z ↦
      (Real.log ^ 2 - fun y ↦ 63 / 50 * Real.log y) z + 2408 / 625) / id)) x ≤ 0
    rw [hderiv'.deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply, Pi.sub_apply]
    have hsquare : 0 ≤ (Real.log x - 163 / 100) ^ 2 := sq_nonneg _
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hxpos
    apply div_nonpos_of_nonpos_of_nonneg _ hx2.le
    have hsimp :
        (2 * Real.log x * x⁻¹ - 63 / 50 * x⁻¹) * x =
          2 * Real.log x - 63 / 50 := by field_simp
    rw [hsimp]
    nlinarith

private theorem momentErrorRatio_nat_le {d : ℕ} (hd : 500 ≤ d) :
    momentErrorRatio d ≤ momentErrorPolynomial (311 / 50) / 500 := by
  have hdR : (500 : ℝ) ≤ d := by exact_mod_cast hd
  have hanti := momentErrorRatio_antitone (by simp) (by simpa using hdR) hdR
  have hlog500pos : (0 : ℝ) < Real.log 500 := Real.log_pos (by norm_num)
  have hpoly : momentErrorPolynomial (Real.log 500) ≤
      momentErrorPolynomial (311 / 50) := by
    have hu := log_five_hundred_lt.le
    unfold momentErrorPolynomial
    nlinarith
  calc
    momentErrorRatio d ≤ momentErrorRatio 500 := hanti
    _ = momentErrorPolynomial (Real.log 500) / 500 := rfl
    _ ≤ momentErrorPolynomial (311 / 50) / 500 := by gcongr

/-- The exact quadratic moment obtained from the first two maximum moments. -/
theorem simplexMaximumExpectation_affine_sq {d : ℕ} [NeZero d]
    (a : ℝ) :
    simplexMaximumExpectation d 1 (fun m ↦ (a - d * m) ^ 2) =
      a ^ 2 - 2 * a * d * (SimplexIntegration.harmonicPowerSum d 1 / (d + 1)) +
        d ^ 2 * ((SimplexIntegration.harmonicPowerSum d 1 ^ 2 +
          SimplexIntegration.harmonicPowerSum d 2) / ((d + 1) * (d + 2))) := by
  let S := SimplexIntegration.standardSimplex d 1
  let μ : Measure (Fin d → ℝ) := volume.restrict S
  let _ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    exact (SimplexIntegration.isCompact_standardSimplex d zero_le_one).measure_lt_top⟩
  let _ : NeZero μ := ⟨by
    change volume.restrict S ≠ 0
    rw [← Measure.measure_univ_ne_zero, Measure.restrict_apply_univ]
    intro hz
    have hreal : volume.real S = 0 := by rw [measureReal_def, hz]; simp
    rw [SimplexIntegration.volume_standardSimplex d zero_le_one] at hreal
    have hpos : (0 : ℝ) < 1 ^ d / d.factorial := by positivity
    exact (ne_of_gt hpos) hreal⟩
  have hM : Integrable (fun x : Fin d → ℝ ↦ simplexMaximum d x) μ := by
    change IntegrableOn (simplexMaximum d) S
    exact (continuous_simplexMaximum d).continuousOn.integrableOn_compact
      (SimplexIntegration.isCompact_standardSimplex d zero_le_one)
  have hM2 : Integrable (fun x : Fin d → ℝ ↦ simplexMaximum d x ^ 2) μ := by
    change IntegrableOn (fun x : Fin d → ℝ ↦ simplexMaximum d x ^ 2) S
    exact (continuous_simplexMaximum d).pow 2 |>.continuousOn.integrableOn_compact
      (SimplexIntegration.isCompact_standardSimplex d zero_le_one)
  have hfun : (fun m : ℝ ↦ (a - d * m) ^ 2) =
      fun m ↦ a ^ 2 + (-2 * a * d) * m + d ^ 2 * m ^ 2 := by
    funext m
    ring
  rw [hfun]
  unfold simplexMaximumExpectation
  change ⨍ x, a ^ 2 + (-2 * a * d) * simplexMaximum d x +
      d ^ 2 * simplexMaximum d x ^ 2 ∂μ = _
  unfold MeasureTheory.average
  have houter :
      (∫ x, (a ^ 2 + (-2 * a * d) * simplexMaximum d x) +
          d ^ 2 * simplexMaximum d x ^ 2 ∂(μ Set.univ)⁻¹ • μ) =
        (∫ x, a ^ 2 + (-2 * a * d) * simplexMaximum d x ∂(μ Set.univ)⁻¹ • μ) +
          ∫ x, d ^ 2 * simplexMaximum d x ^ 2 ∂(μ Set.univ)⁻¹ • μ :=
    integral_add ((integrable_const _).add (hM.const_mul _)).to_average
      (hM2.const_mul _).to_average
  rw [houter]
  have hinner :
      (∫ x, a ^ 2 + (-2 * a * d) * simplexMaximum d x ∂(μ Set.univ)⁻¹ • μ) =
        (∫ _x, a ^ 2 ∂(μ Set.univ)⁻¹ • μ) +
          ∫ x, (-2 * a * d) * simplexMaximum d x ∂(μ Set.univ)⁻¹ • μ :=
    integral_add (integrable_const _).to_average (hM.const_mul _).to_average
  rw [hinner, integral_const_mul, integral_const_mul]
  have hconst : (∫ _x : Fin d → ℝ, a ^ 2 ∂(μ Set.univ)⁻¹ • μ) = a ^ 2 := by
    change (⨍ _x, a ^ 2 ∂μ) = a ^ 2
    exact average_const μ (a ^ 2)
  rw [hconst]
  change a ^ 2 + (-2 * a * d) * simplexMaximumExpectation d 1 id +
      d ^ 2 * simplexMaximumExpectation d 1 (fun m ↦ m ^ 2) = _
  rw [simplexMaximumExpectation_id (d := d) zero_lt_one,
    simplexMaximumExpectation_sq (d := d) zero_lt_one]
  simp only [one_mul, one_pow]
  ring

private theorem simplexMaximumExpectation_sub {d : ℕ} [NeZero d]
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    simplexMaximumExpectation d 1 (fun m ↦ f m - g m) =
      simplexMaximumExpectation d 1 f - simplexMaximumExpectation d 1 g := by
  let S := SimplexIntegration.standardSimplex d 1
  let μ : Measure (Fin d → ℝ) := volume.restrict S
  have hfint : Integrable (fun x : Fin d → ℝ ↦ f (simplexMaximum d x)) μ := by
    change IntegrableOn (fun x : Fin d → ℝ ↦ f (simplexMaximum d x)) S
    exact (hf.comp (continuous_simplexMaximum d)).continuousOn.integrableOn_compact
      (SimplexIntegration.isCompact_standardSimplex d zero_le_one)
  have hgint : Integrable (fun x : Fin d → ℝ ↦ g (simplexMaximum d x)) μ := by
    change IntegrableOn (fun x : Fin d → ℝ ↦ g (simplexMaximum d x)) S
    exact (hg.comp (continuous_simplexMaximum d)).continuousOn.integrableOn_compact
      (SimplexIntegration.isCompact_standardSimplex d zero_le_one)
  unfold simplexMaximumExpectation MeasureTheory.average
  exact integral_sub hfint.to_average hgint.to_average

/-- Splitting a square at its positive and negative parts. -/
theorem simplexMaximumExpectation_lowerTail_eq {d : ℕ} [NeZero d] :
    simplexMaximumExpectation d 1
        (fun m ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2) =
      simplexMaximumExpectation d 1
          (fun m ↦ (Real.log 6 + Real.log d - d * m) ^ 2) -
        simplexMaximumExpectation d 1
          (fun m ↦ max (d * m - Real.log d - Real.log 6) 0 ^ 2) := by
  have hfun : (fun m : ℝ ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2) =
      fun m ↦ (Real.log 6 + Real.log d - d * m) ^ 2 -
        max (d * m - Real.log d - Real.log 6) 0 ^ 2 := by
    funext m
    by_cases h : d * m - Real.log d - Real.log 6 ≤ 0
    · rw [max_eq_right h]
      have h' : 0 ≤ Real.log 6 - (d * m - Real.log d) := by linarith
      rw [max_eq_left h']
      ring
    · have hpos : 0 ≤ d * m - Real.log d - Real.log 6 := le_of_not_ge h
      rw [max_eq_left hpos]
      have h' : Real.log 6 - (d * m - Real.log d) ≤ 0 := by linarith
      rw [max_eq_right h']
      ring
  rw [hfun, simplexMaximumExpectation_sub]
  · fun_prop
  · fun_prop

private theorem affineMoment_strict_lower
    {D H Q L A : ℝ} (hD : 500 ≤ D) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hHupper : H - L < 29 / 50) (hQ : 41 / 25 < Q) (hA : 179 / 100 < A) :
    (121 / 100 : ℝ) ^ 2 + 41 / 25 -
        ((L + 29 / 50) ^ 2 -
          2 * (121 / 100) * (500 / 501) * (L + 29 / 50) +
          3 * (41 / 25)) / D <
      (A + L) ^ 2 - 2 * (A + L) * D * (H / (D + 1)) +
        D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) := by
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D + 1 := by linarith
  have hD2 : 0 < D + 2 := by linarith
  have ht : 0 < L + 29 / 50 := by linarith
  have hHu : H < L + 29 / 50 := by linarith
  have hres : (121 / 100 : ℝ) + (L + 29 / 50) / (D + 1) <
      A + L - D * H / (D + 1) := by
    field_simp
    nlinarith
  have hratio : (500 / 501 : ℝ) * (L + 29 / 50) / D ≤
      (L + 29 / 50) / (D + 1) := by
    field_simp
    nlinarith
  have hbias : (121 / 100 : ℝ) ^ 2 +
      2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D <
        (A + L - D * H / (D + 1)) ^ 2 := by
    have hbase : 0 < (121 / 100 : ℝ) := by norm_num
    have hres' : (121 / 100 : ℝ) +
        (500 / 501) * (L + 29 / 50) / D <
          A + L - D * H / (D + 1) :=
      (by
        calc
          (121 / 100 : ℝ) + (500 / 501) * (L + 29 / 50) / D ≤
              121 / 100 + (L + 29 / 50) / (D + 1) :=
            by linarith
          _ < A + L - D * H / (D + 1) := hres)
    have hleft : 0 ≤ (121 / 100 : ℝ) +
        (500 / 501) * (L + 29 / 50) / D := by positivity
    have hsquares := (sq_lt_sq₀ hleft
      (hleft.trans_lt hres').le).2 hres'
    calc
      (121 / 100 : ℝ) ^ 2 +
          2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D ≤
          (121 / 100 + (500 / 501) * (L + 29 / 50) / D) ^ 2 := by
        let r : ℝ := (500 / 501) * (L + 29 / 50) / D
        calc
          (121 / 100 : ℝ) ^ 2 +
              2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D ≤
              (121 / 100) ^ 2 +
                2 * (121 / 100) * (500 / 501) * (L + 29 / 50) / D + r ^ 2 :=
            le_add_of_nonneg_right (sq_nonneg r)
          _ = (121 / 100 + (500 / 501) * (L + 29 / 50) / D) ^ 2 := by
            dsimp only [r]
            ring
      _ < (A + L - D * H / (D + 1)) ^ 2 := hsquares
  have hcoefQ : 1 - 3 / D < D ^ 2 / ((D + 1) * (D + 2)) := by
    field_simp
    nlinarith
  have hcoefH : D ^ 2 / ((D + 1) ^ 2 * (D + 2)) ≤ 1 / D := by
    field_simp
    nlinarith
  have hQpos : 0 < Q := by linarith
  have hvcoef : (41 / 25 : ℝ) * (1 - 3 / D) <
      Q * (D ^ 2 / ((D + 1) * (D + 2))) := by
    have hone : 0 < 1 - 3 / D := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hD0).2
      linarith
    nlinarith
  have hHsq : H ^ 2 < (L + 29 / 50) ^ 2 := by nlinarith
  have hHterm : D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) ≤
      (L + 29 / 50) ^ 2 / D := by
    have hcoefH0 : 0 ≤ D ^ 2 / ((D + 1) ^ 2 * (D + 2)) := by positivity
    calc
      D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) =
          (D ^ 2 / ((D + 1) ^ 2 * (D + 2))) * H ^ 2 := by ring
      _ ≤ (D ^ 2 / ((D + 1) ^ 2 * (D + 2))) * (L + 29 / 50) ^ 2 :=
        mul_le_mul_of_nonneg_left hHsq.le hcoefH0
      _ ≤ (1 / D) * (L + 29 / 50) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefH (sq_nonneg _)
      _ = (L + 29 / 50) ^ 2 / D := by ring
  have hvariance : (41 / 25 : ℝ) * (1 - 3 / D) -
      (L + 29 / 50) ^ 2 / D <
        D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) -
          (D * H / (D + 1)) ^ 2 := by
    have hid : D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) -
        (D * H / (D + 1)) ^ 2 =
      Q * (D ^ 2 / ((D + 1) * (D + 2))) -
        D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) := by
      field_simp
      ring
    rw [hid]
    linarith
  have hdecomp :
      (A + L) ^ 2 - 2 * (A + L) * D * (H / (D + 1)) +
          D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) =
        (A + L - D * H / (D + 1)) ^ 2 +
          (D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) -
            (D * H / (D + 1)) ^ 2) := by ring
  rw [hdecomp]
  ring_nf at hbias hvariance ⊢
  nlinarith

private noncomputable def paperMomentErrorPolynomial (x : ℝ) : ℝ :=
  x ^ 2 - 15721 / 12525 * x + 4829141 / 1252500

private noncomputable def paperMomentErrorRatio (x : ℝ) : ℝ :=
  paperMomentErrorPolynomial (Real.log x) / x

private theorem paperMomentErrorPolynomial_eq (x : ℝ) :
    paperMomentErrorPolynomial x =
      (x + 29 / 50) ^ 2 -
        2 * (121 / 100) * (500 / 501) * (x + 29 / 50) + 3 * (41 / 25) := by
  unfold paperMomentErrorPolynomial
  ring

private theorem paperMomentErrorRatio_antitone :
    AntitoneOn paperMomentErrorRatio (Ici (500 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (500 : ℝ))
  · intro x hx
    have hxne : x ≠ 0 := by simp only [mem_Ici] at hx; linarith
    have hlog := Real.continuousAt_log hxne
    unfold paperMomentErrorRatio paperMomentErrorPolynomial
    exact ((((hlog.pow 2).sub (continuousAt_const.mul hlog)).add continuousAt_const).div
      continuousAt_id hxne).continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by simp only [interior_Ici, mem_Ioi] at hx; linarith
    have hlog := Real.hasDerivAt_log hxpos.ne'
    unfold paperMomentErrorRatio paperMomentErrorPolynomial
    exact ((((hlog.pow 2).sub (hlog.const_mul (15721 / 12525))).add_const
      (4829141 / 1252500)).div (hasDerivAt_id x) hxpos.ne').differentiableAt
        |>.differentiableWithinAt
  · intro x hx
    have hxpos : 0 < x := by simp only [interior_Ici, mem_Ioi] at hx; linarith
    have hnum := (((Real.hasDerivAt_log hxpos.ne').pow 2).sub
      ((Real.hasDerivAt_log hxpos.ne').const_mul (15721 / 12525))).add_const
        (4829141 / 1252500)
    have hderiv' := hnum.div (hasDerivAt_id x) hxpos.ne'
    unfold paperMomentErrorRatio paperMomentErrorPolynomial
    change deriv (((fun z ↦
      (Real.log ^ 2 - fun y ↦ 15721 / 12525 * Real.log y) z +
        4829141 / 1252500) / id)) x ≤ 0
    rw [hderiv'.deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply, Pi.sub_apply]
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hxpos
    apply div_nonpos_of_nonpos_of_nonneg _ hx2.le
    have hsimp :
        (2 * Real.log x * x⁻¹ - 15721 / 12525 * x⁻¹) * x =
          2 * Real.log x - 15721 / 12525 := by field_simp
    rw [hsimp]
    nlinarith [sq_nonneg (Real.log x - 163 / 100)]

private theorem paperMomentErrorRatio_nat_le {d : ℕ} (hd : 500 ≤ d) :
    paperMomentErrorRatio d ≤ paperMomentErrorPolynomial (311 / 50) / 500 := by
  have hdR : (500 : ℝ) ≤ d := by exact_mod_cast hd
  have hanti := paperMomentErrorRatio_antitone (by simp) (by simpa using hdR) hdR
  have hlog500pos : (0 : ℝ) < Real.log 500 := Real.log_pos (by norm_num)
  have hpoly : paperMomentErrorPolynomial (Real.log 500) ≤
      paperMomentErrorPolynomial (311 / 50) := by
    have hu := log_five_hundred_lt.le
    unfold paperMomentErrorPolynomial
    nlinarith
  calc
    paperMomentErrorRatio d ≤ paperMomentErrorRatio 500 := hanti
    _ = paperMomentErrorPolynomial (Real.log 500) / 500 := rfl
    _ ≤ paperMomentErrorPolynomial (311 / 50) / 500 := by gcongr

/-- Strict `27/10` lower bound for the squared lower tail of the maximum of the `d` genuine
simplex coordinates.  The `(d+1)`-st barycentric coordinate is slack and is excluded. -/
theorem simplexMaximum_lowerTail_sq_gt {d : ℕ} [NeZero d] (hd : 500 ≤ d) :
    (27 / 10 : ℝ) < simplexMaximumExpectation d 1
      (fun m ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hharm : 0 ≤ (harmonic d : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic d := by
      rw [harmonic]
      exact Finset.sum_nonneg fun i _ ↦ by positivity
    exact_mod_cast hq
  have haffine := affineMoment_strict_lower
    (D := (d : ℝ)) (H := (harmonic d : ℝ))
    (Q := SimplexIntegration.harmonicPowerSum d 2)
    (L := Real.log d) (A := Real.log 6)
    (by exact_mod_cast hd) hlog hharm (harmonic_sub_log_lt (by omega))
      (harmonicPowerSum_two_gt hd) log_six_gt
  rw [← paperMomentErrorPolynomial_eq] at haffine
  have haffine' :
      (121 / 100 : ℝ) ^ 2 + 41 / 25 - paperMomentErrorRatio d <
        simplexMaximumExpectation d 1
          (fun m ↦ (Real.log 6 + Real.log d - d * m) ^ 2) := by
    rw [simplexMaximumExpectation_affine_sq]
    simpa [paperMomentErrorRatio, SimplexIntegration.harmonicPowerSum_one] using haffine
  have htail := simplexMaximumExpectation_upperTail_sq_le hd1
  have herror := paperMomentErrorRatio_nat_le hd
  have hendpoint :
      (27 / 10 : ℝ) < (121 / 100) ^ 2 + 41 / 25 - 1 / 3 -
        paperMomentErrorPolynomial (311 / 50) / 500 := by
    norm_num [paperMomentErrorPolynomial]
  rw [simplexMaximumExpectation_lowerTail_eq]
  nlinarith

/-- The rate-partition moment bound, at every positive weighted-simplex mass.  The `d`
coordinates here are the genuine simplex coordinates; the remaining barycentric coordinate is
the implicit slack coordinate. -/
theorem weightedSimplexMoment_gt {d : ℕ} (hd : 500 ≤ d) {W : ℝ} (hW : 0 < W) :
    (27 / 10 : ℝ) <
      SimplexIntegration.weightedSimplexExpectation d W
        (fun u ↦ (max (Real.log (6 * d) -
          (d : ℝ) * SimplexIntegration.weightedRadius u / W) 0) ^ 2) := by
  let _ : NeZero d := ⟨by omega⟩
  let f : ℝ → ℝ := fun m ↦ max (Real.log 6 - ((d : ℝ) * m - Real.log d)) 0 ^ 2
  have h := simplexMaximum_lowerTail_sq_gt (d := d) hd
  rw [simplexMaximumExpectation_eq_weightedRadius (W := 1) one_pos
    (fun m ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2)
    (by fun_prop)]
    at h
  have hscale := weightedSimplexExpectation_scale (d := d) hW f
  rw [← hscale] at h
  dsimp only [f] at h
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hdpos.ne']
  have hfun :
      (fun u : Fin d → ℝ ↦ (max (Real.log 6 + Real.log d -
        (d : ℝ) * SimplexIntegration.weightedRadius u / W) 0) ^ 2) =
      (fun u ↦ max (Real.log 6 - ((d : ℝ) *
        (SimplexIntegration.weightedRadius u / W) - Real.log d)) 0 ^ 2) := by
    funext u
    congr 2
    ring
  rw [hfun]
  exact h

end ReedSolomon.HiddenDerivative.RatePartition
