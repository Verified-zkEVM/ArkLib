/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.VolumeIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weighted simplices and their volumes

For weights `w : ι → ℝ` and a budget `W`, `Set.weightedSimplex w W` is the set of nonnegative
vectors `u : ι → ℝ` with `∑ i, w i * u i ≤ W`. It is the continuous counterpart of
`Finset.natWeightedSimplex` in `ArkLib.Data.Finset.WeightedSimplex`, with an arbitrary finite
index type and arbitrary real weights.

When every weight is positive, the diagonal map `u ↦ (w i * u i)ᵢ` carries the weighted simplex
onto `Set.standardSimplex ι W` and scales Lebesgue measure by `∏ i, w i`. Every integral over the
weighted simplex therefore reduces to one over the standard simplex, with the factor
`(∏ i, w i)⁻¹`. With `n = Fintype.card ι` and `0 ≤ W`, this gives the volume
`W ^ n / (n! * ∏ i, w i)` and the weighted Dirichlet integral.

Positivity of the weights is needed. A zero weight leaves its coordinate unbounded, so the set is
not compact and, for `0 < W`, has infinite measure. A negative weight also makes the set
unbounded, and the volume formula would then be negative. The closedness and measurability
statements hold for all weights.

## Main statements

* `Set.weightedSimplex`, with `weightedSimplex_one` (unit weights give the standard simplex),
  `weightedSimplex_eq_preimage`, `weightedSimplex_eq_image`, and `isCompact_weightedSimplex`.
* `MeasureTheory.setIntegral_weightedSimplex`: the change of variables
  `∫ u in weightedSimplex w W, f u = (∏ i, w i)⁻¹ * ∫ t in standardSimplex ι W, f (t i / w i)ᵢ`,
  for every function `f`.
* `MeasureTheory.integral_weightedSimplex_prod_pow_mul_pow`: the Dirichlet integral with slack
  coordinate `W - ∑ i, w i * u i`.
* `MeasureTheory.volume_real_weightedSimplex` and `MeasureTheory.volume_weightedSimplex`:
  the volume `W ^ n / (n! * ∏ i, w i)`.
* `MeasureTheory.volume_real_weightedSimplex_add_le_mul_exp`: enlarging the budget from `W > 0`
  to `W + r` multiplies the volume by at most `exp (n * r / W)`.
* `MeasureTheory.volume_real_weightedSimplex_succ`: the weights `1, …, n` on `Fin n`, with
  volume `W ^ n / (n!) ^ 2`.

## References

Ports `SimplexIntegration.coordinateWeight`, `weightedSimplex`, `weightedToStandard`,
`standardToWeighted`, `weightedStandardLinearEquiv`, `weightedSimplex_eq_preimage`,
`weightedSimplex_eq_image`, `isCompact_weightedSimplex`, `Continuous.integrableOn_weightedSimplex`,
`ContinuousOn.integrableOn_weightedSimplex`, `weightedToStandard_det`,
`integral_weightedSimplex_eq_standardSimplex`, and `volume_weightedSimplex` from
`ArkLib/ToMathlib/Analysis/Simplex/AffinePushforward.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source fixed the index type `Fin n` and the
weights `coordinateWeight i = i + 1`; here the index type is any `Fintype` and the weights are
any positive reals, so the Jacobian is `∏ i, w i` instead of `n!`. The source's
`volume_weightedSimplex` is the specialization `volume_real_weightedSimplex_succ`. The diagonal
maps and their determinant are private: the public change-of-variables theorem writes the inverse
map `t ↦ (t i / w i)ᵢ` explicitly. `Continuous.integrableOn_weightedSimplex` follows from
`ContinuousOn.integrableOn_weightedSimplex` by `Continuous.continuousOn`. The weighted Dirichlet
integral and the ENNReal volume are new. The file name records that the change of variables is
diagonal linear, not affine. Deferred to later slices: the weighted-radius moments and
expectations in `Simplex/Moments.lean`, which consume `setIntegral_weightedSimplex`.

`volume_real_weightedSimplex_add_le_mul_exp` is the general form of the volume estimate inside the
source's `ReedSolomon.HiddenDerivative.volume_weightedSimplex_add_choose_le_exp` (in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`RankIntegral.lean` at the same revision), which enlarges the budget by `r + (n + 1).choose 2` for
the weights `i + 1`. Here the weights are arbitrary positive reals and `r` is any real number.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Set

variable {ι : Type*} [Fintype ι]

/-- The weighted simplex of nonnegative vectors `u : ι → ℝ` with `∑ i, w i * u i ≤ W`. It is
bounded only when every weight is positive; a zero or negative weight leaves its coordinate
unbounded. -/
def weightedSimplex (w : ι → ℝ) (W : ℝ) : Set (ι → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, w i * u i ≤ W}

/-- Membership in the weighted simplex, unfolded. -/
@[simp]
theorem mem_weightedSimplex {w : ι → ℝ} {W : ℝ} {u : ι → ℝ} :
    u ∈ weightedSimplex w W ↔ (∀ i, 0 ≤ u i) ∧ ∑ i, w i * u i ≤ W :=
  Iff.rfl

/-- With every weight equal to `1`, the weighted simplex is the standard simplex. -/
@[simp]
theorem weightedSimplex_one (W : ℝ) : weightedSimplex (1 : ι → ℝ) W = standardSimplex ι W := by
  ext u
  simp

/-- For positive weights, the weighted simplex is the preimage of the standard simplex under
the diagonal scaling `u ↦ (w i * u i)ᵢ`. Positivity is what makes `0 ≤ w i * u i` equivalent to
`0 ≤ u i`. -/
theorem weightedSimplex_eq_preimage {w : ι → ℝ} (hw : ∀ i, 0 < w i) (W : ℝ) :
    weightedSimplex w W = (fun u i ↦ w i * u i) ⁻¹' standardSimplex ι W := by
  ext u
  simp only [mem_weightedSimplex, mem_preimage, mem_standardSimplex]
  refine and_congr_left' (forall_congr' fun i ↦ ?_)
  exact (mul_nonneg_iff_of_pos_left (hw i)).symm

/-- For positive weights, the weighted simplex is the image of the standard simplex under the
inverse scaling `t ↦ (t i / w i)ᵢ`. -/
theorem weightedSimplex_eq_image {w : ι → ℝ} (hw : ∀ i, 0 < w i) (W : ℝ) :
    weightedSimplex w W = (fun t i ↦ t i / w i) '' standardSimplex ι W := by
  rw [weightedSimplex_eq_preimage hw]
  ext u
  constructor
  · intro hu
    refine ⟨fun i ↦ w i * u i, hu, funext fun i ↦ ?_⟩
    field_simp [(hw i).ne']
  · rintro ⟨t, ht, rfl⟩
    change (fun i ↦ w i * (t i / w i)) ∈ standardSimplex ι W
    convert ht using 1
    funext i
    field_simp [(hw i).ne']

/-- The weighted simplex is closed for all real weights and budgets. -/
theorem isClosed_weightedSimplex (w : ι → ℝ) (W : ℝ) : IsClosed (weightedSimplex w W) := by
  have hnonneg : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    rw [show {x : ι → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  exact hnonneg.inter (isClosed_le
    (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i)) continuous_const)

/-- The weighted simplex is measurable for all real weights and budgets. -/
theorem measurableSet_weightedSimplex (w : ι → ℝ) (W : ℝ) :
    MeasurableSet (weightedSimplex w W) :=
  (isClosed_weightedSimplex w W).measurableSet

/-- For positive weights the weighted simplex is compact, as a continuous image of the standard
simplex. A zero or negative weight makes it unbounded. -/
theorem isCompact_weightedSimplex {w : ι → ℝ} (hw : ∀ i, 0 < w i) (W : ℝ) :
    IsCompact (weightedSimplex w W) := by
  rw [weightedSimplex_eq_image hw]
  exact (isCompact_standardSimplex ι W).image
    (continuous_pi fun i ↦ (continuous_apply i).div_const _)

end Set

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- For positive weights, a function continuous on the weighted simplex is integrable there. -/
theorem _root_.ContinuousOn.integrableOn_weightedSimplex {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    {f : (ι → ℝ) → ℝ} (hf : ContinuousOn f (weightedSimplex w W)) :
    IntegrableOn f (weightedSimplex w W) :=
  hf.integrableOn_compact (isCompact_weightedSimplex hw W)

/-- For positive weights the weighted simplex has finite Lebesgue measure. -/
theorem volume_weightedSimplex_lt_top {w : ι → ℝ} (hw : ∀ i, 0 < w i) (W : ℝ) :
    volume (weightedSimplex w W) < ⊤ :=
  (isCompact_weightedSimplex hw W).measure_lt_top

/-- The coordinatewise scaling `u ↦ (w i * u i)ᵢ` as a measurable equivalence. -/
private noncomputable def scaleEquiv {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    (ι → ℝ) ≃ᵐ (ι → ℝ) where
  toFun u i := w i * u i
  invFun t i := t i / w i
  left_inv u := funext fun i ↦ by field_simp [(hw i).ne']
  right_inv t := funext fun i ↦ by field_simp [(hw i).ne']
  measurable_toFun := (continuous_pi fun i ↦ continuous_const.mul (continuous_apply i)).measurable
  measurable_invFun := (continuous_pi fun i ↦ (continuous_apply i).div_const _).measurable

/-- The diagonal scaling pushes Lebesgue measure forward to `(∏ i, w i)⁻¹` times Lebesgue
measure. -/
private theorem map_scaleEquiv_volume {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    Measure.map (scaleEquiv hw) volume = ENNReal.ofReal (∏ i, w i)⁻¹ • volume := by
  classical
  have hdet : (Matrix.diagonal w).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hw i).ne'
  have hfun : ⇑(scaleEquiv hw) = ⇑(Matrix.toLin' (Matrix.diagonal w)) := by
    funext u i
    simp [scaleEquiv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [hfun, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Matrix.det_diagonal,
    abs_of_pos (inv_pos.mpr (Finset.prod_pos fun i _ ↦ hw i))]

/-- The change of variables from the weighted simplex to the standard simplex: for positive
weights and every function `f`,
`∫ u in weightedSimplex w W, f u = (∏ i, w i)⁻¹ * ∫ t in standardSimplex ι W, f (t i / w i)ᵢ`.
The factor is the inverse Jacobian of `u ↦ (w i * u i)ᵢ`. No integrability hypothesis is needed,
because the substitution is a measurable equivalence that scales the measure by a constant.
Positivity of the weights is needed for the simplex to be the preimage of the standard one. -/
theorem setIntegral_weightedSimplex {w : ι → ℝ} (hw : ∀ i, 0 < w i) (W : ℝ)
    (f : (ι → ℝ) → ℝ) :
    (∫ u in weightedSimplex w W, f u) =
      (∏ i, w i)⁻¹ * ∫ t in standardSimplex ι W, f (fun i ↦ t i / w i) := by
  have hprod : 0 < ∏ i, w i := Finset.prod_pos fun i _ ↦ hw i
  have h := setIntegral_map_equiv (μ := volume) (scaleEquiv hw)
    (fun t ↦ f (fun i ↦ t i / w i)) (standardSimplex ι W)
  rw [map_scaleEquiv_volume hw, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.mpr hprod).le, smul_eq_mul] at h
  have hpre : scaleEquiv hw ⁻¹' standardSimplex ι W = weightedSimplex w W :=
    (weightedSimplex_eq_preimage hw W).symm
  have hback : ∀ u, (fun i ↦ scaleEquiv hw u i / w i) = u := fun u ↦
    (scaleEquiv hw).symm_apply_apply u
  rw [hpre] at h
  simp only [hback] at h
  exact h.symm

/-- The Dirichlet integral on a weighted simplex: for positive weights, `n = Fintype.card ι`, and
`0 ≤ W`, integrating `(∏ i, u i ^ a i) * (W - ∑ i, w i * u i) ^ b` gives
`(∏ i, w i ^ (a i + 1))⁻¹` times the standard Dirichlet integral
`W ^ (n + ∑ i, a i + b) * ((∏ i, (a i)!) * b! / (n + ∑ i, a i + b)!)`.
Each coordinate contributes `w i ^ a i` from its monomial and `w i` from the Jacobian. The
hypotheses are needed already for `a = 0` and `b = 0`, the volume `volume_real_weightedSimplex`. -/
theorem integral_weightedSimplex_prod_pow_mul_pow {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (a : ι → ℕ) (b : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ u in weightedSimplex w W, (∏ i, u i ^ a i) * (W - ∑ i, w i * u i) ^ b) =
      (∏ i, w i ^ (a i + 1))⁻¹ * (W ^ (Fintype.card ι + ∑ i, a i + b) *
        ((∏ i, ((a i).factorial : ℝ)) * b.factorial /
          (Fintype.card ι + ∑ i, a i + b).factorial)) := by
  rw [setIntegral_weightedSimplex hw, ← integral_standardSimplex_prod_pow_mul_pow a b hW,
    ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext t
  have hne : ∀ i, w i ≠ 0 := fun i ↦ (hw i).ne'
  have hsum : ∑ i, w i * (t i / w i) = ∑ i, t i :=
    Finset.sum_congr rfl fun i _ ↦ by field_simp [hne i]
  have hpow : ∏ i, w i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero (a i) (hne i)
  have hprod : ∏ i, w i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hne i
  simp only [hsum, div_pow, Finset.prod_div_distrib, pow_succ, Finset.prod_mul_distrib]
  field_simp

/-- The weighted simplex with positive weights `w` and budget `0 ≤ W` has volume
`W ^ n / (n! * ∏ i, w i)`, where `n = Fintype.card ι`. Both hypotheses are needed: for `W < 0` the
set is empty while `W ^ 0 / 0! = 1`, and for a single weight `-1` the formula is negative. -/
theorem volume_real_weightedSimplex {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ} (hW : 0 ≤ W) :
    volume.real (weightedSimplex w W) =
      W ^ Fintype.card ι / ((Fintype.card ι).factorial * ∏ i, w i) := by
  have h := setIntegral_weightedSimplex hw W (fun _ ↦ (1 : ℝ))
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] at h
  rw [h, volume_real_standardSimplex ι hW]
  field_simp

/-- The volume of the weighted simplex as an extended nonnegative real,
`ofReal (W ^ n / (n! * ∏ i, w i))` for positive weights and `0 ≤ W`. -/
theorem volume_weightedSimplex {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ} (hW : 0 ≤ W) :
    volume (weightedSimplex w W) =
      ENNReal.ofReal (W ^ Fintype.card ι / ((Fintype.card ι).factorial * ∏ i, w i)) := by
  rw [← volume_real_weightedSimplex hw hW, ofReal_measureReal
    (volume_weightedSimplex_lt_top hw W).ne]

/-- Enlarging the budget of a weighted simplex from `W` to `W + r` multiplies its volume by at most
`exp (n * r / W)`, where `n = Fintype.card ι`: for positive weights and `0 < W`,
`volume.real (weightedSimplex w (W + r)) ≤ volume.real (weightedSimplex w W) * exp (n * r / W)`.
The volume ratio is `(1 + r / W) ^ n`, and `1 + x ≤ exp x`.

No hypothesis on `r` is needed: for `W + r < 0` the enlarged simplex is empty, and for
`-W ≤ r ≤ 0` the ratio `(1 + r / W) ^ n` is still at most `exp (n * r / W)`. The hypothesis
`0 < W` is needed: for `W = 0` the right side is the volume of `weightedSimplex w 0`, which is `0`
when `n ≥ 1`, while the left side is positive for `r > 0`. -/
theorem volume_real_weightedSimplex_add_le_mul_exp {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    (hW : 0 < W) (r : ℝ) :
    volume.real (weightedSimplex w (W + r)) ≤
      volume.real (weightedSimplex w W) * Real.exp (Fintype.card ι * r / W) := by
  rcases lt_or_ge (W + r) 0 with hr | hr
  · have hempty : weightedSimplex w (W + r) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun u hu ↦ ?_
      have hnn := (mem_weightedSimplex.mp hu).1
      have h0 : 0 ≤ ∑ i, w i * u i :=
        Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i).le (hnn i)
      linarith [(mem_weightedSimplex.mp hu).2]
    rw [hempty, measureReal_empty]
    exact mul_nonneg measureReal_nonneg (Real.exp_pos _).le
  rw [volume_real_weightedSimplex hw hr, volume_real_weightedSimplex hw hW.le]
  have hbase : W + r ≤ W * Real.exp (r / W) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (r / W)) hW.le
    rwa [mul_add, mul_div_cancel₀ _ hW.ne', mul_one, add_comm r] at h
  have hpow : (W + r) ^ Fintype.card ι ≤
      W ^ Fintype.card ι * Real.exp (Fintype.card ι * r / W) := by
    calc (W + r) ^ Fintype.card ι ≤ (W * Real.exp (r / W)) ^ Fintype.card ι :=
          pow_le_pow_left₀ hr hbase _
      _ = _ := by rw [mul_pow, ← Real.exp_nat_mul, mul_div_assoc]
  have hden : 0 < (Fintype.card ι).factorial * ∏ i, w i := by
    have := Finset.prod_pos fun i (_ : i ∈ Finset.univ) ↦ hw i
    positivity
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hpow hden.le

/-- The weights `1, 2, …, n` on `Fin n`: the product of the weights is `n!`, so the volume is
`W ^ n / (n!) ^ 2` for `0 ≤ W`. This is the source's `volume_weightedSimplex`. -/
theorem volume_real_weightedSimplex_succ (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    volume.real (weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W) =
      W ^ n / (n.factorial : ℝ) ^ 2 := by
  rw [volume_real_weightedSimplex (fun i ↦ by positivity) hW, Fintype.card_fin]
  have hprod : ∏ i : Fin n, ((i : ℝ) + 1) = n.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun k : ℕ ↦ (k : ℝ) + 1) n]
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  rw [hprod, sq]

end MeasureTheory
