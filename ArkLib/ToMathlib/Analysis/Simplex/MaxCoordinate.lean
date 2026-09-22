/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.Moments
public import ArkLib.ToMathlib.Analysis.Simplex.OrderedSimplex
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The largest coordinate of a uniform point of the standard simplex

Tail bounds and moments of the largest coordinate `maxᵢ x i` of a point `x` of the standard
simplex `Set.standardSimplex ι W`.

* **One coordinate.** Translating by `y` in coordinate `i` carries the standard simplex of budget
  `W - y` onto the part of the standard simplex of budget `W` where `y ≤ x i`, so this part has
  volume `(W - y) ^ n / n!` for `0 ≤ y ≤ W`, where `n = Fintype.card ι`.
* **Union bound.** The part where the largest coordinate is at least `y` has volume at most
  `n * (W - y) ^ n / n!`. For `W = 1` and `y = (log n + t) / n` this is at most `exp (-t) / n!`,
  a fraction `exp (-t)` of the volume `1 / n!` of the simplex.
* **Upper tail.** By the layer-cake formula, the average of `max (n * maxᵢ x i - log n - a) 0 ^ 2`
  over the standard simplex of budget `1` is at most `∫ t > 0, exp (-(a + √t)) = 2 * exp (-a)`.
* **Moments.** The largest coordinate has the law of `∑ i, u i` on the weighted simplex with
  weights `1, …, n` (`MeasureTheory.setAverage_standardSimplex_comp_sup'`), so its first two
  moments are those of `MeasureTheory.setAverage_weightedSimplex_succ_sum` and `_sum_sq`.

## Main statements

* `MeasureTheory.volume_real_standardSimplex_inter_le_apply`: the tail of one coordinate.
* `MeasureTheory.volume_real_standardSimplex_inter_le_sup'_le`: the union bound for the largest
  coordinate.
* `MeasureTheory.volume_real_standardSimplex_one_inter_lt_mul_sup'_sub_log_le`: the exponential
  tail of `n * maxᵢ x i - log n`.
* `MeasureTheory.setAverage_standardSimplex_one_max_mul_sup'_sub_log_sub_sq_le`: the upper-tail
  second moment.
* `MeasureTheory.setAverage_standardSimplex_sup'` and
  `MeasureTheory.setAverage_standardSimplex_sup'_sq`: the first two moments of the largest
  coordinate.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped BigOperators

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

/-! ### Tails of the coordinates -/

/-- Translating by `y ≥ 0` in coordinate `i` carries the standard simplex of budget `W - y` onto
the part of the standard simplex of budget `W` where `y ≤ x i`. -/
private theorem preimage_add_single_standardSimplex_inter [DecidableEq ι] (i : ι) {W y : ℝ}
    (hy : 0 ≤ y) :
    (fun x ↦ x + Pi.single i y) ⁻¹' (standardSimplex ι W ∩ {x | y ≤ x i}) =
      standardSimplex ι (W - y) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, mem_standardSimplex, Set.mem_ofPred_eq,
    Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte,
    Pi.single_eq_same]
  constructor
  · rintro ⟨⟨hnn, hsum⟩, hyi⟩
    refine ⟨fun j ↦ ?_, by linarith⟩
    rcases eq_or_ne j i with rfl | hji
    · linarith
    · simpa [hji] using hnn j
  · rintro ⟨hnn, hsum⟩
    refine ⟨⟨fun j ↦ ?_, by linarith⟩, by linarith [hnn i]⟩
    rcases eq_or_ne j i with rfl | hji
    · simpa using add_nonneg (hnn j) hy
    · simpa [hji] using hnn j

/-- The tail of one coordinate of a uniform point of the standard simplex: for `0 ≤ y ≤ W`, the
part of the standard simplex of budget `W` where `y ≤ x i` has volume `(W - y) ^ n / n!`, where
`n = Fintype.card ι`. Both hypotheses are needed: for `y < 0` the part is the whole simplex, of
volume `W ^ n / n!`, and for `W < y` it is empty. -/
theorem volume_real_standardSimplex_inter_le_apply (i : ι) {W y : ℝ} (hy : 0 ≤ y)
    (hyW : y ≤ W) :
    volume.real (standardSimplex ι W ∩ {x | y ≤ x i}) =
      (W - y) ^ Fintype.card ι / (Fintype.card ι).factorial := by
  classical
  rw [← volume_real_standardSimplex ι (sub_nonneg.2 hyW),
    ← preimage_add_single_standardSimplex_inter i hy, measureReal_def, measureReal_def,
    measure_preimage_add_right]

/-- The union bound for the largest coordinate: for `0 ≤ y ≤ W`, the part of the standard
simplex of budget `W` where `y ≤ maxᵢ x i` has volume at most `n * ((W - y) ^ n / n!)`, where
`n = Fintype.card ι`. -/
theorem volume_real_standardSimplex_inter_le_sup'_le [Nonempty ι] {W y : ℝ} (hy : 0 ≤ y)
    (hyW : y ≤ W) :
    volume.real (standardSimplex ι W ∩ {x | y ≤ univ.sup' univ_nonempty x}) ≤
      Fintype.card ι * ((W - y) ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  have hset : standardSimplex ι W ∩ {x | y ≤ univ.sup' univ_nonempty x} =
      ⋃ i, standardSimplex ι W ∩ {x | y ≤ x i} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion, Finset.le_sup'_iff,
      Finset.mem_univ, true_and]
    exact ⟨fun ⟨h, i, hi⟩ ↦ ⟨i, h, hi⟩, fun ⟨i, h, hi⟩ ↦ ⟨h, i, hi⟩⟩
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans_eq ?_
  simp only [volume_real_standardSimplex_inter_le_apply _ hy hyW, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- The largest coordinate of a point of the standard simplex of budget `1` is at most `1`. -/
private theorem sup'_le_one_of_mem_standardSimplex {n : ℕ} [NeZero n] {x : Fin n → ℝ}
    (hx : x ∈ standardSimplex (Fin n) 1) : univ.sup' univ_nonempty x ≤ 1 :=
  Finset.sup'_le _ _ fun i _ ↦
    (Finset.single_le_sum (fun j _ ↦ hx.1 j) (mem_univ i)).trans hx.2

/-- The exponential tail of the largest coordinate: for `n ≠ 0` and every `t`, the part of the
standard simplex of budget `1` where `t < n * maxᵢ x i - log n` has volume at most
`exp (-t) / n!`, a fraction `exp (-t)` of the volume `1 / n!` of the simplex. For `t < 0` the
bound exceeds the volume of the simplex. -/
theorem volume_real_standardSimplex_one_inter_lt_mul_sup'_sub_log_le {n : ℕ} [NeZero n]
    (t : ℝ) :
    volume.real (standardSimplex (Fin n) 1 ∩
        {x | t < n * univ.sup' univ_nonempty x - Real.log n}) ≤
      Real.exp (-t) / n.factorial := by
  have hvol : volume.real (standardSimplex (Fin n) 1) = 1 / n.factorial := by
    rw [volume_real_standardSimplex _ zero_le_one, Fintype.card_fin, one_pow]
  rcases lt_or_ge t 0 with ht | ht
  · refine (measureReal_mono inter_subset_left (volume_standardSimplex_lt_top _ 1).ne).trans ?_
    rw [hvol]
    gcongr
    exact Real.one_le_exp (by linarith)
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hlog : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  set y := (Real.log n + t) / n with hy_def
  have hy : 0 ≤ y := by positivity
  have hsub : standardSimplex (Fin n) 1 ∩
      {x | t < n * univ.sup' univ_nonempty x - Real.log n} ⊆
      standardSimplex (Fin n) 1 ∩ {x | y ≤ univ.sup' univ_nonempty x} := by
    rintro x ⟨hx, hlt⟩
    refine ⟨hx, ?_⟩
    have hlt : t < n * univ.sup' univ_nonempty x - Real.log n := hlt
    change y ≤ _
    rw [hy_def, div_le_iff₀ hn]
    linarith
  rcases le_or_gt y 1 with hy1 | hy1
  · refine (measureReal_mono hsub ((measure_mono inter_subset_left).trans_lt
      (volume_standardSimplex_lt_top _ 1)).ne).trans ?_
    refine (volume_real_standardSimplex_inter_le_sup'_le hy hy1).trans ?_
    simp only [Fintype.card_fin]
    have hpow : (1 - y) ^ n ≤ Real.exp (-(Real.log n + t)) :=
      Real.one_sub_div_pow_le_exp_neg (by rwa [hy_def, div_le_one hn] at hy1)
    have hexp : (n : ℝ) * Real.exp (-(Real.log n + t)) = Real.exp (-t) := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hn, ← mul_assoc,
        mul_inv_cancel₀ hn.ne', one_mul]
    rw [← hexp, mul_div_assoc]
    gcongr
  · have hempty : standardSimplex (Fin n) 1 ∩
        {x | t < n * univ.sup' univ_nonempty x - Real.log n} = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx ↦ ?_
      obtain ⟨hxS, hmax⟩ := hsub hx
      have hmax : y ≤ univ.sup' univ_nonempty x := hmax
      exact absurd (hmax.trans (sup'_le_one_of_mem_standardSimplex hxS)) (not_le.2 hy1)
    rw [hempty, measureReal_empty]
    positivity

/-! ### The upper-tail second moment -/

/-- `∫ t > 0, exp (-√t) = Γ(3) = 2`. -/
private theorem integral_exp_neg_sqrt :
    (∫ t : ℝ in Ioi 0, Real.exp (-Real.sqrt t)) = 2 := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_exp_neg_rpow (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num [Real.Gamma_nat_eq_factorial]

private theorem integrableOn_exp_neg_sqrt :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-Real.sqrt t)) (Ioi 0) := by
  simpa only [Real.sqrt_eq_rpow, Real.rpow_zero, one_mul] using
    integrableOn_rpow_mul_exp_neg_rpow (p := (1 / 2 : ℝ)) (s := (0 : ℝ)) (by norm_num)
      (by norm_num)

/-- The upper-tail second moment of the largest coordinate: for `n ≠ 0` and every `a`,
`⨍ x in standardSimplex (Fin n) 1, max (n * maxᵢ x i - log n - a) 0 ^ 2 ≤ 2 * exp (-a)`. -/
theorem setAverage_standardSimplex_one_max_mul_sup'_sub_log_sub_sq_le {n : ℕ} [NeZero n]
    (a : ℝ) :
    ⨍ x in standardSimplex (Fin n) 1,
      max (n * univ.sup' univ_nonempty x - Real.log n - a) 0 ^ 2 ≤ 2 * Real.exp (-a) := by
  set S := standardSimplex (Fin n) 1 with hS
  set F : (Fin n → ℝ) → ℝ :=
    fun x ↦ max (n * univ.sup' univ_nonempty x - Real.log n - a) 0 ^ 2 with hF
  have hsup : Continuous fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x :=
    Continuous.finset_sup'_apply univ_nonempty fun i _ ↦ continuous_apply i
  have hFc : Continuous F := by
    rw [hF]
    exact (((continuous_const.mul hsup).sub continuous_const).sub continuous_const).max
      continuous_const |>.pow 2
  have hFint : IntegrableOn F S :=
    hFc.continuousOn.integrableOn_compact (isCompact_standardSimplex _ 1)
  have hlayer := Integrable.integral_eq_integral_meas_lt hFint
    (ae_of_all _ fun x ↦ sq_nonneg _)
  have htail : ∀ t ∈ Ioi (0 : ℝ), (volume.restrict S).real {x | t < F x} ≤
      Real.exp (-a) / n.factorial * Real.exp (-Real.sqrt t) := by
    intro t ht
    rw [measureReal_restrict_apply (measurableSet_lt measurable_const hFc.measurable)]
    have hbound := volume_real_standardSimplex_one_inter_lt_mul_sup'_sub_log_le (n := n)
      (a + Real.sqrt t)
    rw [neg_add, Real.exp_add, mul_div_right_comm] at hbound
    refine (measureReal_mono ?_ ((measure_mono inter_subset_left).trans_lt
      (volume_standardSimplex_lt_top _ 1)).ne).trans hbound
    rintro x ⟨hFx, hxS⟩
    refine ⟨hxS, ?_⟩
    have hFx : t < F x := hFx
    change a + Real.sqrt t < _
    have h0 : 0 ≤ max (n * univ.sup' univ_nonempty x - Real.log n - a) 0 := le_max_right _ _
    have hroot : Real.sqrt t < max (n * univ.sup' univ_nonempty x - Real.log n - a) 0 := by
      rw [← Real.sqrt_sq h0]
      exact Real.sqrt_lt_sqrt (le_of_lt ht) hFx
    rcases lt_max_iff.1 hroot with h | h
    · linarith
    · exact absurd h (not_lt.2 (Real.sqrt_nonneg t))
  have hraw : ∫ x in S, F x ≤ 2 * Real.exp (-a) / n.factorial := by
    rw [hlayer]
    calc
      (∫ t in Ioi (0 : ℝ), (volume.restrict S).real {x | t < F x}) ≤
          ∫ t in Ioi (0 : ℝ), Real.exp (-a) / n.factorial * Real.exp (-Real.sqrt t) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ measureReal_nonneg)
          (integrableOn_exp_neg_sqrt.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ htail))
      _ = 2 * Real.exp (-a) / n.factorial := by
        rw [integral_const_mul, integral_exp_neg_sqrt]
        ring
  have hvol : volume.real S = 1 / n.factorial := by
    rw [hS, volume_real_standardSimplex _ zero_le_one, Fintype.card_fin, one_pow]
  have hfac : (0 : ℝ) < n.factorial := by positivity
  rw [setAverage_eq, hvol, smul_eq_mul, one_div, inv_inv]
  calc
    (n.factorial : ℝ) * ∫ x in S, F x ≤ n.factorial * (2 * Real.exp (-a) / n.factorial) :=
      mul_le_mul_of_nonneg_left hraw hfac.le
    _ = 2 * Real.exp (-a) := by field_simp

/-! ### Moments of the largest coordinate -/

/-- The mean of the largest coordinate of a uniform point of the standard simplex: for `n ≠ 0`
and `0 < W`, `⨍ x in standardSimplex (Fin n) W, maxᵢ x i = W * harmonic n / (n + 1)`. -/
theorem setAverage_standardSimplex_sup' (n : ℕ) [NeZero n] {W : ℝ} (hW : 0 < W) :
    ⨍ x in standardSimplex (Fin n) W, univ.sup' univ_nonempty x =
      W * (harmonic n : ℝ) / (n + 1) :=
  (setAverage_standardSimplex_comp_sup' W fun m ↦ m).trans
    (setAverage_weightedSimplex_succ_sum n hW)

/-- The second moment of the largest coordinate of a uniform point of the standard simplex: for
`n ≠ 0` and `0 < W`, with `H₁ = ∑ i < n, 1 / (i + 1)` and `H₂ = ∑ i < n, 1 / (i + 1) ^ 2`,
`⨍ x in standardSimplex (Fin n) W, (maxᵢ x i) ^ 2 = W ^ 2 * (H₁ ^ 2 + H₂) / ((n + 1) * (n + 2))`.
-/
theorem setAverage_standardSimplex_sup'_sq (n : ℕ) [NeZero n] {W : ℝ} (hW : 0 < W) :
    ⨍ x in standardSimplex (Fin n) W, univ.sup' univ_nonempty x ^ 2 =
      W ^ 2 * ((∑ i : Fin n, 1 / ((i : ℝ) + 1)) ^ 2 + ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2) /
        ((n + 1) * (n + 2)) :=
  (setAverage_standardSimplex_comp_sup' W fun m ↦ m ^ 2).trans
    (setAverage_weightedSimplex_succ_sum_sq n hW)

end MeasureTheory
