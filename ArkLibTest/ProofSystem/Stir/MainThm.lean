/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import ArkLib.ProofSystem.Stir.MainThm

/-!
# STIR main theorem and round-by-round soundness: the hypotheses are consistent

The hypotheses of `stir_rbr_soundness` (Lemma 5.4 of [ACFY24stir]) used to be contradictory, so the
lemma was vacuous (#1284). These tests check that, after the restatement:
* the hypotheses are jointly satisfiable, by an explicit instance with `M = 0`
  (`F = ZMod 5`, `ι₀` the four units, `deg = 2`, `k₀ = 2`, `δ₀ = 1/4`);
* the reversed condition `|ιᵢ| ≤ degreeᵢ` is rejected by `ParamConditions`, and it is what made the
  hypotheses contradictory;
* the other conditions that were corrected are exercised: the degree is a power of 2, and the
  repetition parameter of the last round is not constrained;
* the hypotheses of `stir_main` (Theorem 5.1) are satisfiable for every constant `c_F` of the
  field-size bound, which is chosen before the parameters (`main_hypotheses_satisfiable`), and they
  force `degree < |ι|`, so the denominator `log (1 / ρ)` of that bound is positive and the bound is
  not met through a division by zero (`degree_lt_card_of_delta_bounds`, `log_inv_rate_pos`);
* the completeness and soundness relations fit together: the codewords are in the soundness
  language when `0 < δ`, and the strict relation is empty for `δ = 0`
  (`stirRelation_zero_subset_stirOpenRelation`, `stirOpenRelation_zero_eq_empty`), which is why
  `0 < δ₀` and `0 < δ` are assumed.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open NNReal ReedSolomon LinearCode STIR StirIOP

namespace ArkLibTest.StirMainThm

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The four units of `ZMod 5`, as an embedding of `Fin 4`. -/
private def units : Fin 4 ↪ ZMod 5 := ⟨fun i => ((i : ℕ) + 1 : ZMod 5), by decide⟩

/-- The units of `ZMod 5` form a smooth domain: all of the group `(ZMod 5)ˣ`, of order `4 = 2²`. -/
private instance smoothUnits : Smooth units where
  H := ⊤
  a := 1
  h_coset := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Subgroup.coe_top, Units.val_one, one_mul]
    revert x
    decide
  h_card_pow2 := ⟨2, by simp⟩

/-- The domains of the `M = 0` instance. -/
private abbrev domains : Fin (0 + 1) → Type := fun _ => Fin 4

/-- Parameters with `M = 0`: initial degree `2`, folding parameter `2`, and a repetition parameter
`100`, larger than every degree (the last repetition parameter is not constrained). -/
private def params : Params domains (ZMod 5) where
  deg := 2
  foldingParam := fun _ => 2
  φ := fun _ => units
  repeatParam := fun _ => 100

/-- Before any fold the degree is the initial degree (`degree_zero`). -/
example : degree domains params 0 = 2 := degree_zero domains params

private lemma degree_zero_eq : degree domains params 0 = 2 := degree_zero domains params

/-- The parameters of the `M = 0` instance satisfy the conditions of Construction 5.2. -/
private def conditions : ParamConditions domains params where
  h_deg := ⟨1, rfl⟩
  h_foldingParams := fun _ => ⟨1, rfl⟩
  h_deg_ge := by simp [params]
  h_smooth := fun _ => smoothUnits
  h_smooth_lt := fun i => by
    have : i = 0 := Fin.fin_one_eq_zero i
    subst this
    rw [degree_zero_eq]
    simp
  h_repeatP_le := fun i => i.elim0

private noncomputable def dist : Distances 0 := ⟨fun _ => 1 / 4, fun _ => 1⟩

/-- The code `RS[F, ι₀, 2]` has no list-decodability requirement, since `M = 0`. -/
private noncomputable def codes : CodeParams domains params dist where
  C := fun i => code (params.φ i) (degree domains params i)
  h_code := fun _ => rfl
  h_listDecode := fun i hi => absurd (Fin.fin_one_eq_zero i) hi

private lemma rate_eq : rate (code (params.φ 0) (degree domains params 0)) = 1 / 2 := by
  rw [degree_zero_eq, rateOfLinearCode_eq_min_div]
  norm_num

/-- `δ₀ = 1/4 < 1 - B⋆(1/2) = 1 - √(1/2)`. -/
private lemma delta_zero_lt :
    dist.δ 0 < 1 - Bstar (rate (code (params.φ 0) (degree domains params 0))) := by
  rw [rate_eq]
  unfold Bstar dist
  have h : NNReal.sqrt ((1 / 2 : ℚ≥0) : ℝ≥0) < 3 / 4 := by
    have h34 : (3 / 4 : ℝ≥0) = NNReal.sqrt ((3 / 4) ^ 2) := (NNReal.sqrt_sq _).symm
    rw [h34, NNReal.sqrt_lt_sqrt]
    push_cast
    norm_num
  change (1 / 4 : ℝ≥0) < 1 - _
  rw [lt_tsub_iff_right]
  calc (1 / 4 : ℝ≥0) + NNReal.sqrt ((1 / 2 : ℚ≥0) : ℝ≥0) < 1 / 4 + 3 / 4 := by gcongr
    _ = 1 := by norm_num

/-- The hypotheses of `stir_rbr_soundness` are jointly satisfiable, for `M = 0`: the conditions on
the parameters, the list-decodable codes, `0 < δ₀ < 1 - B⋆(ρ₀)`, and the (empty) conditions on
`δᵢ` for `0 < i ≤ M`. -/
theorem rbr_soundness_hypotheses_satisfiable :
    ∃ (P : Params domains (ZMod 5)) (Dist : Distances 0),
      Nonempty (ParamConditions domains P) ∧ Nonempty (CodeParams domains P Dist) ∧
      0 < Dist.δ 0 ∧
      Dist.δ 0 < 1 - Bstar (rate (code (P.φ 0) (degree domains P 0))) ∧
      ∀ {j : Fin (0 + 1)}, j ≠ 0 →
        0 < Dist.δ j ∧
        Dist.δ j < (1 - rate (code (P.φ j) (degree domains P j))
          - 1 / Fintype.card (domains j) : ℝ) ∧
        Dist.δ j < 1 - Bstar (rate (code (P.φ j) (degree domains P j))) :=
  ⟨params, dist, ⟨conditions⟩, ⟨codes⟩, by simp [dist], delta_zero_lt,
    fun hj => absurd (Fin.fin_one_eq_zero _) hj⟩

/-- The old condition `h_repeatP_le : tᵢ + 1 ≤ dᵢ` for every `i : Fin (M + 1)` would have rejected
the repetition parameter `100` of the last round, which Construction 5.2 does not constrain. -/
example : ¬ (params.repeatParam 0 + 1 ≤ degree domains params 0) := by
  rw [degree_zero_eq]
  simp [params]

/-- The reversed condition: a domain no larger than the degree is rejected by `ParamConditions`. -/
theorem not_paramConditions_of_card_le_degree {F : Type} [Field F] [DecidableEq F]
    {M : ℕ} {ι : Fin (M + 1) → Type} [∀ i, Fintype (ι i)] {P : Params ι F}
    (h : Fintype.card (ι 0) ≤ degree ι P 0) : ¬ Nonempty (ParamConditions ι P) :=
  fun ⟨hP⟩ => absurd (hP.h_smooth_lt 0) (not_lt.2 h)

/-- Why the old condition made Lemma 5.4 vacuous: if `|ι₀| ≤ d₀` the code has rate `1`, so
`1 - B⋆(ρ₀) = 0` and no `δ₀ : ℝ≥0` satisfies `δ₀ < 1 - B⋆(ρ₀)`. -/
theorem delta_zero_lt_false_of_card_le_degree {F : Type} [Field F]
    {M : ℕ} {ι : Fin (M + 1) → Type} [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)] {P : Params ι F}
    (h : Fintype.card (ι 0) ≤ degree ι P 0) (δ₀ : ℝ≥0)
    (hδ₀ : δ₀ < 1 - Bstar (rate (code (P.φ 0) (degree ι P 0)))) : False := by
  have hpos : (Fintype.card (ι 0) : ℚ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι 0)).ne'
  have hrate : rate (code (P.φ 0) (degree ι P 0)) = 1 := by
    rw [rateOfLinearCode_eq_min_div, min_eq_right h]
    exact div_self hpos
  rw [hrate] at hδ₀
  simp [Bstar] at hδ₀

/-- The initial degree must be a power of 2: `3` is rejected. -/
theorem not_paramConditions_of_deg_eq_three {F : Type} [Field F] [DecidableEq F]
    {M : ℕ} {ι : Fin (M + 1) → Type} [∀ i, Fintype (ι i)] {P : Params ι F}
    (h : P.deg = 3) : ¬ Nonempty (ParamConditions ι P) := by
  rintro ⟨hP⟩
  obtain ⟨k, hk⟩ := hP.h_deg
  rw [h] at hk
  rcases k with _ | _ | k
  · simp at hk
  · simp at hk
  · have : 4 ≤ 2 ^ (k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

section SignDomain

variable (p : ℕ) [Fact p.Prime] [Fact (2 < p)]

/-- The domain `{1, -1}` of `ZMod p`. -/
private def signs : Fin 2 ↪ ZMod p :=
  ⟨![1, -1], by
    have hne : (1 : ZMod p) ≠ -1 := (ZMod.neg_one_ne_one).symm
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

private lemma signs_zero : signs p 0 = 1 := rfl

private lemma signs_one : signs p 1 = -1 := rfl

private instance smoothSigns : Smooth (signs p) where
  H := Subgroup.zpowers (-1 : (ZMod p)ˣ)
  a := 1
  h_coset := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, Set.mem_image,
      SetLike.mem_coe, Units.val_one, one_mul]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨1, Subgroup.one_mem _, by simp [signs_zero]⟩
      · exact ⟨-1, Subgroup.mem_zpowers _, by simp [signs_one]⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rcases Int.even_or_odd k with he | ho
      · exact ⟨0, by simp [signs_zero, he.neg_one_zpow]⟩
      · exact ⟨1, by simp [signs_one, ho.neg_one_zpow]⟩
  h_card_pow2 := ⟨1, by simp⟩

/-- The code of degree `1` on the two points `{1, -1}` has rate `1/2`. -/
private lemma rate_signs : rate (code (signs p) 1) = 1 / 2 := by
  rw [rateOfLinearCode_eq_min_div]
  norm_num

end SignDomain

/-- The field-size expression of `stir_main` for `secpar = 1`, `degree = 1` and `|ι| = 2` is at most
`100`: `2 * 2^{7/2} / log 2 < 47`. -/
private lemma field_size_expr_le :
    ((1 : ℕ) : ℝ) * 2 ^ 1 * ((1 : ℕ) : ℝ) ^ 2 * ((2 : ℕ) : ℝ) ^ ((7 : ℝ) / 2) /
      Real.log (1 / (1 / 2 : ℝ)) ≤ 100 := by
  have h1 : ((2 : ℕ) : ℝ) ^ ((7 : ℝ) / 2) ≤ 16 := by
    have : ((2 : ℕ) : ℝ) ^ ((7 : ℝ) / 2) ≤ ((2 : ℕ) : ℝ) ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    refine this.trans ?_
    norm_num [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : Real.log (1 / (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  rw [h3, div_le_iff₀ (by linarith)]
  norm_num
  nlinarith [h1, h2]


/-- The hypotheses of `stir_main` are satisfiable for every constant `c_F`: take `L = {1, -1}` in
`ZMod p` for a prime `p` large enough, `degree = 1`, `secpar = 1`, `k = 4` and `δ = 1/8`. -/
theorem main_hypotheses_satisfiable (c_F : ℝ) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Fact (2 < p)) (φ : Fin 2 ↪ ZMod p) (_ : Smooth φ),
      (∃ q : ℕ, 1 = 2 ^ q) ∧ (∃ q : ℕ, 4 = 2 ^ q) ∧ 4 ≤ 4 ∧ (0 : ℝ≥0) < 1 / 8 ∧
      (((1 / 8 : ℝ≥0) : ℝ) < 1 - 1.05 * Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 2) : ℝ))) ∧
      c_F * (((1 : ℕ) : ℝ) * 2 ^ 1 * ((1 : ℕ) : ℝ) ^ 2 *
          (Fintype.card (Fin 2) : ℝ) ^ ((7 : ℝ) / 2) /
          Real.log (1 / (rate (code φ 1) : ℝ))) ≤ Fintype.card (ZMod p) := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (⌈100 * |c_F|⌉₊ + 3)
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨by omega⟩
  refine ⟨p, inferInstance, inferInstance, signs p, smoothSigns p, ⟨0, rfl⟩, ⟨2, rfl⟩, le_rfl,
    by norm_num, ?_, ?_⟩
  · have hs : Real.sqrt (1 / 2) < 0.8 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have h12 : ((1 : ℕ) : ℝ) / (Fintype.card (Fin 2) : ℝ) = 1 / 2 := by simp
    rw [h12]
    have h8 : (((1 / 8 : ℝ≥0)) : ℝ) = 1 / 8 := by push_cast; norm_num
    rw [h8]
    nlinarith [hs, Real.sqrt_nonneg (1 / 2 : ℝ)]
  · rw [rate_signs]
    have hE := field_size_expr_le
    simp only [Fintype.card_fin, Nat.cast_ofNat, ZMod.card] at hE ⊢
    have key : ∀ E : ℝ, 0 ≤ E → E ≤ 100 → c_F * E ≤ p := by
      intro E hE0 hE
      calc c_F * E ≤ |c_F| * E := mul_le_mul_of_nonneg_right (le_abs_self _) hE0
        _ ≤ |c_F| * 100 := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
        _ = 100 * |c_F| := mul_comm _ _
        _ ≤ ⌈100 * |c_F|⌉₊ := Nat.le_ceil _
        _ ≤ p := by exact_mod_cast (by omega : ⌈100 * |c_F|⌉₊ ≤ p)
    push_cast at hE ⊢
    exact key _ (div_nonneg (by positivity) (Real.log_nonneg (by norm_num))) hE

/-- Completeness inputs are in the soundness language: with `0 < δ`, every codeword is strictly
closer than `δ`. -/
theorem stirRelation_zero_subset_stirOpenRelation {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι] (degree : ℕ) (φ : ι ↪ F) {δ : ℝ≥0} (hδ : 0 < δ) :
    stirRelation degree φ 0 ⊆ stirOpenRelation degree φ δ := by
  rintro ⟨⟨_, oracle⟩, _⟩ h
  have h' : δᵣ(oracle (), ReedSolomon.code φ degree) ≤ ((0 : ℝ≥0) : ENNReal) := h
  exact lt_of_le_of_lt h' (by exact_mod_cast hδ)

/-- With `δ = 0` the strict relation is empty, so soundness would have to hold for every oracle,
codewords included: `0 < δ` is needed. -/
theorem stirOpenRelation_zero_eq_empty {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι] (degree : ℕ) (φ : ι ↪ F) :
    stirOpenRelation degree φ 0 = ∅ := by
  ext ⟨⟨_, oracle⟩, _⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have h' : δᵣ(oracle (), ReedSolomon.code φ degree) < ((0 : ℝ≥0) : ENNReal) := h
  exact not_lt_zero h'

/-- The hypotheses `0 < δ < 1 - 1.05 √(degree / |ι|)` of `stir_main` force `degree < |ι|`. -/
theorem degree_lt_card_of_delta_bounds {degree n : ℕ} (hn : 0 < n) (δ : ℝ≥0) (hδPos : 0 < δ)
    (hδub : δ < 1 - 1.05 * Real.sqrt ((degree : ℝ) / n)) : degree < n := by
  by_contra h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (degree : ℝ) / n := by
    rw [le_div_iff₀ hn']
    simpa using (by exact_mod_cast not_lt.1 h : (n : ℝ) ≤ degree)
  have h2 : (1 : ℝ) ≤ Real.sqrt ((degree : ℝ) / n) := by
    rw [Real.one_le_sqrt]; exact h1
  have h3 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδPos
  linarith

/-- So the denominator `log (1 / ρ)` of the field-size bound of `stir_main` is positive: the bound
is not met through a division by zero. -/
theorem log_inv_rate_pos {F : Type} [Field F] {ι : Type} [Fintype ι] [Nonempty ι]
    (φ : ι ↪ F) {degree : ℕ} (hdeg : 0 < degree) (hlt : degree < Fintype.card ι) :
    0 < Real.log (1 / (rate (code φ degree) : ℝ)) := by
  have hrate : (rate (code φ degree) : ℝ) = (degree : ℝ) / Fintype.card ι := by
    rw [rateOfLinearCode_eq_min_div, min_eq_left hlt.le]
    push_cast
    rfl
  rw [hrate]
  apply Real.log_pos
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < degree := by exact_mod_cast hdeg
  rw [one_div, inv_div, lt_div_iff₀ hd]
  simpa using (by exact_mod_cast hlt : (degree : ℝ) < Fintype.card ι)

end ArkLibTest.StirMainThm
