/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Analysis.Simplex.MonomialIntegral
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue integrals on the standard simplex

This file identifies the repeated beta integral with the actual Lebesgue set integral on
`{x : Fin n → ℝ | 0 ≤ x ∧ ∑ i, x i ≤ L}`.  The slack coordinate is `L - ∑ i, x i`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace SimplexIntegration

/-- The closed standard simplex of nonnegative vectors whose coordinate sum is at most `L`. -/
def standardSimplex (n : ℕ) (L : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L}

/-- A coordinate monomial together with a power of the slack coordinate. -/
def simplexMonomial {n : ℕ} (a : Fin n → ℕ) (b : ℕ) (L : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b

theorem isClosed_standardSimplex (n : ℕ) (L : ℝ) : IsClosed (standardSimplex n L) := by
  have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    rw [show {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  have hsum : Continuous (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    continuous_finsetSum Finset.univ fun i _ ↦ continuous_apply i
  exact hnonneg.inter (isClosed_le hsum continuous_const)

theorem isCompact_standardSimplex (n : ℕ) {L : ℝ} (_hL : 0 ≤ L) :
    IsCompact (standardSimplex n L) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : Fin n → ℝ) (fun _ ↦ L))).of_isClosed_subset
    (isClosed_standardSimplex n L)
  intro x hx
  refine ⟨fun i ↦ hx.1 i, fun i ↦ ?_⟩
  have hi : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hx.1 j) (Finset.mem_univ i)
  exact hi.trans hx.2

theorem continuous_simplexMonomial {n : ℕ} (a : Fin n → ℕ) (b : ℕ) (L : ℝ) :
    Continuous (simplexMonomial a b L) := by
  unfold simplexMonomial
  fun_prop

theorem integrableOn_simplexMonomial {n : ℕ} (a : Fin n → ℕ) (b : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    IntegrableOn (simplexMonomial a b L) (standardSimplex n L) :=
  (continuous_simplexMonomial a b L).continuousOn.integrableOn_compact
    (isCompact_standardSimplex n hL)

private theorem standardSimplex_cons {n : ℕ} {L x : ℝ}
    (y : Fin n → ℝ) :
    Fin.cons x y ∈ standardSimplex (n + 1) L ↔
      x ∈ Icc 0 L ∧ y ∈ standardSimplex n (L - x) := by
  constructor
  · rintro ⟨hnonneg, htotal⟩
    have hx : 0 ≤ x := by simpa using hnonneg 0
    have hy : ∀ i, 0 ≤ y i := by
      intro i
      simpa using hnonneg i.succ
    have hsum : x + ∑ i, y i ≤ L := by
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using htotal
    refine ⟨⟨hx, ?_⟩, hy, ?_⟩
    · exact (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hy i)).trans hsum
    · linarith
  · rintro ⟨⟨hx0, hxL⟩, hy, hsum⟩
    have htotal : x + ∑ i, y i ≤ L := by linarith
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hx0
      · simpa using hy j
    · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using htotal

private theorem simplexMonomial_cons {n : ℕ} (a : Fin (n + 1) → ℕ)
    (b : ℕ) (L x : ℝ) (y : Fin n → ℝ) :
    simplexMonomial a b L (Fin.cons x y) =
      x ^ a 0 * simplexMonomial (fun i ↦ a i.succ) b (L - x) y := by
  simp [simplexMonomial, Fin.prod_univ_succ, Fin.sum_univ_succ]
  ring

/-- Fubini recurrence for a standard-simplex monomial integral. -/
theorem integral_standardSimplex_succ {n : ℕ} (a : Fin (n + 1) → ℕ) (b : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ z in standardSimplex (n + 1) L, simplexMonomial a b L z) =
      ∫ x in (0 : ℝ)..L, x ^ a 0 *
        (∫ y in standardSimplex n (L - x),
          simplexMonomial (fun i ↦ a i.succ) b (L - x) y) := by
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm _
  have hint : IntegrableOn (simplexMonomial a b L ∘ e)
      (e ⁻¹' standardSimplex (n + 1) L) :=
    (he.integrableOn_comp_preimage e.measurableEmbedding).2
      (integrableOn_simplexMonomial a b hL)
  have hindicator : Integrable
      ((e ⁻¹' standardSimplex (n + 1) L).indicator
        (simplexMonomial a b L ∘ e)) :=
    hint.integrable_indicator (measurableSet_preimage e.measurable
      (isClosed_standardSimplex (n + 1) L).measurableSet)
  rw [← he.map_eq, setIntegral_map_equiv]
  rw [← integral_indicator (measurableSet_preimage e.measurable
    (isClosed_standardSimplex (n + 1) L).measurableSet)]
  rw [Measure.volume_eq_prod]
  change (∫ z, (e ⁻¹' standardSimplex (n + 1) L).indicator
    (simplexMonomial a b L ∘ e) z ∂volume.prod volume) = _
  rw [integral_prod _ hindicator]
  rw [intervalIntegral.integral_of_le hL]
  rw [setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (0 : ℝ) L
  · rw [indicator_of_mem hx]
    rw [show (∫ y, (e ⁻¹' standardSimplex (n + 1) L).indicator
          (simplexMonomial a b L ∘ e) (x, y)) =
        ∫ y in standardSimplex n (L - x),
          x ^ a 0 * simplexMonomial (fun i ↦ a i.succ) b (L - x) y by
      rw [← integral_indicator (isClosed_standardSimplex n (L - x)).measurableSet]
      apply integral_congr_ae
      filter_upwards [] with y
      have hexy : e (x, y) = Fin.cons x y := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_zero']
      have hmem : (x, y) ∈ e ⁻¹' standardSimplex (n + 1) L ↔
          y ∈ standardSimplex n (L - x) := by
        change e (x, y) ∈ standardSimplex (n + 1) L ↔ _
        rw [hexy, standardSimplex_cons y, and_iff_right hx]
      by_cases hy : y ∈ standardSimplex n (L - x)
      · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
        simp only [Function.comp_apply, hexy, simplexMonomial_cons]
      · rw [Set.indicator_of_notMem (hmem.not.mpr hy), Set.indicator_of_notMem hy]]
    rw [MeasureTheory.integral_const_mul]
  · simp only [Set.indicator_of_notMem hx]
    have hsection : ∀ y : Fin n → ℝ,
        (x, y) ∉ e ⁻¹' standardSimplex (n + 1) L := by
      intro y hy
      apply hx
      have hexy : e (x, y) = Fin.cons x y := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_zero']
      have hy' : e (x, y) ∈ standardSimplex (n + 1) L := hy
      rw [hexy] at hy'
      exact (standardSimplex_cons y).mp hy' |>.1
    simp [Set.indicator_of_notMem, hsection]

/-- The actual Lebesgue integral on a standard simplex equals the repeated beta integral. -/
theorem integral_standardSimplex_eq_monomialIntegral (n : ℕ) (a : Fin n → ℕ) (b : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, simplexMonomial a b L x) =
      monomialIntegral (List.ofFn a) b L := by
  induction n generalizing L b with
  | zero =>
      rw [MeasureTheory.Measure.volume_pi_eq_dirac]
      simp [standardSimplex, simplexMonomial, monomialIntegral, hL]
  | succ n ih =>
      rw [integral_standardSimplex_succ a b hL, List.ofFn_succ]
      simp only [monomialIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hL] at hx
      change x ^ a 0 * (∫ y in standardSimplex n (L - x),
        simplexMonomial (fun i ↦ a i.succ) b (L - x) y) = _
      rw [ih (fun i ↦ a i.succ) b (sub_nonneg.mpr hx.2)]

/-- Factorial formula for a monomial integrated against Lebesgue volume on a standard simplex. -/
theorem integral_standardSimplex_eq (n : ℕ) (a : Fin n → ℕ) (b : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, simplexMonomial a b L x) =
      L ^ (n + ∑ i, a i + b) *
        (((∏ i, (a i).factorial : ℕ) : ℝ) * b.factorial /
          (n + ∑ i, a i + b).factorial) := by
  rw [integral_standardSimplex_eq_monomialIntegral n a b hL,
    monomialIntegral_eq (List.ofFn a) b hL]
  simp only [List.length_ofFn, List.sum_ofFn, List.prod_ofFn, List.map_ofFn,
    Function.comp_apply]

/-- The `n`-dimensional standard simplex has volume `L ^ n / n!`. -/
theorem volume_standardSimplex (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    volume.real (standardSimplex n L) = L ^ n / n.factorial := by
  have h := integral_standardSimplex_eq n (fun _ ↦ 0) 0 hL
  simpa [simplexMonomial, isClosed_standardSimplex n L |>.measurableSet,
    div_eq_mul_inv] using h

end SimplexIntegration
