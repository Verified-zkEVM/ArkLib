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
# The Dirichlet integral on the standard simplex

`Set.standardSimplex ι L` is the set of nonnegative vectors `x : ι → ℝ` with `∑ i, x i ≤ L`,
for an arbitrary finite index type `ι`. It is the full-dimensional corner simplex, not Mathlib's
`stdSimplex`, which is the face `∑ i, x i = 1` and has Lebesgue measure zero.

With `n = Fintype.card ι`, natural exponents `a : ι → ℕ` and `b : ℕ`, and `0 ≤ L`, this file
proves the Dirichlet integral
`∫ x in standardSimplex ι L, (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b =
  L ^ (n + ∑ i, a i + b) * ((∏ i, (a i)!) * b! / (n + ∑ i, a i + b)!)`.
The slack coordinate `L - ∑ i, x i` carries its own exponent, so the formula is symmetric in all
`n + 1` barycentric coordinates. Taking every exponent zero gives the volume `L ^ n / n!`.

The proof integrates out the first coordinate of `Fin (n + 1) → ℝ` (Fubini on
`MeasurableEquiv.piFinSuccAbove`), applies the beta integral `integral_pow_mul_sub_pow`, and
inducts on `n`. The result for an arbitrary `ι` follows by reindexing along
`Fintype.equivFin ι`, which preserves Lebesgue measure and the simplex.

The empty index type is included: `standardSimplex ι L` is then the single point when `0 ≤ L`,
its volume is `1`, and the Dirichlet integral is `L ^ b`. For `L < 0` the simplex is empty,
so the formulas that mention `L ^ n` need `0 ≤ L`.

## Main statements

* `Set.standardSimplex`, with `isClosed_standardSimplex`, `isCompact_standardSimplex`, and
  `standardSimplex_eq_empty` for `L < 0`.
* `MeasureTheory.setIntegral_standardSimplex_comp_equiv`: reindexing coordinates along an
  equivalence of finite index types.
* `MeasureTheory.setIntegral_standardSimplex_succ`: the Fubini recurrence for an arbitrary
  integrable function on `standardSimplex (Fin (n + 1)) L`.
* `MeasureTheory.integral_standardSimplex_prod_pow_mul_pow`: the Dirichlet integral.
* `MeasureTheory.volume_real_standardSimplex` and `MeasureTheory.volume_standardSimplex`:
  the volume `L ^ n / n!`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Set

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The corner simplex of nonnegative vectors `x : ι → ℝ` with `∑ i, x i ≤ L`. It is
full-dimensional, unlike Mathlib's `stdSimplex`, and it is empty when `L < 0`. For an empty
index type it is the whole (one-point) space when `0 ≤ L`. -/
def standardSimplex (ι : Type*) [Fintype ι] (L : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L}

/-- Membership in the standard simplex, unfolded. -/
@[simp]
theorem mem_standardSimplex {L : ℝ} {x : ι → ℝ} :
    x ∈ standardSimplex ι L ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L :=
  Iff.rfl

/-- Every coordinate of a point of the standard simplex lies in `[0, L]`. -/
theorem standardSimplex_subset_Icc (L : ℝ) :
    standardSimplex ι L ⊆ Icc 0 (fun _ ↦ L) := by
  intro x hx
  refine ⟨fun i ↦ hx.1 i, fun i ↦ ?_⟩
  exact (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans hx.2

/-- A negative budget leaves no point: the coordinate sum of a nonnegative vector is nonnegative.
This includes the empty index type, where the sum is `0`. -/
theorem standardSimplex_eq_empty {L : ℝ} (hL : L < 0) : standardSimplex ι L = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ hx.1 i
  linarith [hx.2]

/-- The standard simplex is closed: it is cut out by finitely many non-strict linear
inequalities. -/
theorem isClosed_standardSimplex (ι : Type*) [Fintype ι] (L : ℝ) :
    IsClosed (standardSimplex ι L) := by
  have hnonneg : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    rw [show {x : ι → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  have hsum : Continuous (fun x : ι → ℝ ↦ ∑ i, x i) :=
    continuous_finsetSum Finset.univ fun i _ ↦ continuous_apply i
  exact hnonneg.inter (isClosed_le hsum continuous_const)

/-- The standard simplex is measurable, because it is closed. -/
theorem measurableSet_standardSimplex (ι : Type*) [Fintype ι] (L : ℝ) :
    MeasurableSet (standardSimplex ι L) :=
  (isClosed_standardSimplex ι L).measurableSet

/-- The standard simplex is compact for every real `L`: it is a closed subset of the box
`Icc 0 (fun _ ↦ L)`, which is empty when `L < 0`. -/
theorem isCompact_standardSimplex (ι : Type*) [Fintype ι] (L : ℝ) :
    IsCompact (standardSimplex ι L) :=
  isCompact_Icc.of_isClosed_subset (isClosed_standardSimplex ι L)
    (standardSimplex_subset_Icc L)

/-- Splitting off the first coordinate: `Fin.cons x y` lies in the `(n + 1)`-dimensional simplex
of budget `L` exactly when `0 ≤ x ≤ L` and `y` lies in the `n`-dimensional simplex of the
remaining budget `L - x`. -/
theorem cons_mem_standardSimplex_iff {n : ℕ} {L x : ℝ} {y : Fin n → ℝ} :
    (Fin.cons x y : Fin (n + 1) → ℝ) ∈ standardSimplex (Fin (n + 1)) L ↔
      x ∈ Icc 0 L ∧ y ∈ standardSimplex (Fin n) (L - x) := by
  simp only [mem_standardSimplex, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ, mem_Icc]
  constructor
  · rintro ⟨⟨hx, hy⟩, hsum⟩
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ hy i
    exact ⟨⟨hx, by linarith⟩, hy, by linarith⟩
  · rintro ⟨⟨hx, -⟩, hy, hsum⟩
    exact ⟨⟨hx, hy⟩, by linarith⟩

end Set

namespace MeasureTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A function continuous on the standard simplex is integrable there, by compactness. -/
theorem _root_.ContinuousOn.integrableOn_standardSimplex {f : (ι → ℝ) → ℝ} {L : ℝ}
    (hf : ContinuousOn f (standardSimplex ι L)) : IntegrableOn f (standardSimplex ι L) :=
  hf.integrableOn_compact (isCompact_standardSimplex ι L)

/-- The standard simplex has finite Lebesgue measure, by compactness. -/
theorem volume_standardSimplex_lt_top (ι : Type*) [Fintype ι] (L : ℝ) :
    volume (standardSimplex ι L) < ⊤ :=
  (isCompact_standardSimplex ι L).measure_lt_top

/-- Reindexing coordinates along `e : ι ≃ κ` preserves Lebesgue measure and maps the standard
simplex onto the standard simplex, so an integral over `standardSimplex κ L` can be computed over
`standardSimplex ι L`. No integrability hypothesis is needed because the change of variables is a
measure-preserving equivalence. -/
theorem setIntegral_standardSimplex_comp_equiv (e : ι ≃ κ) (L : ℝ) (f : (κ → ℝ) → ℝ) :
    (∫ y in standardSimplex ι L, f (fun k ↦ y (e.symm k))) =
      ∫ x in standardSimplex κ L, f x := by
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ ↦ ℝ) e
  have hg : MeasurePreserving g := volume_measurePreserving_piCongrLeft (fun _ : κ ↦ ℝ) e
  have hgapp : ∀ y k, g y k = y (e.symm k) := by
    intro y k
    simp [g, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hpre : g ⁻¹' standardSimplex κ L = standardSimplex ι L := by
    ext y
    simp only [mem_preimage, mem_standardSimplex, hgapp]
    rw [e.symm.sum_comp y]
    exact and_congr_left' ⟨fun h i ↦ by simpa using h (e i), fun h k ↦ h _⟩
  have hgfun : ∀ y, g y = fun k ↦ y (e.symm k) := fun y ↦ funext (hgapp y)
  rw [← hg.setIntegral_preimage_emb g.measurableEmbedding, hpre]
  simp only [hgfun]

/-- The Fubini recurrence on the standard simplex: integrating out the first coordinate `x`
leaves an integral over the `n`-dimensional simplex of budget `L - x`, for `x` from `0` to `L`.

The integrability hypothesis is needed for Fubini's theorem; without it the left side is `0` by
convention while the iterated integral need not be. No sign condition on `L` is needed: for
`L < 0` both sides are `0`. -/
theorem setIntegral_standardSimplex_succ {n : ℕ} {L : ℝ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : IntegrableOn f (standardSimplex (Fin (n + 1)) L)) :
    (∫ z in standardSimplex (Fin (n + 1)) L, f z) =
      ∫ x in (0 : ℝ)..L, ∫ y in standardSimplex (Fin n) (L - x), f (Fin.cons x y) := by
  rcases lt_or_ge L 0 with hL | hL
  · rw [standardSimplex_eq_empty hL, Measure.restrict_empty, integral_zero_measure,
      intervalIntegral.integral_symm, intervalIntegral.integral_of_le hL.le]
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ (0 : ℝ)), integral_zero, neg_zero]
    intro x hx
    dsimp only
    rw [standardSimplex_eq_empty (by linarith [hx.1]), Measure.restrict_empty,
      integral_zero_measure]
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm _
  have hexy : ∀ x y, e (x, y) = Fin.cons x y := by
    intro x y
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero']
  have hS := measurableSet_standardSimplex (Fin (n + 1)) L
  have hint : Integrable ((e ⁻¹' standardSimplex (Fin (n + 1)) L).indicator fun z ↦ f (e z))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((he.integrableOn_comp_preimage e.measurableEmbedding).2 hf).integrable_indicator
      (hS.preimage e.measurable)
  rw [← he.setIntegral_preimage_emb e.measurableEmbedding,
    ← integral_indicator (hS.preimage e.measurable), Measure.volume_eq_prod,
    integral_prod _ hint, intervalIntegral.integral_of_le hL,
    setIntegral_congr_set Ioc_ae_eq_Icc, ← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc (0 : ℝ) L
  · rw [indicator_of_mem hx, ← integral_indicator (measurableSet_standardSimplex _ _)]
    congr 1
    funext y
    have hmem : (x, y) ∈ e ⁻¹' standardSimplex (Fin (n + 1)) L ↔
        y ∈ standardSimplex (Fin n) (L - x) := by
      rw [mem_preimage, hexy, cons_mem_standardSimplex_iff, and_iff_right hx]
    by_cases hy : y ∈ standardSimplex (Fin n) (L - x)
    · rw [indicator_of_mem (hmem.mpr hy), indicator_of_mem hy, hexy]
    · rw [indicator_of_notMem (mt hmem.mp hy), indicator_of_notMem hy]
  · rw [indicator_of_notMem hx]
    have hsection : ∀ y, (x, y) ∉ e ⁻¹' standardSimplex (Fin (n + 1)) L := by
      intro y hy
      rw [mem_preimage, hexy, cons_mem_standardSimplex_iff] at hy
      exact hx hy.1
    simp [indicator_of_notMem (hsection _)]

/-- The Dirichlet integral for the index type `Fin n`, by induction on `n`. -/
private theorem integral_standardSimplex_prod_pow_mul_pow_fin (n : ℕ) (a : Fin n → ℕ) (b : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex (Fin n) L, (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b) =
      L ^ (n + ∑ i, a i + b) *
        ((∏ i, ((a i).factorial : ℝ)) * b.factorial / (n + ∑ i, a i + b).factorial) := by
  induction n generalizing L with
  | zero =>
    rw [Measure.volume_pi_eq_dirac]
    simp [standardSimplex, hL, Nat.factorial_ne_zero]
  | succ n ih =>
    have hcont : Continuous fun x : Fin (n + 1) → ℝ ↦ (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b := by
      fun_prop
    rw [setIntegral_standardSimplex_succ hcont.continuousOn.integrableOn_standardSimplex]
    set N := n + ∑ i, a (Fin.succ i) + b
    set C := (∏ i, ((a (Fin.succ i)).factorial : ℝ)) * b.factorial / N.factorial
    have hinner : ∀ x ∈ uIcc 0 L,
        (∫ y in standardSimplex (Fin n) (L - x),
          (∏ i, (Fin.cons x y : Fin (n + 1) → ℝ) i ^ a i) *
            (L - ∑ i, (Fin.cons x y : Fin (n + 1) → ℝ) i) ^ b) =
          x ^ a 0 * ((L - x) ^ N * C) := by
      intro x hx
      rw [uIcc_of_le hL] at hx
      rw [← ih (fun i ↦ a i.succ) (sub_nonneg.mpr hx.2), ← integral_const_mul]
      congr 1
      funext y
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    rw [intervalIntegral.integral_congr hinner]
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_mul_const, integral_pow_mul_sub_pow]
    have he : a 0 + N + 1 = n + 1 + ∑ i, a i + b := by
      simp only [N, Fin.sum_univ_succ]; ring
    rw [he, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    simp only [C]
    field_simp

/-- The Dirichlet integral on the standard simplex, with natural exponents: for
`n = Fintype.card ι` and `0 ≤ L`,
`∫ x in standardSimplex ι L, (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b =
  L ^ (n + ∑ i, a i + b) * ((∏ i, (a i)!) * b! / (n + ∑ i, a i + b)!)`.

The hypothesis `0 ≤ L` is needed: for `L < 0` the simplex is empty, so the left side is `0`,
while the right side is not (for the empty index type and `b = 0` it is `1`). -/
theorem integral_standardSimplex_prod_pow_mul_pow (a : ι → ℕ) (b : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex ι L, (∏ i, x i ^ a i) * (L - ∑ i, x i) ^ b) =
      L ^ (Fintype.card ι + ∑ i, a i + b) *
        ((∏ i, ((a i).factorial : ℝ)) * b.factorial /
          (Fintype.card ι + ∑ i, a i + b).factorial) := by
  let e := (Fintype.equivFin ι).symm
  rw [← setIntegral_standardSimplex_comp_equiv e L]
  have h := integral_standardSimplex_prod_pow_mul_pow_fin (Fintype.card ι) (a ∘ e) b hL
  simp only [Function.comp_apply, e.prod_comp (fun i ↦ ((a i).factorial : ℝ)),
    e.sum_comp a] at h
  rw [← h]
  congr 1
  funext y
  rw [← e.symm.prod_comp, ← e.symm.sum_comp]
  simp

/-- The standard simplex in `n = Fintype.card ι` dimensions has volume `L ^ n / n!` for
`0 ≤ L`. The hypothesis is needed: for `L < 0` the simplex is empty, yet `L ^ 0 / 0! = 1`. -/
theorem volume_real_standardSimplex (ι : Type*) [Fintype ι] {L : ℝ} (hL : 0 ≤ L) :
    volume.real (standardSimplex ι L) = L ^ Fintype.card ι / (Fintype.card ι).factorial := by
  have h := integral_standardSimplex_prod_pow_mul_pow (ι := ι) (fun _ ↦ 0) 0 hL
  simpa [Nat.factorial_ne_zero, div_eq_mul_inv] using h

/-- The volume of the standard simplex as an extended nonnegative real, `ofReal (L ^ n / n!)`
for `0 ≤ L`. -/
theorem volume_standardSimplex (ι : Type*) [Fintype ι] {L : ℝ} (hL : 0 ≤ L) :
    volume (standardSimplex ι L) =
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  rw [← volume_real_standardSimplex ι hL, ofReal_measureReal
    (volume_standardSimplex_lt_top ι L).ne]

end MeasureTheory
