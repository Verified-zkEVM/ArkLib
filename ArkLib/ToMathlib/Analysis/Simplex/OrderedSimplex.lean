/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.WeightedVolume
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The ordered simplex

`Set.orderedSimplex n W` is the chamber of vectors `v : Fin n → ℝ` with
`v 0 ≥ v 1 ≥ ⋯ ≥ v (n - 1) ≥ 0` and `∑ i, v i ≤ W`. It is related to the two other simplices of
this directory by volume-preserving linear maps.

* **Suffix sums.** The map `u ↦ (∑ j ≥ i, u j)ᵢ` is given by an upper unitriangular matrix, so it
  preserves Lebesgue measure. It carries the weighted simplex with weights `1, …, n` onto the
  ordered simplex: the suffix sums of `u` are nonnegative and decreasing exactly when `u` is
  nonnegative, and their total is `∑ j, (j + 1) * u j`. Its first coordinate is `∑ j, u j`.
* **Sorting.** The standard simplex `Set.standardSimplex (Fin n) W` is the union of the `n!`
  chambers `{x | x ∘ σ ∈ orderedSimplex n W}`, one for each permutation `σ`, and two chambers meet
  only on a hyperplane `x i = x j`, a null set. For a function invariant under permuting
  coordinates, each chamber contributes the integral over the ordered simplex.

Together these give the law of the largest coordinate of a uniform point of the standard simplex:
it is the law of the coordinate sum `∑ i, u i` of a uniform point of the weighted simplex with
weights `1, …, n` (`setAverage_standardSimplex_comp_sup'`).

## Main statements

* `Set.orderedSimplex`, with `isCompact_orderedSimplex`.
* `Set.weightedSimplex_succ_eq_preimage_orderedSimplex`: the weighted simplex with weights
  `1, …, n` is the preimage of the ordered simplex under the suffix-sum map.
* `MeasureTheory.setIntegral_weightedSimplex_succ_comp_suffixSum`: the corresponding change of
  variables, with no Jacobian factor; `volume_real_orderedSimplex` follows.
* `MeasureTheory.setIntegral_standardSimplex_of_comp_perm`: for a function invariant under
  permuting coordinates, the integral over the standard simplex is `n!` times the integral over
  the ordered simplex.
* `MeasureTheory.setIntegral_standardSimplex_comp_sup'` and
  `MeasureTheory.setAverage_standardSimplex_comp_sup'`: the law of the largest coordinate.
* `MeasureTheory.setAverage_weightedSimplex_succ_sum_eq_orderedSimplex`: the coordinate sum on the
  weighted simplex has the law of the first coordinate on the ordered simplex.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped BigOperators

namespace Set

variable {n : ℕ} {W : ℝ}

/-- The ordered simplex of vectors `v : Fin n → ℝ` whose coordinates are nonnegative and
decreasing, `v 0 ≥ v 1 ≥ ⋯ ≥ 0`, with total `∑ i, v i ≤ W`. -/
def orderedSimplex (n : ℕ) (W : ℝ) : Set (Fin n → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ Antitone v ∧ ∑ i, v i ≤ W}

/-- Membership in the ordered simplex, unfolded. -/
@[simp]
theorem mem_orderedSimplex {v : Fin n → ℝ} :
    v ∈ orderedSimplex n W ↔ (∀ i, 0 ≤ v i) ∧ Antitone v ∧ ∑ i, v i ≤ W :=
  Iff.rfl

/-- The ordered simplex is the part of the standard simplex with decreasing coordinates. -/
theorem orderedSimplex_eq_inter (n : ℕ) (W : ℝ) :
    orderedSimplex n W = standardSimplex (Fin n) W ∩ {v | Antitone v} := by
  ext v
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩, fun ⟨⟨h₁, h₃⟩, h₂⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- The ordered simplex is closed: it is cut out by finitely many non-strict linear
inequalities. -/
theorem isClosed_orderedSimplex (n : ℕ) (W : ℝ) : IsClosed (orderedSimplex n W) := by
  rw [orderedSimplex_eq_inter]
  refine (isClosed_standardSimplex (Fin n) W).inter ?_
  have h : {v : Fin n → ℝ | Antitone v} = ⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {v | v j ≤ v i} := by
    ext v
    simp [Antitone]
  rw [h]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
    isClosed_le (continuous_apply j) (continuous_apply i)

/-- The ordered simplex is measurable, because it is closed. -/
theorem measurableSet_orderedSimplex (n : ℕ) (W : ℝ) : MeasurableSet (orderedSimplex n W) :=
  (isClosed_orderedSimplex n W).measurableSet

/-- The ordered simplex is compact for every real `W`, as a closed subset of the standard
simplex. -/
theorem isCompact_orderedSimplex (n : ℕ) (W : ℝ) : IsCompact (orderedSimplex n W) :=
  (isCompact_standardSimplex (Fin n) W).of_isClosed_subset (isClosed_orderedSimplex n W)
    (by rw [orderedSimplex_eq_inter]; exact inter_subset_left)

/-- Summing the suffix sums `∑ j ≥ i, u j` over `i` weights `u j` by `j + 1`, the number of
indices `i ≤ j`. -/
theorem sum_sum_Ici_eq (u : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ici i, u j = ∑ j : Fin n, ((j : ℝ) + 1) * u j := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j ↦ Finset.Iic j) fun i j ↦ by simp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
  push_cast
  ring

private theorem Ici_eq_cons_Ici_succ {i : Fin n} (hi : i.val + 1 < n) :
    Finset.Ici i = insert i (Finset.Ici ⟨i.val + 1, hi⟩) := by
  ext j
  simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
  omega

/-- The suffix sums `∑ j ≥ i, u j` are nonnegative and decreasing exactly when every coordinate
of `u` is nonnegative. -/
theorem nonneg_antitone_sum_Ici_iff (u : Fin n → ℝ) :
    ((∀ i, 0 ≤ ∑ j ∈ Finset.Ici i, u j) ∧ Antitone fun i ↦ ∑ j ∈ Finset.Ici i, u j) ↔
      ∀ i, 0 ≤ u i := by
  constructor
  · rintro ⟨hnonneg, hanti⟩ i
    by_cases hi : i.val + 1 < n
    · have hle : i ≤ (⟨i.val + 1, hi⟩ : Fin n) := by simp [Fin.le_def]
      have hstep := hanti hle
      have hnot : i ∉ Finset.Ici (⟨i.val + 1, hi⟩ : Fin n) := by simp [Fin.le_def]
      simp only [Ici_eq_cons_Ici_succ hi, sum_insert hnot] at hstep
      linarith
    · have hIci : Finset.Ici i = {i} := by
        ext j
        simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
        omega
      simpa [hIci] using hnonneg i
  · intro hu
    refine ⟨fun i ↦ sum_nonneg fun j _ ↦ hu j, fun i j hij ↦ ?_⟩
    exact sum_le_sum_of_subset_of_nonneg (Finset.Ici_subset_Ici.2 hij) fun k _ _ ↦ hu k

/-- The weighted simplex with weights `1, …, n` is the preimage of the ordered simplex under the
suffix-sum map `u ↦ (∑ j ≥ i, u j)ᵢ`. -/
theorem weightedSimplex_succ_eq_preimage_orderedSimplex (n : ℕ) (W : ℝ) :
    weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W =
      (fun u i ↦ ∑ j ∈ Finset.Ici i, u j) ⁻¹' orderedSimplex n W := by
  ext u
  simp only [mem_weightedSimplex, mem_preimage, mem_orderedSimplex, sum_sum_Ici_eq]
  rw [← nonneg_antitone_sum_Ici_iff]
  tauto

end Set

namespace MeasureTheory

variable {n : ℕ}

/-! ### The suffix-sum change of variables -/

/-- The upper unitriangular matrix of the suffix-sum map. -/
private def suffixSumMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i ≤ j then 1 else 0

private theorem suffixSumMatrix_mulVec (u : Fin n → ℝ) (i : Fin n) :
    (suffixSumMatrix n).mulVec u i = ∑ j ∈ Ici i, u j := by
  classical
  simp only [suffixSumMatrix, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

private theorem det_suffixSumMatrix (n : ℕ) : (suffixSumMatrix n).det = 1 := by
  have hupper : (suffixSumMatrix n).IsUpperTriangular := fun i j (hji : j < i) ↦ by
    simp [suffixSumMatrix, not_le.2 hji]
  rw [Matrix.det_of_isUpperTriangular hupper]
  simp [suffixSumMatrix]

/-- The suffix-sum map as a measurable equivalence. -/
private noncomputable def suffixSumEquiv (n : ℕ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  let e := LinearMap.equivOfDetNeZero (Matrix.toLin' (suffixSumMatrix n))
    (by rw [LinearMap.det_toLin', det_suffixSumMatrix]; exact one_ne_zero)
  { toEquiv := e.toEquiv
    measurable_toFun := (LinearMap.continuous_on_pi e.toLinearMap).measurable
    measurable_invFun := (LinearMap.continuous_on_pi e.symm.toLinearMap).measurable }

private theorem suffixSumEquiv_apply (u : Fin n → ℝ) :
    suffixSumEquiv n u = fun i ↦ ∑ j ∈ Ici i, u j := by
  funext i
  exact suffixSumMatrix_mulVec u i

private theorem measurePreserving_suffixSumEquiv (n : ℕ) :
    MeasurePreserving (suffixSumEquiv n) volume volume := by
  refine ⟨(suffixSumEquiv n).measurable, ?_⟩
  have hdet : (suffixSumMatrix n).det ≠ 0 := by rw [det_suffixSumMatrix]; exact one_ne_zero
  have hfun : ⇑(suffixSumEquiv n) = ⇑(Matrix.toLin' (suffixSumMatrix n)) := by
    funext u
    rw [suffixSumEquiv_apply, Matrix.toLin'_apply]
    funext i
    rw [suffixSumMatrix_mulVec]
  rw [hfun, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, det_suffixSumMatrix]
  simp

/-- The suffix-sum change of variables: for every function `f`,
`∫ u in weightedSimplex (i + 1) W, f (∑ j ≥ i, u j)ᵢ = ∫ v in orderedSimplex n W, f v`, where the
weights are `1, …, n`. The suffix-sum map is upper unitriangular, so there is no Jacobian factor,
and no integrability hypothesis is needed. -/
theorem setIntegral_weightedSimplex_succ_comp_suffixSum (W : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (∫ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, f fun i ↦ ∑ j ∈ Ici i, u j) =
      ∫ v in orderedSimplex n W, f v := by
  have h := (measurePreserving_suffixSumEquiv n).setIntegral_preimage_emb
    (suffixSumEquiv n).measurableEmbedding f (orderedSimplex n W)
  have hpre : suffixSumEquiv n ⁻¹' orderedSimplex n W =
      weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W := by
    rw [weightedSimplex_succ_eq_preimage_orderedSimplex]
    ext u
    simp only [Set.mem_preimage, suffixSumEquiv_apply]
  simpa only [hpre, suffixSumEquiv_apply] using h

/-- The ordered simplex has the volume of the weighted simplex with weights `1, …, n`, namely
`W ^ n / (n!) ^ 2` for `0 ≤ W`. For `W < 0` the set is empty, while the formula is nonzero for
`n = 0`. -/
theorem volume_real_orderedSimplex (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    volume.real (orderedSimplex n W) = W ^ n / (n.factorial : ℝ) ^ 2 := by
  have h := setIntegral_weightedSimplex_succ_comp_suffixSum (n := n) W fun _ ↦ (1 : ℝ)
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] at h
  rw [← h, volume_real_weightedSimplex_succ n hW]

/-! ### Sorting the coordinates -/

/-- Reading coordinates in the order `σ`, `x ↦ x ∘ σ`, as a measurable equivalence. -/
private noncomputable def permuteEquiv (σ : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm

private theorem permuteEquiv_apply (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    permuteEquiv σ x = x ∘ σ := by
  funext i
  change Equiv.piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm x i = x (σ i)
  simpa using Equiv.piCongrLeft_apply_apply (fun _ : Fin n ↦ ℝ) σ.symm x (σ i)

private theorem measurePreserving_permuteEquiv (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteEquiv σ) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm

/-- The chamber of the standard simplex whose coordinates, read in the order `σ`, decrease. -/
private def chamber (W : ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  permuteEquiv σ ⁻¹' orderedSimplex n W

private theorem measurableSet_chamber (W : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (chamber W σ) :=
  (measurableSet_orderedSimplex n W).preimage (permuteEquiv σ).measurable

private theorem mem_chamber {W : ℝ} {σ : Equiv.Perm (Fin n)} {x : Fin n → ℝ} :
    x ∈ chamber W σ ↔ x ∈ standardSimplex (Fin n) W ∧ Antitone (x ∘ σ) := by
  simp only [chamber, Set.mem_preimage, permuteEquiv_apply, mem_orderedSimplex,
    mem_standardSimplex, Function.comp_apply]
  rw [Equiv.sum_comp σ x]
  constructor
  · rintro ⟨hnonneg, hanti, hsum⟩
    exact ⟨⟨fun i ↦ by simpa using hnonneg (σ.symm i), hsum⟩, hanti⟩
  · rintro ⟨⟨hnonneg, hsum⟩, hanti⟩
    exact ⟨fun i ↦ hnonneg (σ i), hanti, hsum⟩

private theorem iUnion_chamber (W : ℝ) :
    ⋃ σ : Equiv.Perm (Fin n), chamber W σ = standardSimplex (Fin n) W := by
  ext x
  simp only [mem_iUnion, mem_chamber]
  refine ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨Tuple.sort fun i ↦ -x i, hx, fun i j hij ↦ ?_⟩⟩
  have h := Tuple.monotone_sort (fun i ↦ -x i) hij
  simp only [Function.comp_apply] at h ⊢
  linarith

/-- The hyperplane `x i = x j` with `i ≠ j` is a Lebesgue null set. -/
private theorem volume_setOf_apply_eq_apply {i j : Fin n} (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  classical
  let s : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i - LinearMap.proj j)
  have hs : (s : Set (Fin n → ℝ)) = {x | x i = x j} := by
    ext x
    simp [s, sub_eq_zero]
  have htop : s ≠ ⊤ := by
    intro h
    have hmem : (Pi.single i 1 : Fin n → ℝ) ∈ s := h ▸ Submodule.mem_top
    simp [s, Ne.symm hij] at hmem
  rw [← hs]
  exact Measure.addHaar_submodule volume s htop

private theorem pairwise_aedisjoint_chamber (W : ℝ) :
    Pairwise fun σ τ : Equiv.Perm (Fin n) ↦ AEDisjoint volume (chamber W σ) (chamber W τ) := by
  intro σ τ hστ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra h
    push Not at h
    exact hστ (Equiv.ext h)
  refine measure_mono_null (fun x hx ↦ ?_) (volume_setOf_apply_eq_apply hi)
  have heq := Tuple.unique_antitone (mem_chamber.1 hx.1).2 (mem_chamber.1 hx.2).2
  exact congrFun heq i

private theorem setIntegral_chamber {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (σ : Equiv.Perm (Fin n)) x, f (x ∘ σ) = f x)
    (W : ℝ) (σ : Equiv.Perm (Fin n)) :
    ∫ x in chamber W σ, f x = ∫ v in orderedSimplex n W, f v := by
  have h := (measurePreserving_permuteEquiv σ).setIntegral_preimage_emb
    (permuteEquiv σ).measurableEmbedding f (orderedSimplex n W)
  simp only [permuteEquiv_apply, hf] at h
  exact h

private theorem integrableOn_chamber_iff {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (σ : Equiv.Perm (Fin n)) x, f (x ∘ σ) = f x)
    (W : ℝ) (σ : Equiv.Perm (Fin n)) :
    IntegrableOn f (chamber W σ) ↔ IntegrableOn f (orderedSimplex n W) := by
  have h := (measurePreserving_permuteEquiv σ).integrableOn_comp_preimage
    (permuteEquiv σ).measurableEmbedding (f := f) (s := orderedSimplex n W)
  have hcomp : f ∘ permuteEquiv σ = f := funext fun x ↦ by
    simp only [Function.comp_apply, permuteEquiv_apply, hf]
  rwa [hcomp] at h

/-- Sorting the coordinates: for a function `f` invariant under permuting coordinates,
`∫ x in standardSimplex (Fin n) W, f x = n! * ∫ v in orderedSimplex n W, f v`. The standard
simplex is the union of the `n!` chambers `{x | x ∘ σ ∈ orderedSimplex n W}`, which overlap only
on null sets, and each contributes the integral over the ordered simplex. No integrability
hypothesis is needed: if `f` is not integrable on the ordered simplex, it is integrable neither
there nor on the standard simplex, and both sides are `0`. -/
theorem setIntegral_standardSimplex_of_comp_perm {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (σ : Equiv.Perm (Fin n)) x, f (x ∘ σ) = f x) (W : ℝ) :
    ∫ x in standardSimplex (Fin n) W, f x = n.factorial * ∫ v in orderedSimplex n W, f v := by
  by_cases hint : IntegrableOn f (orderedSimplex n W)
  · have hunion : IntegrableOn f (⋃ σ : Equiv.Perm (Fin n), chamber W σ) :=
      integrableOn_finite_iUnion.2 fun σ ↦ (integrableOn_chamber_iff hf W σ).2 hint
    rw [← iUnion_chamber W, integral_iUnion_ae
      (fun σ ↦ (measurableSet_chamber W σ).nullMeasurableSet)
      (pairwise_aedisjoint_chamber W) hunion, tsum_fintype]
    simp_rw [setIntegral_chamber hf W]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  · have hstd : ¬IntegrableOn f (standardSimplex (Fin n) W) := fun h ↦ hint <|
      (integrableOn_chamber_iff hf W 1).1 <| h.mono_set <| by
        rw [← iUnion_chamber W]
        exact subset_iUnion (chamber W) 1
    rw [integral_undef hint, integral_undef hstd, mul_zero]

/-- The weighted simplex with weights `1, …, n` and the standard simplex: for a function `f`
invariant under permuting coordinates,
`∫ x in standardSimplex (Fin n) W, f x = n! * ∫ u in weightedSimplex (i + 1) W, f (∑ j ≥ i, u j)ᵢ`.
-/
theorem setIntegral_standardSimplex_eq_weightedSimplex_succ {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ (σ : Equiv.Perm (Fin n)) x, f (x ∘ σ) = f x) (W : ℝ) :
    ∫ x in standardSimplex (Fin n) W, f x =
      n.factorial * ∫ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W,
        f fun i ↦ ∑ j ∈ Ici i, u j := by
  rw [setIntegral_standardSimplex_of_comp_perm hf, setIntegral_weightedSimplex_succ_comp_suffixSum]

/-- The standard simplex has `n!` times the volume of the weighted simplex with weights
`1, …, n`, for every `W`. -/
theorem volume_real_standardSimplex_eq_factorial_mul (n : ℕ) (W : ℝ) :
    volume.real (standardSimplex (Fin n) W) =
      n.factorial * volume.real (weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W) := by
  have h := setIntegral_standardSimplex_eq_weightedSimplex_succ (n := n)
    (f := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ rfl) W
  simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using h

/-! ### The largest coordinate -/

/-- The largest coordinate of a point with decreasing coordinates is its first. -/
theorem sup'_univ_eq_apply_zero_of_antitone [NeZero n] {v : Fin n → ℝ} (hv : Antitone v) :
    univ.sup' univ_nonempty v = v 0 :=
  le_antisymm (Finset.sup'_le _ _ fun i _ ↦ hv (Fin.zero_le i))
    (Finset.le_sup' v (mem_univ 0))

/-- The largest coordinate is invariant under permuting coordinates. -/
theorem sup'_univ_comp_perm [NeZero n] (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    univ.sup' univ_nonempty (x ∘ σ) = univ.sup' univ_nonempty x := by
  refine le_antisymm (Finset.sup'_le _ _ fun i _ ↦ Finset.le_sup' x (mem_univ (σ i)))
    (Finset.sup'_le _ _ fun i _ ↦ ?_)
  have h := Finset.le_sup' (x ∘ σ) (mem_univ (σ.symm i))
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h

/-- The largest coordinate on the standard simplex and the coordinate sum on the weighted simplex
with weights `1, …, n`: for every function `g`,
`∫ x in standardSimplex (Fin n) W, g (maxᵢ x i) =
  n! * ∫ u in weightedSimplex (i + 1) W, g (∑ i, u i)`.
The first suffix sum of `u` is `∑ i, u i`, and it is the largest one when `u` is nonnegative. -/
theorem setIntegral_standardSimplex_comp_sup' [NeZero n] (W : ℝ) (g : ℝ → ℝ) :
    ∫ x in standardSimplex (Fin n) W, g (univ.sup' univ_nonempty x) =
      n.factorial * ∫ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, g (∑ i, u i) := by
  rw [setIntegral_standardSimplex_eq_weightedSimplex_succ
    (f := fun x ↦ g (univ.sup' univ_nonempty x)) (fun σ x ↦ by rw [sup'_univ_comp_perm]) W]
  congr 1
  refine setIntegral_congr_fun (measurableSet_weightedSimplex _ W) fun u hu ↦ ?_
  have hanti := ((nonneg_antitone_sum_Ici_iff u).2 hu.1).2
  rw [sup'_univ_eq_apply_zero_of_antitone hanti]
  congr 1
  exact Finset.sum_congr (by ext j; simp) fun _ _ ↦ rfl

/-- The law of the largest coordinate: for every function `g` and every `W`, the average of
`g (maxᵢ x i)` over the standard simplex equals the average of `g (∑ i, u i)` over the weighted
simplex with weights `1, …, n`. Both the integrals and the volumes differ by the factor `n!`. -/
theorem setAverage_standardSimplex_comp_sup' [NeZero n] (W : ℝ) (g : ℝ → ℝ) :
    ⨍ x in standardSimplex (Fin n) W, g (univ.sup' univ_nonempty x) =
      ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, g (∑ i, u i) := by
  rw [setAverage_eq, setAverage_eq, setIntegral_standardSimplex_comp_sup',
    volume_real_standardSimplex_eq_factorial_mul, smul_eq_mul, smul_eq_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ (by positivity), one_mul]

/-- The coordinate sum on the weighted simplex with weights `1, …, n` has the law of the first
coordinate on the ordered simplex: for every function `g` and every `W`,
`⨍ u in weightedSimplex (i + 1) W, g (∑ i, u i) = ⨍ v in orderedSimplex n W, g (v 0)`. -/
theorem setAverage_weightedSimplex_succ_sum_eq_orderedSimplex [NeZero n] (W : ℝ) (g : ℝ → ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, g (∑ i, u i) =
      ⨍ v in orderedSimplex n W, g (v 0) := by
  have hIci : Finset.Ici (0 : Fin n) = Finset.univ := by ext j; simp
  have hint : (∫ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, g (∑ i, u i)) =
      ∫ v in orderedSimplex n W, g (v 0) := by
    rw [← setIntegral_weightedSimplex_succ_comp_suffixSum W fun v ↦ g (v 0)]
    simp only [hIci]
  have hvol := setIntegral_weightedSimplex_succ_comp_suffixSum (n := n) W fun _ ↦ (1 : ℝ)
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] at hvol
  rw [setAverage_eq, setAverage_eq, hint, hvol]

end MeasureTheory
