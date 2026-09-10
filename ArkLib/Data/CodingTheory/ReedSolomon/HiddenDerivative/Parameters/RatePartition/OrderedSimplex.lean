/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.Moments
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.IdentDistrib

/-!
# Ordered coordinates for the rate-partition simplex

The paper's weighted simplex uses the weights `1, ..., d`.  The cumulative-coordinate map

`v i = ∑ j ≥ i, u j`

has determinant one.  It sends that weighted simplex to the chamber

`v 0 ≥ v 1 ≥ ... ≥ 0`, `∑ i, v i ≤ W`,

and sends the unweighted radius `∑ i, u i` to the first ordered coordinate.  This is the
source-integral-facing form of the ordered-simplex change of variables; in particular, it does
not use the legacy hidden-derivative convention in which the first higher jet has weight zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The chamber of nonnegative decreasing coordinates with total mass at most `W`. -/
def orderedSimplex (d : ℕ) (W : ℝ) : Set (Fin d → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ Antitone v ∧ ∑ i, v i ≤ W}

/-- The upper-unitriangular matrix taking differences to cumulative coordinates. -/
def cumulativeMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ if i ≤ j then 1 else 0

/-- Cumulative coordinates `v i = ∑ j ≥ i, u j`. -/
noncomputable def cumulativeCoordinates (d : ℕ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLin' (cumulativeMatrix d)

@[simp]
theorem cumulativeCoordinates_apply {d : ℕ} (u : Fin d → ℝ) (i : Fin d) :
    cumulativeCoordinates d u i = ∑ j ∈ Finset.Ici i, u j := by
  classical
  simp only [cumulativeCoordinates, cumulativeMatrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct]
  calc
    (∑ j, (if i ≤ j then 1 else 0) * u j) =
        ∑ j ∈ Finset.univ.filter (i ≤ ·), u j := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp_all
    _ = ∑ j ∈ Finset.Ici i, u j := by
      congr 1
      ext j
      simp

theorem cumulativeMatrix_isUpperTriangular (d : ℕ) :
    (cumulativeMatrix d).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  have hnot : ¬i ≤ j := not_le_of_gt hji
  simp [cumulativeMatrix, hnot]

/-- The cumulative-coordinate determinant is exactly one, not merely nonzero. -/
theorem cumulativeCoordinates_det (d : ℕ) :
    LinearMap.det (cumulativeCoordinates d) = 1 := by
  classical
  rw [cumulativeCoordinates, LinearMap.det_toLin',
    Matrix.det_of_isUpperTriangular (cumulativeMatrix_isUpperTriangular d)]
  simp [cumulativeMatrix]

/-- The linear equivalence supplied by the determinant-one cumulative matrix. -/
noncomputable def cumulativeLinearEquiv (d : ℕ) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  LinearMap.equivOfDetNeZero (cumulativeCoordinates d) (by simp [cumulativeCoordinates_det])

@[simp]
theorem cumulativeLinearEquiv_apply {d : ℕ} (u : Fin d → ℝ) :
    cumulativeLinearEquiv d u = cumulativeCoordinates d u := by
  simp [cumulativeLinearEquiv]

private theorem Ici_eq_insert_Ici_succ {d : ℕ} (i : Fin d) (hi : i.val + 1 < d) :
    Finset.Ici i = insert i (Finset.Ici ⟨i.val + 1, hi⟩) := by
  ext j
  simp only [Finset.mem_Ici, Finset.mem_insert]
  constructor
  · intro hij
    by_cases hji : j = i
    · exact Or.inl hji
    · right
      change i.val + 1 ≤ j.val
      change i.val ≤ j.val at hij
      have hne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
      omega
  · rintro (rfl | hij)
    · exact le_rfl
    · change i.val + 1 ≤ j.val at hij
      change i.val ≤ j.val
      omega

private theorem cumulativeCoordinates_sub_succ {d : ℕ} (u : Fin d → ℝ)
    (i : Fin d) (hi : i.val + 1 < d) :
    cumulativeCoordinates d u i - cumulativeCoordinates d u ⟨i.val + 1, hi⟩ = u i := by
  classical
  rw [cumulativeCoordinates_apply, cumulativeCoordinates_apply,
    Ici_eq_insert_Ici_succ i hi, Finset.sum_insert]
  · ring
  · simp only [Finset.mem_Ici]
    change ¬i.val + 1 ≤ i.val
    omega

private theorem cumulativeCoordinates_last {d : ℕ} (u : Fin (d + 1) → ℝ) :
    cumulativeCoordinates (d + 1) u (Fin.last d) = u (Fin.last d) := by
  rw [cumulativeCoordinates_apply]
  have hIci : Finset.Ici (Fin.last d) = {Fin.last d} := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_singleton]
    exact ⟨fun h ↦ Fin.le_antisymm (Fin.le_last j) h, fun h ↦ h ▸ le_rfl⟩
  rw [hIci]
  simp

/-- Cumulative coordinates are decreasing exactly when their successive differences are
nonnegative.  Together with nonnegativity of the final coordinate this recovers all source
coordinates. -/
theorem cumulativeCoordinates_nonnegative_iff {d : ℕ} (u : Fin d → ℝ) :
    (∀ i, 0 ≤ cumulativeCoordinates d u i) ∧ Antitone (cumulativeCoordinates d u) ↔
      ∀ i, 0 ≤ u i := by
  constructor
  · rintro ⟨hnonneg, hanti⟩ i
    by_cases hi : i.val + 1 < d
    · have hle : i ≤ (⟨i.val + 1, hi⟩ : Fin d) := by
        change i.val ≤ i.val + 1
        omega
      have hstep := hanti hle
      rw [← cumulativeCoordinates_sub_succ u i hi]
      linarith
    · cases d with
      | zero => exact Fin.elim0 i
      | succ d =>
          have hid : i = Fin.last d := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst i
          rw [← cumulativeCoordinates_last u]
          exact hnonneg (Fin.last d)
  · intro hu
    constructor
    · intro i
      rw [cumulativeCoordinates_apply]
      exact Finset.sum_nonneg fun j _ ↦ hu j
    · intro i j hij
      rw [cumulativeCoordinates_apply, cumulativeCoordinates_apply]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk ↦ by simp only [Finset.mem_Ici] at hk ⊢; exact hij.trans hk)
        (fun k _ _ ↦ hu k)

/-- Summing cumulative coordinates applies the weights `1, ..., d` to the source tuple. -/
theorem sum_cumulativeCoordinates {d : ℕ} (u : Fin d → ℝ) :
    (∑ i, cumulativeCoordinates d u i) =
      ∑ j, SimplexIntegration.coordinateWeight j * u j := by
  classical
  simp_rw [cumulativeCoordinates_apply]
  calc
    (∑ i, ∑ j ∈ Finset.Ici i, u j) =
        ∑ i, ∑ j, if i ≤ j then u j else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext j
            simp
          · intro j _
            simp
    _ = ∑ j, ∑ i, if i ≤ j then u j else 0 := Finset.sum_comm
    _ = ∑ j, SimplexIntegration.coordinateWeight j * u j := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ i, if i ≤ j then u j else 0) = ∑ _i ∈ Finset.Iic j, u j := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext i
            simp
          · intro i _
            simp
        _ = SimplexIntegration.coordinateWeight j * u j := by
          simp [Fin.card_Iic, SimplexIntegration.coordinateWeight]

/-- The paper's weighted simplex is exactly the preimage of the ordered chamber. -/
theorem weightedSimplex_eq_cumulative_preimage (d : ℕ) (W : ℝ) :
    SimplexIntegration.weightedSimplex d W =
      cumulativeCoordinates d ⁻¹' orderedSimplex d W := by
  ext u
  simp only [SimplexIntegration.weightedSimplex, orderedSimplex, Set.mem_ofPred_eq,
    Set.mem_preimage]
  rw [← cumulativeCoordinates_nonnegative_iff, sum_cumulativeCoordinates]
  tauto

/-- The determinant-one map identifies the weighted simplex with the ordered chamber. -/
theorem weightedSimplex_eq_cumulativeLinearEquiv_preimage (d : ℕ) (W : ℝ) :
    SimplexIntegration.weightedSimplex d W =
      cumulativeLinearEquiv d ⁻¹' orderedSimplex d W := by
  rw [weightedSimplex_eq_cumulative_preimage]
  ext u
  simp only [Set.mem_preimage, cumulativeLinearEquiv_apply]

theorem orderedSimplex_eq_cumulativeLinearEquiv_image (d : ℕ) (W : ℝ) :
    orderedSimplex d W =
      cumulativeLinearEquiv d '' SimplexIntegration.weightedSimplex d W := by
  rw [weightedSimplex_eq_cumulativeLinearEquiv_preimage]
  ext v
  constructor
  · intro hv
    refine ⟨(cumulativeLinearEquiv d).symm v, ?_,
      (cumulativeLinearEquiv d).apply_symm_apply v⟩
    simpa using hv
  · rintro ⟨u, hu, rfl⟩
    exact hu

/-- Ordered chambers are compact, hence measurable and suitable for normalized integration. -/
theorem isCompact_orderedSimplex (d : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    IsCompact (orderedSimplex d W) := by
  rw [orderedSimplex_eq_cumulativeLinearEquiv_image]
  exact (SimplexIntegration.isCompact_weightedSimplex d hW).image
    (LinearMap.continuous_on_pi (cumulativeCoordinates d))

/-- The cumulative change of variables preserves Lebesgue volume exactly. -/
theorem cumulativeLinearEquiv_map_volume (d : ℕ) :
    Measure.map (cumulativeLinearEquiv d) volume = volume := by
  change Measure.map (cumulativeCoordinates d) volume = volume
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · simp [cumulativeCoordinates_det]
  · simp [cumulativeCoordinates_det]

private noncomputable def cumulativeMeasurableEquiv (d : ℕ) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) where
  toEquiv := cumulativeLinearEquiv d
  measurable_toFun :=
    (LinearMap.continuous_on_pi (cumulativeCoordinates d)).measurable
  measurable_invFun :=
    (LinearMap.continuous_on_pi (cumulativeLinearEquiv d).symm.toLinearMap).measurable

/-- Permute tuple coordinates.  Lebesgue product measure is invariant under this map. -/
noncomputable def permuteCoordinates {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin d ↦ ℝ) σ.symm

@[simp]
theorem permuteCoordinates_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Fin d → ℝ)
    (i : Fin d) :
    permuteCoordinates σ x i = x (σ i) := by
  change Equiv.piCongrLeft (fun _ : Fin d ↦ ℝ) σ.symm x i = x (σ i)
  simpa using
    (Equiv.piCongrLeft_apply_apply (fun _ : Fin d ↦ ℝ) σ.symm x (σ i))

theorem permuteCoordinates_map_volume {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Measure.map (permuteCoordinates σ) volume = volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin d ↦ ℝ) σ.symm).map_eq

/-- A permutation chamber consists of standard-simplex points whose coordinates, read in the
order `σ`, are decreasing. -/
def permutationChamber {d : ℕ} (W : ℝ) (σ : Equiv.Perm (Fin d)) : Set (Fin d → ℝ) :=
  {x | x ∈ SimplexIntegration.standardSimplex d W ∧ Antitone (x ∘ σ)}

theorem permutationChamber_eq_preimage_ordered {d : ℕ} (W : ℝ)
    (σ : Equiv.Perm (Fin d)) :
    permutationChamber W σ = permuteCoordinates σ ⁻¹' orderedSimplex d W := by
  ext x
  simp only [permutationChamber, SimplexIntegration.standardSimplex, orderedSimplex,
    Set.mem_ofPred_eq, Set.mem_preimage, permuteCoordinates_apply]
  constructor
  · rintro ⟨⟨hnonneg, hsum⟩, hanti⟩
    refine ⟨fun i ↦ hnonneg (σ i), ?_, ?_⟩
    · intro i j hij
      have h := hanti hij
      change x (σ j) ≤ x (σ i) at h
      rw [permuteCoordinates_apply, permuteCoordinates_apply]
      exact h
    calc
      (∑ i, x (σ i)) = ∑ i, x i := σ.bijective.sum_comp x
      _ ≤ W := hsum
  · rintro ⟨hnonneg, hanti, hsum⟩
    refine ⟨⟨fun i ↦ ?_, ?_⟩, ?_⟩
    · simpa using hnonneg (σ.symm i)
    · calc
        (∑ i, x i) = ∑ i, x (σ i) := (σ.bijective.sum_comp x).symm
        _ ≤ W := hsum
    · intro i j hij
      change x (σ j) ≤ x (σ i)
      have h := hanti hij
      simpa only [permuteCoordinates_apply] using h

theorem isCompact_permutationChamber {d : ℕ} {W : ℝ} (hW : 0 ≤ W)
    (σ : Equiv.Perm (Fin d)) : IsCompact (permutationChamber W σ) := by
  apply (SimplexIntegration.isCompact_standardSimplex d hW).of_isClosed_subset
  · rw [permutationChamber_eq_preimage_ordered]
    have he : (permuteCoordinates σ : (Fin d → ℝ) → (Fin d → ℝ)) =
        fun x ↦ x ∘ σ := by
      funext x i
      exact permuteCoordinates_apply σ x i
    rw [he]
    exact (isCompact_orderedSimplex d hW).isClosed.preimage (by fun_prop)
  · intro x hx
    exact hx.1

private theorem volume_coordinate_eq_coordinate {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    volume {x : Fin d → ℝ | x i = x j} = 0 := by
  classical
  let shear : Matrix.TransvectionStruct (Fin d) ℝ := ⟨i, j, hij, -1⟩
  let linear : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Matrix.toLin' shear.toMatrix
  have hpres : MeasurePreserving linear := Real.volume_preserving_transvectionStruct shear
  let hyperplane : Set (Fin d → ℝ) := {x | x i = 0}
  have hhyper : volume hyperplane = 0 := by
    exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin d ↦ volume) i 0
  have hpre : linear ⁻¹' hyperplane = {x : Fin d → ℝ | x i = x j} := by
    ext x
    change Matrix.mulVec (Matrix.transvection i j (-1)) x i = 0 ↔ x i = x j
    have happly : Matrix.mulVec (Matrix.transvection i j (-1)) x i = x i - x j := by
      simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
      ring
    rw [happly, sub_eq_zero]
  rw [← hpre]
  calc
    volume (linear ⁻¹' hyperplane) = Measure.map linear volume hyperplane := by
      exact (Measure.map_apply hpres.measurable
        (measurableSet_singleton 0 |>.preimage (measurable_pi_apply i))).symm
    _ = volume hyperplane := by rw [hpres.map_eq]
    _ = 0 := hhyper

theorem iUnion_permutationChamber {d : ℕ} (W : ℝ) :
    (⋃ σ : Equiv.Perm (Fin d), permutationChamber W σ) =
      SimplexIntegration.standardSimplex d W := by
  ext x
  constructor
  · simp only [Set.mem_iUnion, permutationChamber, Set.mem_ofPred_eq]
    rintro ⟨σ, hx, _⟩
    exact hx
  · intro hx
    let σ := Tuple.sort (fun i ↦ -x i)
    refine Set.mem_iUnion.2 ⟨σ, hx, ?_⟩
    have hmono := Tuple.monotone_sort (fun i ↦ -x i)
    intro i j hij
    have h := hmono hij
    change -x (σ i) ≤ -x (σ j) at h
    change x (σ j) ≤ x (σ i)
    exact neg_le_neg_iff.mp h

theorem permutationChamber_pairwise_ae_disjoint {d : ℕ} (W : ℝ) :
    Pairwise (fun σ τ : Equiv.Perm (Fin d) ↦
      AEDisjoint volume (permutationChamber W σ) (permutationChamber W τ)) := by
  intro σ τ hστ
  have hpoint : ∃ i, σ i ≠ τ i := by
    by_contra h
    push Not at h
    apply hστ
    apply Equiv.ext
    exact h
  obtain ⟨i, hi⟩ := hpoint
  rw [AEDisjoint]
  apply measure_mono_null (t := {x : Fin d → ℝ | x (σ i) = x (τ i)})
  · rintro x ⟨hxσ, hxτ⟩
    have heq := Tuple.unique_antitone hxσ.2 hxτ.2
    exact congrFun heq i
  · exact volume_coordinate_eq_coordinate hi

/-- Set integrals transport from the weighted simplex to the ordered chamber with no Jacobian
factor. -/
theorem integral_weightedSimplex_comp_cumulative (d : ℕ) (W : ℝ)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ u in SimplexIntegration.weightedSimplex d W,
        f (cumulativeCoordinates d u)) =
      ∫ v in orderedSimplex d W, f v := by
  let e := cumulativeMeasurableEquiv d
  have hmap : Measure.map e volume = volume := cumulativeLinearEquiv_map_volume d
  have hchange := setIntegral_map_equiv (μ := volume) e f (orderedSimplex d W)
  rw [hmap] at hchange
  have hpre : e ⁻¹' orderedSimplex d W = SimplexIntegration.weightedSimplex d W := by
    change cumulativeLinearEquiv d ⁻¹' orderedSimplex d W = _
    exact (weightedSimplex_eq_cumulativeLinearEquiv_preimage d W).symm
  rw [hpre] at hchange
  change (∫ u in SimplexIntegration.weightedSimplex d W,
      f (cumulativeCoordinates d u)) = ∫ v in orderedSimplex d W, f v
  change (∫ u in SimplexIntegration.weightedSimplex d W, f (e u)) = _
  exact hchange.symm

/-- The unweighted weighted-simplex radius becomes the first ordered coordinate. -/
theorem cumulativeCoordinates_zero_eq_weightedRadius {d : ℕ} [NeZero d] (u : Fin d → ℝ) :
    cumulativeCoordinates d u 0 = SimplexIntegration.weightedRadius u := by
  rw [cumulativeCoordinates_apply]
  have hIci : Finset.Ici (0 : Fin d) = Finset.univ := by
    ext j
    simp
  rw [hIci]
  rfl

/-- A normalized integral form of the source-facing ordered-coordinate law. -/
theorem weightedSimplexExpectation_eq_orderedHead {d : ℕ} {W : ℝ} (_hW : 0 < W)
    (f : ℝ → ℝ) :
    SimplexIntegration.weightedSimplexExpectation (d + 1) W
        (fun u ↦ f (SimplexIntegration.weightedRadius u)) =
      ⨍ v in orderedSimplex (d + 1) W, f (v 0) := by
  let _ : NeZero (d + 1) := ⟨by omega⟩
  rw [SimplexIntegration.weightedSimplexExpectation, MeasureTheory.setAverage_eq,
    MeasureTheory.setAverage_eq]
  have hvol : volume.real (SimplexIntegration.weightedSimplex (d + 1) W) =
      volume.real (orderedSimplex (d + 1) W) := by
    have h := integral_weightedSimplex_comp_cumulative (d + 1) W (fun _ ↦ (1 : ℝ))
    simpa using h
  rw [← hvol]
  congr 1
  simpa only [cumulativeCoordinates_zero_eq_weightedRadius] using
    integral_weightedSimplex_comp_cumulative (d + 1) W (fun v ↦ f (v 0))

end ReedSolomon.HiddenDerivative.RatePartition
