/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Translation


/-!
# Point independence of the weighted-support local rank

Translation in the global `X` and `Y₀` variables preserves the weighted support.  The local
constraint at an arbitrary point is therefore the zero-point constraint precomposed with a
linear automorphism of the support, so its actual rank is independent of the point.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d D m W : ℕ} {L : ℝ}

private def supportHigherWeight : JetVariable d → ℕ
  | none => 0
  | some j => j.val - 1

private def supportCoarseWeight (D : ℕ) : JetVariable d → ℕ
  | none => 1
  | some _ => D

private theorem weight_supportHigherWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight supportHigherWeight u = fullHigherJetWeight u := by
  simp [supportHigherWeight, fullHigherJetWeight, Finsupp.weight_eq_sum, Fintype.sum_option]

private theorem weight_supportCoarseWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (supportCoarseWeight D) u = u none + D * totalJetDegree u := by
  simp [supportCoarseWeight, Finsupp.weight_eq_sum, Fintype.sum_option,
    totalJetDegree, Finsupp.degree_eq_sum, Finset.mul_sum, mul_comm]

/-- Point translation preserves both no-band support inequalities. The same theorem applies
at negative coordinates, so preservation also holds for the inverse translation. -/
theorem globalPointTranslation_mem_weightedSupportSpace (hD : 0 < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ weightedSupportSpace R D d W L hD) :
    globalPointTranslation center received Q ∈ weightedSupportSpace R D d W L hD := by
  rw [mem_weightedSupportSpace_iff] at hQ ⊢
  intro e he
  have hhigher := globalPointTranslation_support_weight_le supportHigherWeight
    (by simp [supportHigherWeight]) (by simp [supportHigherWeight]) center received
    (a := W) (fun u hu ↦ by rw [weight_supportHigherWeight]; exact (hQ u hu).1) he
  have hQne : Q ≠ 0 := by
    intro hzero
    simp [hzero] at he
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hceil : 0 < ⌈L⌉₊ := (Nat.zero_le _).trans_lt (Nat.lt_ceil.mpr (hQ u hu).2)
  have hcoarse := globalPointTranslation_support_weight_le (supportCoarseWeight D)
    (by simp [supportCoarseWeight]) (by simp [supportCoarseWeight]) center received
    (a := ⌈L⌉₊ - 1) (fun u hu ↦ by
      rw [weight_supportCoarseWeight]
      have := Nat.lt_ceil.mpr (hQ u hu).2
      omega) he
  rw [weight_supportHigherWeight] at hhigher
  rw [weight_supportCoarseWeight] at hcoarse
  exact ⟨hhigher, Nat.lt_ceil.mp (by omega)⟩

/-- Monomial indices for the finite no-band support. -/
abbrev WeightedSupportIndex (D d W : ℕ) (L : ℝ) (hD : 0 < D) :=
  ↥(weightedSupportExponents D d W L hD)

/-- Point translation restricts to a linear automorphism of the weighted support. -/
def weightedSupportPointTranslation (hD : 0 < D) (center received : R) :
    weightedSupportSpace R D d W L hD ≃ₗ[R]
      weightedSupportSpace R D d W L hD where
  toFun Q := ⟨globalPointTranslation center received Q,
    globalPointTranslation_mem_weightedSupportSpace hD center received Q.2⟩
  invFun Q := ⟨globalPointTranslation (-center) (-received) Q,
    globalPointTranslation_mem_weightedSupportSpace hD (-center) (-received) Q.2⟩
  left_inv Q := by
    apply Subtype.ext
    exact AlgHom.congr_fun (globalPointTranslation_neg_comp center received) Q.1
  right_inv Q := by
    apply Subtype.ext
    simpa only [neg_neg, AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun (globalPointTranslation_neg_comp (-center) (-received)) Q.1
  map_add' Q P := by ext; simp
  map_smul' a Q := by ext; simp

/-- Coordinate form of the actual local constraint restricted to the weighted support. -/
def weightedSupportLocalCoordinateConstraint (hD : 0 < D) (center received : R) :
    weightedSupportSpace R D d W L hD →ₗ[R] (LowContactIndex d m → R) :=
  (localConstraintCoordinatesAt m center received).domRestrict _

/-- The coordinate-map rank is likewise independent of the point. -/
theorem finrank_range_weightedSupportLocalCoordinateConstraint_eq_zero
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
        (L := L) hD center received)) =
      Module.finrank F (LinearMap.range
        (weightedSupportLocalCoordinateConstraint (R := F) (d := d) (m := m) (W := W)
          (L := L) hD 0 0)) := by
  let e := weightedSupportPointTranslation (d := d) (W := W)
    (L := L) hD center received
  have hmap : weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
      (L := L) hD center received =
      (weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
        (L := L) hD 0 0).comp e.toLinearMap := by
    apply LinearMap.ext
    intro Q
    ext row
    unfold weightedSupportLocalCoordinateConstraint localConstraintCoordinatesAt
    simp only [LinearMap.domRestrict_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    change (lowContactCoefficients m)
        (unscaledLocalSubstitution d center received Q.1) row =
      (lowContactCoefficients m)
        (unscaledLocalSubstitution d 0 0
          (globalPointTranslation center received Q.1)) row
    rw [← AlgHom.comp_apply,
      unscaledLocalSubstitution_zero_comp_globalPointTranslation center received]
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ e.range]

/-- Canonical infinite-row matrix of the actual weighted-support local coordinate map. -/
def weightedSupportLocalCoordinateMatrix (hD : 0 < D) (center received : R) :
    Matrix (LowContactIndex d m)
      (WeightedSupportIndex D d W L hD) R :=
  fun row column =>
    localConstraintCoordinatesAt m center received
      (MvPolynomial.monomial column.1 1) row

/-- The monomial basis with its reducible support-space type made explicit. -/
def weightedSupportTypedBasis (hD : 0 < D) :
    Module.Basis (WeightedSupportIndex D d W L hD) R
      (weightedSupportSpace R D d W L hD) :=
  weightedSupportBasis (F := R) (d := d) (W := W)
    (L := L) hD

private theorem weightedSupportTypedBasis_apply (hD : 0 < D)
    (column : WeightedSupportIndex D d W L hD) :
    (weightedSupportTypedBasis (R := R) (d := d) (W := W)
      (L := L) hD column :
        DifferentialPolynomial R d) = MvPolynomial.monomial column.1 1 := by
  unfold weightedSupportTypedBasis weightedSupportBasis
  change AddMonoidAlgebra.ofCoeff
      (↑((Finsupp.supportedEquivFinsupp
        (↑(weightedSupportExponents D d W L hD) :
          Set (JetVariable d →₀ ℕ))).symm (Finsupp.single column (1 : R)))) =
      MvPolynomial.monomial column.1 (1 : R)
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

@[simp] theorem weightedSupportLocalCoordinateMatrix_apply (hD : 0 < D)
    (center received : R) (row : LowContactIndex d m)
    (column : WeightedSupportIndex D d W L hD) :
    weightedSupportLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (L := L) hD center received row column =
      localConstraintCoordinatesAt m center received
        (MvPolynomial.monomial column.1 1) row := by
  rfl

/-- The canonical matrix rank is the actual coordinate-map range dimension. -/
theorem rank_weightedSupportLocalCoordinateMatrix
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (L := L) hD center received).rank =
      Module.finrank F (LinearMap.range
        (weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
          (L := L) hD center received)) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  let b := weightedSupportTypedBasis (R := F) (d := d) (W := W)
    (L := L) hD
  let f := weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
    (L := L) hD center received
  have hrange : Submodule.span F
      (Set.range (weightedSupportLocalCoordinateMatrix (d := d) (m := m) (W := W)
        (L := L) hD center received).col) =
      LinearMap.range f := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨column, rfl⟩
      refine ⟨b column, ?_⟩
      ext row
      simp only [Matrix.col_apply, weightedSupportLocalCoordinateMatrix]
      change f (b column) row = localConstraintCoordinatesAt m center received
          (MvPolynomial.monomial column.1 1) row
      unfold f weightedSupportLocalCoordinateConstraint b
      simp only [LinearMap.domRestrict_apply]
      rw [weightedSupportTypedBasis_apply]
    · rintro _ ⟨Q, rfl⟩
      rw [← b.sum_repr Q]
      simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro column _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨column, ?_⟩
      ext row
      simp only [Matrix.col_apply, weightedSupportLocalCoordinateMatrix]
      change localConstraintCoordinatesAt m center received
          (MvPolynomial.monomial column.1 1) row = f (b column) row
      unfold f weightedSupportLocalCoordinateConstraint b
      simp only [LinearMap.domRestrict_apply]
      rw [weightedSupportTypedBasis_apply]
  rw [hrange]

/-- The canonical local matrix rank is point independent, even with its infinite row type. -/
theorem rank_weightedSupportLocalCoordinateMatrix_eq_zero
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (L := L) hD center received).rank =
      (weightedSupportLocalCoordinateMatrix (d := d) (m := m) (W := W)
        (R := F) (L := L) hD 0 0).rank := by
  calc
    _ = Module.finrank F (LinearMap.range
        (weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
          (L := L) hD center received)) :=
      rank_weightedSupportLocalCoordinateMatrix hD center received
    _ = Module.finrank F (LinearMap.range
        (weightedSupportLocalCoordinateConstraint (R := F) (d := d) (m := m) (W := W)
          (L := L) hD 0 0)) :=
      finrank_range_weightedSupportLocalCoordinateConstraint_eq_zero hD center received
    _ = _ := (rank_weightedSupportLocalCoordinateMatrix hD (0 : F) 0).symm

/-- Coordinate extraction cannot have larger rank than the actual polynomial-valued local map. -/
theorem rank_weightedSupportLocalCoordinateMatrix_le_actual
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (m := m) (W := W)
      (L := L) hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (d := d) (W := W)
          (L := L) m hD center received)) := by
  let _ : Module.Finite F (weightedSupportSpace F D d W L hD) :=
    Module.Finite.of_basis
      (weightedSupportBasis (F := F) (d := d) (W := W)
        (L := L) hD)
  rw [rank_weightedSupportLocalCoordinateMatrix]
  have hcomp : weightedSupportLocalCoordinateConstraint (d := d) (m := m) (W := W)
      (L := L) hD center received =
      (lowContactCoefficients (R := F) (d := d) m).comp
        (weightedSupportLocalConstraint (d := d) (W := W)
          (L := L) m hD center received) := by
    apply LinearMap.ext
    intro Q
    ext row
    simp [weightedSupportLocalCoordinateConstraint, localConstraintCoordinatesAt,
      weightedSupportLocalConstraint, localConstraintAt, lowContactCoefficients,
      projectLowContact, coeff_filterLocalMonomials, row.2]
  rw [hcomp, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

private theorem map_unscaledLocalImage_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : JetVariable d) :
    MvPolynomial.map (algebraMap F E) (unscaledLocalImage d 0 0 v) =
      unscaledLocalImage d 0 0 v := by
  rcases v with _ | j
  · simp [unscaledLocalImage]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp [unscaledLocalImage, localCorrection]
    · simp [unscaledLocalImage]

/-- Zero-point canonical entries commute with extension of the coefficient field. -/
theorem weightedSupportLocalCoordinateMatrix_zero_baseChange
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hD : 0 < D) :
    weightedSupportLocalCoordinateMatrix (R := E) (d := d) (m := m) (W := W)
      (L := L) hD 0 0 =
      (weightedSupportLocalCoordinateMatrix (R := F) (d := d) (m := m) (W := W)
        (L := L) hD 0 0).map (algebraMap F E) := by
  ext row column
  simp only [weightedSupportLocalCoordinateMatrix_apply, Matrix.map_apply]
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp only [unscaledLocalSubstitution, MvPolynomial.bind₁_monomial,
    map_one, map_mul, map_prod, map_pow]
  simp_rw [map_unscaledLocalImage_zero]

/-- The arbitrary-point canonical matrix over an extension field is bounded by the source-field
zero-point matrix rank. -/
theorem rank_weightedSupportLocalCoordinateMatrix_le_base
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hD : 0 < D) (center received : E) :
    (weightedSupportLocalCoordinateMatrix (R := E) (d := d) (m := m) (W := W)
      (L := L) hD center received).rank ≤
      (weightedSupportLocalCoordinateMatrix (R := F) (d := d) (m := m) (W := W)
        (L := L) hD 0 0).rank := by
  rw [rank_weightedSupportLocalCoordinateMatrix_eq_zero hD center received,
    weightedSupportLocalCoordinateMatrix_zero_baseChange (F := F) (E := E) hD]
  exact Matrix.rank_map_algebraMap_le _

/-- Final local-rank seam: every extension-field point block is bounded by the source-field
actual zero-point weighted-support rank. -/
theorem rank_weightedSupportLocalCoordinateMatrix_le_base_actual
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hD : 0 < D) (center received : E) :
    (weightedSupportLocalCoordinateMatrix (R := E) (d := d) (m := m) (W := W)
      (L := L) hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) :=
  (rank_weightedSupportLocalCoordinateMatrix_le_base (F := F) hD center received).trans
    (rank_weightedSupportLocalCoordinateMatrix_le_actual hD (0 : F) 0)

/-- The actual weighted-support local rank is independent of the center and received value. -/
theorem finrank_range_weightedSupportLocalConstraint_eq_zero
    {F : Type*} [Field F] (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := L) m hD center received)) =
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
  let e := weightedSupportPointTranslation (d := d) (W := W)
    (L := L) hD center received
  have hmap : weightedSupportLocalConstraint (d := d) (W := W)
      (L := L) m hD center received =
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := L) m hD 0 0).comp e.toLinearMap := by
    apply LinearMap.ext
    intro Q
    exact localConstraintAt_eq_zero_comp_globalPointTranslation center received Q.1
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ e.range]

end ReedSolomon.HiddenDerivative
