/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Translation
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank

/-!
# Point independence of the weighted-support local rank

The translation `globalPointTranslation center received` (`X ↦ center + X`,
`Y₀ ↦ received + Y₀`) preserves `weightedSupportSpace R D d W L hD`. Its support conditions
weight bounds with nonnegative weights on `X` and `Y₀`. The local constraint map at
`(center, received)` is the constraint map at `(0, 0)` after this translation.
Composing with a linear automorphism does not change the range, so over a field the rank of the
local constraint map on the weighted support space does not depend on the point.

The same holds for the coordinate form of the constraint map, which records the coefficients of
contact order below `m`, and for its matrix `weightedSupportLocalCoordinateMatrix` in the monomial
basis. That matrix has one column per eligible exponent and one row per exponent of contact order
below `m`; for `0 < m` the row type is infinite, since a visible jet (for `0 < d`) or `E` (for
`d = 0`) has contact weight zero. Applying a ring homomorphism `f` to the entries
of the matrix at `(center, received)` gives the matrix at `(f center, f received)`. For a field
extension `E` of `F` and the point `(0, 0)`, the matrix over `E` is therefore the image of the
matrix over `F`, and its rank is at most the rank over `F`. Hence the rank at an arbitrary point
over `E` is at most the rank at `(0, 0)` over `F`, and at most the rank of the polynomial-valued
constraint map at `(0, 0)` over `F`.

## Main statements

* `globalPointTranslation_mem_weightedSupportSpace` and `weightedSupportPointTranslation`:
  translation preserves the weighted support and restricts to a linear automorphism of it.
* `finrank_range_weightedSupportLocalConstraint_eq_zero` and
  `finrank_range_weightedSupportLocalCoordinateConstraint_eq_zero`: the ranks at any point equal
  the ranks at `(0, 0)`.
* `rank_weightedSupportLocalCoordinateMatrix`: the matrix rank is the rank of the coordinate map.
* `weightedSupportLocalCoordinateMatrix_map`: applying a ring homomorphism `f` to the entries of
  the matrix at `(center, received)` gives the matrix at `(f center, f received)`.
* `rank_weightedSupportLocalCoordinateMatrix_le_base` and
  `rank_weightedSupportLocalCoordinateMatrix_le_base_actual`: the extension-field bounds.

## References

* [BCPZZ26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d D W : ℕ} {L : ℝ}

/-! ### Translation preserves the weighted support -/

/-- The coarse weight: `X` has weight `1` and every jet variable has weight `D`. -/
private def coarseWeight (D : ℕ) : JetVariable d → ℕ
  | none => 1
  | some _ => D

private theorem weight_coarseWeight (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (coarseWeight D) u = u none + D * totalJetDegree u := by
  simp [coarseWeight, Finsupp.weight_eq_sum, Fintype.sum_option, totalJetDegree_eq_sum,
    Finset.mul_sum, mul_comm]

/-- Translation of `X` and `Y₀` preserves the weighted support space. Both support conditions
are weight bounds whose weights are nonnegative on `X` and `Y₀`: the higher-jet weight is at most
`W`, and the coarse weight `u X + D * totalJetDegree u` is below `L`, that is at most
`⌈L⌉₊ - 1`. The statement holds for every point, so it also covers the inverse translation by
`(-center, -received)`. -/
theorem globalPointTranslation_mem_weightedSupportSpace (hD : 0 < D) (center received : R)
    {Q : DifferentialPolynomial R d} (hQ : Q ∈ weightedSupportSpace R D d W L hD) :
    globalPointTranslation center received Q ∈ weightedSupportSpace R D d W L hD := by
  rw [mem_weightedSupportSpace_iff] at hQ ⊢
  intro e he
  have hhigher := globalPointTranslation_mem_restrictWeightAtMost (w := jetHigherWeight)
    (Nat.zero_le _) (Nat.zero_le _) center received (a := W)
    (mem_restrictWeightAtMost.mpr fun u hu => (hQ u hu).1)
  have hcoarse := globalPointTranslation_mem_restrictWeightAtMost (w := coarseWeight D)
    (Nat.zero_le _) (Nat.zero_le _) center received (a := ⌈L⌉₊ - 1)
    (mem_restrictWeightAtMost.mpr fun u hu => by
      rw [weight_coarseWeight]
      have := Nat.lt_ceil.mpr (hQ u hu).2
      omega)
  have hQne : Q ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hceil : 0 < ⌈L⌉₊ := (Nat.zero_le _).trans_lt (Nat.lt_ceil.mpr (hQ u hu).2)
  have he' := mem_restrictWeightAtMost.mp hcoarse e he
  rw [weight_coarseWeight] at he'
  exact ⟨mem_restrictWeightAtMost.mp hhigher e he, Nat.lt_ceil.mp (by omega)⟩

/-- Translation by `(center, received)` as a linear automorphism of the weighted support space.
Its inverse is translation by `(-center, -received)`. -/
def weightedSupportPointTranslation (hD : 0 < D) (center received : R) :
    weightedSupportSpace R D d W L hD ≃ₗ[R] weightedSupportSpace R D d W L hD where
  toFun Q := ⟨globalPointTranslation center received Q,
    globalPointTranslation_mem_weightedSupportSpace hD center received Q.2⟩
  invFun Q := ⟨globalPointTranslation (-center) (-received) Q,
    globalPointTranslation_mem_weightedSupportSpace hD (-center) (-received) Q.2⟩
  left_inv Q := Subtype.ext <|
    AlgHom.congr_fun (globalPointTranslation_neg_comp center received) Q.1
  right_inv Q := Subtype.ext <| by
    simpa only [neg_neg, AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun (globalPointTranslation_neg_comp (-center) (-received)) Q.1
  map_add' Q P := by ext; simp
  map_smul' a Q := by ext; simp

/-- The underlying polynomial of the translate of `Q` is `globalPointTranslation center received`
applied to `Q`. -/
@[simp]
theorem coe_weightedSupportPointTranslation_apply (hD : 0 < D) (center received : R)
    (Q : weightedSupportSpace R D d W L hD) :
    (weightedSupportPointTranslation hD center received Q : DifferentialPolynomial R d) =
      globalPointTranslation center received Q.1 :=
  rfl

/-! ### Point independence of the ranks -/

/-- The local constraint map of order `m` at `(center, received)` on the weighted support space
has the same rank over a field as the map at `(0, 0)`: it is the map at `(0, 0)` composed with the
automorphism `weightedSupportPointTranslation`. -/
theorem finrank_range_weightedSupportLocalConstraint_eq_zero {F : Type*} [Field F] (m : ℕ)
    (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L) m hD center received)) =
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) := by
  have hmap : weightedSupportLocalConstraint (d := d) (W := W) (L := L) m hD center received =
      (weightedSupportLocalConstraint m hD 0 0).comp
        (weightedSupportPointTranslation hD center received).toLinearMap :=
    LinearMap.ext fun Q => localConstraintAt_eq_zero_globalPointTranslation center received Q.1
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The coordinate form of `weightedSupportLocalConstraint`: the vector of coefficients of
contact order below `m` of the unscaled local substitution at `(center, received)`. -/
def weightedSupportLocalCoordinateConstraint (m : ℕ) (hD : 0 < D) (center received : R) :
    weightedSupportSpace R D d W L hD →ₗ[R] (LowContactIndex d m → R) :=
  (localConstraintCoordinatesAt m center received).domRestrict _

/-- The coordinate constraint map at `(center, received)` has the same rank over a field as the
map at `(0, 0)`, by the same translation argument as
`finrank_range_weightedSupportLocalConstraint_eq_zero`. -/
theorem finrank_range_weightedSupportLocalCoordinateConstraint_eq_zero {F : Type*} [Field F]
    (m : ℕ) (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalCoordinateConstraint (d := d) (W := W) (L := L) m hD center
        received)) =
      Module.finrank F (LinearMap.range
        (weightedSupportLocalCoordinateConstraint (R := F) (d := d) (W := W) (L := L) m hD 0
          0)) := by
  have hmap : weightedSupportLocalCoordinateConstraint (d := d) (W := W) (L := L) m hD center
      received = (weightedSupportLocalCoordinateConstraint m hD 0 0).comp
        (weightedSupportPointTranslation hD center received).toLinearMap := by
    refine LinearMap.ext fun Q => ?_
    simp only [weightedSupportLocalCoordinateConstraint, localConstraintCoordinatesAt,
      LinearMap.comp_apply, LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe, coe_weightedSupportPointTranslation_apply]
    rw [← AlgHom.comp_apply, unscaledLocalSubstitution_comp_globalPointTranslation, add_zero,
      add_zero]
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-! ### The coordinate matrix -/

/-- The matrix of `weightedSupportLocalCoordinateConstraint` in the monomial basis: its column
at an eligible exponent `u` is the low-contact coefficient vector of the local substitution of
`monomial u 1` (`weightedSupportLocalCoordinateMatrix_apply`). The row type `LowContactIndex d m`
is infinite for `0 < m`, because some local variable has contact weight zero: a visible jet for
`0 < d`, and `E` for `d = 0`. -/
def weightedSupportLocalCoordinateMatrix (m : ℕ) (hD : 0 < D) (center received : R) :
    Matrix (LowContactIndex d m) ↥(weightedSupportExponents D d W L hD) R :=
  Matrix.of fun row column =>
    weightedSupportLocalCoordinateConstraint m hD center received
      (weightedSupportSpaceBasis R D d W L hD column) row

/-- A matrix entry is the corresponding local-constraint coordinate of the basis monomial: the
entry at `(row, column)` is coordinate `row` of `localConstraintCoordinatesAt` applied to
`monomial column 1`. -/
@[simp]
theorem weightedSupportLocalCoordinateMatrix_apply (m : ℕ) (hD : 0 < D) (center received : R)
    (row : LowContactIndex d m) (column : ↥(weightedSupportExponents D d W L hD)) :
    weightedSupportLocalCoordinateMatrix m hD center received row column =
      localConstraintCoordinatesAt m center received (monomial column.1 1) row := by
  simp only [weightedSupportLocalCoordinateMatrix, weightedSupportLocalCoordinateConstraint,
    weightedSupportSpaceBasis, Matrix.of_apply, LinearMap.domRestrict_apply]
  exact congrArg (fun p => localConstraintCoordinatesAt m center received p row)
    (coe_basisRestrictSupport_apply _ column)

/-- The rank of the coordinate matrix is the rank of the coordinate constraint map. This is
`Matrix.rank_of_basis`; the infinite row type causes no difficulty. -/
theorem rank_weightedSupportLocalCoordinateMatrix {F : Type*} [Field F] (m : ℕ) (hD : 0 < D)
    (center received : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center received).rank =
      Module.finrank F (LinearMap.range
        (weightedSupportLocalCoordinateConstraint (d := d) (W := W) (L := L) m hD center
          received)) :=
  Matrix.rank_of_basis _ _

/-- The rank of the coordinate matrix does not depend on the point. -/
theorem rank_weightedSupportLocalCoordinateMatrix_eq_zero {F : Type*} [Field F] (m : ℕ)
    (hD : 0 < D) (center received : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center received).rank =
      (weightedSupportLocalCoordinateMatrix (R := F) (d := d) (W := W) (L := L) m hD 0 0).rank :=
  by rw [rank_weightedSupportLocalCoordinateMatrix, rank_weightedSupportLocalCoordinateMatrix,
    finrank_range_weightedSupportLocalCoordinateConstraint_eq_zero]

/-- The coordinate constraint map is the polynomial-valued map followed by the extraction of the
low-contact coefficients, so its rank is at most the rank of `weightedSupportLocalConstraint`. -/
theorem rank_weightedSupportLocalCoordinateMatrix_le_actual {F : Type*} [Field F] (m : ℕ)
    (hD : 0 < D) (center received : F) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (d := d) (W := W) (L := L) m hD center received)) := by
  have : Module.Finite F (weightedSupportSpace F D d W L hD) :=
    Module.Finite.of_basis (weightedSupportSpaceBasis F D d W L hD)
  have hcomp : weightedSupportLocalCoordinateConstraint (d := d) (W := W) (L := L) m hD center
      received = (lowContactCoefficients m).comp
        (weightedSupportLocalConstraint m hD center received) := by
    refine LinearMap.ext fun Q => funext fun row => ?_
    simp [weightedSupportLocalCoordinateConstraint, localConstraintCoordinatesAt,
      weightedSupportLocalConstraint, localConstraintAt, lowContactCoefficients, row.2]
  rw [rank_weightedSupportLocalCoordinateMatrix, hcomp, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

/-! ### Coefficient maps -/

/-- Applying a ring homomorphism `f` to every entry of the coordinate matrix at
`(center, received)` gives the coordinate matrix at `(f center, f received)`. The monomial basis
vectors have coefficient `1`, which `f` preserves. -/
theorem weightedSupportLocalCoordinateMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (m : ℕ)
    (hD : 0 < D) (center received : R) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center
      received).map f =
      weightedSupportLocalCoordinateMatrix m hD (f center) (f received) := by
  ext row column
  simp only [Matrix.map_apply, weightedSupportLocalCoordinateMatrix_apply,
    localConstraintCoordinatesAt, lowContactCoefficients, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.pi_apply, lcoeff_apply]
  rw [← coeff_map, map_unscaledLocalSubstitution, map_monomial, map_one]

/-- At the point `(0, 0)` the coordinate matrix over an `F`-algebra `E` is the image of the
coordinate matrix over `F`. -/
theorem weightedSupportLocalCoordinateMatrix_zero_baseChange {F E : Type*} [CommRing F]
    [CommRing E] [Algebra F E] (m : ℕ) (hD : 0 < D) :
    weightedSupportLocalCoordinateMatrix (R := E) (d := d) (W := W) (L := L) m hD 0 0 =
      (weightedSupportLocalCoordinateMatrix (R := F) m hD 0 0).map (algebraMap F E) := by
  rw [weightedSupportLocalCoordinateMatrix_map, map_zero]

/-- For a field extension `E` of `F`, the coordinate matrix at any point over `E` has rank at
most the coordinate matrix at `(0, 0)` over `F`. The point is moved to `(0, 0)` by
`rank_weightedSupportLocalCoordinateMatrix_eq_zero`, and the matrix at `(0, 0)` over `E` is the
image of the one over `F`. -/
theorem rank_weightedSupportLocalCoordinateMatrix_le_base {F E : Type*} [Field F] [Field E]
    [Algebra F E] (m : ℕ) (hD : 0 < D) (center received : E) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center received).rank ≤
      (weightedSupportLocalCoordinateMatrix (R := F) (d := d) (W := W) (L := L) m hD 0 0).rank := by
  rw [rank_weightedSupportLocalCoordinateMatrix_eq_zero,
    weightedSupportLocalCoordinateMatrix_zero_baseChange (F := F)]
  exact Matrix.rank_map_le _ _

/-- For a field extension `E` of `F`, the coordinate matrix at any point over `E` has rank at
most the rank over `F` of the polynomial-valued local constraint map at `(0, 0)` on the weighted
support space. -/
theorem rank_weightedSupportLocalCoordinateMatrix_le_base_actual {F E : Type*} [Field F]
    [Field E] [Algebra F E] (m : ℕ) (hD : 0 < D) (center received : E) :
    (weightedSupportLocalCoordinateMatrix (d := d) (W := W) (L := L) m hD center received).rank ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) :=
  (rank_weightedSupportLocalCoordinateMatrix_le_base (F := F) m hD center received).trans
    (rank_weightedSupportLocalCoordinateMatrix_le_actual m hD 0 0)

end ReedSolomon.HiddenDerivative
