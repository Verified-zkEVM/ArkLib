/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ChallengeDegree
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.SupportedRows

/-!
# The local constraint matrix of a family of source columns

Given received points `(centers i, received i)` indexed by `ι` and source columns indexed by `κ`,
`localConstraintMatrix m centers received columns` has one row for each point `i` and each local
exponent of contact order below `m`, and one column for each source column. Its entry is the
coefficient of that local exponent in the unscaled substitution of the column's monomial at the
point. A coefficient vector `v` is in its kernel exactly when the interpolant
`SourceColumn.interpolant columns v` satisfies the local constraints at every point.

The row type is infinite for `m > 0`, but only finitely many rows are nonzero.
`localConstraintSupportedRows` is the finite set of these rows, and
`supportedLocalConstraintMatrix` is the restriction to them. The restriction has the same kernel,
and after any ring homomorphism into a field the same rank.

Over a polynomial ring `F[X]` in a symbolic challenge, with constant centers and received values
of challenge degree at most `ℓ`, the column of a source column with `Y₀` exponent `y₀` has
challenge degree at most `ℓ * y₀`. A row whose local exponent has jet degree `t` has challenge
degree at most `ℓ * (y₀ + ∑_j higher j - t)` in that column, and is zero there when `t` exceeds
the column's total jet degree.

## Main statements

* `localConstraintMatrix_mulVec_eq_zero_iff`: the kernel is the set of coefficient vectors whose
  interpolant satisfies all the local constraints.
* `mem_localConstraintSupportedRows_iff`: the supported rows are the rows with a nonzero entry.
* `supportedLocalConstraintMatrix_mulVec_eq_zero_iff` and
  `rank_map_supportedLocalConstraintMatrix`: the restriction to the supported rows keeps the
  kernel and the rank.
* `natDegree_localConstraintMatrix_le`, `natDegree_localConstraintMatrix_le_sub` and
  `localConstraintMatrix_eq_zero_of_lt`: the entry bounds over a polynomial ring.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

open PolynomialDifferential
open scoped Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ} {ι κ : Type*}

/-! ### The matrix and its kernel -/

/-- The local constraint matrix: the entry in row `(i, e)` and column `j` is the coefficient of
the low-contact exponent `e` in the unscaled substitution of `(columns j).polynomial` at
`(centers i, received i)`. -/
def localConstraintMatrix (m : ℕ) (centers received : ι → R) (columns : κ → SourceColumn d) :
    Matrix (ι × LowContactIndex d m) κ R := fun row j =>
  localConstraintCoordinatesAt m (centers row.1) (received row.1) (columns j).polynomial row.2

/-- An entry of the local constraint matrix is a coefficient of a substituted column. -/
@[simp]
theorem localConstraintMatrix_apply (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ) :
    localConstraintMatrix m centers received columns row j =
      (unscaledLocalSubstitution d (centers row.1) (received row.1)
        (columns j).polynomial).coeff row.2.1 :=
  rfl

variable [Fintype κ]

/-- Row `(i, e)` of `M *ᵥ v` is the coordinate at `e` of the local constraints of the interpolant
at point `i`. -/
theorem localConstraintMatrix_mulVec_apply (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (v : κ → R) (row : ι × LowContactIndex d m) :
    (localConstraintMatrix m centers received columns *ᵥ v) row =
      localConstraintCoordinatesAt m (centers row.1) (received row.1)
        (SourceColumn.interpolant columns v) row.2 := by
  simp only [Matrix.mulVec, dotProduct, SourceColumn.interpolant_eq_sum_smul, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A coefficient vector is in the kernel of the local constraint matrix exactly when its
interpolant satisfies the local constraints at every point. -/
theorem localConstraintMatrix_mulVec_eq_zero_iff (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (v : κ → R) :
    localConstraintMatrix m centers received columns *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i)
        (SourceColumn.interpolant columns v) := by
  simp only [satisfiesLocalConstraints_iff_coordinates_eq_zero, funext_iff, Pi.zero_apply,
    localConstraintMatrix_mulVec_apply, Prod.forall]

/-! ### Supported rows -/

variable [Fintype ι]

/-- The rows `(i, e)` of the local constraint matrix with a nonzero entry: `e` lies in the support
of the substitution of some column at point `i`. -/
def localConstraintSupportedRows (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) : Finset (ι × LowContactIndex d m) := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.biUnion fun j =>
    ((unscaledLocalSubstitution d (centers i) (received i) (columns j).polynomial).support.subtype
      fun e => localContactOrder d e < m).image (Prod.mk i)

/-- A row is supported exactly when it has a nonzero entry. -/
theorem mem_localConstraintSupportedRows_iff (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) :
    row ∈ localConstraintSupportedRows m centers received columns ↔
      ∃ j, localConstraintMatrix m centers received columns row j ≠ 0 := by
  classical
  obtain ⟨i, e⟩ := row
  simp only [localConstraintSupportedRows, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_subtype, mem_support_iff, Prod.mk.injEq,
    localConstraintMatrix_apply]
  constructor
  · rintro ⟨i', j, e', he', rfl, rfl⟩
    exact ⟨j, he'⟩
  · rintro ⟨j, hj⟩
    exact ⟨i, j, e, hj, rfl, rfl⟩

/-- The local constraint matrix restricted to its supported rows. -/
def supportedLocalConstraintMatrix (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) :
    Matrix (localConstraintSupportedRows m centers received columns) κ R :=
  (localConstraintMatrix m centers received columns).submatrix Subtype.val id

/-- Every row with a nonzero entry is a supported row. -/
theorem localConstraintMatrix_ne_zero_mem_range (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ)
    (h : localConstraintMatrix m centers received columns row j ≠ 0) :
    row ∈ Set.range
      (Subtype.val : localConstraintSupportedRows m centers received columns → _) :=
  ⟨⟨row, (mem_localConstraintSupportedRows_iff m centers received columns row).mpr ⟨j, h⟩⟩, rfl⟩

/-- Restricting to the supported rows does not change the kernel. -/
theorem supportedLocalConstraintMatrix_mulVec_eq_zero_iff (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (v : κ → R) :
    supportedLocalConstraintMatrix m centers received columns *ᵥ v = 0 ↔
      localConstraintMatrix m centers received columns *ᵥ v = 0 :=
  Matrix.submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range _ _
    (localConstraintMatrix_ne_zero_mem_range m centers received columns) v

/-- After a ring homomorphism into a field, restricting to the supported rows does not change the
rank. -/
theorem rank_map_supportedLocalConstraintMatrix {K : Type*} [Field K] (φ : R →+* K) (m : ℕ)
    (centers received : ι → R) (columns : κ → SourceColumn d) :
    ((supportedLocalConstraintMatrix m centers received columns).map φ).rank =
      ((localConstraintMatrix m centers received columns).map φ).rank := by
  rw [supportedLocalConstraintMatrix, ← Matrix.submatrix_map]
  refine Matrix.rank_submatrix_eq_of_ne_zero_mem_range _ _ fun row j h => ?_
  refine localConstraintMatrix_ne_zero_mem_range m centers received columns row j fun h' => ?_
  rw [Matrix.map_apply, h', map_zero] at h
  exact h rfl

end ReedSolomon.HiddenDerivative

/-! ### Entry bounds over a polynomial ring -/

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ} {ι κ : Type*}

/-- With constant centers and received values of challenge degree at most `ℓ`, the column of a
source column with `Y₀` exponent `y₀` has challenge degree at most `ℓ * y₀`. -/
theorem natDegree_localConstraintMatrix_le (m ℓ : ℕ) (centers : ι → R) (received : ι → R[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ) (columns : κ → SourceColumn d)
    (row : ι × LowContactIndex d m) (j : κ) :
    (localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns row j).natDegree ≤
      ℓ * (columns j).y₀ :=
  SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le ℓ _ (hreceived row.1) _ _

/-- With constant centers and received values of challenge degree at most `ℓ`, the entry in a
row whose local exponent has jet degree `t` and a column of total jet degree `y₀ + ∑_j higher j`
has challenge degree at most `ℓ * (y₀ + ∑_j higher j - t)`. -/
theorem natDegree_localConstraintMatrix_le_sub (m ℓ : ℕ) (centers : ι → R)
    (received : ι → R[X]) (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ) :
    (localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns row j).natDegree ≤
      ℓ * ((columns j).y₀ + ∑ k, (columns j).higher k -
        row.2.1.weight (localJetDegreeWeight d)) :=
  SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le_sub ℓ _ (hreceived row.1) _ _

/-- An entry vanishes when the jet degree of its row exceeds the total jet degree of its column.
This holds for all centers and received values. -/
theorem localConstraintMatrix_eq_zero_of_lt (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ)
    (hlt : (columns j).y₀ + ∑ k, (columns j).higher k <
      row.2.1.weight (localJetDegreeWeight d)) :
    localConstraintMatrix m centers received columns row j = 0 :=
  SourceColumn.coeff_unscaledLocalSubstitution_eq_zero_of_lt _ _ _ hlt

end ReedSolomon.HiddenDerivative
