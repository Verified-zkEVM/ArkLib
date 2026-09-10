/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedLine
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.GradedRank

/-!
# Primitive symbolic interpolation for received polynomial curves

The received value at each evaluation point is an arbitrary polynomial in the challenge.
Only finitely many local coefficients occur in the source columns. Restricting to their
support gives a finite polynomial matrix with exactly the same kernel as the full local
constraint system. A rational-function rank bound then supplies a primitive interpolant
which stays nonzero after every field extension and challenge specialization.

The rank bound is an explicit hypothesis here; this module does not assert a capacity theorem.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), symbolic interpolation for polynomial
  curves.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential
open scoped Matrix

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation

variable {F : Type*} [Field F] {d n N : ℕ}

/-- The full local coefficient matrix for a polynomial received word. -/
def constraintMatrix (m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (columns : Fin N → SourceColumn d) :
    Matrix (Fin n × LowContactIndex d m) (Fin N) F[X] := fun row j ↦
  localConstraintCoordinatesAt m (C (centers row.1)) (w row.1)
    (columns j).polynomial row.2

/-- Precisely the local rows supported by at least one supplied source column. -/
def supportedRows (m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (columns : Fin N → SourceColumn d) : Finset (Fin n × LowContactIndex d m) := by
  classical
  exact Finset.univ.biUnion fun i ↦ Finset.univ.biUnion fun j ↦
    (lowContactSupport m
      (localConstraintAt m (C (centers i)) (w i) (columns j).polynomial)).image (Prod.mk i)

theorem mem_supportedRows_of_entry_ne_zero (m : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (row : Fin n × LowContactIndex d m) (j : Fin N)
    (h : constraintMatrix m centers w columns row j ≠ 0) :
    row ∈ supportedRows m centers w columns := by
  classical
  simp only [supportedRows, Finset.mem_biUnion]
  refine ⟨row.1, Finset.mem_univ _, j, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨row.2, ?_, rfl⟩
  have hsupp : row.2.1 ∈
      (localConstraintAt m (C (centers row.1)) (w row.1)
        (columns j).polynomial).support := by
    rw [MvPolynomial.mem_support_iff]
    simpa [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
      localConstraintAt, projectLowContact, coeff_filterLocalMonomials, row.2.2] using h
  simpa [lowContactSupport] using hsupp

/-- The finite symbolic matrix, indexed by the supported local rows. -/
def finiteConstraintMatrix (m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (columns : Fin N → SourceColumn d) :
    Matrix (Fin (Fintype.card {r // r ∈ supportedRows m centers w columns})) (Fin N) F[X] :=
  (constraintMatrix m centers w columns).submatrix
    (fun i ↦ ((Fintype.equivFin {r // r ∈ supportedRows m centers w columns}).symm i).1)
    (Equiv.refl _)

/-- Dropping identically zero rows leaves the polynomial kernel unchanged. -/
theorem finiteConstraintMatrix_kernel_iff (m : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (columns : Fin N → SourceColumn d) (v : Fin N → F[X]) :
    (finiteConstraintMatrix m centers w columns) *ᵥ v = 0 ↔
      (constraintMatrix m centers w columns) *ᵥ v = 0 := by
  classical
  constructor
  · intro h
    funext row
    by_cases hr : row ∈ supportedRows m centers w columns
    · have hi := congrFun h
        ((Fintype.equivFin {r // r ∈ supportedRows m centers w columns}) ⟨row, hr⟩)
      simpa [finiteConstraintMatrix, Matrix.mulVec, dotProduct] using hi
    · change ∑ j, constraintMatrix m centers w columns row j * v j = 0
      apply Finset.sum_eq_zero
      intro j _
      have hz : constraintMatrix m centers w columns row j = 0 := by
        by_contra hne
        exact hr (mem_supportedRows_of_entry_ne_zero m centers w columns row j hne)
      simp [hz]
  · intro h
    funext i
    exact congrFun h
      ((Fintype.equivFin {r // r ∈ supportedRows m centers w columns}).symm i).1

/-- Each source column has challenge degree at most batching degree times its `Y₀` exponent. -/
theorem constraintMatrix_degree_le (m ℓ : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (row : Fin n × LowContactIndex d m) (j : Fin N) :
    (constraintMatrix m centers w columns row j).natDegree ≤ ℓ * (columns j).y₀ := by
  have h := sourceMonomial_curve_unscaled_coeffDegreeLE (d := d)
    (centers row.1) (w row.1) ℓ (hw row.1)
    (columns j).x (columns j).y₀ (columns j).higher
  simpa [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
    SourceColumn.polynomial_eq_sourceMonomial] using h row.2.1

/-- A translated matrix entry from source grade `t` to local row grade `u` has challenge
degree at most `ℓ (t-u)`.  This is the degree premise used by shifted polynomial kernels. -/
theorem constraintMatrix_degree_le_grade_shift (m ℓ : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (row : Fin n × LowContactIndex d m) (j : Fin N) :
    (constraintMatrix m centers w columns row j).natDegree ≤
      ℓ * ((columns j).y₀ + ∑ k, (columns j).higher k - localJetDegree row.2.1) := by
  have h := sourceMonomial_curve_unscaled_coeff_natDegree_le_shift
    (d := d) (localJetDegreeWeight (d := d))
    (by simp [localJetDegreeWeight, localT])
    (by simp [localJetDegreeWeight, localE, localAux])
    (by intro k; simp [localJetDegreeWeight, localY])
    (centers row.1) (w row.1) ℓ (hw row.1)
    (columns j).x (columns j).y₀ (columns j).higher row.2.1
  simpa [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
    SourceColumn.polynomial_eq_sourceMonomial, localJetDegree] using h

/-- Entries above their source jet grade are identically zero, including when the batching
degree is zero. -/
theorem constraintMatrix_eq_zero_of_source_grade_lt_row_grade (m ℓ : ℕ)
    (centers : Fin n → F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (row : Fin n × LowContactIndex d m) (j : Fin N)
    (hgrade : (columns j).y₀ + ∑ k, (columns j).higher k < localJetDegree row.2.1) :
    constraintMatrix m centers w columns row j = 0 := by
  have h := sourceMonomial_curve_unscaled_coeff_eq_zero_of_weight_gt
    (d := d) (localJetDegreeWeight (d := d))
    (by simp [localJetDegreeWeight, localT])
    (by simp [localJetDegreeWeight, localE, localAux])
    (by intro k; simp [localJetDegreeWeight, localY])
    (centers row.1) (w row.1) ℓ (hw row.1)
    (columns j).x (columns j).y₀ (columns j).higher row.2.1 hgrade
  simpa [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
    SourceColumn.polynomial_eq_sourceMonomial, localJetDegree] using h

/-- The matrix kernel is exactly the local-constraint condition on the assembled interpolant. -/
theorem constraintMatrix_kernel_iff (m : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (columns : Fin N → SourceColumn d) (v : Fin N → F[X]) :
    (constraintMatrix m centers w columns) *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i) (interpolant columns v) := by
  classical
  have heq (row : Fin n × LowContactIndex d m) :
      ((constraintMatrix m centers w columns) *ᵥ v) row =
        localConstraintCoordinatesAt m (C (centers row.1)) (w row.1)
          (interpolant columns v) row.2 := by
    rw [interpolant, Matrix.mulVec, dotProduct, map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    change localConstraintCoordinatesAt m (C (centers row.1)) (w row.1)
      (columns j).polynomial row.2 * v j = _
    rw [show MvPolynomial.monomial (columns j).exponent (v j) =
        v j • (columns j).polynomial by
          rw [SourceColumn.polynomial, MvPolynomial.smul_monomial]
          simp, LinearMap.map_smul]
    simp [mul_comm]
  constructor
  · intro h i
    rw [satisfiesLocalConstraints_iff_coordinates_eq_zero]
    funext e
    rw [← heq (i, e), congrFun h (i, e)]
    rfl
  · intro h
    funext row
    rw [heq]
    exact congrFun ((satisfiesLocalConstraints_iff_coordinates_eq_zero
      m (C (centers row.1)) (w row.1) (interpolant columns v)).mp (h row.1)) row.2

/-- A strict rational-function rank deficit gives a primitive, universally nonvanishing
symbolic curve interpolant. The coefficient height reflects the batching degree `ℓ`. -/
theorem exists_primitive_interpolant_of_rank_le (m ℓ ν r : ℕ)
    (centers : Fin n → F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hrank : ((finiteConstraintMatrix m centers w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ r) (hrN : r < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ r * (ℓ * ν) / (N - r)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i) (interpolant columns v) := by
  let M := finiteConstraintMatrix m centers w columns
  let s := (M.map (algebraMap F[X] (RatFunc F))).rank
  have hs : s ≤ r := hrank
  have hdeg : ∀ i j, (M i j).natDegree ≤ ℓ * ν := by
    intro i j
    exact (constraintMatrix_degree_le m ℓ centers w hw columns _ j).trans
      (Nat.mul_le_mul_left ℓ (hy₀ j))
  obtain ⟨v, hv, hMv, hvdeg, hp, hnozero⟩ :=
    Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq M hdeg
      (show (M.map (algebraMap F[X] (RatFunc F))).rank = s from rfl) (hs.trans_lt hrN)
  refine ⟨v, hv, ?_, hp, ?_, ?_⟩
  · intro j
    exact (hvdeg j).trans (Nat.div_le_div (Nat.mul_le_mul_right (ℓ * ν) hs)
      (Nat.sub_le_sub_left hs N) (Nat.sub_ne_zero_of_lt hrN))
  · intro E _ ι z
    exact map_interpolant_ne_zero columns hcolumns v ι z (hnozero ι z)
  · exact (constraintMatrix_kernel_iff m centers w columns v).mp
      ((finiteConstraintMatrix_kernel_iff m centers w columns v).mp hMv)

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
