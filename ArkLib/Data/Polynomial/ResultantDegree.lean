/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph, Quang Dao
-/
module

public import CompPoly.ToMathlib.Polynomial.BivariateDegree
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Coefficient-variable degree bounds for resultants

The Sylvester matrix has one column budget per shifted input polynomial. Summing those budgets
bounds the degree of every determinant term. Adapted from Alexander Hicks and Aleph's
field-only result in ArkLib (Apache-2.0), generalizing the
`ps_nat_degree_resultant_le` argument to commutative coefficient rings and explicit coefficient
budgets, including padded resultants. For `R = F[Z]`, the resulting bound is in the middle `X`
axis of `F[Z][X][Y]`.

Source and adaptation: the native ArkLib theorem is at
https://github.com/Verified-zkEVM/ArkLib/blob/66f3d089a41704597f54d641b78254d2a8f361f8/ArkLib/Data/CodingTheory/PolishchukSpielman/Resultant.lean#L43-L98
The explicit coefficient budgets and derivative corollaries below extend that argument.
No donor compatibility modules are imported.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- A padded resultant's coefficient-variable degree is bounded by the Sylvester column count
times each input's coefficient-degree budget. No degree or nonzero assumptions are necessary. -/
theorem natDegree_resultant_le_of_coeff_natDegree_le
    (P Q : Polynomial (Polynomial R)) (m n A B : ℕ)
    (hP : ∀ j, (P.coeff j).natDegree ≤ A) (hQ : ∀ j, (Q.coeff j).natDegree ≤ B) :
    (resultant P Q m n).natDegree ≤ n * A + m * B := by
  classical
  let M := sylvester P Q m n
  let cb : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m ↦ B) (fun _ : Fin n ↦ A)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n)) :
      (M (σ i) i).natDegree ≤ cb i := by
    cases i using Fin.addCases with
    | left j =>
      simp only [cb, Fin.addCases_left]
      have hM : M (σ (.castAdd n j)) (.castAdd n j) =
          if (σ (.castAdd n j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) then
            Q.coeff ((σ (.castAdd n j) : ℕ) - j) else 0 := by
        simp [M, sylvester]
      rw [hM]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [cb, Fin.addCases_right]
      have hM : M (σ (.natAdd m j)) (.natAdd m j) =
          if (σ (.natAdd m j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) then
            P.coeff ((σ (.natAdd m j) : ℕ) - j) else 0 := by
        simp [M, sylvester]
      rw [hM]
      split_ifs
      · exact hP _
      · simp
  change M.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le Finset.univ (fun i ↦ M (σ i) i)).trans ?_
  refine (Finset.sum_le_sum (fun i _ ↦ hentry σ i)).trans ?_
  simp [cb, Fin.sum_univ_add, Nat.add_comm]

/-- The resultant degree bound in terms of each input's inner-variable degree. -/
theorem natDegree_resultant_le_degreeX (P Q : Polynomial (Polynomial R)) (m n : ℕ) :
    (resultant P Q m n).natDegree ≤ n * Bivariate.degreeX P + m * Bivariate.degreeX Q :=
  natDegree_resultant_le_of_coeff_natDegree_le P Q m n _ _
    (Bivariate.coeff_natDegree_le_degreeX P) (Bivariate.coeff_natDegree_le_degreeX Q)

/-- Differentiating in the outer variable does not increase any coefficient-variable degree. -/
theorem coeff_derivative_natDegree_le (P : Polynomial (Polynomial R)) (j : ℕ) :
    (P.derivative.coeff j).natDegree ≤ (P.coeff (j + 1)).natDegree := by
  rw [coeff_derivative]
  rw [show (j : Polynomial R) + 1 = C ((j : R) + 1) by simp]
  exact natDegree_mul_C_le _ _

/-- The actual-degree derivative resultant obeys the usual `(2d-1)D` coefficient-variable
bound, also in small characteristic where the derivative degree may drop. -/
theorem natDegree_resultant_derivative_le (P : Polynomial (Polynomial R)) :
    (resultant P P.derivative).natDegree ≤ (2 * P.natDegree - 1) * Bivariate.degreeX P := by
  have h := natDegree_resultant_le_of_coeff_natDegree_le P P.derivative
    P.natDegree P.derivative.natDegree (Bivariate.degreeX P) (Bivariate.degreeX P)
    (Bivariate.coeff_natDegree_le_degreeX P)
    (fun j ↦ (coeff_derivative_natDegree_le P j).trans
      (Bivariate.coeff_natDegree_le_degreeX P (j + 1)))
  calc
    _ ≤ (P.derivative.natDegree + P.natDegree) * Bivariate.degreeX P := by
      simpa only [add_mul] using h
    _ ≤ (2 * P.natDegree - 1) * Bivariate.degreeX P := by
      apply Nat.mul_le_mul_right
      have hd := natDegree_derivative_le P
      omega

/-- Padding the derivative to degree `d - 1` obeys the same coefficient-variable bound.
The derivative may have smaller actual degree, including in positive characteristic. -/
theorem natDegree_resultant_derivative_padded_le (P : Polynomial (Polynomial R)) :
    (resultant P P.derivative P.natDegree (P.natDegree - 1)).natDegree ≤
      (2 * P.natDegree - 1) * Bivariate.degreeX P := by
  have h := natDegree_resultant_le_of_coeff_natDegree_le P P.derivative
    P.natDegree (P.natDegree - 1) (Bivariate.degreeX P) (Bivariate.degreeX P)
    (Bivariate.coeff_natDegree_le_degreeX P)
    (fun j ↦ (coeff_derivative_natDegree_le P j).trans
      (Bivariate.coeff_natDegree_le_degreeX P (j + 1)))
  have hn : P.natDegree - 1 + P.natDegree = 2 * P.natDegree - 1 := by omega
  simpa only [← add_mul, hn] using h

end Polynomial
