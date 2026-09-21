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

## Total-degree bounds

Suppose `P, Q : R[X][X]` have declared outer degrees `m`, `n` and satisfy the coefficient
triangles `i + deg_X (P.coeff i) ≤ dP` for `i ≤ m` and `i + deg_X (Q.coeff i) ≤ dQ` for `i ≤ n`;
for `m` and `n` the actual outer degrees, these say that `P` and `Q` have total degree at most
`dP` and `dQ`. Then `deg_X (resultant P Q m n) + m * n ≤ n * dP + m * dQ`. The proof bounds each
nonzero Sylvester determinant term by column weights and uses that a permutation preserves the
sum of the row indices. For the derivative, `dQ = dP - 1`, which gives the bound
`(2 * b - 1) * j - b ^ 2` of the source.

## Main statements

* `natDegree_resultant_le_of_coeff_natDegree_le`: the column-budget bound `n * A + m * B`.
* `natDegree_resultant_derivative_le` and `natDegree_resultant_derivative_padded_le`: the
  `(2 * d - 1) * degreeX P` bound for the derivative resultant.
* `natDegree_resultant_add_mul_le_of_coeff_add_le` and
  `natDegree_resultant_le_of_coeff_add_le`: the total-degree bound
  `n * dP + m * dQ - m * n`.
* `natDegree_resultant_le_mul_of_coeff_add_le`: the Bezout bound `dP * dQ`.
* `natDegree_resultant_derivative_padded_add_sq_le` and
  `natDegree_resultant_derivative_padded_le_of_coeff_add_le`: the derivative case
  `deg_X (resultant A A.derivative b (b - 1)) ≤ (2 * b - 1) * j - b ^ 2`.

The total-degree bounds are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Polynomial/DerivativeResultantDegree.lean`:
`natDegree_separableResultant_add_sq_le_of_le`, `natDegree_separableResultant_add_sq_le`,
`natDegree_separableResultant_le_totalDegree_of_le` and
`natDegree_separableResultant_le_totalDegree`. The source proves only the derivative case, for
`separableResultant A b = resultant A.derivative A (b - 1) b`, and assumes `0 < b` and
`A.natDegree = b`. Here the proof is done once for two arbitrary polynomials with declared
degrees, and the derivative case is a corollary stated in main's argument order
`resultant A A.derivative b (b - 1)`, which has the same value
(`resultant_comm_sub_one` in `ArkLib.Data.Polynomial.ResultantSpecialization`). Neither `0 < b`
nor `A.natDegree = b` is needed: only coefficients of index at most `b` enter the Sylvester
matrix, and for `b = 0` both sides are `0`. The source's forms with the triangle at every index
are the special case of the `i ≤ b` forms and are not restated.

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

/-! ### Total-degree bounds -/

/-- The weighted Sylvester-determinant bound. Let `P, Q : R[X][X]` be written in an outer
variable `Y`, with declared degrees `m` and `n`, and suppose that the coefficients satisfy the
total-degree conditions `i + deg_X (P.coeff i) ≤ dP` for `i ≤ m` and
`i + deg_X (Q.coeff i) ≤ dQ` for `i ≤ n`. Then
`deg_X (resultant P Q m n) + m * n ≤ n * dP + m * dQ`.

Every nonzero term of the Sylvester determinant takes, in each column, a coefficient whose
`Y`-index is the row minus the column offset. Summing over a permutation, the rows and the
offsets cancel except for `m * n`, which is subtracted from the column budgets `n * dP + m * dQ`.
With the budgets `A := dP` and `B := dQ`, `natDegree_resultant_le_of_coeff_natDegree_le` gives
`n * dP + m * dQ` without the subtraction. With the budgets `A`, `B` set to the largest
coefficient degrees instead, the two bounds are incomparable.

Only the coefficients with index at most the declared degree occur in the Sylvester matrix, so
`P` and `Q` may have actual degree below `m` and `n`; coefficients above the declared degrees
are ignored. The hypothesis at `i = m` gives `m ≤ dP`, which covers the determinant terms that
vanish. No condition on `R` beyond commutativity is needed. -/
theorem natDegree_resultant_add_mul_le_of_coeff_add_le
    (P Q : Polynomial (Polynomial R)) (m n dP dQ : ℕ)
    (hP : ∀ i ≤ m, i + (P.coeff i).natDegree ≤ dP)
    (hQ : ∀ i ≤ n, i + (Q.coeff i).natDegree ≤ dQ) :
    (resultant P Q m n).natDegree + m * n ≤ n * dP + m * dQ := by
  classical
  let M := sylvester P Q m n
  let w : Fin (m + n) → ℕ :=
    Fin.addCases (fun c : Fin m ↦ dQ + c) (fun c : Fin n ↦ dP + c)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n)) (hne : M (σ i) i ≠ 0) :
      (M (σ i) i).natDegree + σ i ≤ w i := by
    cases i using Fin.addCases with
    | left j =>
      have hM : M (σ (.castAdd n j)) (.castAdd n j) =
          if (σ (.castAdd n j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) then
            Q.coeff ((σ (.castAdd n j) : ℕ) - j) else 0 := by
        simp [M, sylvester]
      rw [hM] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hb := hQ ((σ (.castAdd n j) : ℕ) - j) (by have := h.2; omega)
        have hl := h.1
        simp only [w, Fin.addCases_left]
        omega
      · exact absurd rfl hne
    | right j =>
      have hM : M (σ (.natAdd m j)) (.natAdd m j) =
          if (σ (.natAdd m j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) then
            P.coeff ((σ (.natAdd m j) : ℕ) - j) else 0 := by
        simp [M, sylvester]
      rw [hM] at hne ⊢
      split_ifs at hne ⊢ with h
      · have hb := hP ((σ (.natAdd m j) : ℕ) - j) (by have := h.2; omega)
        have hl := h.1
        simp only [w, Fin.addCases_right]
        omega
      · exact absurd rfl hne
  set S := (∑ c : Fin m, (c : ℕ)) + ∑ c : Fin n, (c : ℕ)
  have hw : ∑ i, w i = m * dQ + n * dP + S := by
    simp only [w, S, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hidx : ∑ i : Fin (m + n), (i : ℕ) = m * n + S := by
    simp only [S, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hmn : m * n ≤ n * dP := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left n ((Nat.le_add_right m _).trans (hP m le_rfl))
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (m + n)))),
      (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree ≤ n * dP + m * dQ - m * n := by
    intro σ _
    refine (natDegree_smul_le _ _).trans ?_
    by_cases hz : ∃ i, M (σ i) i = 0
    · obtain ⟨i, hi⟩ := hz
      have hprod : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hprod, natDegree_zero]
      exact Nat.zero_le _
    · simp only [not_exists] at hz
      have h1 := natDegree_prod_le Finset.univ (fun i ↦ M (σ i) i)
      have h2 : ∑ i, ((M (σ i) i).natDegree + σ i) ≤ ∑ i, w i :=
        Finset.sum_le_sum fun i _ ↦ hentry σ i (hz i)
      have h3 : ∑ i, ((σ i : Fin (m + n)) : ℕ) = ∑ i : Fin (m + n), (i : ℕ) :=
        Equiv.sum_comp σ (fun i ↦ (i : ℕ))
      rw [Finset.sum_add_distrib, h3, hw, hidx] at h2
      omega
  have hdet := natDegree_sum_le_of_forall_le _ _ hterm
  rw [← Matrix.det_apply] at hdet
  change M.det.natDegree + m * n ≤ _
  omega

/-- The weighted Sylvester-determinant bound of
`natDegree_resultant_add_mul_le_of_coeff_add_le`, written with truncated subtraction:
`deg_X (resultant P Q m n) ≤ n * dP + m * dQ - m * n`. The subtraction does not truncate, since
the hypotheses give `m ≤ dP`. -/
theorem natDegree_resultant_le_of_coeff_add_le
    (P Q : Polynomial (Polynomial R)) (m n dP dQ : ℕ)
    (hP : ∀ i ≤ m, i + (P.coeff i).natDegree ≤ dP)
    (hQ : ∀ i ≤ n, i + (Q.coeff i).natDegree ≤ dQ) :
    (resultant P Q m n).natDegree ≤ n * dP + m * dQ - m * n :=
  Nat.le_sub_of_add_le (natDegree_resultant_add_mul_le_of_coeff_add_le P Q m n dP dQ hP hQ)

/-- The Bezout bound for resultants: under the total-degree conditions of
`natDegree_resultant_add_mul_le_of_coeff_add_le`, `deg_X (resultant P Q m n) ≤ dP * dQ`.
It follows from `n * dP + m * dQ - m * n = dP * dQ - (dP - m) * (dQ - n)`, using `m ≤ dP` and
`n ≤ dQ`, which the hypotheses at `i = m` and `i = n` supply. The bound is weaker than the
weighted one whenever `m < dP` and `n < dQ`. -/
theorem natDegree_resultant_le_mul_of_coeff_add_le
    (P Q : Polynomial (Polynomial R)) (m n dP dQ : ℕ)
    (hP : ∀ i ≤ m, i + (P.coeff i).natDegree ≤ dP)
    (hQ : ∀ i ≤ n, i + (Q.coeff i).natDegree ≤ dQ) :
    (resultant P Q m n).natDegree ≤ dP * dQ := by
  have h := natDegree_resultant_add_mul_le_of_coeff_add_le P Q m n dP dQ hP hQ
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right m _).trans (hP m le_rfl))
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right n _).trans (hQ n le_rfl))
  nlinarith

/-- The total-degree bound for the padded derivative resultant. If `A : R[X][X]` satisfies
`i + deg_X (A.coeff i) ≤ j` for every `i ≤ b`, then
`deg_X (resultant A A.derivative b (b - 1)) + b ^ 2 ≤ (2 * b - 1) * j`.

This is `natDegree_resultant_add_mul_le_of_coeff_add_le` with `P := A`, `Q := A.derivative`,
`dP := j` and `dQ := j - 1`: differentiation lowers the `Y`-index by one and does not raise the
coefficient degree (`coeff_derivative_natDegree_le`). The bound is sharp: for
`A = Y ^ 2 - X ^ 2` over `ℚ` both sides of the truncated form equal `2`, while
`natDegree_resultant_derivative_padded_le` gives `(2 * 2 - 1) * degreeX A = 6`. The two bounds
are incomparable: for `A = Y ^ 2` this one gives `2` and the `degreeX` bound gives `0`.

`b` is a declared degree. `A` may have actual degree below `b`, and the derivative may have
degree below `b - 1`, as in positive characteristic. For `b = 0` both sides are `0`. -/
theorem natDegree_resultant_derivative_padded_add_sq_le
    (A : Polynomial (Polynomial R)) (b j : ℕ)
    (hA : ∀ i ≤ b, i + (A.coeff i).natDegree ≤ j) :
    (resultant A A.derivative b (b - 1)).natDegree + b ^ 2 ≤ (2 * b - 1) * j := by
  rcases b with _ | k
  · simp
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hA (k + 1) le_rfl; omega⟩
  have hQ : ∀ i ≤ k, i + (A.derivative.coeff i).natDegree ≤ j' := fun i hi ↦ by
    have h1 := coeff_derivative_natDegree_le A i
    have h2 := hA (i + 1) (by omega)
    omega
  have h := natDegree_resultant_add_mul_le_of_coeff_add_le A A.derivative (k + 1) k (j' + 1) j'
    hA hQ
  rw [Nat.add_sub_cancel, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  nlinarith

/-- `natDegree_resultant_derivative_padded_add_sq_le` with truncated subtraction:
`deg_X (resultant A A.derivative b (b - 1)) ≤ (2 * b - 1) * j - b ^ 2`. The subtraction does not
truncate, because the hypothesis at `i = b` gives `b ≤ j`. -/
theorem natDegree_resultant_derivative_padded_le_of_coeff_add_le
    (A : Polynomial (Polynomial R)) (b j : ℕ)
    (hA : ∀ i ≤ b, i + (A.coeff i).natDegree ≤ j) :
    (resultant A A.derivative b (b - 1)).natDegree ≤ (2 * b - 1) * j - b ^ 2 :=
  Nat.le_sub_of_add_le (natDegree_resultant_derivative_padded_add_sq_le A b j hA)

end Polynomial
