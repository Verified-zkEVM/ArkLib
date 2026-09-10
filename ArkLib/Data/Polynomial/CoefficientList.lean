/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.DegreeTruncationSemantics

/-!
# Ascending coefficients and fixed-width descending vectors

Computable polynomials store coefficients in ascending order. Decoder outputs use descending
order and retain leading zeros to make every vector have the same width. `padReverse` performs
this conversion without changing the represented polynomial. Its width guarantee assumes that
the input fits; overlong inputs are preserved, so callers cannot silently lose coefficients.
-/

@[expose] public section

namespace Polynomial.CoefficientList

variable {F : Type*} [CommSemiring F]

/-- Reverse an ascending list and prepend zeros to reach the requested width. -/
def padReverse (width : ℕ) (bs : List F) : List F :=
  List.replicate (width - bs.length) 0 ++ bs.reverse

/-- A fitting input has exactly the requested output width, including leading zeros. -/
theorem padReverse_length (width : ℕ) (bs : List F) (h : bs.length ≤ width) :
    (padReverse width bs).length = width := by simp [padReverse]; omega

/-- Interpret an ascending list as a polynomial, independently of any padding width. -/
noncomputable def ascendingPolynomial (bs : List F) : F[X] :=
  JetHornerMachine.coefficientPolynomial bs.reverse

private theorem ascendingPolynomial_cons (b : F) (bs : List F) :
    ascendingPolynomial (b :: bs) = ascendingPolynomial bs * X + C b := by
  simp [ascendingPolynomial, JetHornerMachine.coefficientPolynomial,
    List.reverse_cons, List.foldl_append]

/-- Missing entries denote zero; the physical list therefore specifies every coefficient. -/
theorem ascendingPolynomial_coeff (bs : List F) (j : ℕ) :
    (ascendingPolynomial bs).coeff j = bs.getD j 0 := by
  induction bs generalizing j with
  | nil => simp [ascendingPolynomial, JetHornerMachine.coefficientPolynomial]
  | cons b bs ih =>
      cases j <;> simp [ascendingPolynomial_cons, Polynomial.coeff_mul_X, ih]

/-- Reversal changes the storage convention, and padding contributes only higher zeros. -/
theorem padReverse_polynomial (width : ℕ) (bs : List F) :
    JetHornerMachine.coefficientPolynomial (padReverse width bs) = ascendingPolynomial bs :=
  JetHornerMachine.coefficientPolynomial_zero_prefix (width - bs.length) bs.reverse

/-- Materializing all coefficients below a strict degree bound preserves the polynomial. -/
theorem ascendingPolynomial_ofFn (k : ℕ) (p : F[X]) (hdegree : p.degree < k) :
    ascendingPolynomial (List.ofFn fun i : Fin k => p.coeff i) = p := by
  ext j
  rw [ascendingPolynomial_coeff]
  by_cases hj : j < k
  · simp [List.getD, hj]
  · have hz : p.coeff j = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (hdegree.trans_le (by exact_mod_cast Nat.le_of_not_gt hj))
    simp [List.getD, hj, hz]

end Polynomial.CoefficientList
