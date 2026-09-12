/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Executable univariate Sylvester resultants

The matrix is assembled from stored input coefficients and its determinant is
computed by the existing `Matrix.det`. The exact refinement theorem identifies
it with Mathlib's padded resultant. The checked entrypoint rejects degree
bounds smaller than either input's actual degree. No roots, factors, resultant
values, or solver certificates are supplied to the executable functions.

This is the generic univariate resultant stage, not the multivariate toric
producer or its isolated-root coverage theorem. Padded degrees are intentional:
extra padding may change the resultant, including its sign. At degrees zero
and zero, the empty determinant is one, following the existing resultant
convention; this value alone does not certify absence of common roots.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.Univariate

open CompPoly

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- Assemble the padded Sylvester matrix directly from stored coefficients.
The first `m` columns contain translates of `g`; the last `n` contain `f`. -/
def storedSylvester (f g : CPolynomial R) (m n : ℕ) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  .of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)

/-- Compute the determinant of the stored padded Sylvester matrix.
No degree check is made here; `checkedResultant` is the guarded entrypoint. -/
def storedResultant (f g : CPolynomial R) (m n : ℕ) : R :=
  (storedSylvester f g m n).det

/-- Compute a padded resultant only when both bounds cover the original inputs. -/
def checkedResultant (f g : CPolynomial R) (m n : ℕ) : Option R :=
  if f.natDegree ≤ m ∧ g.natDegree ≤ n then some (storedResultant f g m n) else none

/-- Every stored matrix entry is exactly the coefficient of its original input. -/
theorem storedSylvester_eq (f g : CPolynomial R) (m n : ℕ) :
    storedSylvester f g m n = Polynomial.sylvester f.toPoly g.toPoly m n := by
  simp [storedSylvester, Polynomial.sylvester, CPolynomial.coeff_toPoly]

/-- The executed determinant is precisely the existing padded resultant. -/
theorem storedResultant_eq (f g : CPolynomial R) (m n : ℕ) :
    storedResultant f g m n = Polynomial.resultant f.toPoly g.toPoly m n := by
  rw [storedResultant, storedSylvester_eq]
  rfl

/-- Successful checked execution is equivalent to the semantic degree guards
and the exact resultant value, with no backend-correctness premise. -/
theorem checkedResultant_eq_some_iff (f g : CPolynomial R) (m n : ℕ) (r : R) :
    checkedResultant f g m n = some r ↔
      f.toPoly.natDegree ≤ m ∧ g.toPoly.natDegree ≤ n ∧
        Polynomial.resultant f.toPoly g.toPoly m n = r := by
  simp only [checkedResultant, CPolynomial.natDegree_toPoly, storedResultant_eq]
  split_ifs with h
  · simp [h.1, h.2]
  · simp [← and_assoc, h]

/-- Adequate explicit bounds always produce the computed resultant. -/
theorem checkedResultant_success (f g : CPolynomial R) (m n : ℕ)
    (hf : f.toPoly.natDegree ≤ m) (hg : g.toPoly.natDegree ≤ n) :
    checkedResultant f g m n = some (Polynomial.resultant f.toPoly g.toPoly m n) :=
  (checkedResultant_eq_some_iff f g m n _).mpr ⟨hf, hg, rfl⟩

/-- Rejection means exactly that at least one supplied degree bound is too small. -/
theorem checkedResultant_eq_none_iff (f g : CPolynomial R) (m n : ℕ) :
    checkedResultant f g m n = none ↔
      ¬ (f.toPoly.natDegree ≤ m ∧ g.toPoly.natDegree ≤ n) := by
  simp [checkedResultant, CPolynomial.natDegree_toPoly]

end ArkLib.Rojas.Producer.Univariate
