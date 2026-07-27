/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martin
-/
import CompPoly.Multivariate.Restrict
import CompPoly.Multivariate.MvPolyEquiv
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
  # Correspondence of `CMvPolynomial` degree restriction with Mathlib's submodules

  Additions to `CompPoly.Multivariate.Restrict` not yet upstreamed to CompPoly.

  This completes the `TODO` in `CompPoly/Multivariate/Restrict.lean`: transporting the computable
  degree-bounded restrictions `CMvPolynomial.restrictTotalDegree` / `CMvPolynomial.restrictDegree`
  across the `fromCMvPolynomial` bridge lands inside Mathlib's degree-bounded submodules
  `MvPolynomial.restrictTotalDegree` / `MvPolynomial.restrictDegree`. This is what establishes
  correctness of the computable restriction operations with respect to Mathlib's submodule API.
-/

namespace CPoly

open CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Every variable degree of `restrictDegree d p` is at most `d`, at the `CMvPolynomial` level.

  This lifts the per-monomial bound `degreeOf_le_of_mem_monomials_restrictDegree` to the
  polynomial's `degreeOf`, which is the supremum over its monomials. -/
lemma degreeOf_restrictDegree_le (d : ℕ) (p : CMvPolynomial n R) (i : Fin n) :
    (CMvPolynomial.restrictDegree d p).degreeOf i ≤ d := by
  unfold CMvPolynomial.degreeOf
  refine Finset.sup_le ?_
  intro m hm
  exact degreeOf_le_of_mem_monomials_restrictDegree
    (d := d) (p := p) ((List.mem_toFinset).1 hm) i

/-- Transporting `restrictTotalDegree d p` across `fromCMvPolynomial` lands in Mathlib's
  total-degree submodule `MvPolynomial.restrictTotalDegree (Fin n) R d`. -/
theorem fromCMvPolynomial_restrictTotalDegree_mem (d : ℕ) (p : CMvPolynomial n R) :
    fromCMvPolynomial (CMvPolynomial.restrictTotalDegree d p) ∈
      MvPolynomial.restrictTotalDegree (Fin n) R d := by
  rw [MvPolynomial.mem_restrictTotalDegree, ← totalDegree_equiv (S := R)]
  exact totalDegree_restrictTotalDegree_le d p

/-- Transporting `restrictDegree d p` across `fromCMvPolynomial` lands in Mathlib's per-variable
  degree submodule `MvPolynomial.restrictDegree (Fin n) R d`. -/
theorem fromCMvPolynomial_restrictDegree_mem (d : ℕ) (p : CMvPolynomial n R) :
    fromCMvPolynomial (CMvPolynomial.restrictDegree d p) ∈
      MvPolynomial.restrictDegree (Fin n) R d := by
  rw [MvPolynomial.mem_restrictDegree_iff_sup]
  intro i
  rw [← MvPolynomial.degreeOf_def,
    ← congrFun (degreeOf_equiv (S := R) (p := CMvPolynomial.restrictDegree d p)) i]
  exact degreeOf_restrictDegree_le d p i

end CPoly
