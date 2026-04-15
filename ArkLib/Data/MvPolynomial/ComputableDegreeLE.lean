/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import CompPoly.Data.MvPolynomial.Notation
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv
import CompPoly.Multivariate.Restrict
import ArkLib.Data.MvPolynomial.Degrees

/-!
# Bounded-degree computable multivariate polynomials

This file provides the computable `CMvPolynomial` counterpart of Mathlib's
`MvPolynomial.restrictDegree` carrier.

The goal is to preserve the abstract-facing "bounded degree" interface shape while migrating the
underlying execution path onto `CompPoly.CMvPolynomial`.
-/

namespace CPoly
namespace CMvPolynomial

open MvPolynomial

variable (n : ℕ) (R : Type) [CommSemiring R] (d : ℕ)

/-- Computable multivariate polynomials in `n` variables whose degree in each variable is `≤ d`. -/
abbrev degreeLE : Type _ :=
  { p : CPoly.CMvPolynomial n R // ∀ i : Fin n, p.degreeOf i ≤ d }

namespace degreeLE

variable {n : ℕ} {R : Type} [CommSemiring R] {d : ℕ}

@[simp] theorem coe_mk (p : CPoly.CMvPolynomial n R) (hp : ∀ i : Fin n, p.degreeOf i ≤ d) :
    ((⟨p, hp⟩ : CPoly.CMvPolynomial.degreeLE n R d) : CPoly.CMvPolynomial n R) = p := rfl

/-- Bridge back to Mathlib's `MvPolynomial` bounded-degree carrier. -/
def val [BEq R] [LawfulBEq R] (p : CPoly.CMvPolynomial.degreeLE n R d) : MvPolynomial (Fin n) R :=
  CPoly.fromCMvPolynomial (p : CPoly.CMvPolynomial n R)

theorem property [BEq R] [LawfulBEq R] (p : CPoly.CMvPolynomial.degreeLE n R d) :
    val p ∈ R⦃≤ d⦄[X Fin n] := by
  rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
  intro i
  have hdeg : MvPolynomial.degreeOf i (val p) = (p : CPoly.CMvPolynomial n R).degreeOf i := by
    simpa [val] using
      (congrFun (CPoly.degreeOf_equiv (S := R) (p := (p : CPoly.CMvPolynomial n R))) i).symm
  rw [hdeg]
  exact p.2 i

@[ext] theorem ext {p q : CPoly.CMvPolynomial.degreeLE n R d}
    (h : (p : CPoly.CMvPolynomial n R) = (q : CPoly.CMvPolynomial n R)) : p = q :=
  Subtype.ext h

open CPoly CMvPolynomial in
private theorem degreeOf_restrictDegree_le [BEq R] [LawfulBEq R]
    (d : Nat) (i : Fin n) (p : CPoly.CMvPolynomial n R) :
    (CPoly.CMvPolynomial.restrictDegree d p).degreeOf i ≤ d := by
  sorry
/-- Canonical bounded-degree wrapper around a raw computable polynomial. -/
def ofCMvPolynomial [BEq R] [LawfulBEq R] (d : ℕ) (p : CPoly.CMvPolynomial n R) :
    CPoly.CMvPolynomial.degreeLE n R d :=
  ⟨CPoly.CMvPolynomial.restrictDegree d p, fun i => degreeOf_restrictDegree_le d i p⟩

instance [BEq R] [LawfulBEq R] : Zero (CPoly.CMvPolynomial.degreeLE n R d) :=
  ⟨ofCMvPolynomial d 0⟩

instance [BEq R] [LawfulBEq R] : OfNat (CPoly.CMvPolynomial.degreeLE n R d) 0 :=
  ⟨0⟩

instance [BEq R] [LawfulBEq R] : Inhabited (CPoly.CMvPolynomial.degreeLE n R d) :=
  ⟨0⟩

section Univariate

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] {d : ℕ}

private def coeffMonomial (k : Fin (d + 1)) : CPoly.CMvMonomial 1 :=
  Vector.ofFn (fun _ => k.val)

/-- Coefficient vector for a bounded-degree computable univariate polynomial. -/
def coeffVec (p : CPoly.CMvPolynomial.degreeLE 1 R d) : Fin (d + 1) → R :=
  fun k => CPoly.CMvPolynomial.coeff (coeffMonomial (d := d) k) (p : CPoly.CMvPolynomial 1 R)

/-- Build a bounded-degree computable univariate polynomial from its coefficient vector. -/
def ofCoeffVec (coeffs : Fin (d + 1) → R) : CPoly.CMvPolynomial.degreeLE 1 R d :=
  ofCMvPolynomial d (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k) (coeffs k))

@[simp] theorem coeffVec_ofCoeffVec (coeffs : Fin (d + 1) → R) :
    coeffVec (ofCoeffVec (R := R) (d := d) coeffs) = coeffs := by
  sorry

@[simp] theorem ofCoeffVec_coeffVec (p : CPoly.CMvPolynomial.degreeLE 1 R d) :
    ofCoeffVec (R := R) (d := d) (coeffVec p) = p := by
  sorry

/-- Bounded-degree computable univariate polynomials are equivalent to coefficient vectors. -/
def coeffEquiv : CPoly.CMvPolynomial.degreeLE 1 R d ≃ (Fin (d + 1) → R) where
  toFun := coeffVec
  invFun := ofCoeffVec (R := R) (d := d)
  left_inv := ofCoeffVec_coeffVec (R := R) (d := d)
  right_inv := coeffVec_ofCoeffVec (R := R) (d := d)

end Univariate

end degreeLE

/-- Stable constructor for the bounded-degree computable carrier. -/
def ofDegreeLE [BEq R] [LawfulBEq R] (d : ℕ) (p : CPoly.CMvPolynomial n R) :
    CPoly.CMvPolynomial.degreeLE n R d :=
  degreeLE.ofCMvPolynomial d p

/-- Computable multilinear polynomials. -/
abbrev multilinear (n : ℕ) (R : Type) [CommSemiring R] : Type _ :=
  CPoly.CMvPolynomial.degreeLE n R 1

/-- Computable multiquadratic polynomials. -/
abbrev multiquadratic (n : ℕ) (R : Type) [CommSemiring R] : Type _ :=
  CPoly.CMvPolynomial.degreeLE n R 2

end CMvPolynomial
end CPoly
