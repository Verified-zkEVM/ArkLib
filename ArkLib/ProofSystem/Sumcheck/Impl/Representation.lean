/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Univariate.ToPoly.Impl
public import CompPoly.Data.MvPolynomial.Notation

/-!
# Computable Sumcheck round messages

The actual message is a canonical coefficient array with a degree proof. Runtime queries use
Horner evaluation. The mathematical polynomial is reconstructed from its explicit coefficient
support, so both representations can be produced at runtime.
-/

@[expose] public section

namespace Sumcheck.Impl.Representation

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- A bounded computable univariate polynomial, including the zero polynomial. -/
abbrev Message := {p : CompPoly.CPolynomial R // p.degree ≤ (deg : WithBot ℕ)}

/-- Evaluation of the actual coefficient array by Horner's algorithm. -/
def evaluate (q : Message R deg) (x : R) : R := q.val.evalHorner x

variable [BEq R] [LawfulBEq R]

/-- Convert the coefficient array to the degree-bounded mathematical message. -/
def toMessage (q : Message R deg) : Polynomial.degreeLE R deg :=
  let p : Polynomial R := .ofFinsupp (.ofCoeff {
    support := q.val.support
    toFun := q.val.coeff
    mem_support_toFun := CompPoly.CPolynomial.mem_support_iff q.val })
  have hp : p = q.val.toPoly := by
    ext i
    exact CompPoly.CPolynomial.coeff_toPoly q.val i
  ⟨p, by
    rw [hp]
    apply Polynomial.mem_degreeLE.mpr
    rw [← CompPoly.CPolynomial.degree_toPoly]
    exact q.property⟩

/-- Conversion preserves the coefficient-array interpretation. -/
theorem toMessage_val (q : Message R deg) : (toMessage R deg q).val = q.val.toPoly := by
  ext i
  exact CompPoly.CPolynomial.coeff_toPoly q.val i

/-- The runtime answer is exactly the answer of the mathematical interpretation. -/
theorem evaluate_eq (q : Message R deg) (x : R) :
    evaluate R deg q x = (toMessage R deg q).val.eval x := by
  rw [toMessage_val]
  exact (CompPoly.CPolynomial.eval_horner_eq_eval x q.val).trans
    (CompPoly.CPolynomial.eval_toPoly x q.val)

end Sumcheck.Impl.Representation
