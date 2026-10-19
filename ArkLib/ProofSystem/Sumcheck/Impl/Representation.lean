/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Univariate.ToPoly.Impl
public import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound

/-!
# Computable Sumcheck round messages

The actual message is a canonical coefficient array with a degree proof. Runtime queries use
Horner evaluation. Conversion to the mathematical polynomial is solely its specification map.
-/

@[expose] public section

namespace Sumcheck.Impl.Representation

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- A bounded computable univariate polynomial, including the zero polynomial. -/
abbrev Message := {p : CompPoly.CPolynomial R // p.degree ≤ (deg : WithBot ℕ)}

/-- Evaluation of the actual coefficient array by Horner's algorithm. -/
def evaluate (q : Message R deg) (x : R) : R := q.val.evalHorner x

variable [BEq R] [LawfulBEq R]

/-- Proof-only interpretation as the existing degree-bounded mathematical message. -/
noncomputable def toMessage (q : Message R deg) : Interaction.SingleRound.Message R deg :=
  ⟨q.val.toPoly, by
    apply Polynomial.mem_degreeLE.mpr
    rw [← CompPoly.CPolynomial.degree_toPoly]
    exact q.property⟩

/-- The runtime answer is exactly the answer of the mathematical interpretation. -/
theorem evaluate_eq (q : Message R deg) (x : R) :
    evaluate R deg q x = (toMessage R deg q).val.eval x := by
  exact (CompPoly.CPolynomial.eval_horner_eq_eval x q.val).trans
    (CompPoly.CPolynomial.eval_toPoly x q.val)

end Sumcheck.Impl.Representation
