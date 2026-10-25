/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Univariate.ToPoly.Impl
public import ArkLib.ToCompPoly.Univariate.Raw.Horner
public import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
-- The bridge unfolds only the package canonical-to-raw mathematical interpretation.
import all CompPoly.Univariate.ToPoly.Core

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
def evaluate (q : Message R deg) (x : R) : R :=
  CompPoly.CPolynomial.Raw.evalHornerSeeded x q.val.val

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
  rw [evaluate, CompPoly.CPolynomial.Raw.evalHornerSeeded_eq_evalHorner,
    CompPoly.CPolynomial.Raw.evalHorner_eq_eval]
  exact (CompPoly.CPolynomial.Raw.eval_toPoly_eq_eval x q.val.val).symm

end Sumcheck.Impl.Representation
