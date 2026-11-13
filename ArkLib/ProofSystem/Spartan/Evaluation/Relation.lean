/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Realization

/-!
# Spartan row-evaluation claims

The scalar check retains the equality factor, including when it vanishes. The output relation
asserts the three row evaluations; the scalar check alone does not establish those assertions.
-/

@[expose] public section

namespace Spartan.Evaluation

open MvPolynomial Realization

variable {R : Type} [CommRing R] (pp : PublicParams)

/-- The three honest row-product evaluations, computed from the retained tables. -/
def values (stmt : Statement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) : R1CS.MatrixIdx → R :=
  fun i => rowEval (oracles (.inl i)) (R1CS.𝕫 stmt.x (oracles (.inr 0))) stmt.r_x

/-- The first virtual polynomial has the claimed terminal value. -/
def inputRelation (stmt : Statement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) : Prop :=
  eval stmt.r_x (Algebra.firstVirtual (fun i => oracles (.inl i))
    (R1CS.𝕫 stmt.x (oracles (.inr 0))) stmt.τ) = stmt.e

/-- The scalar equation checked when the three values are sent. -/
def check (stmt : Statement (R := R) pp) (v : R1CS.MatrixIdx → R) : Prop :=
  eqWeight stmt.τ stmt.r_x * (v .A * v .B - v .C) = stmt.e

instance [DecidableEq R] (stmt : Statement (R := R) pp) (v : R1CS.MatrixIdx → R) :
    Decidable (check pp stmt v) := inferInstanceAs (Decidable (_ = _))

/-- Each sent value is the evaluation of its original row-product polynomial. -/
def outputRelation (stmt : Statement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) (v : R1CS.MatrixIdx → R) : Prop :=
  ∀ i, v i = eval stmt.r_x
    (Algebra.rowProduct (oracles (.inl i)) (R1CS.𝕫 stmt.x (oracles (.inr 0))))

/-- Honest row values satisfy the output relation. -/
theorem values_correct (stmt : Statement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) :
    outputRelation pp stmt oracles (values pp stmt oracles) := by
  intro i
  exact rowEval_eq _ _ _

/-- Substituting honest row values identifies the scalar check with the first terminal claim. -/
theorem check_values_iff (stmt : Statement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) :
    check pp stmt (values pp stmt oracles) ↔ inputRelation pp stmt oracles := by
  change firstEval (fun i => oracles (.inl i))
    (R1CS.𝕫 stmt.x (oracles (.inr 0))) stmt.τ stmt.r_x = stmt.e ↔ _
  exact (congrArg (fun v : R => v = stmt.e)
    (firstVirtual_realizes (fun i => oracles (.inl i))
      (R1CS.𝕫 stmt.x (oracles (.inr 0))) stmt.τ stmt.r_x)).to_iff

/-- A passing scalar check and true row claims recover the first terminal claim. -/
theorem inputRelation_of_check (stmt : Statement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) (v : R1CS.MatrixIdx → R)
    (hc : check pp stmt v) (hv : outputRelation pp stmt oracles v) :
    inputRelation pp stmt oracles := by
  have heq : v = values pp stmt oracles := by
    funext i
    exact (hv i).trans (rowEval_eq _ _ _).symm
  exact (check_values_iff pp stmt oracles).1 (heq ▸ hc)

end Spartan.Evaluation
