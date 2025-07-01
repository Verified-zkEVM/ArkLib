/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Simple (Oracle) Reduction: Check if a predicate / claim on a statement is satisfied

  This is a zero-round (oracle) reduction. There is no witness.

  1. Reduction version: the input relation becomes a predicate on the statement. Verifier checks
     this predicate, and returns the same statement if successful.

  2. Oracle reduction version: the input relation becomes an oracle computation having as oracles
     the oracle statements, and taking in the (non-oracle) statement as an input (i.e. via
     `ReaderT`), and returning a `Prop`. Verifier performs this oracle computation, and returns the
     same statement & oracle statement if successful.

  In both cases, the output relation is trivial (since the input relation has been checked by the
  verifier).
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace CheckClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

/-- The prover for the `CheckClaim` reduction. -/
@[inline, specialize]
def prover : Prover oSpec Statement Unit Statement Unit ![] where
  PrvState := fun _ => Statement
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => (stmt, ())

variable (pred : Statement → Prop) [DecidablePred pred]

/-- The verifier for the `CheckClaim` reduction. -/
@[inline, specialize]
def verifier : Verifier oSpec Statement Statement ![] where
  verify := fun stmt _ => do guard (pred stmt); return stmt

/-- The reduction for the `CheckClaim` reduction. -/
@[inline, specialize]
def reduction : Reduction oSpec Statement Unit Statement Unit ![] where
  prover := prover oSpec Statement
  verifier := verifier oSpec Statement pred

variable [oSpec.FiniteRange]

/-- The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the
  input relation, and the output relation being always true. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement pred).perfectCompleteness { ⟨stmt, _⟩ | pred stmt }
    Set.univ := by
  simp [reduction, Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    prover, verifier]

/-- The `CheckClaim` reduction satisfies perfect round-by-round knowledge soundness. -/
theorem reduction_rbr_knowledge_soundness : True := sorry

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

/-- The oracle prover for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit Statement OStatement Unit ![] where
  PrvState := fun _ => Statement × (∀ i, OStatement i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => (stmt, ())

variable (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
  (hPred : ∀ stmt, (pred stmt).neverFails)

/-- The oracle verifier for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement OStatement ![] where
  verify := fun stmt _ => do let _ ← pred stmt; return stmt
  embed := Embedding.inl
  hEq := by intro i; simp

/-- The oracle reduction for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit Statement OStatement Unit ![] where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement pred

variable {Statement} {OStatement}

def toRelInput : Set ((Statement × (∀ i, OStatement i)) × Unit) :=
  { ⟨⟨stmt, oStmt⟩, _⟩ | simulateQ' (toOracleImpl OStatement oStmt) (pred stmt) (hPred stmt) }

-- theorem oracleProver_run

variable [oSpec.FiniteRange]

/-- The `CheckClaim` reduction satisfies perfect completeness. -/
@[simp]
theorem oracleReduction_completeness :
    (oracleReduction oSpec Statement OStatement pred).perfectCompleteness (toRelInput pred hPred)
    Set.univ := by
  simp [OracleReduction.perfectCompleteness, OracleReduction.toReduction, OracleVerifier.toVerifier,
    oracleReduction, oracleProver, oracleVerifier, toRelInput]
  simp [Reduction.run, Prover.run, Verifier.run, simOracle2]
  sorry

theorem oracleReduction_rbr_knowledge_soundness : True := sorry

end OracleReduction

end CheckClaim
