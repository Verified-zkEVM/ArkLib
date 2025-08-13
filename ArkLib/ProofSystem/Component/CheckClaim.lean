/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

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

  Note: after the refactor (to disallow failure in `OracleComp`), this may become a special case
  of `ReduceClaim`.
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace CheckClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

/-- The prover for the `CheckClaim` reduction. -/
@[inline, specialize]
def prover : Prover oSpec Statement Unit Statement Unit !p[] where
  PrvState := fun _ => Statement
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

variable (pred : Statement → Prop) [DecidablePred pred]

/-- The verifier for the `CheckClaim` reduction. -/
@[inline, specialize]
def verifier : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => do guard (pred stmt); return stmt

/-- The reduction for the `CheckClaim` reduction. -/
@[inline, specialize]
def reduction : Reduction oSpec Statement Unit Statement Unit !p[] where
  prover := prover oSpec Statement
  verifier := verifier oSpec Statement pred

@[reducible, simp]
def relIn : Set (Statement × Unit) := { ⟨stmt, _⟩ | pred stmt }

@[reducible, simp]
def relOut : Set (Statement × Unit) := Set.univ

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the
  input relation, and the output relation being always true. -/
@[simp]
theorem reduction_completeness (h : init.neverFails) [Nonempty σ] :
    (reduction oSpec Statement pred).perfectCompleteness init impl
    (relIn Statement pred) (relOut Statement) := by
  -- Don't know why we need `Nonempty σ` here. TODO: figure out why
  simp only [reduction, Reduction.perfectCompleteness_eq_prob_one,
    Reduction.run, Prover.run, Prover.runToRound, Verifier.run,
    prover, verifier]
  intro stmt wit valid
  simp
  aesop

/-- The `CheckClaim` reduction satisfies perfect round-by-round knowledge soundness. -/
theorem verifier_rbr_knowledge_soundness :
    (verifier oSpec Statement pred).rbrKnowledgeSoundness init impl
      (relIn Statement pred) (relOut Statement) 0 := by
  simp only [Verifier.rbrKnowledgeSoundness, Nat.reduceAdd, relIn, relOut, verifier, guard_eq,
    ChallengeIdx, Challenge, liftComp_query, OracleSpec.SubSpec.liftM_query_eq_liftM_liftM,
    OracleSpec.liftM_append_right_eq, bind_pure_comp, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind, comp_apply, simulateQ_map, simulateQ_query, StateT.run_map, map_bind,
    Functor.map_map, Pi.zero_apply, ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff,
    support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right,
    exists_prop, not_exists, not_and, forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq,
    IsEmpty.forall_iff, implies_true, exists_const_iff, and_true]
  sorry

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

/-- The oracle prover for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  PrvState := fun _ => Statement × (∀ i, OStatement i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

variable (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
  (hPred : ∀ stmt, (pred stmt).neverFails)

/-- The oracle verifier for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement OStatement !p[] where
  verify := fun stmt _ => do let _ ← pred stmt; return stmt
  embed := Embedding.inl
  hEq := by intro i; simp

/-- The oracle reduction for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement pred

variable {Statement} {OStatement}

@[reducible, simp]
def toRelInput : Set ((Statement × (∀ i, OStatement i)) × Unit) :=
  { ⟨⟨stmt, oStmt⟩, _⟩ | simulateQ' (toOracleImpl OStatement oStmt) (pred stmt) (hPred stmt) }

-- theorem oracleProver_run

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `CheckClaim` reduction satisfies perfect completeness. -/
@[simp]
theorem oracleReduction_completeness (h : init.neverFails) :
    (oracleReduction oSpec Statement OStatement pred).perfectCompleteness init impl
    (toRelInput pred hPred) Set.univ := by
  -- TODO: fix this proof once `OracleComp` no longer has failure
  simp only [OracleReduction.perfectCompleteness, toRelInput, OracleReduction.toReduction,
    oracleReduction, oracleProver, Nat.reduceAdd, Fin.isValue, MessageIdx, Message, ChallengeIdx,
    Challenge, Fin.reduceLast, oracleVerifier, bind_pure_comp, OracleVerifier.toVerifier,
    simulateQ_map, Embedding.inl_apply, eq_mpr_eq_cast, cast_eq, Functor.map_map,
    Reduction.perfectCompleteness_eq_prob_one, Set.mem_setOf_eq, StateT.run'_eq, Set.mem_univ,
    true_and, probEvent_eq_one_iff, probFailure_eq_zero_iff, neverFails_bind_iff, h,
    neverFails_map_iff, support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
    exists_and_right, exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall,
    Fin.forall_fin_zero_pi, Prod.mk.injEq]
  simp only [Reduction.run, Prover.run, Verifier.run, toOracleImpl, simulateQ']
  simp only [ChallengeIdx, Fin.reduceLast, Prover.runToRound_zero_of_prover_first, Fin.isValue,
    bind_pure_comp, liftM_eq_liftComp, liftComp_map, Functor.map_map, pure_bind]
  intro stmt oStmt _
  sorry
  -- simp [Reduction.run, Prover.run, Verifier.run, simOracle2]
  -- aesop

theorem oracleReduction_rbr_knowledge_soundness : True := sorry

end OracleReduction

end CheckClaim
