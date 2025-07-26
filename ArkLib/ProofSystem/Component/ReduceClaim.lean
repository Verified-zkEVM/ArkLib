/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Simple (Oracle) Reduction: Locally / non-interactively reduce a claim

  This is a zero-round (oracle) reduction.

  1. Reduction version: there are mappings between `StmtIn → StmtOut` and `WitIn → WitOut`. The
     prover and verifier applies these mappings to the input statement and witness, and returns the
     output statement and witness.

  This reduction is secure via pull-backs on relations. In other words, the outputs of the reduction
  satisfies some relation `relOut` if and only if the inputs satisfy the relation
  `relIn := relOut (mapStmt ·) (mapWit ·)`.

  2. Oracle reduction version: same as above, but with the extra mapping `OStmtIn → OStmtOut`,
     defined as an oracle simulation / embedding.

  This oracle reduction is secure via pull-backs on relations. In other words, the outputs of the
  reduction satisfies some relation `relOut` if and only if the inputs satisfy the relation
  `relIn := relOut ((mapStmt ·) ⊗ (mapOStmt ·)) (mapWit ·)`.
-/

namespace ReduceClaim

variable {ι : Type} (oSpec : OracleSpec ι)
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)]
  (mapStmt : StmtIn → StmtOut) (mapWit : WitIn → WitOut)

section Reduction

/-- The prover for the `ReduceClaim` reduction. -/
def prover : Prover oSpec StmtIn WitIn StmtOut WitOut ![] where
  PrvState | 0 => StmtIn × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨stmt, wit⟩ => (mapStmt stmt, mapWit wit)

/-- The verifier for the `ReduceClaim` reduction. -/
def verifier : Verifier oSpec StmtIn StmtOut ![] where
  verify := fun stmt _ => pure (mapStmt stmt)

/-- The reduction for the `ReduceClaim` reduction. -/
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut ![] where
  prover := prover oSpec mapStmt mapWit
  verifier := verifier oSpec mapStmt

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))

/-- The `ReduceClaim` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_completeness (h : init.neverFails)
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn ↔
      (mapStmt stmtIn, mapWit witIn) ∈ relOut) :
    (reduction oSpec mapStmt mapWit).perfectCompleteness init impl relIn relOut := by
  simp [reduction, Reduction.run, Prover.run, Prover.runToRound, Verifier.run,
    prover, verifier, hRel, h]
  aesop

-- TODO: round-by-round knowledge soundness

end Reduction

section OracleReduction

variable
  -- Require map on indices to go the other way
  (embedIdx : ιₛₒ ↪ ιₛᵢ) (hEq : ∀ i, OStmtIn (embedIdx i) = OStmtOut i)

/-- The oracle prover for the `ReduceClaim` oracle reduction. -/
def oracleProver : OracleProver oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut ![] where
  PrvState := fun _ => (StmtIn × (∀ i, OStmtIn i)) × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ =>
    ((mapStmt stmt, fun i => (hEq i) ▸ oStmt (embedIdx i)), mapWit wit)

/-- The oracle verifier for the `ReduceClaim` oracle reduction. -/
def oracleVerifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut ![] where
  verify := fun stmt _ => pure (mapStmt stmt)
  embed := .trans embedIdx .inl
  hEq := by intro i; simp [hEq]

/-- The oracle reduction for the `ReduceClaim` oracle reduction. -/
def oracleReduction : OracleReduction oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut ![] where
  prover := oracleProver oSpec mapStmt mapWit embedIdx hEq
  verifier := oracleVerifier oSpec mapStmt embedIdx hEq

variable {oSpec} {mapStmt} {mapWit} {embedIdx} {hEq}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))

/-- The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem oracleReduction_completeness (h : init.neverFails)
    (hRel : ∀ stmtIn oStmtIn witIn,
      ((stmtIn, oStmtIn), witIn) ∈ relIn ↔
      ((mapStmt stmtIn, fun i => (hEq i) ▸ oStmtIn (embedIdx i)), mapWit witIn) ∈ relOut) :
    (oracleReduction oSpec mapStmt mapWit embedIdx hEq).perfectCompleteness init impl
      relIn relOut := by
  -- TODO: clean up this proof
  simp only [OracleReduction.perfectCompleteness, oracleReduction, OracleReduction.toReduction,
    OracleVerifier.toVerifier,
    Reduction.perfectCompleteness_eq_prob_one, ProtocolSpec.ChallengeIdx, StateT.run'_eq,
    OracleComp.probEvent_eq_one_iff, OracleComp.probFailure_eq_zero_iff,
    OracleComp.neverFails_bind_iff, h, OracleComp.neverFails_map_iff, true_and,
    OracleComp.support_bind, OracleComp.support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
    exists_and_right, exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall,
    Fin.forall_fin_zero_pi, Prod.mk.injEq]
  simp only [Reduction.run, Prover.run, Verifier.run, oracleProver, oracleVerifier]
  simp only [ProtocolSpec.ChallengeIdx, Fin.reduceLast, Nat.reduceAdd, ProtocolSpec.MessageIdx,
    ProtocolSpec.Message, ProtocolSpec.Challenge, Prover.runToRound_zero_of_prover_first,
    Fin.isValue, id_eq, bind_pure_comp, map_pure, OracleComp.simulateQ_pure,
    Function.Embedding.trans_apply, Function.Embedding.inl_apply, eq_mpr_eq_cast,
    OracleComp.liftM_eq_liftComp, OracleComp.liftComp_pure, StateT.run_pure,
    OracleComp.neverFails_pure, implies_true, OracleComp.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, and_imp, true_and]
  aesop

-- TODO: round-by-round knowledge soundness

end OracleReduction

end ReduceClaim
