/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

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

variable [oSpec.FiniteRange] (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))

/-- The `ReduceClaim` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_completeness (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn ↔
    (mapStmt stmtIn, mapWit witIn) ∈ relOut) :
    (reduction oSpec mapStmt mapWit).perfectCompleteness
      relIn relOut := by
  simp [reduction, Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    prover, verifier, hRel]

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

variable [oSpec.FiniteRange]
  (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))

/-- The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem oracleReduction_completeness (hRel : ∀ stmtIn oStmtIn witIn,
    ((stmtIn, oStmtIn), witIn) ∈ relIn ↔
    ((mapStmt stmtIn, fun i => (hEq i) ▸ oStmtIn (embedIdx i)), mapWit witIn) ∈ relOut) :
    (oracleReduction oSpec mapStmt mapWit embedIdx hEq).perfectCompleteness
      relIn relOut := by
  sorry

-- TODO: round-by-round knowledge soundness

end OracleReduction

end ReduceClaim
