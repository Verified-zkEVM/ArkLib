/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Simple (Oracle) Reduction: Locally / non-interactively reduce a claim

  This is a zero-round (oracle) reduction.

  1. Reduction version: there are mappings between `StmtIn → StmtOut` and `StmtIn → WitIn → WitOut`.
     Note the second mapping between witnesses may depend on the input statement as well. The prover
     and verifier applies these mappings to the input statement and witness, and returns the output
     statement and witness.

  This reduction is secure via pull-backs on relations. What this means is as follows:
  - Completeness holds if for the outputs of the reduction satisfies some relation `relOut` whenever
    the inputs satisfy the relation `relIn := relOut (mapStmt ·) (mapWit ·)`
  - (Round-by-round) knowledge soundness holds if there exists an inverse mapping
    `StmtIn → WitOut → WitIn` on witnesses (for extraction) such that
    `(mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn`.

  2. Oracle reduction version: same as above, but with the extra mapping `OStmtIn → OStmtOut`,
     defined as an oracle simulation / embedding.

  This oracle reduction is secure via pull-backs on relations, similar to the reduction version,
  except that `mapStmt` is replaced by `mapStmt ⊗ mapOStmt`.
-/

namespace ReduceClaim

variable {ι : Type} (oSpec : OracleSpec ι)
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)]
  (mapStmt : StmtIn → StmtOut) (mapWit : StmtIn → WitIn → WitOut)

section Reduction

/-- The prover for the `ReduceClaim` reduction. -/
def prover : Prover oSpec StmtIn WitIn StmtOut WitOut !p[] where
  PrvState | 0 => StmtIn × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨stmt, wit⟩ => pure (mapStmt stmt, mapWit stmt wit)

/-- The verifier for the `ReduceClaim` reduction. -/
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => pure (mapStmt stmt)

/-- The reduction for the `ReduceClaim` reduction. -/
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut !p[] where
  prover := prover oSpec mapStmt mapWit
  verifier := verifier oSpec mapStmt

variable {oSpec} {mapStmt} {mapWit}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))

/-- The `ReduceClaim` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_completeness (h : init.neverFails)
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn ↔
      (mapStmt stmtIn, mapWit stmtIn witIn) ∈ relOut) :
    (reduction oSpec mapStmt mapWit).perfectCompleteness init impl relIn relOut := by
  simp [reduction, Reduction.run, Prover.run, Prover.runToRound, Verifier.run,
    prover, verifier, hRel, h]
  aesop

/-- The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping
  `mapWitInv` from the output witness to the input witness. -/
def extractor (mapWitInv : StmtIn → WitOut → WitIn) :
    Extractor.RoundByRound oSpec StmtIn WitIn WitOut !p[] (fun _ => WitIn) where
  eqIn := rfl
  extractMid := fun i => Fin.elim0 i
  extractOut := fun stmtIn _ witOut => mapWitInv stmtIn witOut

variable {mapWitInv : StmtIn → WitOut → WitIn}

/-- The knowledge state function for the `ReduceClaim` reduction. -/
def knowledgeStateFunction (hRel : ∀ stmtIn witOut,
      (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    (verifier oSpec mapStmt).KnowledgeStateFunction
      init impl relIn relOut (extractor mapWitInv) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => ⟨stmtIn, witIn⟩ ∈ relIn
  toFun_empty := fun stmtIn witIn => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun stmtIn _ witOut h => by simp_all [extractor, Verifier.run, verifier]

/-- The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
@[simp]
theorem verifier_rbrKnowledgeSoundness (hRel : ∀ stmtIn witOut,
      (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    (verifier oSpec mapStmt).rbrKnowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨_, _, knowledgeStateFunction relIn relOut hRel, ?_⟩
  simp only [ProtocolSpec.ChallengeIdx, Matrix.vecEmpty]
  exact fun _ _ _ i => Fin.elim0 i.1

end Reduction

section OracleReduction

variable
  -- Require map on indices to go the other way
  (embedIdx : ιₛₒ ↪ ιₛᵢ) (hEq : ∀ i, OStmtIn (embedIdx i) = OStmtOut i)

@[reducible, simp]
def mapOStmt (oStmtIn : ∀ i, OStmtIn i) : ∀ i, OStmtOut i := fun i => (hEq i) ▸ oStmtIn (embedIdx i)

/-- The oracle prover for the `ReduceClaim` oracle reduction. -/
def oracleProver : OracleProver oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut !p[] where
  PrvState := fun _ => (StmtIn × (∀ i, OStmtIn i)) × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ =>
    pure ((mapStmt stmt, mapOStmt embedIdx hEq oStmt), mapWit stmt wit)

/-- The oracle verifier for the `ReduceClaim` oracle reduction. -/
def oracleVerifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut !p[] where
  verify := fun stmt _ => pure (mapStmt stmt)
  embed := .trans embedIdx .inl
  hEq := by intro i; simp [hEq]

/-- The oracle reduction for the `ReduceClaim` oracle reduction. -/
def oracleReduction : OracleReduction oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut !p[] where
  prover := oracleProver oSpec mapStmt mapWit embedIdx hEq
  verifier := oracleVerifier oSpec mapStmt embedIdx hEq

variable {oSpec} {mapStmt} {mapWit} {embedIdx} {hEq}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))

/-- The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem oracleReduction_completeness (h : init.neverFails)
    (hRel : ∀ stmtIn oStmtIn witIn,
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn) ∈ relOut) :
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

variable {mapWitInv : (StmtIn × (∀ i, OStmtIn i)) → WitOut → WitIn}

/-- The knowledge state function for the `ReduceClaim` oracle reduction. -/
def oracleKnowledgeStateFunction (hRel : ∀ stmtIn oStmtIn witOut,
      ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifier oSpec mapStmt embedIdx hEq).KnowledgeStateFunction
      init impl relIn relOut (extractor mapWitInv) where
  toFun | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn⟩ _ witIn => ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ ∈ relIn
  toFun_empty := fun stmtIn witIn => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ _ witOut h => by
    simp_all [Verifier.run, oracleVerifier, OracleVerifier.toVerifier]
    aesop

/-- The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness (hRel : ∀ stmtIn oStmtIn witOut,
      ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifier oSpec mapStmt embedIdx hEq).rbrKnowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨_, _, oracleKnowledgeStateFunction relIn relOut hRel, ?_⟩
  simp only [ProtocolSpec.ChallengeIdx, Matrix.vecEmpty]
  exact fun _ _ _ i => Fin.elim0 i.1

end OracleReduction

end ReduceClaim
