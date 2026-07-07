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
theorem reduction_completeness --(h : init.neverFails)
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn ↔
      (mapStmt stmtIn, mapWit stmtIn witIn) ∈ relOut) :
    (reduction oSpec mapStmt mapWit).perfectCompleteness init impl relIn relOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  have hrun : (reduction oSpec mapStmt mapWit).run stmtIn witIn =
      (pure ((default, (mapStmt stmtIn, mapWit stmtIn witIn)), mapStmt stmtIn) :
        OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run, Prover.runToRound]
    rfl
  simp only [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ support
      (Prod.fst <$> (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨(hRel stmtIn witIn).mp hIn, rfl⟩

/-- The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping
  `mapWitInv` from the output witness to the input witness. -/
def extractor (mapWitInv : StmtIn → WitOut → WitIn) :
    Extractor.RoundByRound oSpec StmtIn WitIn WitOut !p[] (fun _ => WitIn) where
  eqIn := rfl
  extractMid := fun i => Fin.elim0 i
  extractOut := fun stmtIn _ witOut => mapWitInv stmtIn witOut

variable {mapWitInv : StmtIn → WitOut → WitIn}


@[simp]
lemma support_liftM (m : Type _ → Type _) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α} (mx : m α) : support (liftM mx : OptionT m α) = support mx := by
  simp

@[simp]
lemma support_mk (m : Type _ → Type _) [Monad m] [MonadLiftT m SetM]
    {α} (mx : m (Option α)) :
    support (OptionT.mk mx) = {x | some x ∈ support mx} := by
  rfl

/-- The knowledge state function for the `ReduceClaim` reduction. -/
def knowledgeStateFunction (hRel : ∀ stmtIn witOut,
      (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    (verifier oSpec mapStmt).KnowledgeStateFunction
      init impl relIn relOut (extractor mapWitInv) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => ⟨stmtIn, witIn⟩ ∈ relIn
  toFun_empty := fun stmtIn witIn => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun stmtIn _ witOut h => by
    -- Verifier deterministically returns `mapStmt stmtIn`; from positive probability we extract
    -- `(mapStmt stmtIn, witOut) ∈ relOut`, then invoke `hRel` to land in `relIn`.
    simp only [Verifier.run, verifier] at h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure (mapStmt stmtIn) : OptionT (OracleComp oSpec) StmtOut)).run' s =
        pure (some (mapStmt stmtIn)) := by
      change (simulateQ impl
        (pure (some (mapStmt stmtIn)) : OracleComp oSpec (Option StmtOut))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some (mapStmt stmtIn)) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hRel stmtIn witOut hrel

/-- The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
@[simp]
theorem verifier_rbrKnowledgeSoundness (hRel : ∀ stmtIn witOut,
      (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    (verifier oSpec mapStmt).rbrKnowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨_, _, knowledgeStateFunction relIn relOut hRel, ?_⟩
  simp only [ProtocolSpec.ChallengeIdx]
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

/-- The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation.

  Proof strategy mirrors the non-oracle `reduction_completeness`: the prover deterministically
  returns the mapped output, the verifier deterministically computes `mapStmt`, and the
  positive-probability output is exactly the mapped element which lies in `relOut` by `hRel`. -/
@[simp]
theorem oracleReduction_completeness --(h : init.neverFails)
    (hRel : ∀ stmtIn oStmtIn witIn,
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn) ∈ relOut) :
    (oracleReduction oSpec mapStmt mapWit embedIdx hEq).perfectCompleteness init impl
      relIn relOut := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmtIn, oStmtIn⟩ witIn hIn
  -- Reduce the run to a deterministic `pure` of the expected output.
  have hrun : (oracleReduction oSpec mapStmt mapWit embedIdx hEq).toReduction.run
      ⟨stmtIn, oStmtIn⟩ witIn =
      (pure ((default,
          ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
          (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) :
        OptionT (OracleComp _) _) := by
    simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, oracleProver,
      oracleVerifier, OracleVerifier.toVerifier, Prover.run, Verifier.run, Prover.runToRound]
    rfl
  rw [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) : OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ support
      (Prod.fst <$> (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨hRel stmtIn oStmtIn witIn hIn, rfl⟩
  -- -- TODO: clean up this proof
  -- simp only [OracleReduction.perfectCompleteness, oracleReduction, OracleReduction.toReduction,
  --   OracleVerifier.toVerifier,
  --   Reduction.perfectCompleteness_eq_prob_one, ProtocolSpec.ChallengeIdx, StateT.run'_eq,
  --   OracleComp.probEvent_eq_one_iff, OracleComp.probFailure_eq_zero_iff,
  --   OracleComp.neverFails_bind_iff, h, OracleComp.neverFails_map_iff, true_and,
  --   OracleComp.support_bind, OracleComp.support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
  --   exists_and_right, exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall,
  --   Fin.forall_fin_zero_pi, Prod.mk.injEq]
  -- simp only [Reduction.run, Prover.run, Verifier.run, oracleProver, oracleVerifier]
  -- simp only [ProtocolSpec.ChallengeIdx, Fin.reduceLast, Nat.reduceAdd, ProtocolSpec.MessageIdx,
  --   ProtocolSpec.Message, ProtocolSpec.Challenge, Prover.runToRound_zero_of_prover_first,
  --   Fin.isValue, id_eq, bind_pure_comp, map_pure, OracleComp.simulateQ_pure,
  --   Function.Embedding.trans_apply, Function.Embedding.inl_apply, eq_mpr_eq_cast,
  --   OracleComp.liftM_eq_liftComp, OracleComp.liftComp_pure, StateT.run_pure,
  --   OracleComp.neverFails_pure, implies_true, OracleComp.support_pure, Set.mem_singleton_iff,
  --   Prod.mk.injEq, and_imp, true_and]
  -- aesop

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
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ _ witOut => by
    intro h
    simp only [Verifier.run, oracleVerifier, OracleVerifier.toVerifier] at h
    change ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    -- The oracle verifier deterministically returns the pair
    -- `(mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)`, so the simulated run is definitionally
    -- `pure (some ...)` and positive probability forces `x` to equal that pair.
    have hxc : some x ∈ support ((simulateQ impl
        (pure (some (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) :
          OracleComp oSpec (Option (StmtOut × (∀ i, OStmtOut i))))).run' s) := hx
    rw [simulateQ_pure] at hxc
    change some x ∈ support (Prod.fst <$> (pure
      (some (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) : StateT σ ProbComp _).run s) at hxc
    rw [StateT.run_pure] at hxc
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hxc
    cases (Option.some.inj hxc)
    exact hRel stmtIn oStmtIn witOut hrel

/-- The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness (hRel : ∀ stmtIn oStmtIn witOut,
      ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifier oSpec mapStmt embedIdx hEq).rbrKnowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨_, _, oracleKnowledgeStateFunction relIn relOut hRel, ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

end OracleReduction

end ReduceClaim
