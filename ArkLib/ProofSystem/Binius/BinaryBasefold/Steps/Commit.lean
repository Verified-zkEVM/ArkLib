/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

section CommitStep

def commitPrvState (i : Fin ℓ) : Fin (1 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  | ⟨1, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

def getCommitProverFinalOutput (i : Fin ℓ)
    (inputPrvState : commitPrvState (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 0) :
  (↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩) → L) ×
  commitPrvState (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 1 :=
  let (stmtIn, oStmtIn, witIn) := inputPrvState
  let fᵢ_succ := witIn.f
  let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (oStmtIn := oStmtIn) (newOracleFn := fᵢ_succ) (h_destIdx := by rfl)
    -- The only thing the prover does is to sends f_{i+1} as an oracle
  (fᵢ_succ, (stmtIn, oStmtOut, witIn))

/-! The prover for the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  PrvState := commitPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun inputPrvState => by
    let res := getCommitProverFinalOutput 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i inputPrvState
    exact pure res
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  output := fun ⟨stmt, oStmt, wit⟩ => by
    exact pure ⟨⟨stmt, oStmt⟩, wit⟩

/-! The oracle verifier for the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn _pSpecChallenges => do
    pure stmtIn
  embed := (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i hCR).embed
  hEq := (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i hCR).hEq

/-! The oracle reduction that is the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleReduction (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  prover := commitOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  verifier := commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i hCR

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-!
Perfect completeness for the commit step oracle reduction.

This theorem proves that the honest prover-verifier interaction for the commit step
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
The proof follows the same pattern as `foldOracleReduction_perfectCompleteness`:
1. Unroll the 1-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes (trivial - no verification)
4. For correctness: apply the logic completeness lemma

**Key Difference from Fold Step:**
- No challenges (1-message protocol)
- No verification check
- Just extends the oracle with the new function
-/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
theorem commitOracleReduction_perfectCompleteness (hInit : NeverFail init) (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (oracleReduction := commitOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i hCR)
      (init := init)
      (impl := impl) := by
  -- Step 1: Unroll the 1-message reduction
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (oSpec := []ₒ)
    (hInit := hInit) (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [commitOracleReduction]
  let step := (commitStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (mp := mp) i (hCR := hCR))
  let strongly_complete : step.IsStronglyComplete := commitStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (i := i) (hCR := hCR)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    dsimp only [commitOracleProver, commitOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk1]
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro r_i' h_r_i'_mem_query_1_support
    conv =>
      enter [2];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, bind_pure_comp, liftComp_eq_liftM, OptionT.mem_support_iff,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, Prod.mk.eta, probFailure_eq_zero,
        implies_true]
    rw [and_true]
    -- erw [OptionT.probFailure_mk]
    -- simp only [ChallengeIdx, Challenge, MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero,
    --       -- simp only [probOutput_eq_zero_iff]
    -- rw [OptionT.support_run_eq]
    -- rw [OptionT.probOutput_none_bind_eq_zero_iff]
    simp only [bind_pure_comp]
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1];
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, MessageIdx,
        OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    simp_all only
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    conv at h_vStmtOut_mem_support =>
      -- erw [simulateQ_bind]
      -- turn the simulated oracle query into OracleInterface.answer form
      -- rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      -- change vStmtOut ∈ (Bind.bind (m := (OracleComp []ₒ)) _ _).support
      -- erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      -- simp  [bind_pure_comp,
      -- OptionT.simulateQ_map, OptionT.simulateQ_ite, OptionT.simulateQ_pure,
      -- OptionT.support_map_run, OptionT.support_ite_run, support_pure,
      -- OptionT.support_failure_run, Set.mem_image, Set.mem_ite_empty_right,
      -- Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]
      -- rw [bind_pure_comp]
      dsimp only [Functor.map]
      -- rw [OptionT.simulateQ_bind]
      -- erw [support_bind]
      -- rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
      simp only [show OptionT.pure (m := (OracleComp ([]ₒ +
        ([OracleStatement 𝔽q β ϑ i.castSucc]ₒ + [pSpecFold.Message]ₒ)))) = pure by rfl]
      simp only [support_pure, Set.mem_singleton_iff]
    simp only [show OptionT.pure (m := (OracleComp ([]ₒ))) = pure by rfl]
    rw [h_vStmtOut_mem_support]
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, OptionT.run_pure, probOutput_eq_zero_iff, support_pure,
      Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [
      support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Prod.exists
    ] at hx_mem_support
    conv at hx_mem_support =>
      erw [OptionT.support_mk, support_pure]
      simp only [
        Set.mem_singleton_iff, Option.some.injEq, Set.setOf_eq_eq_singleton, Prod.mk.injEq,
        OptionT.mem_support_iff,
        OptionT.run_monadLift, support_map, Set.mem_image, exists_eq_right, Fin.succ_one_eq_two,
        id_eq, guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
      dsimp only [monadLift, MonadLift.monadLift]
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, Fin.reduceLast, liftComp_eq_liftM] at hx_mem_support
    obtain ⟨newOracleFn, lastPrvState, h_prvFinalState_eq,
      ⟨h_prvOut_mem_support, h_verOut_mem_support⟩⟩ := hx_mem_support
    conv at h_prvFinalState_eq =>
      dsimp only [getCommitProverFinalOutput, commitOracleProver]
      rw [Prod.mk.injEq]
    conv at h_prvOut_mem_support =>
      dsimp only [commitOracleProver, commitOracleVerifier, OracleVerifier.toVerifier,
        FullTranscript.mk1]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [liftComp_id]
      rw [support_liftComp]
      simp only [h_prvFinalState_eq, Fin.val_succ, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq]
    conv at h_verOut_mem_support =>
      dsimp only [commitOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk1]
      erw [_root_.simulateQ_pure]
      simp only [show OptionT.pure (m := (OracleComp ([]ₒ +
        ([OracleStatement 𝔽q β ϑ i.castSucc]ₒ + [pSpecFold.Message]ₒ)))) = pure by rfl]
      simp only [support_pure, Set.mem_singleton_iff]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      simp only [support_pure, Set.mem_singleton_iff, Function.comp_apply,
        Set.iUnion_iUnion_eq_left, OptionT.support_OptionT_pure_run, Option.some.injEq,
        Prod.mk.injEq]
      erw [support_pure]
      simp only [Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq]
      -- pure equalities now
    -- Step 2e: Apply the logic completeness lemma
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn)
       (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecCommit] at hj
        cases j using Fin.cases
        case zero => simp at hj
        case succ j' => exact j'.elim0
      )
    obtain ⟨newOracleFn_eq, lastPrvState_eq⟩ := h_prvFinalState_eq
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_mem_support
    obtain ⟨verStmtOut_eq, verOStmtOut_eq⟩ := h_verOut_mem_support
    -- Step 2f: Simplify the verifier check
    -- simp only [commitStepLogic] at h_V_check
    -- unfold FullTranscript.mk1 at h_V_check
    simp only [Fin.isValue] at h_V_check
    rw [
      -- lastPrvState_eq,
      prvStmtOut_eq, prvOStmtOut_eq, prvWitOut_eq,
      verStmtOut_eq, verOStmtOut_eq,
    ]
    constructor
    · rw [newOracleFn_eq]
      exact h_rel
    · constructor
      · rfl -- or `exact h_agree.1`
      · rw [newOracleFn_eq]
        exact h_agree.2

open scoped NNReal

def commitKnowledgeError {i : Fin ℓ}
    (m : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, hj⟩ => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_P_to_V_eq_V_to_P] at hj -- not a V challenge

/-! The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def commitRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

/-! Note : stmtIn and witMid already advances to state `(i+1)` from the fold step,
while oStmtIn is not. -/
def commitKStateProp (i : Fin ℓ) (m : Fin (1 + 1))
  (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc i_1)
  (tr : Transcript m (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
  : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut: use transcript message as oracle (what verifier sees)
    -- The verifier sees tr.messages ⟨0, rfl⟩ as the new oracle, not witMid.f
    let newOracle := tr.messages ⟨0, rfl⟩
    let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (newOracleFn := newOracle) (h_destIdx := by rfl)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtOut)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)

/-! Knowledge state function (KState) for single round -/
def commitKState (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp)
      i hCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    commitKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
      (tr := tr) (mp:=mp)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    -- commitKStateProp 0 = foldStepRelOutProp i (same masterKStateProp)
    rw [cast_eq]
    simp only [foldStepRelOut, foldStepRelOutProp, Set.mem_setOf_eq, commitKStateProp]
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- For pSpecCommit, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    intro h_kState_round1
    unfold commitKStateProp masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]
    -- Round-1 state is bad ∨ good under Option B.
    cases h_kState_round1 with
    | inl hBad =>
      left
      have hBad_cast :=
        incrementalBadEventExistsProp_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR oStmtIn
          _ _ hBad
      exact hBad_cast
    | inr hGood =>
      have h_sumcheck : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H := hGood.1
      have h_struct : witnessStructuralInvariant 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn witMid := hGood.2.1
      have h_init : firstOracleWitnessConsistencyProp 𝔽q β witMid.t
          (getFirstOracle 𝔽q β
            (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
              oStmtIn
              (msg : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (domainIdx := ⟨i.val + 1, by omega⟩)))) := hGood.2.2.1
      have h_fold : oracleFoldingConsistencyProp 𝔽q β (i := i.succ) stmtIn.challenges
          (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
            oStmtIn
            (msg : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (domainIdx := ⟨i.val + 1, by omega⟩))) := hGood.2.2.2
      have h_init_cast : firstOracleWitnessConsistencyProp 𝔽q β witMid.t
          (getFirstOracle 𝔽q β oStmtIn) := by
        have h_pos : 0 < toOutCodewordsCount ℓ ϑ i.castSucc := by
          exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ i.castSucc)
        have h_init' := h_init
        simp only [getFirstOracle, snoc_oracle, h_pos] at h_init' ⊢
        exact h_init'
      have h_fold_cast :
          oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc) (Fin.init stmtIn.challenges)
            oStmtIn := by
        exact oracleFoldingConsistencyProp_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR _ oStmtIn _ h_fold
      right
      exact ⟨h_sumcheck, h_struct, h_init_cast, h_fold_cast⟩
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- probEvent_relOut_gt_0: the relOut is satisified under oracle verifier's execution
    -- Now we simp the probEvent_relOut_gt_0 to extract equalities for stmtOut, oStmtOut as
      -- deterministic computations (oracle verifier execution) of stmtIn, oStmtIn
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (𝓑 := 𝓑) (mp := mp) i hCR).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (𝓑 := 𝓑) (mp := mp) i hCR).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      simp only [commitOracleVerifier]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      simp only [simulateQ_pure, pure_bind, Function.comp_apply]
      dsimp only [ProbComp]
      simp only [MessageIdx, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, exists_eq_right,
        exists_and_right]
      ---
      erw [simulateQ_bind]
      erw [simulateQ_pure]
      simp only [pure_bind, support_map, Set.mem_image, Prod.exists, exists_and_right,
        exists_eq_right]
      erw [simulateQ_pure, support_pure]
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq, exists_eq_right]
    rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
    simp only [Nat.reduceAdd]
    -- h_relOut : ((stmtOut, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
    simp only [roundRelation, roundRelationProp, Set.mem_setOf_eq] at h_relOut
    set extractedWitIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ :=
      (commitRbrExtractor 𝔽q β i).extractOut (stmtIn, oStmtIn) tr witOut
    -- extractedWitIn = witOut by definition of commitRbrExtractor
    -- ⊢ commitKStateProp 𝔽q β i (Fin.last 1) stmtIn extractedWitIn oStmtIn tr
    unfold commitKStateProp
    simp only [Fin.reduceLast, Fin.isValue, Fin.val_succ, h_stmtOut_eq] at h_relOut ⊢
    -- Key: goal's oStmt = snoc_oracle oStmtIn (tr.messages ⟨0, rfl⟩) = oStmtOut
    let msgIdx0 : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx := ⟨0, rfl⟩
    have h_oStmt_eq : snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) (oStmtIn := oStmtIn)
        (newOracleFn := tr.messages msgIdx0) = oStmtOut := by
      have h_oStmt_eq' :=
        snoc_oracle_eq_mkVerifierOStmtOut_commitStep 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR oStmtIn
          (tr.messages msgIdx0) tr rfl
      rw [← h_oStmtOut_eq] at h_oStmt_eq'
      exact h_oStmt_eq'
    rw [h_oStmt_eq]
    exact h_relOut

/-! RBR knowledge soundness for a single round oracle verifier -/
omit [SampleableType L] in
theorem commitOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := mp) i hCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  use commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use commitKState (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR
  intro stmtIn witIn prover ⟨j, hj⟩
  cases j using Fin.cases with
  | zero => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_fin_one,
    Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' => exact Fin.elim0 j'

end CommitStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
