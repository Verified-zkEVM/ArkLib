/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

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

section FoldStep

/-! The prover for the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    -- Both stmt and wit advances, but oStmt only advances at the commitment rounds only
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where
  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    -- USE THE SHARED KERNEL (Guarantees match with foldStepLogic)
    let h_i := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
    -- Return message and update state
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  -- | ⟨2, h⟩ => nomatch h -- no challenge after third message
  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let t := FullTranscript.mk2 (pSpec := pSpecFold (L := L)) h_i r_i'
    -- 2. Delegate to Logic Instance
    pure ((foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).proverOut stmt wit oStmt t)

/-! The oracle verifier for the `i`-th round of Binary Foldfold. -/
open Classical in
def foldOracleVerifier (i : Fin ℓ) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (pSpec := pSpecFold (L := L)) where
  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn pSpecChallenges => do
    let h_i ← query (spec := [(pSpecFold (L := L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' := pSpecChallenges ⟨1, rfl⟩
    let t := FullTranscript.mk2 h_i r_i'
    let logic := (foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  -- Reuse embed and hEq from foldStepLogic to ensure consistency
  embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).embed
  hEq := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).hEq

/-! The oracle reduction that is the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)) where
  prover := foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i
  verifier := foldOracleVerifier 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Simplifies membership in a conditional singleton set.
  `x ∈ (if c then {a} else {b})` is equivalent to `x = (if c then a else b)`.
-/
lemma mem_ite_singleton {α : Type*} {c : Prop} [Decidable c] {a b x : α} :
    (x ∈ (if c then {a} else {b} : Set α)) ↔ (x = if c then a else b) := by
  split_ifs with h
  · simp only [Set.mem_singleton_iff] -- Case c is True: x ∈ {a} ↔ x = a
  · simp only [Set.mem_singleton_iff] -- Case c is False: x ∈ {b} ↔ x = b

/-!
Perfect completeness for the binary folding oracle reduction.

This theorem proves that the honest prover-verifier interaction for one round of binary folding
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
1. Unroll the 2-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes on honest prover messages
4. For correctness: extract the challenge from the support and apply the logic completeness lemma

**Key Technique:**
- Use `foldStep_is_logic_complete` to get the pure logic properties
- Convert the challenge function by proving the only valid challenge index is 1
- Rewrite all intermediate variables to their concrete values
- Apply the logic properties to complete the proof
-/
open Classical in
omit [DecidableEq 𝔽q] in
theorem foldOracleReduction_perfectCompleteness (hInit : NeverFail init) (i : Fin ℓ)
  :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc (mp := mp))
      (relOut := strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i (mp := mp))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
      (init := init)
      (impl := impl) := by
  classical
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  -- **NOTE**: this requires `ProtocolSpec.challengeOracleInterface` to avoid conflict
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecFold (L := L)) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [foldOracleReduction, foldOracleProver, foldOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk2]
  let step := (foldStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
  let strongly_complete : step.IsStronglyComplete := foldStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (i := i)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
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
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro h_receive_challenge_fn h_receive_challenge_fn_mem_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
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
      erw [simulateQ_bind]
      -- turn the simulated oracle query into OracleInterface.answer form
      change vStmtOut ∈ _root_.support (Bind.bind (m := (OracleComp []ₒ)) _ _)
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      -- simp  [bind_pure_comp,
      -- OptionT.simulateQ_map, OptionT.simulateQ_ite, OptionT.simulateQ_pure,
      -- OptionT.support_map_run, OptionT.support_ite_run, support_pure,
      -- OptionT.support_failure_run, Set.mem_image, Set.mem_ite_empty_right,
      -- Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]
      rw [bind_pure_comp]
      dsimp only [Functor.map]
      rw [OptionT.simulateQ_bind]
      erw [support_bind]
      rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (foldProverComputeMsg 𝔽q β i witIn) r_i').challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r_i'
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [OptionT.run_pure, probOutput_pure, reduceCtorEq, ↓reduceIte]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [ support_bind, support_pure,
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
    simp only [Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero, ChallengeIdx,
      liftComp_eq_liftM, liftM_pure, liftComp_pure, support_pure, Set.mem_singleton_iff,
      Fin.reduceLast, MessageIdx, Message, exists_eq_left] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvOut_eq, h_verOut_mem_support⟩
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      erw [simulateQ_bind]
      simp only [show OptionT.pure (m := (OracleComp ([]ₒ + ([OracleStatement 𝔽q β ϑ i.castSucc]ₒ +
        [pSpecFold.Message]ₒ)))) = pure by rfl]
      rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (foldProverComputeMsg 𝔽q β i witIn) r1).challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r1
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue, pure_bind] at h_verOut_mem_support
    erw [simulateQ_pure, liftM_pure] at h_verOut_mem_support
    simp only [Fin.isValue, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    rcases h_verOut_mem_support with ⟨verStmtOut_eq, verOStmtOut_eq⟩
    dsimp only [foldStepLogic, foldProverComputeMsg, step, getFoldProverFinalOutput] at prvOut_eq
    rw [Prod.mk.injEq, Prod.mk.injEq] at prvOut_eq
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := prvOut_eq
    constructor
    · rw [prvWitOut_eq, verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2

open scoped NNReal

open Classical in
/-! Definition of the per-round RBR KS error for Binary FoldFold.
This combines the Sumcheck error (2/|L|) and the LDT Bad Event probability.
For round i : rbrKnowledgeError(i) = err_SC + err_BE where
- err_SC = 2/|L| (Schwartz-Zippel for degree 1)
- err_BE = |S^(last_oracle_domain_index_of_i + ϑ)| / |L|
-/
def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
  let err_SC := (2 : ℝ≥0) / (Fintype.card L)
  -- Distributed fold-error budget: one incremental bad-event charge per fold round.
  let err_BE :=
    let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ i.castSucc
    (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨lastDomainIdx.val + ϑ, by
        have h_le := getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc
        omega⟩) : ℝ≥0) / (Fintype.card L)
  err_SC + err_BE

/-! WitMid type for fold step: Witness i.succ at final round, Witness i.castSucc otherwise.
This allows the extractor to work with the actual output witness type at the final round. -/
def foldWitMid (i : Fin ℓ) : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨1, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨2, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-! The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly.

Key design: WitMid at the final round (m=2) is Witness i.succ, matching WitOut.
This allows extractOut to be identity and simplifies toFun_full proofs. -/
noncomputable def foldRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L))
    (WitMid := foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _oStmtIn⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both are Witness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1, i.e., Witness i.succ → Witness i.castSucc
      -- Extract backward using the transcript
      {
        t := witMidSucc.t,
        H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ)
          (t := witMidSucc.t) (m := mp.multpoly stmtIn.ctx)
          (i := i.castSucc) (challenges := stmtIn.challenges),
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witMidSucc.t
          (challenges := stmtIn.challenges)
      }
  -- extractOut is now identity since WitMid (Fin.last 2) = WitOut = Witness i.succ
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-! This follows the KState of sum-check -/
def foldKStateProp {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := h_i.val.eval r_i'
    let stmtOut : Statement (L := L) Context i.succ := {
        -- same  as in Verifier's output & getFoldProverFinalOutput
      ctx := stmtMid.ctx,
      sumcheck_target := newSumcheckTarget,
      challenges := Fin.snoc stmtMid.challenges r_i'
    }
    let oStmtOut := oStmtMid
    let witOut := witMid
    -- Use OUTPUT state: stmtIdx advances to i.succ, oracleIdx stays at i.castSucc (no new oracle)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        let explicitVCheck :=
          h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
          -- we also keep the output-state sumcheck consistency
          sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

-- Note: this fold step couldn't carry bad-event errors, because we don't have oracles yet.

/-! Knowledge state function (KState) for single round -/
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).KnowledgeStateFunction init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (extractor := foldRbrExtractor (mp:=mp) (𝓡 := 𝓡) (ϑ := ϑ) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    foldKStateProp (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmtMid := stmtMid) (witMid := witMid) (oStmtMid := oStmtMid)
  toFun_empty := fun _ _ => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    -- For pSpecFold, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Direction.not_V_to_P_eq_P_to_V] at hDir
    subst h_m_eq_0
    intro h_kState_round1
    unfold foldKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]
    -- At round 1: bad ∨ (localChecks ∧ structural ∧ initial ∧ oracleFoldingConsistency)
    -- At round 0: bad ∨ (sumcheckConsistency ∧ structural ∧ initial ∧ oracleFoldingConsistency)
    cases h_kState_round1 with
    | inl h_bad =>
      exact Or.inl h_bad
    | inr h_good =>
      have h_explicit := h_good.1.1
      have h_localized := h_good.1.2
      have h_struct : witnessStructuralInvariant 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtMid witMid := h_good.2.1
      have h_init : firstOracleWitnessConsistencyProp 𝔽q β witMid.t
          (getFirstOracle 𝔽q β oStmtMid) := h_good.2.2.1
      have h_fold := h_good.2.2.2
      have h_sumcheck : sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H := by
        simp_rw [h_localized] at h_explicit
        rw [h_explicit.symm]
        exact getSumcheckRoundPoly_sum_eq (L := L) (ℓ := ℓ) (𝓑 := 𝓑) (i := i) (h := witMid.H)
      exact Or.inr ⟨h_sumcheck, h_struct, h_init, h_fold⟩
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          _root_.support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (𝓑 := 𝓑) (mp := mp) i).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (𝓑 := 𝓑) (mp := mp) i).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [foldOracleVerifier]
      -- dsimp only [StateT.run]
      -- simp only [simulateQ_bind, simulateQ_query, simulateQ_pure]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      -- enter [1, i_1, 2, 1, x]
      simp only [simulateQ_bind]
      unfold OracleInterface.answer
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        OptionT.simulateQ_failure', bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure',
        bind_map_left, Function.comp_apply]
      simp only [support_ite]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
      erw [simulateQ_bind]
      enter [1, x, 1, 2, 1, 2];
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    conv at h_output_mem_V_run_support =>
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, Function.comp_apply]
    erw [support_bind] at h_output_mem_V_run_support
    let step := (foldStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2 (msg0 := _) (msg1 := _)) with h_V_check_def
    by_cases h_V_check : V_check
    · simp only [Fin.isValue, Matrix.cons_val_zero, h_V_check, ↓reduceIte, OptionT.run_pure,
        simulateQ_pure, Function.comp_apply, Set.mem_iUnion, exists_prop, Prod.exists,
        exists_and_right] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      simp only [simulateQ_pure, Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, exists_eq_right,
        exists_eq_left] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at h_output_mem_V_run_support
      -- simp only [support_map, Set.mem_image, exists_prop] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue] -- simp the `match`
      dsimp only [foldStepRelOut, foldStepRelOutProp, masterKStateProp] at h_relOut
      simp only [Fin.val_succ, Set.mem_setOf_eq] at h_relOut
      dsimp only [foldKStateProp]
      set h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨⟨0, by simp only [Nat.reduceAdd,
        Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.ofNat_pos]⟩, rfl⟩ with h_i_def
      set r_i' : L := tr.challenges ⟨⟨1, by simp only [Nat.reduceAdd, Fin.reduceLast,
        Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.one_lt_ofNat]⟩, rfl⟩ with h_i_def
      set extractedWitLast : Witness (L := L) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ :=
        (foldRbrExtractor 𝔽q β i).extractOut (stmtIn, oStmtIn) tr witOut
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by
        rw [h_oStmtOut_eq]
        funext j
        -- ⊢ OracleVerifier.mkVerifierOStmtOut (foldStepLogic 𝔽q β i).embed ⋯ oStmtIn tr j
        --   = oStmtIn j
        simp only [foldStepLogic, Prod.mk.eta, Fin.isValue, MessageIdx, Fin.is_lt, ↓reduceDIte,
          Fin.eta, Fin.zero_eta, Fin.mk_one, Function.Embedding.coeFn_mk, Sum.inl.injEq,
          OracleVerifier.mkVerifierOStmtOut_inl, cast_eq]
      have h_stmtOut_challenges_eq :
        ((Fin.snoc stmtIn.challenges r_i') : Fin (↑i + 1) → L) = stmtOut.challenges := by
        -- use the h_stmtOut_eq to prove this
        rw [h_stmtOut_eq]
        unfold foldStepLogic foldVerifierStmtOut
        simp only [Fin.val_succ, Fin.isValue, Fin.snoc_inj, true_and]
        rfl
      rw [h_oStmtOut_eq_oStmtIn] at h_relOut
      have h_stmtOut_sumcheck_target_eq :
          stmtOut.sumcheck_target = (Polynomial.eval r_i' ↑h_i) := by
        rw [h_stmtOut_eq]; rfl
      dsimp only [masterKStateProp]
      rw [h_stmtOut_sumcheck_target_eq] at h_relOut
      have h_explicit : h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtIn.sumcheck_target := by
        have h_explicit' := h_V_check
        simp only at h_explicit' ⊢
        exact h_explicit'
      cases h_relOut with
      | inl h_bad =>
        have h_bad' : incrementalBadEventExistsProp 𝔽q β i.succ
            (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) oStmtIn
            (Fin.snoc stmtIn.challenges r_i') := by
          have h_bad'' := h_bad
          simp only [h_stmtOut_challenges_eq] at h_bad'' ⊢
          exact h_bad''
        exact Or.inl h_bad'
      | inr h_good =>
        refine Or.inr ?_
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact ⟨h_explicit, h_good.1⟩
        · have h_struct := h_good.2.1
          simp only [h_stmtOut_eq] at h_struct ⊢
          exact h_struct
        · have h_init := h_good.2.2.1
          simp only at h_init ⊢
          exact h_init
        · have h_res := h_good.2.2.2
          simp only [h_stmtOut_eq] at ⊢ h_res
          exact h_res
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_failure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      simp only [simulateQ_pure, Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        ] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, reduceCtorEq] at h_output_mem_V_run_support

/-! This follows the KState of sum-check -/
def foldKStateProps {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := h_i.val.eval r_i'
    let stmtOut : Statement (L := L) Context i.succ := { -- same as in getFoldProverFinalOutput
      ctx := stmtMid.ctx,
      sumcheck_target := newSumcheckTarget,
      challenges := Fin.snoc stmtMid.challenges r_i'
    }
    let oStmtOut := oStmtMid
    let witOut := witMid
    -- Use OUTPUT state: stmtIdx advances to i.succ, oracleIdx stays at i.castSucc (no new oracle)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        -- we reduce the sumcheck consistency check here
        sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

/-
The fold-step extraction failure event implies either:
1. a sumcheck bad event at the sampled challenge, or
2. an incremental folding bad event at the current oracle frontier.

More precisely:
- **Sumcheck bad**: `h_i ≠ h_star ∧ h_i.eval r_i' = h_star.eval r_i'`,
  where `h_star = getSumcheckRoundPoly ℓ 𝓑 i witIn.H`.
- **Folding bad**: an incremental bad-event witness exists at frontier `i.castSucc`
  using challenges extended by `r_i'`.

Proof plan for `foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent`:

Goal shape:
  Doom-escape at challenge round `⟨1, rfl⟩` gives an existential `witMid` with
  `¬kSF@castSucc` and `kSF@succ`; we must derive:
  `badSumcheckEventProp r_i' h_i h_star(witIn) ∨ incrementalFoldingBadEvent`.

Plan:
1. Unfold the doom-escape witness:
   Expand `rbrExtractionFailureEvent`, `foldKnowledgeStateFunction`, and `foldKStateProp`
   at rounds `m=1` and `m=2`, obtaining the two KState facts carried by `witMid`.

2. Isolate the KState core:
   From `masterKStateProp`, separate local checks from the core disjunction
   `incrementalBadEventExistsProp ∨ oracleWitnessConsistency`.

3. Split by the incremental bad event:
   Case A: `incrementalFoldingBadEvent` holds; finish by `Or.inr`.
   Case B: `¬ incrementalFoldingBadEvent`; show this forces the KState-2 core to use
   `oracleWitnessConsistency` (good branch).

4. Overlap-cancellation for bad events:
   In Case B, any bad event witnessed at round 2 must already be present at round 1.
   Old events are preserved backward to round 1 (same oracle frontier / challenge prefix),
   contradicting `¬kSF@round1`. Hence no bad-event branch remains.

5. Fix the round polynomial on the good branch:
   Use the good branch (`oracleWitnessConsistency`, plus local checks) to identify the
   witness-derived round polynomial and compare it with `h_i`.
   Then combine with `¬kSF@round1` to obtain:
   `h_i ≠ h_star` and `h_i(r_i') = h_star(r_i')`.

6. Conclude sumcheck bad:
   Package Step 5 as `badSumcheckEventProp r_i' h_i h_star(witIn)` and finish by `Or.inl`.

Expected helper lemmas:
- backward preservation of incremental bad events from round-2 to round-1 view;
- extraction of localized round-poly equalities from fold-step local checks.
-/
omit [SampleableType L] [DecidableEq 𝔽q] in
lemma firstOracleWitnessConsistency_unique (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {t₁ t₂ : MultilinearPoly L ℓ}
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  classical
  have h₁_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₁ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) (tpoly := t₁)).2 h₁
  have h₂_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₂ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) (tpoly := t₂)).2 h₂
  rw [h₁_some] at h₂_some
  injection h₂_some with h_t

/-! Extract the round-`i` witness (before the verifier challenge) from a fold-step output
witness. -/
@[reducible]
def foldStepWitBeforeFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc :=
  (foldRbrExtractor.{0} (mp := mp) 𝔽q β i).extractMid
    (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid

/-! Canonical fold-step round polynomial extracted from a specific `witMid`. -/
@[reducible]
def foldStepHStarFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    L⦃≤ 2⦄[X] :=
  let witBefore := foldStepWitBeforeFromWitMid
    (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i stmtOStmtIn h_i r_i' witMid
  getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := witBefore.H)

/-! At the same fold-step output state, `witnessStructuralInvariant`
and `firstOracleWitnessConsistencyProp` determine a unique witness.
Consequently, any witness-dependent extracted `h_star` is canonical. -/
omit [SampleableType L] [DecidableEq 𝔽q] in
lemma foldStep_oracleWitnessConsistency_unique_witMid (i : Fin ℓ)
    (stmtOut : Statement (L := L) Context i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut witMid₂)
    (h_init₁ : firstOracleWitnessConsistencyProp 𝔽q β witMid₁.t
      (getFirstOracle 𝔽q β oStmt))
    (h_init₂ : firstOracleWitnessConsistencyProp 𝔽q β witMid₂.t
      (getFirstOracle 𝔽q β oStmt)) :
    witMid₁ = witMid₂ := by
  classical
  have h_t : witMid₁.t = witMid₂.t := by
    exact firstOracleWitnessConsistency_unique 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := i) (oStmt := oStmt) (h₁ := h_init₁) (h₂ := h_init₂)
  have h_H : witMid₁.H = witMid₂.H := by
    calc
      witMid₁.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid₁.t)
        (m := mp.multpoly stmtOut.ctx) (i := i.succ)
        (challenges := stmtOut.challenges) := h_struct₁.1
      _ = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid₂.t)
        (m := mp.multpoly stmtOut.ctx) (i := i.succ)
        (challenges := stmtOut.challenges) := by simp only [Fin.val_succ, h_t]
      _ = witMid₂.H := h_struct₂.1.symm
  have h_f : witMid₁.f = witMid₂.f := by
    calc
      witMid₁.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i.succ) (t := witMid₁.t) (challenges := stmtOut.challenges) := h_struct₁.2
      _ = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i.succ) (t := witMid₂.t)
        (challenges := stmtOut.challenges) := by simp only [Fin.val_succ, h_t]
      _ = witMid₂.f := h_struct₂.2.symm
  cases witMid₁
  cases witMid₂
  simp only [Fin.val_succ, Witness.mk.injEq] at h_t h_H h_f ⊢
  exact ⟨h_t, h_H, h_f⟩

omit [SampleableType L] [DecidableEq 𝔽q] in
lemma foldStepHStarFromWitMid_eq_of_oracleWitnessConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
        ctx := stmtOStmtIn.1.ctx
      } witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
        ctx := stmtOStmtIn.1.ctx
      } witMid₂)
    (h_init₁ : firstOracleWitnessConsistencyProp 𝔽q β witMid₁.t
      (getFirstOracle 𝔽q β stmtOStmtIn.2))
    (h_init₂ : firstOracleWitnessConsistencyProp 𝔽q β witMid₂.t
      (getFirstOracle 𝔽q β stmtOStmtIn.2)) :
    foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid₁ =
    foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid₂ := by
  have h_wit_eq :
      witMid₁ = witMid₂ := foldStep_oracleWitnessConsistency_unique_witMid
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) (ϑ := ϑ)
        (i := i)
        (stmtOut := {
          sumcheck_target := h_i.val.eval r_i',
          challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
          ctx := stmtOStmtIn.1.ctx
        })
        (oStmt := stmtOStmtIn.2) h_struct₁ h_struct₂ h_init₁ h_init₂
  subst h_wit_eq
  rfl

/-! Fresh incremental bad-event for the **latest oracle block** at the fold-step:
`¬ E_before ∧ E_after`, where `E_*` is `incrementalFoldingBadEvent` evaluated
before/after appending `r_i'`. -/
@[reducible]
def foldStepFreshDoomPreservationEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L) : Prop :=
  let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
  let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
  let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
  let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
  let kBefore : ℕ := min ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
  -- NOTE: actually `kBefore` is always less than `ϑ`, so `kBefore + 1 ≤ ϑ`
  have h_j_val : j.val = i.val / ϑ := by
    have h_i_lt_ℓ : i.val < ℓ := i.isLt
    have h_i_cast_lt_ℓ : i.val < ℓ := by simp only [h_i_lt_ℓ]
    dsimp only [j, getLastOraclePositionIndex]
    unfold toOutCodewordsCount
    simp only [Fin.val_castSucc, h_i_lt_ℓ, ↓reduceIte, add_tsub_cancel_right]
  have h_cur_eq : curOracleDomainIdx.val = (i.val / ϑ) * ϑ := by
    dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
    simp only [h_j_val]
  have h_diff_lt : stmtIdxBefore.val - curOracleDomainIdx.val < ϑ := by
    have h_div_mod : (i.val / ϑ) * ϑ + i.val % ϑ = i.val := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i.val ϑ
    have h_cur_le : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
        _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
    have h_sum : curOracleDomainIdx.val + i.val % ϑ = stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val + i.val % ϑ = (i.val / ϑ) * ϑ + i.val % ϑ := by
          simp only [h_cur_eq]
        _ = i.val := h_div_mod
    have h_diff_eq : stmtIdxBefore.val - curOracleDomainIdx.val = i.val % ϑ := by omega
    rw [h_diff_eq]
    exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
  have h_kBefore_lt : kBefore < ϑ := by
    exact lt_of_le_of_lt
      (Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)) h_diff_lt
  let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
    have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := Nat.pos_of_neZero 𝓡
    dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]
    omega
  ⟩
  let r_prefix : Fin kBefore → L := fun cId => challengesBefore
    ⟨curOracleDomainIdx.val + cId.val, by
      have h_k_le_stmt : kBefore ≤ stmtIdxBefore.val - curOracleDomainIdx.val :=
        Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
      have h_cId_lt_k : cId.val < kBefore := cId.isLt
      omega
    ⟩
  let E_before :=
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore ≤ ϑ := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
      (h_k_le := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val))
      (h_midIdx := by simp only)
      (h_destIdx := rfl)
      (h_destIdx_le := by
        simp only [(oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)), j, destIdx,
          curOracleDomainIdx])
      (f_block_start := stmtOStmtIn.2 j)
      (r_challenges := r_prefix)
  let E_after :=
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (block_start_idx := curOracleDomainIdx)
    (midIdx := ⟨curOracleDomainIdx.val + (kBefore + 1), by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      have h_k_le : kBefore + 1 ≤ ϑ := Nat.succ_le_of_lt h_kBefore_lt
      have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
        oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      omega
    ⟩)
    (destIdx := destIdx) (k := kBefore + 1)
    (h_k_le := Nat.succ_le_of_lt h_kBefore_lt)
    (h_midIdx := by simp only)
    (h_destIdx := rfl)
    (h_destIdx_le := by
      simp only [(oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)), j, destIdx,
        curOracleDomainIdx])
    (f_block_start := stmtOStmtIn.2 j)
    (r_challenges := Fin.snoc r_prefix r_i')
  ¬ E_before ∧ E_after

/-! Oracle-witness consistency for a candidate fold-step output witness. -/
@[reducible]
def foldStepWitMidOracleConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt : Statement (L := L) Context i.succ := {
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
      ctx := stmtOStmtIn.1.ctx
  }
  let structural := witnessStructuralInvariant 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt witMid
  let initial := firstOracleWitnessConsistencyProp 𝔽q β witMid.t (getFirstOracle 𝔽q β stmtOStmtIn.2)
  structural ∧ initial

/-! Proof sketch:
let `j` be the **oracle position index** of the last oracle at oracle frontier `i`.
Note that `k = i - j * ϑ < ϑ`, since if `k = ϑ`,
  then `i` must be an oracle domain, therefore `k = 0`, contradiction.
We have:
  h_bad_after =  `|__|__|...|__|__|j*ϑ|====i===(i+1)| ↔ exists_bad_until_j OR incBad(j -> i+1)`
  h_not_fresh = `¬(¬incBad(j -> i) ∧ incBad(j -> i+1)) ↔ incBad(j -> i) ∨ (¬incBad(j -> i+1))`
Goal: h_bad_before = `|__|__|...|__|__|j*ϑ|====i| = exists_bad_until_j OR incBad(j -> i)`
--------
We rcases on h_not_fresh:
  If `incBad(j -> i)` holds, then h_bad_before = true, Q.E.D.
  else we have `¬incBad(j -> i+1)`,
    which implies `exists_bad_until_j` to be true from `h_bad_after`
    => `h_bad_before = true` by definition
-/
omit [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] in
private theorem fin_fun_heq_of_cast {m n : ℕ} (h : m = n)
    (f : Fin m → L) (g : Fin n → L)
    (hfg : ∀ i : Fin m, f i = g (Fin.cast h i)) :
    HEq f g := by
  subst h
  apply heq_of_eq
  funext i
  simpa using hfg i

set_option maxHeartbeats 200000 in
-- This bad-event backward step expands several nested verifier definitions before omega closes.
lemma incrementalBadEventExistsProp_fold_step_backward (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L)
    (h_bad_after : incrementalBadEventExistsProp 𝔽q β i.succ
      (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) stmtOStmtIn.2
      (Fin.snoc stmtOStmtIn.1.challenges r_i'))
    (h_not_fresh : ¬ foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i') :
  incrementalBadEventExistsProp 𝔽q β i.castSucc
      (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
      stmtOStmtIn.1.challenges := by
  classical
  unfold incrementalBadEventExistsProp at h_bad_after ⊢
  rcases h_bad_after with ⟨j, hj⟩
  by_cases h_old : j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc
  · refine ⟨j, ?_⟩
    have hj_copy := hj
    dsimp at hj_copy ⊢
    have h_k_full : j.val * ϑ + ϑ ≤ i.val := by
      exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc) (j := j) (hj := h_old)
    have hk_after : min ϑ (i.val + 1 - j.val * ϑ) = ϑ := by
      omega
    have hk_before : min ϑ (i.val - j.val * ϑ) = ϑ := by
      omega
    let afterSlice : Fin ϑ → L := fun cId =>
      Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i'
        ⟨j.val * ϑ + cId.val, by
          have h_idx_lt : j.val * ϑ + cId.val < i.val := by
            exact lt_of_lt_of_le (Nat.add_lt_add_left cId.isLt (j.val * ϑ)) h_k_full
          exact lt_trans h_idx_lt (Nat.lt_succ_self i.val)⟩
    let beforeSlice : Fin ϑ → L := fun cId =>
      stmtOStmtIn.1.challenges
        ⟨j.val * ϑ + cId.val, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left cId.isLt (j.val * ϑ)) h_k_full⟩
    have h_challenges : afterSlice = beforeSlice := by
      have h_slice :=
        getFoldingChallenges_init_succ_eq (r := r) (L := L) (𝓡 := 𝓡) (ϑ := ϑ)
          (i := i) (j := j) (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i')
          (h := h_k_full)
      simp at h_slice
      exact h_slice.symm
    let blockStart : Fin r := ⟨j.val * ϑ, by
      exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) j).isLt⟩
    let blockDest : Fin r := ⟨j.val * ϑ + ϑ, by
      exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))⟩
    have hj_after_full :
        incrementalFoldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := blockStart)
          (k := ϑ)
          (h_k_le := le_rfl)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := afterSlice) := by
      convert hj_copy using 1
      · apply Fin.eq_of_val_eq
        dsimp [blockDest]
        omega
      · exact hk_after.symm
      · have h_afterSlice_heq :
            HEq
              (fun cId : Fin (min ϑ (i.val + 1 - j.val * ϑ)) =>
                Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i'
                  ⟨j.val * ϑ + cId.val, by
                    have h_cId_lt :
                        cId.val < i.val + 1 - j.val * ϑ := by
                      exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                    have h_block_le : j.val * ϑ ≤ i.val + 1 := by
                      omega
                    calc
                      j.val * ϑ + cId.val < j.val * ϑ + (i.val + 1 - j.val * ϑ) :=
                        Nat.add_lt_add_left h_cId_lt (j.val * ϑ)
                      _ = i.val + 1 := Nat.add_sub_of_le h_block_le⟩)
              afterSlice := by
          apply fin_fun_heq_of_cast hk_after
          intro cId
          dsimp [afterSlice]
        exact HEq.symm h_afterSlice_heq
    have h_bad_after_full :
        foldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := blockStart)
          (destIdx := blockDest)
          (steps := ϑ)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_i := stmtOStmtIn.2 j)
          (r_challenges := afterSlice) := by
      exact
        (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
          (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ)
          (block_start_idx := blockStart)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := by rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := afterSlice)).1 hj_after_full
    have h_bad_before_full := h_bad_after_full
    rw [h_challenges] at h_bad_before_full
    have hj_before_full :
        incrementalFoldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := blockStart)
          (k := ϑ)
          (h_k_le := le_rfl)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := beforeSlice) := by
      exact
        (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
          (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ)
          (block_start_idx := blockStart)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := by rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := beforeSlice)).2 h_bad_before_full
    convert hj_before_full using 1
    · apply Fin.eq_of_val_eq
      dsimp [blockDest]
      omega
    · have h_beforeSlice_heq :
          HEq
            (fun cId : Fin (min ϑ (i.val - j.val * ϑ)) =>
              stmtOStmtIn.1.challenges
                ⟨j.val * ϑ + cId.val, by
                  have h_cId_lt :
                      cId.val < i.val - j.val * ϑ := by
                    exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                  have h_block_le : j.val * ϑ ≤ i.val := by
                    exact le_trans (by omega) h_k_full
                  calc
                    j.val * ϑ + cId.val < j.val * ϑ + (i.val - j.val * ϑ) :=
                      Nat.add_lt_add_left h_cId_lt (j.val * ϑ)
                    _ = i.val := Nat.add_sub_of_le h_block_le⟩)
            beforeSlice := by
        apply fin_fun_heq_of_cast hk_before
        intro cId
        dsimp [beforeSlice]
      exact h_beforeSlice_heq
  · refine ⟨j, ?_⟩
    have hj_copy := hj
    dsimp at hj_copy ⊢
    have h_j_last : j = getLastOraclePositionIndex ℓ ϑ i.castSucc := by
      apply Fin.eq_of_val_eq
      have hj_lt : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
        have hj_lt' := j.isLt
        simp only [OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj_lt'
        exact hj_lt'
      have h_val : j.val = toOutCodewordsCount ℓ ϑ i.castSucc - 1 := by
        have h_ge : toOutCodewordsCount ℓ ϑ i.castSucc ≤ j.val + 1 := by
          omega
        omega
      dsimp [getLastOraclePositionIndex]
      exact h_val
    subst j
    dsimp [foldStepFreshDoomPreservationEvent] at h_not_fresh
    have h_j_val : (getLastOraclePositionIndex ℓ ϑ i.castSucc).val = i.val / ϑ := by
      dsimp only [getLastOraclePositionIndex]
      unfold toOutCodewordsCount
      simp only [Fin.val_castSucc, i.isLt, ↓reduceIte, add_tsub_cancel_right]
    have h_diff_lt :
        i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ < ϑ := by
      rw [h_j_val, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]
      exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
    have h_diff_eq :
        i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ = i.val % ϑ := by
      rw [h_j_val, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]
    have h_last_le :
        (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ ≤ i.val := by
      rw [h_j_val, Nat.mul_comm]
      have h_div := Nat.div_mul_le_self i.val ϑ
      rw [Nat.mul_comm] at h_div
      exact h_div
    have hk_after_last :
        min ϑ (i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) =
          min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) + 1 := by
      rw [show i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ =
          (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) + 1 by
            omega]
      rw [h_diff_eq]
      have h_mod_lt : i.val % ϑ < ϑ := by
        exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
      omega
    let kBefore : ℕ := min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)
    let prefixSlice : Fin kBefore → L := fun cId =>
      stmtOStmtIn.1.challenges
        ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
          have h_min_le :
              kBefore ≤ i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
            dsimp [kBefore]
            exact Nat.min_le_right ϑ _
          have h_cId_lt :
              cId.val < i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
            exact lt_of_lt_of_le cId.isLt h_min_le
          have h_idx_lt :
              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val < i.val := by
            omega
          exact h_idx_lt⟩
    let afterSlice : Fin (kBefore + 1) → L := fun cId =>
      Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i'
        ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
          have h_cId_le : cId.val ≤ kBefore := by
            exact Nat.lt_succ_iff.mp cId.isLt
          have h_idx_le :
              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val ≤ i.val := by
            dsimp [kBefore] at h_cId_le
            have h_min_le :
                min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) ≤
                  i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ :=
              Nat.min_le_right ϑ _
            omega
          exact lt_of_le_of_lt h_idx_le (Nat.lt_succ_self i.val)⟩
    let freshSlice : Fin (kBefore + 1) → L := Fin.snoc (α := fun _ => L) prefixSlice r_i'
    have h_after_challenges : afterSlice = freshSlice := by
      funext cId
      by_cases h_lt : cId.val < kBefore
      · have h_idx_lt :
            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val < i.val := by
          dsimp [kBefore] at h_lt
          omega
        simp [afterSlice, freshSlice, prefixSlice, Fin.snoc, h_lt, h_idx_lt]
      · have h_eq_last :
            cId.val = kBefore := by
          omega
        have h_idx_eq :
            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val = i.val := by
          rw [h_eq_last]
          dsimp [kBefore]
          omega
        have h_not_idx_lt :
            ¬ (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val < i.val := by
          omega
        simp [afterSlice, freshSlice, prefixSlice, Fin.snoc, h_lt, h_idx_eq]
    let blockStart : Fin r := ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ, by
      exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Nat.le_of_lt (lt_of_le_of_lt h_last_le i.isLt))⟩
    let blockMidAfter : Fin r :=
      ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + (kBefore + 1), by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        dsimp [kBefore]
        omega⟩
    let blockDest : Fin r := ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + ϑ, by
      exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc)
          (j := getLastOraclePositionIndex ℓ ϑ i.castSucc))⟩
    have h_after_last_afterSlice :
        incrementalFoldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := blockStart)
          (k := kBefore + 1)
          (h_k_le := by
            dsimp [kBefore]
            omega)
          (midIdx := blockMidAfter)
          (destIdx := blockDest)
          (h_midIdx := rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc)
            (j := getLastOraclePositionIndex ℓ ϑ i.castSucc))
          (f_block_start := stmtOStmtIn.2 (getLastOraclePositionIndex ℓ ϑ i.castSucc))
          (r_challenges := afterSlice) := by
      convert hj_copy using 1
      · apply Fin.eq_of_val_eq
        dsimp [blockStart, blockMidAfter, kBefore]
        omega
      · dsimp [kBefore]
        omega
      · have h_afterSlice_heq :
            HEq
              (fun cId : Fin
                  (min ϑ (i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)) =>
                Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i'
                  ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
                    have h_cId_lt :
                        cId.val <
                          i.val + 1 -
                            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
                      exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                    have h_block_le :
                        (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ ≤ i.val + 1 := by
                      omega
                    calc
                      (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val <
                          (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ +
                            (i.val + 1 -
                              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) :=
                        Nat.add_lt_add_left h_cId_lt _
                      _ = i.val + 1 := Nat.add_sub_of_le h_block_le⟩)
              afterSlice := by
          apply fin_fun_heq_of_cast hk_after_last
          intro cId
          dsimp [afterSlice]
        exact HEq.symm h_afterSlice_heq
    have h_after_last' := h_after_last_afterSlice
    rw [h_after_challenges] at h_after_last'
    by_contra h_before_false
    exact h_not_fresh ⟨h_before_false, h_after_last'⟩
lemma foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑) (init := init)
        (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn)
    (transcript := FullTranscript.mk1 h_i) (challenge := r_i')) :
    let incrementalFoldingBadEvent :=
      foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
    incrementalFoldingBadEvent ∨ (
      ¬incrementalFoldingBadEvent ∧
      (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (foldStepWitMidOracleConsistency (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i r_i' witMid)
        ∧ (badSumcheckEventProp r_i' h_i
            (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid))
      )
    ) := by
  classical
  let incrementalFoldingBadEvent : Prop :=
    foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [foldKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold foldKStateProp at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    Transcript.concat] at h_kState_before_false h_kState_after_true
  by_cases h_bad : incrementalFoldingBadEvent
  · left
    exact h_bad
  · right
    refine ⟨h_bad, ?_⟩
    -- Under ¬ fresh bad-event, the m=2 KState cannot be on the bad branch.
    have h_after_good_exists : ∃ h_after_good, h_kState_after_true = Or.inr h_after_good := by
      cases h_kState_after_true with
      | inl h_bad_after =>
        exfalso
        have h_bad_before : incrementalBadEventExistsProp 𝔽q β i.castSucc
          (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
          stmtOStmtIn.1.challenges :=
          incrementalBadEventExistsProp_fold_step_backward 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            i stmtOStmtIn r_i' h_bad_after h_bad
        exact h_kState_before_false (Or.inl h_bad_before)
      | inr h_after_good =>
        exact ⟨h_after_good, rfl⟩
    rcases h_after_good_exists with ⟨h_after_good, rfl⟩
    have h_explicit_after :
        h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtOStmtIn.1.sumcheck_target := by
      exact h_after_good.1.1
    have h_sumcheck_after :
        sumcheckConsistencyProp (𝓑 := 𝓑) (Polynomial.eval r_i' h_i.val) witMid.H := by
      exact h_after_good.1.2
    have h_consistency : foldStepWitMidOracleConsistency 𝔽q β i stmtOStmtIn h_i r_i' witMid :=
      ⟨h_after_good.2.1, h_after_good.2.2.1⟩
    have h_left_from_consistency :
        badSumcheckEventProp r_i' h_i
          (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid) := by
      have h_wit_struct_after :
          witMid.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid.t)
            (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i.succ)
            (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i') := by
        exact h_consistency.1.1
      let H_before : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid.t)
          (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i.castSucc)
          (challenges := stmtOStmtIn.1.challenges)
      let h_star_extracted : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H_before)
      have h_eval_eq_extracted :
          Polynomial.eval r_i' h_i.val = Polynomial.eval r_i' h_star_extracted.val := by
        unfold sumcheckConsistencyProp at h_sumcheck_after
        rw [h_wit_struct_after] at h_sumcheck_after
        rw [projectToMidSumcheckPoly_succ (L := L) (ℓ := ℓ) (t := witMid.t)
          (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i)
          (challenges := stmtOStmtIn.1.challenges) (r_i' := r_i')] at h_sumcheck_after
        have h_sum_eq :=
          projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := 𝓑) (ℓ := ℓ)
            (i := i) (Hᵢ := H_before) (rᵢ := r_i')
        have h_sum_eq' :
            Polynomial.eval r_i' h_star_extracted.val =
              ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
                (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i)
                  (Hᵢ := H_before) (rᵢ := r_i')).val.eval x := by
          have h_sum_eq' := h_sum_eq
          dsimp only [h_star_extracted] at h_sum_eq' ⊢
          exact h_sum_eq'
        calc
          Polynomial.eval r_i' h_i.val
              = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
                  (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i)
                    (Hᵢ := H_before) (rᵢ := r_i')).val.eval x := h_sumcheck_after
          _ = Polynomial.eval r_i' h_star_extracted.val := by
            symm
            exact h_sum_eq'
      have h_hi_ne_extracted : h_i ≠ h_star_extracted := by
        intro h_eq
        apply h_kState_before_false
        right
        refine ⟨?_, ?_, ?_, ?_⟩
        · constructor
          · exact h_explicit_after
          · have h_eq' := h_eq
            simp only [h_star_extracted, H_before, foldRbrExtractor, Fin.isValue] at h_eq' ⊢
            exact h_eq'
        · unfold witnessStructuralInvariant
          simp only [Fin.val_castSucc, foldRbrExtractor, Fin.zero_eta, Fin.isValue,
            Fin.succ_zero_eq_one, Fin.mk_one, Fin.succ_one_eq_two,
            Fin.coe_ofNat_eq_mod, Nat.reduceMod, and_self]
        · exact h_consistency.2
        · have h_folding_after := h_after_good.2.2.2
          unfold oracleFoldingConsistencyProp at h_folding_after ⊢
          intro j hj
          have h_fold_j := h_folding_after j hj
          unfold isCompliant at h_fold_j ⊢
          rcases h_fold_j with ⟨h_fw_close, h_next_close, h_iter⟩
          refine ⟨h_fw_close, h_next_close, ?_⟩
          have h_gc (y : L) :
              getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
                (Fin.take ↑i.castSucc (Nat.le_succ ↑i.castSucc)
                  (Fin.snoc (α := fun _ : Fin i.succ => L) stmtOStmtIn.1.challenges y))
                (↑j * ϑ) (h := by
                  exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc)
                    (j := j) (hj := hj)) =
              getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
                stmtOStmtIn.1.challenges
                (↑j * ϑ) (h := by
                  exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc)
                    (j := j) (hj := hj)) := by
            ext cId
            dsimp [getFoldingChallenges]
            simp only [Fin.init_snoc]
          erw [h_gc _] at h_iter
          exact h_iter
      change badSumcheckEventProp r_i' h_i h_star_extracted
      exact ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
    exact ⟨witMid, h_consistency, h_left_from_consistency⟩

#check prop_4_20_2_incremental_bad_event_probability
/-! Per-transcript bound: for the first prover message `msg0`, the probability (over the verifier
  challenge `y`) that extraction fails is at most `foldKnowledgeError`. Stated for
  `P (FullTranscript.mk1 msg0)` so it matches the goal after `tsum_uniform_Pr_eq_Pr` in the main
  soundness proof.
  **Proof strategy:**
  1. **Implication**: Show that extraction failure `P(tr, y)` implies either
    - a SINGLE sumcheck “bad” event
    - or an incremental folding bad event (bad oracle / consistency failure)
  2. **Monotonicity**: Conclude `Pr[P] ≤ Pr[SZ ∨ BE]` via `prob_mono`.
  3. **Union bound**: Apply `Pr_or_le` to get `Pr[SZ ∨ BE] ≤ Pr[SZ] + Pr[BE]`.
  4. **Schwartz–Zippel**: Bound `Pr[SZ]` by `1/|L|` using univariate degree-1
    agreement (lemmas from Instances.lean)
  5. **Bad event**: Bound `Pr[BE]` using the incremental folding bad-event probability
    (`prop_4_20_2_incremental_bad_event_probability`).
  6. **Combine**: Add the two bounds and match the RHS to `foldKnowledgeError`. -/
lemma foldStep_doom_escape_probability_bound (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑)
          (init := init) (impl := impl) (σ := σ) 𝔽q β i)
        (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) ⟨1, rfl⟩
          stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, by rfl⟩ := by
  classical
  let doomEvent := fun y : L =>
    rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑)
        (init := init) (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) ⟨1, rfl⟩
      stmtOStmtIn (FullTranscript.mk1 h_i) y
  let sumcheckBadEvent : L → Prop := fun y =>
    let incrementalFoldingBadEvent :=
      foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
    (¬incrementalFoldingBadEvent ∧
        (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (foldStepWitMidOracleConsistency (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i y witMid)
        ∧ (badSumcheckEventProp y h_i
            (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn h_i y witMid))
      ))
  let incrementalBadFoldEvent := fun y : L =>
    foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
  let incrementalBadFoldEvent_or_sumcheckBadEvent := fun y : L =>
    (incrementalBadFoldEvent y) ∨ (sumcheckBadEvent y)
  have h_prob_mono := prob_mono (D := $ᵖ L)
    (f := doomEvent) (g := incrementalBadFoldEvent_or_sumcheckBadEvent)
    (h_imp := by
      intro y h_doomEscape
      have h_imp := (foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent
          (mp := mp) (𝓑 := 𝓑) (init := init) (impl := impl) 𝔽q β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i)
          (r_i' := y) (doomEscape := h_doomEscape))
      dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, sumcheckBadEvent,
        incrementalBadFoldEvent]
      by_cases h_bad : foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
      · exact Or.inl h_bad
      · cases h_imp with
        | inl h_bad' => exact False.elim (h_bad h_bad')
        | inr h_sum => exact Or.inr h_sum
    )
  refine le_trans h_prob_mono ?_
  dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, foldKnowledgeError]
  apply le_trans (
      Pr_or_le ($ᵖ L) (f := incrementalBadFoldEvent) (g := sumcheckBadEvent)
  )
  conv_rhs => simp only [ENNReal.coe_add]; rw [add_comm]
  apply add_le_add
  · dsimp only [incrementalBadFoldEvent, foldStepFreshDoomPreservationEvent]
    let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
    let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
    let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
    let kBefore : ℕ := min ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
    have h_j_val : j.val = i.val / ϑ := by
      have h_i_lt_ℓ : i.val < ℓ := i.isLt
      have h_i_cast_lt_ℓ : i.val < ℓ := by
        simp only [h_i_lt_ℓ]
      dsimp only [j, getLastOraclePositionIndex]
      unfold toOutCodewordsCount
      simp only [Fin.val_castSucc, h_i_lt_ℓ, ↓reduceIte, add_tsub_cancel_right]
    have h_cur_eq : curOracleDomainIdx.val = (i.val / ϑ) * ϑ := by
      dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
      simp only [h_j_val]
    have h_diff_lt : stmtIdxBefore.val - curOracleDomainIdx.val < ϑ := by
      have h_div_mod : (i.val / ϑ) * ϑ + i.val % ϑ = i.val := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod i.val ϑ
      have h_cur_le : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
        dsimp only [stmtIdxBefore]
        calc
          curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
          _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
      have h_sum : curOracleDomainIdx.val + i.val % ϑ = stmtIdxBefore.val := by
        dsimp only [stmtIdxBefore]
        calc
          curOracleDomainIdx.val + i.val % ϑ = (i.val / ϑ) * ϑ + i.val % ϑ := by
            simp only [h_cur_eq]
          _ = i.val := h_div_mod
      have h_diff_eq : stmtIdxBefore.val - curOracleDomainIdx.val = i.val % ϑ := by omega
      rw [h_diff_eq]
      exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
    have h_kBefore_lt : kBefore < ϑ := by
      exact lt_of_le_of_lt
        (Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)) h_diff_lt
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
      have _ : 𝓡 > 0 := Nat.pos_of_neZero 𝓡
      dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]
      omega
    ⟩
    let r_prefix : Fin kBefore → L := fun cId => challengesBefore
      ⟨curOracleDomainIdx.val + cId.val, by
        have h_k_le_stmt : kBefore ≤ stmtIdxBefore.val - curOracleDomainIdx.val :=
          Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_cId_lt_k : cId.val < kBefore := cId.isLt
        omega
      ⟩
    have h_res := prop_4_20_2_incremental_bad_event_probability 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx_i := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore ≤ ϑ := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (midIdx_i_succ := ⟨curOracleDomainIdx.val + kBefore + 1, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore + 1 ≤ ϑ := Nat.succ_le_of_lt h_kBefore_lt
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
        (h_k_lt := h_kBefore_lt)
        (h_midIdx_i := by simp only)
        (h_midIdx_i_succ := by simp only)
        (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
        (f_block_start := stmtOStmtIn.2 j)
      (r_prefix := r_prefix)
    dsimp only [destIdx, curOracleDomainIdx, j, kBefore, r_prefix, stmtIdxBefore, challengesBefore]
      at h_res
    have h_cur_le_stmt : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
        _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
    have h_kBefore_eq : kBefore = stmtIdxBefore.val - curOracleDomainIdx.val := by
      dsimp only [kBefore]
      exact Nat.min_eq_right (Nat.le_of_lt h_diff_lt)
    have h_kAfter_eq : min ϑ (i.succ.val - curOracleDomainIdx.val) = kBefore + 1 := by
      have h_cur_le_i : curOracleDomainIdx.val ≤ i.val := by
        have h_cur_le_i' := h_cur_le_stmt
        simp only [stmtIdxBefore] at h_cur_le_i'
        exact h_cur_le_i'
      have h_sub_succ : i.val + 1 - curOracleDomainIdx.val
        = (i.val - curOracleDomainIdx.val) + 1 := by
        have h_sub_succ' := Nat.succ_sub h_cur_le_i
        rw [Nat.succ_eq_add_one] at h_sub_succ'
        exact h_sub_succ'
      have h_kBefore_eq' : kBefore = i.val - curOracleDomainIdx.val := by
        have h_kBefore_eq'' := h_kBefore_eq
        simp only [stmtIdxBefore] at h_kBefore_eq''
        exact h_kBefore_eq''
      simp only [Fin.val_succ]
      rw [h_sub_succ, ← h_kBefore_eq']
      exact Nat.min_eq_right (Nat.succ_le_of_lt h_kBefore_lt)
    have h_snoc_eq :
        ∀ r_new : L,
          (fun cId : Fin (kBefore + 1) =>
            if h : curOracleDomainIdx.val + cId.val < stmtIdxBefore.val then
              challengesBefore ⟨curOracleDomainIdx.val + cId.val, h⟩
            else
              r_new) = Fin.snoc r_prefix r_new := by
      intro r_new
      funext cId
      by_cases h_lt : cId.val < kBefore
      · have h_guard : curOracleDomainIdx.val + cId.val < stmtIdxBefore.val := by
          omega
        simp [Fin.snoc, r_prefix, h_lt, h_guard]
      · have h_guard_false : ¬ curOracleDomainIdx.val + cId.val < stmtIdxBefore.val := by
          omega
        simp [Fin.snoc, h_lt, h_guard_false]
    conv_rhs => simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      ENNReal.coe_div, ENNReal.coe_natCast]
    exact h_res
  · dsimp only [sumcheckBadEvent]
    -- Strategy: ignore the `foldStepFreshDoomPreservationEvent`, plus `oracleWitnessConsistency`
      -- guarantees uniqueness of witMid, then we can transform this to prove the bound via
        -- `probability_bound_badSumcheckEventProp`
    let compatPred : MultilinearPoly L ℓ → Prop := fun t =>
      firstOracleWitnessConsistencyProp 𝔽q β t (getFirstOracle 𝔽q β stmtOStmtIn.2)
    by_cases hCompat : ∃ t : MultilinearPoly L ℓ, compatPred t
    · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
      let H_fixed : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t_fixed)
          (m := mp.multpoly stmtOStmtIn.1.ctx)
          (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
      let h_star_fixed : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H_fixed)
      have h_prob_mono_sum := prob_mono (D := $ᵖ L)
        (f := fun y => sumcheckBadEvent y)
        (g := fun y => badSumcheckEventProp y h_i h_star_fixed)
        (h_imp := by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, h_bad⟩
          have h_t_eq : witMid.t = t_fixed :=
            firstOracleWitnessConsistency_unique 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := i)
              (oStmt := stmtOStmtIn.2) (h₁ := h_cons.2) (h₂ := h_t_fixed_compat)
          have h_bad' := h_bad
          simp only [h_star_fixed, H_fixed, foldStepHStarFromWitMid,
            foldStepWitBeforeFromWitMid, foldRbrExtractor, Fin.isValue, h_t_eq] at h_bad' ⊢
          exact h_bad'
        )
      refine le_trans h_prob_mono_sum ?_
      have h_sz := probability_bound_badSumcheckEventProp (h_i := h_i) (h_star := h_star_fixed)
      conv_rhs =>
        rw [ENNReal.coe_div (hr := by
          simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])]
        simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
      exact h_sz
    · have h_prob_mono_false := prob_mono (D := $ᵖ L)
        (f := fun y => sumcheckBadEvent y)
        (g := fun _ => False)
        (h_imp := by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, _h_bad⟩
          exact (hCompat ⟨witMid.t, h_cons.2⟩).elim
        )
      refine le_trans h_prob_mono_false ?_
      simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
        eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-! RBR knowledge soundness for a single round oracle verifier -/
open Classical in
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  apply OracleReduction.unroll_rbrKnowledgeSoundness (kSF := foldKnowledgeStateFunction
    (mp:=mp) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 𝔽q β i)
  intro stmtOStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑) (init := init) (impl := impl) (σ := σ) 𝔽q β i)
    (foldRbrExtractor (mp := mp) 𝔽q β i)
    j
    stmtOStmtIn
  rw [OracleReduction.probEvent_soundness_goal_unroll_log' (pSpec := pSpecFold
    (L := L)) (P := P) (impl := impl) (prover := prover) (i := j) (stmt := stmtOStmtIn)
    (wit := witIn) (s := initState)]
  have h_j_eq_1 : j = ⟨1, rfl⟩ := by
    match j with
    | ⟨0, h0⟩ => nomatch h0
    | ⟨1, _⟩ => rfl
  subst h_j_eq_1
  conv_lhs => simp only [Fin.isValue, Fin.castSucc_one];
  rw [OracleReduction.soundness_unroll_runToRound_1_P_to_V_pSpec_2
    (pSpec := pSpecFold (L := L)) (prover := prover) (hDir0 := rfl)]
  simp only [Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero, ChallengeIdx,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self, Message, Fin.succ_zero_eq_one, Nat.reduceAdd,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, FullTranscript.mk1_eq_snoc, bind_pure_comp,
    liftComp_eq_liftM, bind_map_left, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, Functor.map_map]
  rw [probEvent_bind_eq_tsum]
  apply OracleReduction.ENNReal.tsum_mul_le_of_le_of_sum_le_one
  · -- Bound the conditional probability for each transcript
    intro x
    -- rw [OracleComp.probEvent_map]
    simp only [Fin.isValue, probEvent_map]
    let q : OracleQuery [(pSpecFold (L := L)).Challenge]ₒ _ := query ⟨⟨1, by rfl⟩, ()⟩
    erw [OracleReduction.probEvent_StateT_run_ignore_state
      (comp := simulateQ (impl.addLift challengeQueryImpl) (liftM (query q.input)))
      (s := x.2)
      (P := fun a => P (FullTranscript.mk1 x.1.1) (q.cont a))]
    rw [probEvent_eq_tsum_ite]
    erw [simulateQ_query]
    simp only [ChallengeIdx, Challenge, Fin.isValue, Nat.reduceAdd, Fin.castSucc_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, monadLift_self,
      QueryImpl.addLift_def, QueryImpl.liftTarget_self, StateT.run'_eq, StateT.run_map,
      Functor.map_map, ge_iff_le]
    have h_L_inhabited : Inhabited L := ⟨0⟩
    conv_lhs =>
      enter [1, x_1, 2, 1, 2]
      rw [addLift_challengeQueryImpl_input_run_eq_liftM_run (impl := impl) (q := q) (s := x.2)]
    erw [StateT.run_monadLift, monadLift_self, liftComp_id]
    rw [bind_pure_comp]
    conv =>
      enter [1, 1, x_1, 2]
      rw [Functor.map_map]
      rw [← probEvent_eq_eq_probOutput]
      rw [probEvent_map]
      rw [OracleQuery.cont_apply]
      dsimp only [MonadLift.monadLift]
      rw [OracleQuery.cont_apply]
      dsimp only [q]
    simp_rw [OracleQuery.input_query, OracleQuery.snd_query]
    conv_lhs => change (∑' (x_1 : L), _)
    simp only [Function.comp_id]
    conv =>
      enter [1, 1, x_1, 2]
      rw [probEvent_eq_eq_probOutput]
      change Pr[=x_1 | $ᵗ L]
      rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr (L := _) (x := x_1)]
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr
      (L := L) (P := fun x_1 => P (FullTranscript.mk1 x.1.1) (q.2 x_1))]
      -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    change Pr_{ let y ← $ᵖ L }[ P (FullTranscript.mk1 x.1.1) y ] ≤
      foldKnowledgeError 𝔽q β i ⟨1, by rfl⟩
    -- Apply the per-transcript bound
    exact foldStep_doom_escape_probability_bound 𝔽q β (i := i)
      (stmtOStmtIn := stmtOStmtIn) (h_i := x.1.1) (init := init) (impl := impl) (mp := mp)
      (𝓑 := 𝓑) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply tsum_probOutput_le_one

end FoldStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
