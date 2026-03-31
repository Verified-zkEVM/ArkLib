/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
-- open scoped Binius.BinaryBasefold
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

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

open Classical in
/-! The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    -- Compute the message using the honest transcript from logic
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    -- Construct the transcript from the message and challenges (no challenges in this step)
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Delegate to the logic instance for prover output
    pure ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).proverOut stmtIn witIn oStmtIn t)

/-! The verifier for the final sumcheck step -/
open Classical in
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Get the logic instance
    let logic := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    -- Use guard for verifier check (fails if check doesn't pass)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).embed
  hEq := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).hEq

/-! The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

/-! Perfect completeness for the final sumcheck step -/
omit [DecidableEq 𝔽q] in
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
    (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    -- Pr[⊥ | (...) : OracleComp ... (Option ...)] = 0
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option] -- split into two summands
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
      rw [OptionT.simulateQ_simOracle2_liftM_query_T2] -- V queries P's message
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
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      Fin.val_last, exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [Fin.isValue, Fin.val_last, OptionT.run_pure, probOutput_eq_zero_iff, support_pure,
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
    simp only [Fin.isValue, Challenge, ChallengeIdx,
      liftComp_eq_liftM, liftM_pure, liftComp_pure, support_pure, Set.mem_singleton_iff,
      MessageIdx, Message] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    rcases hx_mem_support with ⟨prvWitOut, h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support =>
      dsimp only [finalSumcheckStepLogic]
      simp only [Fin.val_last, Fin.isValue, Prod.mk.injEq, and_true]
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      simp only [Set.mem_singleton_iff]
      change some (verStmtOut, verOStmtOut) ∈ _root_.support (liftComp _ _)
      rw [support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      simp only [Fin.isValue, Fin.val_last, OptionT.simulateQ_simOracle2_liftM_query_T2, pure_bind,
        OptionT.simulateQ_bind, toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
        Set.mem_iUnion, exists_prop]
      rw [simulateQ_ite]; erw [simulateQ_pure]
      simp only [OptionT.simulateQ_failure']
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1
        (msg0 := _))with h_V_check_def
    -- Step 2e: Apply the logic completeness lemma
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue] at h_verOut_mem_support
    erw [support_bind, support_pure] at h_verOut_mem_support
    simp only [Set.mem_singleton_iff, Fin.isValue, Set.iUnion_iUnion_eq_left,
      OptionT.support_OptionT_pure_run, exists_eq_left, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    rcases h_verOut_mem_support with ⟨verStmtOut_eq, verOStmtOut_eq⟩
    obtain ⟨prvStmtOut_eq, prvOStmtOut_eq⟩ := h_prvOut_mem_support
    constructor
    · rw [verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2

/-! RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

omit [SampleableType L] in
/-! When final-sumcheck oracle consistency holds, extractMLP must succeed.

This connects the proximity-based `finalSumcheckStepOracleConsistencyProp` to the decoder:
- That prop implies oracle folding consistency and final compliance (last oracle → constant)
- Folding consistency implies the first oracle is within unique decoding radius
- Berlekamp-Welch decoder succeeds when within UDR, returning `some` -/
omit [SampleableType L] in
lemma extractMLP_some_of_oracleFoldingConsistency
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (h_oracle_consistency : finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtOut) (oStmtOut := oStmt)) :
    -- extractMLP is used in `finalSumcheckRbrExtractor`
    ∃ tpoly, extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmt) = some tpoly := by
  -- Proof strategy: the first oracle must be fiberwise-close due to isCompliant
    -- constraint, hence it's UDR-close, Q.E.D
  have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  dsimp only [finalSumcheckStepOracleConsistencyProp] at h_oracle_consistency
  rcases h_oracle_consistency with ⟨h_oracle_cons, h_final_cons⟩
  let j0 : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨0, by
    exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
  ⟩
  by_cases h_ℓ_eq_ϑ : ℓ = ϑ
  · -- We reason on h_final_cons
    have h_div : ℓ / ϑ = 1 := by
      rw [h_ℓ_eq_ϑ]; rw [Nat.div_self (n := ϑ) (H := by omega)]
    have h_getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = 0 := by
      dsimp only [getLastOraclePositionIndex]
      simp only [toOutCodewordsCount_last, Fin.mk_eq_zero, h_div]
    let jLast : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    have h_jLast_eq_zero : jLast = 0 := by
      dsimp only [jLast]
      exact h_getLastOraclePositionIndex_last
    have h_jLast_val : jLast.val = 0 := by
      exact congrArg Fin.val h_jLast_eq_zero
    let zeroIdxLast : Fin r := ⟨↑jLast * ϑ, by
      have h_r_pos : 0 < r := Nat.pos_of_neZero r
      rw [h_jLast_val, zero_mul]
      exact h_r_pos⟩
    let destIdxLast : Fin r := ⟨↑jLast * ϑ + ϑ, by
      have h_ℓ_lt_r : ℓ < r := by omega
      have h_ϑ_lt_r : ϑ < r := by
        rw [← h_ℓ_eq_ϑ]
        exact h_ℓ_lt_r
      rw [h_jLast_val, zero_mul, zero_add]
      exact h_ϑ_lt_r⟩
    let challengesLast : Fin ϑ → L := fun cId =>
      stmtOut.challenges ⟨↑jLast * ϑ + ↑cId, by
        simp only [h_jLast_eq_zero, Fin.coe_ofNat_eq_mod, toOutCodewordsCount_last, h_ℓ_eq_ϑ,
          Nat.zero_mod, zero_mul, zero_add, Fin.val_last, cId.isLt]⟩
    have h_zeroIdxLast : zeroIdxLast.val = 0 := by
      simp [zeroIdxLast, h_jLast_eq_zero]
    have h_zeroIdxLast_eq : zeroIdxLast = 0 := Fin.eq_of_val_eq h_zeroIdxLast
    have h_destIdxLast : destIdxLast = 0 + ϑ := by
      simp [destIdxLast, h_jLast_eq_zero]
    have h_destIdxLast_le : destIdxLast ≤ ℓ := by
      simp only [h_jLast_eq_zero, Fin.coe_ofNat_eq_mod, toOutCodewordsCount_last, h_ℓ_eq_ϑ,
        Nat.zero_mod, zero_mul, zero_add, le_refl, destIdxLast]
    have h_compl0 :
        isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := zeroIdxLast)
          (steps := ϑ)
          (destIdx := destIdxLast)
          (h_destIdx := by
            rw [h_zeroIdxLast_eq]
            exact h_destIdxLast)
          (h_destIdx_le := h_destIdxLast_le)
          (f_i := oStmt jLast)
          (f_i_plus_steps := fun _ => stmtOut.final_constant)
          (challenges := challengesLast) := by
      have h_final_cons' := h_final_cons
      simp only [jLast, zeroIdxLast, destIdxLast, challengesLast] at h_final_cons' ⊢
      exact h_final_cons'
    rcases (extractMLP_some_of_isCompliant_at_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ϑ)
      (zero_Idx := zeroIdxLast)
      (h_zero_Idx := h_zeroIdxLast)
      (destIdx := destIdxLast)
      (h_destIdx := h_destIdxLast)
      (h_destIdx_le := h_destIdxLast_le)
      (f_i := oStmt jLast)
      (f_next := fun _ => stmtOut.final_constant)
      (challenges := challengesLast)
      (h_compl := h_compl0)) with
      ⟨tpoly, h_extract⟩
    refine ⟨tpoly, ?_⟩
    convert h_extract using 1
    congr 1
    funext x
    dsimp [getFirstOracle]
    refine OracleStatement.oracle_eval_congr (oStmtIn := oStmt)
      (h_j := h_jLast_eq_zero.symm) (h_x := ?_)
    simp only [Fin.coe_ofNat_eq_mod, cast_cast]
  · -- We reason on h_oracle_cons
    dsimp only [oracleFoldingConsistencyProp] at h_oracle_cons
    have h_lt : ϑ < ℓ := by omega
    have h_div_gt_1 : ℓ / ϑ > 1 := by
      have h_res := (Nat.div_lt_div_right (a := ϑ) (b := ϑ) (c := ℓ) (ha := by omega)
        (by simp only [dvd_refl]) (by exact hdiv.out)).mpr h_lt
      rw [Nat.div_self (n := ϑ) (H := by omega)] at h_res
      exact h_res
    have h_j0_next_lt : ↑j0 + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := by
      dsimp only [j0]
      rw [toOutCodewordsCount_last]
      exact h_div_gt_1
    let zeroIdx0 : Fin r := ⟨↑j0 * ϑ, by
      have h_r_pos : 0 < r := Nat.pos_of_neZero r
      dsimp only [j0]
      rw [zero_mul]
      exact h_r_pos⟩
    let destIdx0 : Fin r := ⟨↑j0 * ϑ + ϑ, by
      have h_ℓ_lt_r : ℓ < r := by omega
      have h_ϑ_lt_r : ϑ < r := lt_of_le_of_lt h_le h_ℓ_lt_r
      dsimp only [j0]
      rw [zero_mul, zero_add]
      exact h_ϑ_lt_r⟩
    have h_zeroIdx0 : zeroIdx0.val = 0 := by
      simp [zeroIdx0, j0]
    have h_destIdx0 : destIdx0 = 0 + ϑ := by
      simp [destIdx0, j0]
    have h_destIdx0_le : destIdx0 ≤ ℓ := by
      dsimp only [destIdx0, j0]
      rw [zero_mul, zero_add]
      exact h_le
    have h_k_next_le_last : ↑j0 * ϑ + ϑ ≤ Fin.last ℓ := by
      exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := j0) (hj := h_j0_next_lt)
    let fNext0 : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx0 :=
      getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := Fin.last ℓ)
        oStmt j0 h_j0_next_lt
        (destDomainIdx := destIdx0)
        (h_destDomainIdx := by simp only [destIdx0])
    let challenges0 : Fin ϑ → L :=
      getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (k := ↑j0 * ϑ) (h := h_k_next_le_last)
    have h_isCompliant_f₀ :
        isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := zeroIdx0) (steps := ϑ)
          (destIdx := destIdx0)
          (h_destIdx := by
            rw [h_zeroIdx0]
            exact h_destIdx0)
          (h_destIdx_le := h_destIdx0_le)
          (f_i := oStmt ⟨↑j0, by exact j0.isLt⟩)
          (f_i_plus_steps := fNext0)
          (challenges := challenges0) := by
      have h_oracle_cons' := h_oracle_cons j0 h_j0_next_lt
      simp only [zeroIdx0, destIdx0, fNext0, challenges0] at h_oracle_cons' ⊢
      exact h_oracle_cons'
    rcases (extractMLP_some_of_isCompliant_at_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ϑ)
      (zero_Idx := zeroIdx0)
      (h_zero_Idx := h_zeroIdx0)
      (destIdx := destIdx0)
      (h_destIdx := h_destIdx0)
      (h_destIdx_le := h_destIdx0_le)
      (f_i := oStmt ⟨↑j0, by exact j0.isLt⟩)
      (f_next := fNext0)
      (challenges := challenges0)
      (h_compl := h_isCompliant_f₀)) with
      ⟨tpoly, h_extract⟩
    refine ⟨tpoly, ?_⟩
    dsimp only [getFirstOracle, j0] at h_extract ⊢
    exact h_extract

/-! When oracle folding consistency holds from first oracle through the final constant,
the extracted polynomial's evaluation at challenges equals the final constant.

This is the key lemma connecting extraction to the final sumcheck verification:
- `oracleFoldingConsistencyProp` ensures all intermediate foldings are correct
- `h_finalFolding` (isCompliant to final constant) ensures the last step is correct
- Together, they imply the extracted `tpoly` satisfies `tpoly.eval(challenges) = c` -/
omit [SampleableType L] in
private theorem UDRCodeword_heq_of_fin_eq
    {i j : Fin r} (hij : i = j)
    (h_i : i ≤ ℓ) (h_j : j ≤ ℓ)
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g)
    (h₁ : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := h_i) (f := f))
    (h₂ : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := j) (h_i := h_j) (f := g)) :
    HEq
      (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := h_i) (f := f) (h_within_radius := h₁))
      (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := j) (h_i := h_j) (f := g) (h_within_radius := h₂)) := by
  cases hij
  cases hfg
  apply heq_of_eq
  exact UDRCodeword_eq_of_close (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (h_i := h_i) (f := f) h₁ h₂

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
private theorem iterated_fold_heq_of_fin_eq
    (i : Fin r) (steps : ℕ)
    {destIdx₁ destIdx₂ : Fin r} (hij : destIdx₁ = destIdx₂)
    (h_destIdx₁ : ↑destIdx₁ = ↑i + steps)
    (h_destIdx₂ : ↑destIdx₂ = ↑i + steps)
    (h_destIdx_le₁ : ↑destIdx₁ ≤ ℓ) (h_destIdx_le₂ : ↑destIdx₂ ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) :
    HEq
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx₁)
        h_destIdx₁ h_destIdx_le₁ f r_challenges)
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx₂)
        h_destIdx₂ h_destIdx_le₂ f r_challenges) := by
  cases hij
  apply heq_of_eq
  funext y
  cases proof_irrel_heq h_destIdx₁ h_destIdx₂
  cases proof_irrel_heq h_destIdx_le₁ h_destIdx_le₂
  rfl

private def finalOracleBlockIdx
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Fin r :=
  ⟨t * ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
    exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩)⟩

private def finalPrefixChallenges
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    Fin (t * ϑ) → L := fun cId =>
  stmtOut.challenges ⟨cId, by
    exact lt_of_lt_of_le cId.isLt
      (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))⟩

private def finalBlockChallenges
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    Fin ϑ → L := fun cId =>
  stmtOut.challenges ⟨t * ϑ + cId, by
    have h_lt : t * ϑ + cId.val < t * ϑ + ϑ := by
      omega
    exact lt_of_lt_of_le h_lt
      (oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))⟩

private def finalDecodedPrefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (finalOracleBlockIdx (ℓ := ℓ)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := t * ϑ)
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := f₀)
    (r_challenges := finalPrefixChallenges stmtOut t ht)

private def finalOracleRaw
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) := by
  change OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (ϑ := ϑ) (i := Fin.last ℓ) ⟨t, ht⟩
  exact oStmtOut ⟨t, ht⟩

private def finalOracleDecoded
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
      (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
      (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_within_radius := h_close)

omit [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] in
private theorem finalOracleBlockIdx_zero
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht = 0 := by
  apply Fin.eq_of_val_eq
  dsimp [finalOracleBlockIdx]
  simp only [zero_mul]

private def finalOracleClose
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Prop :=
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := oStmtOut ⟨t, ht⟩)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem finalOracleDecoded_eq_of_close
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close₁ h_close₂ : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close₁ =
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close₂ := by
  cases Subsingleton.elim h_close₁ h_close₂
  rfl

set_option maxHeartbeats 10000 in
-- This transitivity lemma unfolds two nested iterated folds before the final congruence step.
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero ϑ] in
private theorem finalDecodedPrefixFold_step
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        t (Nat.lt_of_succ_lt ht))
      (steps := ϑ)
      (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t + 1) ht)
      (h_destIdx := by
        dsimp [finalOracleBlockIdx]
        rw [Nat.add_mul, Nat.one_mul])
      (h_destIdx_le := by
        dsimp [finalOracleBlockIdx]
        rw [Nat.add_mul, Nat.one_mul]
        exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
      (f := finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
      (r_challenges := finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht) =
    finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht := by
  dsimp [finalDecodedPrefixFold]
  have h_transitivity := iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r))
    (midIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t (Nat.lt_of_succ_lt ht))
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t + 1) ht)
    (steps₁ := t * ϑ) (steps₂ := ϑ)
    (h_midIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add])
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add]
      rw [Nat.add_mul, Nat.one_mul])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      rw [Nat.add_mul, Nat.one_mul]
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (f := f₀)
    (r_challenges₁ := finalPrefixChallenges
      (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
    (r_challenges₂ := finalBlockChallenges
      (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
  rw [h_transitivity]
  funext y
  have h_steps_eq : t * ϑ + ϑ = (t + 1) * ϑ := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r)) (steps := t * ϑ + ϑ) (steps' := (t + 1) * ϑ)
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t + 1) ht)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add]
      rw [Nat.add_mul, Nat.one_mul])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      rw [Nat.add_mul, Nat.one_mul]
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (h_steps_eq_steps' := h_steps_eq)
    (f := f₀)
    (r_challenges := Fin.append
      (finalPrefixChallenges
        (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
      (finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht))
    (y := y)]
  have h_challenges_eq :
      (fun cId : Fin ((t + 1) * ϑ) =>
        Fin.append
          (finalPrefixChallenges
            (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
          (finalBlockChallenges
            (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
          ⟨cId, by
            have h_cast_lt : cId.val < t * ϑ + ϑ := by
              have h_lt' : cId.val < (t + 1) * ϑ := cId.isLt
              omega
            exact h_cast_lt⟩) =
      finalPrefixChallenges (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut (t + 1) ht := by
    funext cId
    dsimp only [finalPrefixChallenges, finalBlockChallenges, Fin.append, Fin.addCases]
    by_cases h : cId.val < t * ϑ
    · simp only [h, ↓reduceDIte, Fin.castLT_mk]
    · simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      congr 1
      simp only [Fin.mk.injEq]
      omega
  rw [h_challenges_eq]

set_option maxHeartbeats 10000 in
-- This base-oracle decoded equality uses subsingleton transport on close proofs.
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem firstOracleDecoded_eq_f₀
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (h_close0 : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)) :
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
      (h_within_radius := h_close0) = f₀ := by
  cases Subsingleton.elim h_close0 h_close_first
  exact h_dec0_eq_f0

set_option maxHeartbeats 10000 in
-- This zero-step oracle identification needs extra heartbeats for the dependent cast cleanup.
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
private theorem finalOracleRaw_zero_heq_getFirstOracle
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    HEq
      (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht)
      (getFirstOracle 𝔽q β oStmtOut) := by
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) := by
    exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx0
  have h_j0 :
      (⟨0, ht⟩ : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))) =
      ⟨0, by
        letI := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
        exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))⟩ := by
    apply Fin.eq_of_val_eq
    rfl
  exact funext_heq h_dom (fun _ => rfl) (by
    intro y
    apply heq_of_eq
    cases h_j0
    dsimp [finalOracleRaw, getFirstOracle]
    rw [cast_cast]
    simp)

set_option maxHeartbeats 10000 in
-- This zero-step close transport crosses from the final-oracle view back to the first oracle.
private theorem finalOracleClose_zero_eq_first
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close0 : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut) := by
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  change UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
      (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
      (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) at h_close0
  exact UDRClose_of_fin_eq (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx0
    (finalOracleRaw_zero_heq_getFirstOracle (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht)
    h_close0

-- This zero-case decoded equality combines UDRCodeword transport with a zero-step fold rewrite.
set_option maxHeartbeats 10000 in
private theorem finalOracleDecoded_zero_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close0 : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) :
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0 =
    finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ 0 ht := by
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  have h_raw0_heq :
      HEq
        (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht)
        (getFirstOracle 𝔽q β oStmtOut) :=
    finalOracleRaw_zero_heq_getFirstOracle (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht
  have h_close0_first :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut) := by
    exact finalOracleClose_zero_eq_first (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht h_close0
  have h_decoded0_heq_f₀ :
      HEq
        (finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0)
        f₀ := by
    have h_decoded0_heq_first :
        HEq
          (finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0)
          (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
            (h_within_radius := h_close0_first)) := by
      exact UDRCodeword_heq_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx0
        (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (by simp) h_raw0_heq h_close0 h_close0_first
    exact h_decoded0_heq_first.trans
      (heq_of_eq (firstOracleDecoded_eq_f₀ (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut f₀ h_close_first h_dec0_eq_f0 h_close0_first))
  have h_prefix_zero_heq :
      HEq
        (finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ 0 ht)
        f₀ := by
    have h_dom0 :
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate
          (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)) =
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) := by
      exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx0
    exact funext_heq h_dom0 (fun _ => rfl) (by
      intro y
      apply heq_of_eq
      dsimp [finalDecodedPrefixFold]
      rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (steps := 0 * ϑ) (steps' := 0)
        (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
        (h_destIdx := by
          dsimp [finalOracleBlockIdx]
          simp only [zero_mul, add_zero])
        (h_destIdx_le := by
          exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (h_steps_eq_steps' := by simp only [zero_mul]) (f := f₀)
        (r_challenges := finalPrefixChallenges
          (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut 0 ht) (y := y)]
      rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))
        (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
        (h_destIdx := by
          dsimp [finalOracleBlockIdx]
          simp only [zero_mul])
        (h_destIdx_le := by
          exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (f := f₀)
        (r_challenges := fun cId => finalPrefixChallenges
          (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut 0 ht ⟨cId, by omega⟩)])
  exact eq_of_heq (h_decoded0_heq_f₀.trans h_prefix_zero_heq.symm)

set_option maxHeartbeats 10000 in
-- This current-close extractor unfolds one oracle-consistency witness and reindexes the block.
omit [CharP L 2] [SampleableType L] in
private theorem finalOracleClose_curr
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t (Nat.lt_of_succ_lt ht) := by
  let jCurr : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨t, Nat.lt_of_succ_lt ht⟩
  have h_complCurr := h_oracle_cons jCurr ht
  rcases h_complCurr with ⟨h_fw_curr, _, _⟩
  exact UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Nat.lt_of_succ_lt ht))
    (steps := ϑ)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx, jCurr, oraclePositionToDomainIndex])
    (h_destIdx_le := by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jCurr)
      dsimp [finalOracleBlockIdx, jCurr, oraclePositionToDomainIndex] at h_le ⊢
      omega)
    (f := oStmtOut jCurr)
    h_fw_curr

private def finalOracleDecodedAt
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close

private def finalDecodedPrefixAt
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht

private def finalOracleNextIdxOrig
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Fin r :=
  ⟨t * ϑ + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
    exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩

private def finalOracleNextRaw
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (Fin.last ℓ) oStmtOut ⟨t, Nat.lt_of_succ_lt ht⟩ ht
    (destDomainIdx := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_destDomainIdx := by rfl)

private def finalOracleNextClose
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Prop :=
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := by
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (f := finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)

private def finalOracleNextCodeword
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : finalOracleNextClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := by
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (f := finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_within_radius := h_close)

private axiom finalOracleDecoded_next_heq
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close_next : finalOracleNextClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_close_next_final : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht) :
    HEq
      (finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next)
      (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close_next_final)

private axiom finalDecodedPrefixAt_succ_heq
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    HEq
      (finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht)
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨t * ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
          exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩)
        (steps := ϑ)
        (destIdx := ⟨t * ϑ + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
          exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)⟩)
        (h_destIdx := by rfl)
        (h_destIdx_le := by
          exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht))
        (f := finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
        (r_challenges := finalBlockChallenges
          (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht))

set_option maxHeartbeats 50000 in
-- This transport-heavy step theorem needs extra heartbeats after the explicit HEq alignment.
private theorem finalOracleDecoded_succ_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close_curr : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t (Nat.lt_of_succ_lt ht))
    (h_curr_eq :
      finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t (Nat.lt_of_succ_lt ht) h_close_curr =
      finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
    (h_close_next_final : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht) :
    finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close_next_final =
    finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht := by
  let ht_prev : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := Nat.lt_of_succ_lt ht
  let jCurr : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨t, ht_prev⟩
  have h_complCurr := h_oracle_cons jCurr ht
  rcases h_complCurr with ⟨h_fw_curr, h_close_next, h_fold_curr⟩
  have h_close_curr_fw :
      finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev :=
    finalOracleClose_curr (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons t ht
  have h_curr_decoded_eq :
      finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr_fw =
      finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr := by
    exact finalOracleDecoded_eq_of_close (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr_fw h_close_curr
  dsimp [finalOracleDecodedAt, finalDecodedPrefixAt, finalOracleDecoded, finalOracleRaw, jCurr,
    oraclePositionToDomainIndex, getFoldingChallenges, finalOracleBlockIdx] at h_fold_curr h_curr_decoded_eq h_curr_eq
  rw [h_curr_decoded_eq, h_curr_eq] at h_fold_curr
  have h_rhs_heq :
      HEq
        (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨t * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
            exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jCurr)⟩)
          (h_i := by
            exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jCurr))
          (f := getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (Fin.last ℓ) oStmtOut jCurr ht
            (destDomainIdx := ⟨t * ϑ + ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
              exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jCurr)⟩)
            (h_destDomainIdx := by rfl))
          (h_within_radius := h_close_next))
        (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close_next_final) := by
    exact finalOracleDecoded_next_heq (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next h_close_next_final
  have h_fold_curr_heq := (heq_of_eq h_fold_curr).trans h_rhs_heq
  have h_blockChallenges_eq :
      getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (t * ϑ)
        (h := by
          exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := jCurr) (hj := ht)) =
      finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht := by
    funext cId
    dsimp [getFoldingChallenges, finalBlockChallenges, jCurr, oraclePositionToDomainIndex]
  rw [h_blockChallenges_eq] at h_fold_curr_heq
  have h_res :
      HEq
        (finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht)
        (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close_next_final) := by
    exact (finalDecodedPrefixAt_succ_heq (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht).trans h_fold_curr_heq
  exact eq_of_heq h_res.symm

set_option maxHeartbeats 100000 in
-- This induction over all final oracles repeatedly invokes the transport-heavy successor theorem.
private theorem finalOracleDecoded_nat_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀) :
    ∀ t, ∀ ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ),
      ∀ h_close : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht,
        finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close =
        finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht := by
  intro t
  induction t with
  | zero =>
      intro ht
      intro h_close
      exact finalOracleDecoded_zero_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut f₀
        h_close_first h_dec0_eq_f0 ht h_close
  | succ t ih =>
      intro ht
      intro h_close
      have ht_prev : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := by
        omega
      have h_close_curr :
          finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev :=
        finalOracleClose_curr (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons t ht
      have h_curr_eq :
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr =
          finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht_prev :=
        ih ht_prev h_close_curr
      exact finalOracleDecoded_succ_eq_prefixFold (𝔽q := 𝔽q) (β := β)
        (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut
        oStmtOut h_oracle_cons f₀ t ht h_close_curr h_curr_eq h_close

set_option maxHeartbeats 10000 in
-- This positive-index wrapper is a thin specialization of the nat-index theorem.
private theorem finalOracleDecoded_pos_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (_h_j_pos : 0 < j.val)
    (h_close_j : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut j.val j.isLt) :
    finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut j.val j.isLt h_close_j =
    finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ j.val j.isLt := by
  exact finalOracleDecoded_nat_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons f₀
    h_close_first h_dec0_eq_f0 j.val j.isLt h_close_j

set_option maxHeartbeats 20000 in
-- This extraction-to-final-constant proof expands the final verifier and its consistency witness.
lemma extracted_t_poly_eval_eq_final_constant
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tpoly : MultilinearPoly L ℓ)
    (h_extractMLP : extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmtOut) = some tpoly)
    (h_finalSumcheckStepOracleConsistency : finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtOut) (oStmtOut := oStmtOut)) :
    stmtOut.final_constant = tpoly.val.eval stmtOut.challenges := by
  -- Proof strategy:
    -- 1. We can see that tpoly satisifes firstOracleWitnessConsistencyProp
    -- 2. From h_finalSumcheckStepOracleConsistency, we can inductively prove that
      -- UDR-decoded(f_j) = iterated_fold (UDR-decoded(f_0), challenges_{0->j*ϑ})
    -- 3. We have UDR-decoded(f_0) = encoded (tpoly's evaluations)
    -- 4. We have UDR-decoded(f_{ℓ/ϑ}) = fun x => stmtOut.final_constant
    -- 5. Therefore, tpoly.val.eval stmtOut.challenges = stmtOut.final_constant
      -- Somehow similar to the strict version `iterated_fold_to_const_strict`
  classical
  have h_final_consistency := h_finalSumcheckStepOracleConsistency
  dsimp only [finalSumcheckStepOracleConsistencyProp] at h_final_consistency
  rcases h_final_consistency with ⟨h_oracle_cons, h_final_cons⟩
  let P₀ : L⦃< 2^ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => tpoly.val.eval (bitsOfIndex ω))
  let f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := (0 : Fin r)) :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_pair :
      pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp)
        (f := getFirstOracle 𝔽q β oStmtOut) (g := f₀) := by
    have h_pair' :=
      (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (f := getFirstOracle 𝔽q β oStmtOut) (tpoly := tpoly)).1 h_extractMLP
    dsimp only [f₀] at h_pair' ⊢
    exact h_pair'
  let C₀ : Set ((sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) → L) :=
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)))
  have h_f0_mem : f₀ ∈ C₀ := by
    dsimp [C₀, f₀]
    change polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := (0 : Fin r)) (P := P₀) ∈
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r))
    have h_codeword :=
      (getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (P := P₀)).property
    unfold getBBF_Codeword_of_poly at h_codeword
    dsimp only at h_codeword
    exact h_codeword
  have h_close_first :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut) := by
    unfold UDRClose
    calc
      2 * Δ₀(getFirstOracle 𝔽q β oStmtOut, C₀) ≤
          2 * Δ₀(getFirstOracle 𝔽q β oStmtOut, f₀) := by
        rw [ENat.mul_le_mul_left_iff (ha := by
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
          (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])]
        exact Code.distFromCode_le_dist_to_mem (C := C₀)
          (u := getFirstOracle 𝔽q β oStmtOut) (v := f₀) h_f0_mem
      _ < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) := by
        norm_cast
  have h_neZero_C₀ : NeZero ‖C₀‖₀ := by
    have h_dist_ne_zero :
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) ≠ 0 := by
      rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp)]
      omega
    dsimp [C₀]
    dsimp only [BBF_CodeDistance] at h_dist_ne_zero ⊢
    exact ⟨h_dist_ne_zero⟩
  letI : NeZero ‖C₀‖₀ := h_neZero_C₀
  have h_f0_close_to_first :
      Δ₀(getFirstOracle 𝔽q β oStmtOut, f₀) ≤ Code.uniqueDecodingRadius C₀ := by
    have h_pair_close := h_pair
    dsimp only [pair_UDRClose, C₀] at h_pair_close
    exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C₀)).2 h_pair_close
  have h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀ := by
    symm
    exact Code.eq_of_le_uniqueDecodingRadius (C := C₀)
      (u := getFirstOracle 𝔽q β oStmtOut)
      (v := f₀)
      (w := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first))
      (hv := h_f0_mem)
      (hw := by
        have h_mem :=
          UDRCodeword_mem_BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
            (h_within_radius := h_close_first)
        dsimp only [C₀] at h_mem ⊢
        exact h_mem)
      (huv := h_f0_close_to_first)
      (huw := by
        have h_dist :=
          dist_to_UDRCodeword_le_uniqueDecodingRadius 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (h_i := by simp)
            (f := getFirstOracle 𝔽q β oStmtOut) (h_within_radius := h_close_first)
        dsimp only [C₀] at h_dist ⊢
        exact h_dist)
  have h_oracle_cons' := h_oracle_cons
  dsimp only [oracleFoldingConsistencyProp] at h_oracle_cons'
  rcases h_final_cons with ⟨h_fw_last, h_close_const, h_fold_last⟩
  have h_last_const := congr_fun h_fold_last 0
  simp only at h_last_const
  -- The last decoded oracle equals the constant oracle fun _ => stmtOut.final_constant.
  -- We apply the same unique-decoding argument as for the first oracle, but now at the
  -- last oracle index with code C_last and center u := oStmtOut jLast.
  let jLast : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  let lastDomainIdx : Fin r :=
    ⟨jLast.val * ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := jLast.val * ϑ)
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)⟩
  let k := lastDomainIdx.val
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, lastDomainIdx, jLast]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  let C_last : Set ((sDomain 𝔽q β h_ℓ_add_R_rate lastDomainIdx) → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := lastDomainIdx)
  let finalDomainIdx : Fin r := ⟨k + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ)
    rw [h_k]
    exact le_of_eq (Nat.sub_add_cancel h_ϑ_le_ℓ)⟩
    -- final virtual oracle's evaluation domain
  let C_final : Set ((sDomain 𝔽q β h_ℓ_add_R_rate finalDomainIdx) → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := finalDomainIdx)
  have h_finalDomainIdx_le : finalDomainIdx ≤ ℓ := by
    dsimp [finalDomainIdx]
    rw [h_k]
    exact le_of_eq (Nat.sub_add_cancel h_ϑ_le_ℓ)
  -- Constant codeword is in C_final
  have h_const_mem : (fun _ => stmtOut.final_constant) ∈ C_final := by
    dsimp [C_final]
    exact constFunc_mem_BBFCode 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalDomainIdx)
      (h_i := h_finalDomainIdx_le)
      stmtOut.final_constant
  have h_lastDomainIdx_le : lastDomainIdx ≤ ℓ := by
    dsimp [lastDomainIdx, jLast]
    exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)
  let f_last_raw : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) lastDomainIdx := by
    change OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := Fin.last ℓ) jLast
    exact oStmtOut jLast
  have h_close_last :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := lastDomainIdx) (h_i := h_lastDomainIdx_le) (f := f_last_raw) := by
    have h_close_last' :=
      UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := lastDomainIdx) (steps := ϑ) (h_destIdx := by rfl)
        (h_destIdx_le := by
          dsimp [lastDomainIdx, jLast]
          exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jLast))
        (f := f_last_raw) h_fw_last
    dsimp [f_last_raw, lastDomainIdx, jLast] at h_close_last' ⊢
    exact h_close_last'
  let f_last : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) lastDomainIdx :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := lastDomainIdx) (h_i := h_lastDomainIdx_le) (f := f_last_raw)
      (h_within_radius := h_close_last)
  let f_final_virtual : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) finalDomainIdx :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalDomainIdx) (h_i := h_finalDomainIdx_le)
      (f := fun _ => stmtOut.final_constant) (h_within_radius := h_close_const)
  let preFinalChallenges : (Fin k) → L := fun cId => stmtOut.challenges ⟨cId, by
    simp only [Fin.val_last]; omega⟩
  let finalChallenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ).val = ℓ := rfl
      simp only [Fin.val_last, gt_iff_lt]
      -- ⊢ ℓ - ϑ + ↑cId < ℓ
      omega
    ⟩
  -- **f_last = iterated_fold (f_0, ...)**
  let f_f₀_folded_to_last := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := k) (destIdx := lastDomainIdx) (h_destIdx := by
      dsimp only [k]; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
    (h_destIdx_le := by omega) (f := f₀) (r_challenges := preFinalChallenges)
  have h_f_last_eq_iterated_fold_f₀ :
    f_last = f_f₀_folded_to_last := by
    have h_last_decoded_eq_prefix :
        finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut jLast.val jLast.isLt h_close_last =
        finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ jLast.val jLast.isLt := by
      exact finalOracleDecoded_nat_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons f₀
        h_close_first h_dec0_eq_f0 jLast.val jLast.isLt h_close_last
    have h_f_last_eq_decoded :
        f_last =
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut jLast.val jLast.isLt h_close_last := by
      have h_h_i_eq :
          h_lastDomainIdx_le =
            oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast) := by
        apply Subsingleton.elim
      cases h_h_i_eq
      rfl
    have h_preFinalChallenges_eq :
        finalPrefixChallenges (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut jLast.val jLast.isLt =
        preFinalChallenges := by
      funext cId
      dsimp [finalPrefixChallenges, preFinalChallenges, k, jLast]
    rw [h_f_last_eq_decoded, h_last_decoded_eq_prefix]
    dsimp [f_f₀_folded_to_last, finalDecodedPrefixFold, k, lastDomainIdx, jLast]
    rw [h_preFinalChallenges_eq]
  -- **f_final_virtual = iterated_fold (f_last, ...)**
  let f_last_folded_to_final := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := lastDomainIdx) (steps := ϑ) (destIdx := finalDomainIdx) (h_destIdx := by
      change finalDomainIdx.val = k + ϑ; rw [h_k]; dsimp only [finalDomainIdx]; omega
    )
    (h_destIdx_le := by
      dsimp only [finalDomainIdx]; omega
    ) (f := f_last)
    (r_challenges := finalChallenges)
  have h_f_final_virtual_eq :
    f_last_folded_to_final = f_final_virtual := by
    dsimp [f_last_folded_to_final, f_final_virtual, f_last, f_last_raw, finalChallenges,
      lastDomainIdx, finalDomainIdx, jLast]
    exact h_fold_last
  have h_f_final_virtual_eq_const :
      f_final_virtual = fun _ => stmtOut.final_constant := by
    dsimp [f_final_virtual]
    exact UDRCodeword_constFunc_eq_self (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := finalDomainIdx)
      h_finalDomainIdx_le stmtOut.final_constant
  -- **=> f_final_virtual = iterated_fold (f_0, ...)**
  -- Now we construct the nested `iterated_fold` form
  rw [h_f_final_virtual_eq_const] at h_f_final_virtual_eq
  dsimp only [f_last_folded_to_final] at h_f_final_virtual_eq
  rw [h_f_last_eq_iterated_fold_f₀] at h_f_final_virtual_eq
  dsimp only [f_f₀_folded_to_last] at h_f_final_virtual_eq
  -- h_f_final_virtual_eq : (fun x ↦ stmtOut.final_constant) =
  --  iterated_fold 𝔽q β lastDomainIdx ϑ ⋯ ⋯
    -- (iterated_fold 𝔽q β 0 k ⋯ ⋯ f₀ preFinalChallenges) finalChallenges
  rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_destIdx := by
      rw [h_k]; dsimp only [finalDomainIdx];
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega
    )
  ] at h_f_final_virtual_eq
  have h_congr_steps := iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := k + ϑ) (destIdx := finalDomainIdx)
    (h_destIdx := by
      rw [h_k]; dsimp only [finalDomainIdx];
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
    (h_destIdx_le := by dsimp only [finalDomainIdx]; omega)
    (h_steps_eq_steps' := by rw [h_k]; omega)
    (f := f₀) (r_challenges := Fin.append preFinalChallenges finalChallenges) (steps' := ℓ)
  have h_congr_steps_fn := funext (h := h_congr_steps)
  rw [h_congr_steps_fn] at h_f_final_virtual_eq
  -- Hint: study the proof strategy of `finalSumcheckStep_verifierCheck_passed`,
    -- `iterated_fold_to_const_strict`, `iterated_fold_to_level_ℓ_is_constant`
  rw [iterated_fold_to_level_ℓ_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (destIdx := finalDomainIdx) (h_destIdx := by
      dsimp only [finalDomainIdx]
      rw [h_k]
      exact Nat.sub_add_cancel h_ϑ_le_ℓ) (t := tpoly)]
      at h_f_final_virtual_eq
  have h_res := congr_fun (h := h_f_final_virtual_eq) (a := 0)
  rw [← h_res]
  have h_concat_challenges_eq : (fun (cId : Fin ℓ) =>
    (Fin.append preFinalChallenges finalChallenges) ⟨cId, by
      rw [h_k]; rw [Nat.sub_add_cancel (n := ℓ) (m := ϑ) (h := by omega)]; simp only [cId.isLt]⟩)
    = (fun (cId : Fin ℓ) => (stmtOut.challenges cId)) := by
    funext cId
    dsimp only [preFinalChallenges, finalChallenges]
    by_cases h : cId.val < k
    · -- Case 1: cId < k_steps, so it's from the first part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      -- dsimp only [preFinalChallenges]
      simp only [h, ↓reduceDIte, Fin.castLT_mk, Fin.eta]
    · -- Case 2: cId >= k_steps, so it's from the second part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      congr 1; apply Fin.eq_of_val_eq; simp only; rw [add_comm]; omega
  rw [h_concat_challenges_eq]; rfl

def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
 | ⟨1, _⟩ => Unit

/-! The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ)) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl -- witMidSucc is of type Unit
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle 𝔽q β oStmtMid
    let polyOpt := extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ⟩) (f := f0)
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ - ↑(Fin.last ℓ))] := ⟨MvPolynomial.C stmtMid.sumcheck_target,
      by
        simp only [Fin.val_last, mem_restrictDegree, MvPolynomial.mem_support_iff,
          MvPolynomial.coeff_C, ne_eq, ite_eq_right_iff, Classical.not_imp, and_imp, forall_eq',
          Finsupp.coe_zero, Pi.zero_apply, zero_le, implies_true]⟩
    match polyOpt with
    | none =>
      -- Extraction failed - use constant H to satisfy sumcheckConsistencyProp trivially
      exact {
        t := ⟨0, by apply zero_mem⟩,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      -- Build H_ℓ from t and challenges r'
      exact {
        t := tpoly,
        -- projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := tpoly)
          -- (m := BBF_SumcheckMultiplierParam.multpoly stmtMid.ctx)
          -- (i := Fin.last ℓ) (challenges := stmtMid.challenges),
        H := H_constant,
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (mp := BBF_SumcheckMultiplierParam)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    let sumcheckFinalCheck : Prop := stmtIn.sumcheck_target
      = eqTilde (stmtIn.ctx.t_eval_point) stmtIn.challenges * c
    let finalFoldingProp := finalSumcheckStepFoldingStateProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ
        · exact hdiv.out) (input := ⟨stmtOut, oStmtIn⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-! The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) )
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    finalSumcheckKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (tr := tr) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    rw [cast_eq]; rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- toFun_next is impacted by how we build extractMid
    -- For pSpecCommit, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- declare c and stmtOut as in KState (m=1), as well as in honest verifier
    -- For the final sumcheck step, there is a single P→V message carrying the final constant,
    -- so we can read it directly from `msg` without reconstructing a truncated transcript.
    let c : L := msg
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    intro h_kState_round1
    unfold finalSumcheckKStateProp finalSumcheckStepFoldingStateProp
      masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    -- At m=1 we have local final-check and (oracle-consistency ∨ block-bad-event).
    -- At m=0 the target is Option-B masterKState:
    -- incremental-bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    obtain ⟨h_V_check, h_core⟩ := h_kState_round1
    -- Case split on the m=1 final-folding state: consistency or block bad-event.
    cases h_core with
    | inl hConsistent =>
      -- When we have finalSumcheckStepOracleConsistencyProp, extractMLP must succeed.
      have ⟨tpoly, h_extractMLP⟩ := extractMLP_some_of_oracleFoldingConsistency 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) (h_oracle_consistency := hConsistent)
      refine Or.inr ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local check at m=0
        unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod]
        simp only [MvPolynomial.eval_C, sum_const, Fintype.card_piFinset, card_map, card_univ,
          Fintype.card_fin, prod_const, tsub_self, Fintype.card_eq_zero, pow_zero, one_smul]
      · -- witnessStructuralInvariant
        unfold finalSumcheckRbrExtractor witnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [projectToMidSumcheckPoly_at_last_eq]
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            (BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          rw [h_V_check]
          congr 1
          change c = tpoly.val.eval stmtIn.challenges
          exact extracted_t_poly_eval_eq_final_constant 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly)
            (h_extractMLP := h_extractMLP) (h_finalSumcheckStepOracleConsistency := hConsistent)
        simp only
          [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
      · -- firstOracleWitnessConsistencyProp
        dsimp only [finalSumcheckRbrExtractor, firstOracleWitnessConsistencyProp]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle 𝔽q β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- Hybrid plan: map terminal block bad-event to incremental bad-event at m=0.
      exact Or.inl (
        (badEventExistsProp_iff_incrementalBadEventExistsProp_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
  -- Same pattern as relay: verifier output (stmtOut, oStmtOut) + h_relOut ⇒ commitKStateProp 1
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          _root_.support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (𝓑 := 𝓑)).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (𝓑 := 𝓑)).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support => -- same as fold step
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [finalSumcheckVerifier]
      -- dsimp only [StateT.run]
      -- simp only [simulateQ_bind, simulateQ_query, simulateQ_pure]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      -- enter [1, i_1, 2, 1, x]
      simp only [simulateQ_bind]
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
      simp only [Fin.isValue, id_eq, FullTranscript.mk1_eq_snoc, support_map, Set.mem_image,
        Prod.exists, exists_and_right, exists_eq_right]
      erw [simulateQ_bind]
      enter [1, x, 1, 1, 1, 2];
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    conv at h_output_mem_V_run_support =>
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, Function.comp_apply]
    erw [support_bind] at h_output_mem_V_run_support
    let step := (finalSumcheckStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    by_cases h_V_check : V_check
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_pure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      simp only [simulateQ_pure, Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        ] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
        exists_eq_right] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue]
      -- h_relOut : ((stmtOut, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
      simp only [finalSumcheckRelOut, finalSumcheckRelOutProp, Set.mem_setOf_eq] at h_relOut
      -- Goal: commitKStateProp 1 stmtIn oStmtIn tr witOut
      unfold finalSumcheckKStateProp
      -- Unfold the sendMessage, receiveChallenge, output logic of prover
      dsimp only
      -- stmtOut = stmtIn; need oStmtOut = snoc_oracle oStmtIn witOut.f so goal matches h_relOut
      simp only [h_stmtOut_eq] at h_relOut ⊢
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
      -- c equals tr.messages ⟨0, rfl⟩
      constructor
      · -- First conjunct: sumcheck_target = eqTilde r challenges * c
        exact h_V_check
      · -- Second conjunct:
        -- finalSumcheckStepFoldingStateProp ({ toStatement := stmtIn, final_constant := c }, oStmtIn)
        rw [h_oStmtOut_eq_oStmtIn] at h_relOut
        exact h_relOut
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_failure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      simp only [simulateQ_pure, Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        simulateQ_pure] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and,
        exists_false] at h_output_mem_V_run_support -- False

omit [Fintype L] [CharP L 2] in
/-! Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑)
        (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) )
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
      (rbrKnowledgeError := finalSumcheckKnowledgeError) := by
  use FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
  use finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckKnowledgeStateFunction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) init impl
  intro stmtIn witIn prover ⟨j, hj⟩
  -- pSpecFinalSumcheckStep has 1 message (ChallengeIdx = Fin 1); same pattern as commit
  cases j using Fin.cases with
  | zero => simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
    Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
    -- bound for challenge index 0 (P→V only, no V challenge)
  | succ j' => exact Fin.elim0 j'

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
