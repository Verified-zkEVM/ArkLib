/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.Data.FieldTheory.AdditiveNTT.Impl
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

namespace Binius.BinaryBasefold.CoreInteraction
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

instance foldStepLogic_verifierCheck_decidable (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (t : FullTranscript (pSpec := pSpecFold)) :
    Decidable ((foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := mp) i).verifierCheck stmtIn t) :=
  show Decidable (foldVerifierCheck i stmtIn (𝓑 := 𝓑) (t.messages ⟨0, rfl⟩)) from inferInstance

/-! The prover for the `i`-th round of Binary Foldfold. -/
def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    -- Both stmt and wit advances, but oStmt only advances at the commitment rounds only
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where
  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    let h_i := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let t := FullTranscript.mk2 (pSpec := pSpecFold (L := L)) h_i r_i'
    pure ((foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := mp) i).proverOut stmt wit oStmt t)

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
  verify := fun stmtIn pSpecChallenges => do
    let h_i ← query (spec := [(pSpecFold (L := L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' := pSpecChallenges ⟨1, rfl⟩
    guard (foldVerifierCheck (𝓑 := 𝓑) i stmtIn h_i)
    pure (foldVerifierStmtOut i stmtIn h_i r_i')
  embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).embed
  hEq := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).hEq

/-! Canonical fold-step reduction routed to the computable companion stack. -/
@[reducible]
def foldOracleReduction (i : Fin ℓ)
    (prover : OracleProver
      (oSpec := []ₒ)
      (StmtIn := Statement (L := L) Context i.castSucc)
      (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (StmtOut := Statement (L := L) Context i.succ)
      (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpec := pSpecFold (L := L))) :
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
  prover := prover
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
theorem foldOracleReduction_perfectCompleteness
  (i : Fin ℓ)
  (prover : OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)))
  (hInit : NeverFail init)
  :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc (mp := mp))
      (relOut := strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i (mp := mp))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i prover)
      (init := init)
      (impl := impl) := by sorry
/- Original proof depends on foldStepLogic.proverOut which is now sorry'd for computability. -/
/-
  classical
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecFold (L := L)) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [foldOracleReduction, foldOracleVerifier,
    OracleVerifier.toVerifier,
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
      simp only [OptionT.simulateQ_failure]
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
      simp only [OptionT.simulateQ_failure]
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
-/

open scoped NNReal

open Classical in
/-! Definition of the per-round RBR KS error for Binary FoldFold.
This combines the Sumcheck error (2/|L|) and the LDT Bad Event probability.
For round i : rbrKnowledgeError(i) = err_SC + err_BE where
- err_SC = 2/|L| (Schwartz-Zippel for degree 1)
- err_BE = |S^(last_oracle_domain_index_of_i + ϑ)| / |L|
-/
noncomputable def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
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
    let h_star : FoldMessage L :=
      getSumcheckRoundMessage (L := L) (ℓ := ℓ) (𝓑 := 𝓑) (i := i) witMid.H
    let h_i : FoldMessage L := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck :=
          FoldMessage.eval h_i (𝓑 0) + FoldMessage.eval h_i (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : FoldMessage L := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := FoldMessage.eval h_i r_i'
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
          FoldMessage.eval h_i (𝓑 0) + FoldMessage.eval h_i (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
          -- we also keep the output-state sumcheck consistency
          sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

-- Note: this fold step couldn't carry bad-event errors, because we don't have oracles yet.

/-! Knowledge state function (KState) for single round -/
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp)
      i).KnowledgeStateFunction init impl
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
        exact getSumcheckRoundMessage_sum_eq (L := L) (ℓ := ℓ) (𝓑 := 𝓑)
          (i := i) witMid.H
      exact Or.inr ⟨h_sumcheck, h_struct, h_init, h_fold⟩
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by sorry

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
    let h_star : FoldMessage L :=
      getSumcheckRoundMessage (L := L) (ℓ := ℓ) (𝓑 := 𝓑) (i := i) witMid.H
    let h_i : FoldMessage L := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck :=
          FoldMessage.eval h_i (𝓑 0) + FoldMessage.eval h_i (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : FoldMessage L := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := FoldMessage.eval h_i r_i'
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
  where `h_star = getSumcheckRoundMessage ℓ 𝓑 i witIn.H`.
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
lemma firstOracleWitnessConsistency_unique (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {t₁ t₂ : MultilinearPoly L ℓ}
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  sorry

/-! Extract the round-`i` witness (before the verifier challenge) from a fold-step output
witness. -/
@[reducible]
noncomputable def foldStepWitBeforeFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc :=
  (foldRbrExtractor.{0} (mp := mp) 𝔽q β i).extractMid
    (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid

/-! Canonical fold-step round polynomial extracted from a specific `witMid`. -/
@[reducible]
noncomputable def foldStepHStarFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    FoldMessage L :=
  let witBefore := foldStepWitBeforeFromWitMid
    (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i stmtOStmtIn h_i r_i' witMid
  getSumcheckRoundMessage (L := L) (ℓ := ℓ) (𝓑 := 𝓑) (i := i) witBefore.H

/-! At the same fold-step output state, `witnessStructuralInvariant`
and `firstOracleWitnessConsistencyProp` determine a unique witness.
Consequently, any witness-dependent extracted `h_star` is canonical. -/
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

lemma foldStepHStarFromWitMid_eq_of_oracleWitnessConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := FoldMessage.eval h_i r_i',
        challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
        ctx := stmtOStmtIn.1.ctx
      } witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := FoldMessage.eval h_i r_i',
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
  sorry

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
      sumcheck_target := FoldMessage.eval h_i r_i',
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
        (foldStepWitMidOracleConsistency 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ) (mp := mp)
          (i := i) stmtOStmtIn h_i r_i' witMid)
        ∧ badSumcheckEventProp r_i' (FoldMessage.eval h_i)
            (FoldMessage.eval
              (foldStepHStarFromWitMid (mp := mp) 𝔽q β
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
                i stmtOStmtIn h_i r_i' witMid))
      )
    ) := by
  sorry

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
    (`prop_4_21_2_incremental_bad_event_probability`).
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
  sorry

/-! RBR knowledge soundness for a single round oracle verifier -/
open Classical in
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp)
      i).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by sorry

end FoldStep
end SingleIteratedSteps
end Binius.BinaryBasefold.CoreInteraction
