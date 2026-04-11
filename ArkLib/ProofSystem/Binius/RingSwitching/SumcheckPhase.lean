/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.RingSwitching.Spec
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Module Binius.BinaryBasefold TensorProduct Nat Matrix ProbabilityTheory
open scoped NNReal

/-!
# Ring-Switching Core Interaction Phase

This module implements the core interactive sumcheck phase of the ring-switching protocol.

### Iterated Sumcheck Steps
6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.

Each iteration of the loop constitutes a single round:
- Round i (for i = 1, ..., ℓ'):
  1. Prover sends sumcheck polynomial h_i(X) over large field L
  2. Verifier samples challenge α_i ∈ L
    - Prover & verifier updates state based on challenge

This is the core computational phase with ℓ' rounds, each with 2 messages, and is the main
source of RBR knowledge soundness error.

### Final Sumcheck Step
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
9. `V` requires `s_{ℓ'} ?=`
  `(Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`. -/

namespace Binius.RingSwitching.SumcheckPhase
section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable (aOStmtIn : AbstractOStmtIn L ℓ')

section IteratedSumcheckStep
variable (i : Fin ℓ')

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check: validates that s = h(0) + h(1). -/
@[reducible]
def sumcheckVerifierCheck (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (h_i : FoldMessage L) : Prop :=
  FoldMessage.eval h_i (𝓑 0) + FoldMessage.eval h_i (𝓑 1) = stmtIn.sumcheck_target

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def sumcheckVerifierStmtOut (stmtIn : Statement (L := L) (ℓ := ℓ')
    (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (h_i : FoldMessage L) (r_i' : L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := FoldMessage.eval h_i r_i',
      challenges := Fin.snoc stmtIn.challenges r_i'
    }

/-- Pure prover message computation: computes h_i from the witness. -/
@[reducible]
def sumcheckProverComputeMsg (witIn : SumcheckWitness L ℓ' i.castSucc) :
    FoldMessage L :=
  Binius.RingSwitching.getSumcheckRoundMessage
    (κ := κ) (L := L) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (i := i) witIn.H

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def sumcheckProverWitOut (_stmtIn : Statement (L := L) (ℓ := ℓ')
  (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (witIn : SumcheckWitness L ℓ' i.castSucc) (r_i' : L) : SumcheckWitness L ℓ' i.succ :=
  {
      t' := witIn.t',
      H := Binius.RingSwitching.projectToNextSumcheckPoly (κ := κ)
        (L := L) (ℓ := ℓ) (ℓ' := ℓ')
        (i := i) witIn.H r_i'
  }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the i-th round of Ring Switching Sumcheck. -/
def sumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
      (SumcheckWitness L ℓ' i.castSucc)
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
      (SumcheckWitness L ℓ' i.succ)
      (pSpecSumcheckRound L) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.castSucc
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.succ
  verifierCheck := fun stmtIn transcript =>
    sumcheckVerifierCheck
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑)
      (i := i) stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    sumcheckVerifierStmtOut
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (i := i) stmtIn
      (transcript.messages ⟨0, rfl⟩) (transcript.challenges ⟨1, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg : FoldMessage L := @sumcheckProverComputeMsg κ L _ _ ℓ ℓ' 𝓑 i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let h_i := transcript.messages ⟨0, rfl⟩
    let r_i' := transcript.challenges ⟨1, rfl⟩
    let stmtOut := sumcheckVerifierStmtOut
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (i := i) stmtIn h_i r_i'
    let witOut := sumcheckProverWitOut
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (i := i) stmtIn witIn r_i'
    ((stmtOut, oStmtIn), witOut)

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the sumcheck phase. -/
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc
      × FoldMessage L
  | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc ×
    (∀ j, aOStmtIn.OStmtIn j) ×
    SumcheckWitness L ℓ' i.castSucc × FoldMessage L × L

/-- The prover for the `i`-th round of Ring Switching. -/
def iteratedSumcheckOracleProver (i : Fin ℓ') :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  PrvState := iteratedSumcheckPrvState κ L K ℓ ℓ' aOStmtIn i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
    | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
      let h_i : FoldMessage L := @sumcheckProverComputeMsg κ L _ _ ℓ ℓ' 𝓑 i wit
      pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
    | ⟨1, h⟩ => fun _ => do
      nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
      pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let logic := sumcheckStepLogic
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (i := i)
    let t := FullTranscript.mk2 h_i r_i'
    pure (logic.proverOut stmt wit oStmt t)

/-- The oracle verifier for the `i`-th round of Ring Switching. -/
def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) where
  verify := fun stmtIn pSpecChallenges => do
    let _keepβ := β
    let _keeph_l := h_l
    let _keepOStmt := aOStmtIn
    let h_i : FoldMessage L ← query (spec := [(pSpecSumcheckRound L).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩
    guard <| sumcheckVerifierCheck
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑)
      (i := i) stmtIn h_i
    pure <| sumcheckVerifierStmtOut
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (i := i) stmtIn h_i r_i'
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction that is the `i`-th round of Ring Switching. -/
def iteratedSumcheckOracleReduction (i : Fin ℓ') :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  prover := iteratedSumcheckOracleProver
    (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (i := i)
  verifier := iteratedSumcheckOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i

/-! ## Strong Completeness Theorem -/

lemma sumcheckStep_is_logic_complete (i : Fin ℓ') :
    (sumcheckStepLogic
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (i := i)).IsStronglyComplete := by
  sorry

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ') (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.castSucc)
      (relOut := strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)
      (init := init) (impl := impl) := by
  sorry
  /- Step 1: Unroll the 2-message reduction to convert from probability to logic
  -- **NOTE**: this requires `ProtocolSpec.challengeOracleInterface` to avoid conflict
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecSumcheckRound L) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver,
    iteratedSumcheckOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk2]
  let step := (sumcheckStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)) (i := i)
  let strongly_complete : step.IsStronglyComplete := by
    -- TODO: restore `sumcheckStep_is_logic_complete i` after elaboration/instance audit (`NeZero ↑i`).
    sorry
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
      rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      change vStmtOut ∈ support (Bind.bind (m := (OracleComp []ₒ)) _ _)
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
        (msg1 := (FullTranscript.mk2
          (sumcheckProverComputeMsg κ L ℓ ℓ' i witIn)
          r_i').challenges
          ⟨1, rfl⟩))
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
    simp only [Fin.isValue, OptionT.run_pure, probOutput_none_pure_some_eq_zero]
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
        (msg1 := (FullTranscript.mk2
          (sumcheckProverComputeMsg κ L ℓ ℓ' i witIn)
          r1).challenges
          ⟨1, rfl⟩)) with h_V_check_def
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
    dsimp only [sumcheckStepLogic, sumcheckProverComputeMsg, step] at prvOut_eq
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

noncomputable def iteratedSumcheckRoundKnowledgeError (_ : Fin ℓ') : ℝ≥0 := (2 : ℝ≥0) / (Fintype.card L)

/-- Witness type at each message index for the iterated sumcheck step
  (counterpart of BBF `foldWitMid`).
  At m=0,1 we have input-round witness; at m=2 we have output-round witness so extractOut can
    be identity. -/
def iteratedSumcheckWitMid (i : Fin ℓ') : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨2, _⟩ => SumcheckWitness L ℓ' i.succ

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both SumcheckWitness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1: extract backward from output witness using input challenges
      {
        t' := witMidSucc.t',
        H := projectToMidSumcheckPoly (κ := κ)
          (L := L) (ℓ := ℓ) (ℓ' := ℓ') (t := witMidSucc.t')
          (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
          (i := i.castSucc) (challenges := stmtIn.challenges)
      }
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-- KState for the iterated sumcheck step, matching the structure of Binary Basefold's
`foldKStateProp`:
- m=0: same as relIn (masterKStateProp at i.castSucc with sumcheckConsistencyProp)
- m=1: after P sends hᵢ(X), before V sends r'ᵢ (explicitVCheck ∧ localizedRoundPolyCheck)
- m=2: after V sends r'ᵢ — OUTPUT state (masterKStateProp at i.succ with stmtOut, witMid,
  sumcheckConsistencyProp)
  At m=2, witMid has type SumcheckWitness i.succ (via iteratedSumcheckWitMid). -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmtMid : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (witMid : iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i) m)
    (oStmtMid : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as relIn (sumcheckRoundRelation at i.castSucc)
    RingSwitching.masterKStateProp κ L K ℓ ℓ'
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks := sumcheckConsistencyProp
        (sumcheckTarget := stmtMid.sumcheck_target) (H := witMid.H))
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r'ᵢ
    let h_star : FoldMessage L :=
      getSumcheckRoundMessage
        (κ := κ) (L := L) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (i := i) witMid.H
    let h_i : FoldMessage L := tr.messages ⟨0, rfl⟩
    RingSwitching.masterKStateProp κ L K ℓ ℓ' aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks :=
        let explicitVCheck :=
          FoldMessage.eval h_i (𝓑 0) + FoldMessage.eval h_i (𝓑 1) = stmtMid.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r'ᵢ: use OUTPUT state (witMid is already SumcheckWitness i.succ)
    let h_i : FoldMessage L := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ :=
      sumcheckVerifierStmtOut (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') i stmtMid h_i r_i'
    let oStmtOut := oStmtMid
    let witOut := witMid
    RingSwitching.masterKStateProp κ L K ℓ ℓ' aOStmtIn
      (stmtIdx := i.succ)
      (stmt := stmtOut) (oStmt := oStmtOut) (wit := witOut)
      (localChecks :=
        let explicitVCheck :=
          FoldMessage.eval h_i (𝓑 0) + FoldMessage.eval h_i (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
        sumcheckConsistencyProp (sumcheckTarget := stmtOut.sumcheck_target) (H := witOut.H)
      )

/-- Knowledge state function (KState) for single round -/
  def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i)) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    iteratedSumcheckKStateProp
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (i := i) (m := m) (tr := tr)
      (stmtMid := stmtMid) (witMid := witMid) (oStmtMid := oStmtMid)
  toFun_empty := by
    intro stmtIn witMid
    cases stmtIn
    rfl
  toFun_next := by
    sorry
  toFun_full := by
    sorry

/-- Extraction failure implies a witness-dependent bad sumcheck event (no folding here).
  The extracted `witMid` also carries oracle compatibility at the same `oStmt`. -/
lemma iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) (r_i' : L)
      (doomEscape : rbrExtractionFailureEvent
      (kSF := iteratedSumcheckKnowledgeStateFunction
        κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (init := init) (impl := impl) i)
      (extractor := iteratedSumcheckRbrExtractor
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i))
      (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := FullTranscript.mk1 h_i)
      (challenge := r_i')) :
    ∃ witMid : SumcheckWitness L ℓ' i.succ,
      aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2) ∧
      let witBefore : SumcheckWitness L ℓ' i.castSucc :=
        (iteratedSumcheckRbrExtractor.{0, 0}
          (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
          (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i)).extractMid
          (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid
      let h_star : FoldMessage L := getSumcheckRoundMessage
        (κ := κ) (L := L) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (i := i) witBefore.H
      badSumcheckEventProp r_i' (FoldMessage.eval h_i) (FoldMessage.eval h_star) := by
  sorry

/-- Per-transcript bound: for prover message h_i, the probability (over verifier challenge y)
  that extraction fails is at most iteratedSumcheckRoundKnowledgeError (2/|L|).
  Counterpart of BBF `foldStep_doom_escape_probability_bound`; no folding bad event here. -/
lemma iteratedSumcheck_doom_escape_probability_bound (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction
          κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor
          (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
          (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      iteratedSumcheckRoundKnowledgeError L ℓ' i := by
  sorry

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i.succ)
      (rbrKnowledgeError := fun _ => iteratedSumcheckRoundKnowledgeError L ℓ' i) := by
  sorry
  /- Original proof commented out
  intro stmtOStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (kSF := iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K)
    (ℓ := ℓ) (ℓ' := ℓ') (β := β) (𝓑 := 𝓑) (h_l := h_l) aOStmtIn (impl := impl) (init := init) i)
    (iteratedSumcheckRbrExtractor
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i))
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
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr (L := L) (P :=
      fun x_1 => P (FullTranscript.mk1 x.1.1) (q.2 x_1))]
    -- Make this explicit using change
    -- Apply the per-transcript bound (Ring-switching counterpart of
      -- foldStep_doom_escape_probability_bound)
    exact iteratedSumcheck_doom_escape_probability_bound (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓑 := 𝓑) (β := β) (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i)
      (stmtOStmtIn := stmtOStmtIn) (h_i := x.1.1)
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply tsum_probOutput_le_one
  -/

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check: validates that s_{ℓ'} = eq_tilde_eval * s'.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁ (r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
Then `V` computes the final eq value: `(Σ_{u ∈ {0,1}^κ} eq̃ (u_0, ..., u_{κ-1},`
  `r''_0, ..., r''_{κ-1}) ⋅ e_u)`
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_ {κ-1},`
  `r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`. -/
@[reducible]
def finalSumcheckVerifierCheck
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (s' : L) : Prop :=
  let eq_tilde_eval : L :=
    compute_final_eq_value
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  stmtIn.sumcheck_target = eq_tilde_eval * s'

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def finalSumcheckVerifierStmtOut
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (s' : L) : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }

/-- Pure prover message computation: computes s' from the witness. -/
@[reducible]
def finalSumcheckProverComputeMsg
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')) : L :=
  CPoly.CMvPolynomial.eval stmtIn.challenges witIn.t'

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def finalSumcheckProverWitOut (witIn : SumcheckWitness L ℓ' (Fin.last ℓ')) : WitMLP L ℓ' :=
    { t := witIn.t' }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the final sumcheck step.
This is a 1-message protocol where the prover sends the final constant s'. -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
      (SumcheckWitness L ℓ' (Fin.last ℓ'))
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (MLPEvalStatement L ℓ')
      (WitMLP L ℓ')
      (pSpecFinalSumcheckStep (L := L)) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn (Fin.last ℓ')
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ aOStmtIn.toStrictRelInput
  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K ℓ ℓ' stmtIn (transcript.messages ⟨0, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl
  honestProverTranscript := fun stmtIn witIn _oStmtIn _chal =>
    let s' : L := finalSumcheckProverComputeMsg
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') witIn stmtIn
    FullTranscript.mk1 s'
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let s' : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K ℓ ℓ' stmtIn s'
    let witOut := finalSumcheckProverWitOut (L := L) (ℓ' := ℓ') witIn
    ((stmtOut, oStmtIn), witOut)

/-! ## Helper Lemmas for Strong Completeness -/

/-- At `Fin.last ℓ'`, the sumcheck consistency sum is over 0 variables,
simplifying to a single evaluation. This is analogous to Binary Basefold's
simplification of `𝓑^ᶠ(0) = {∅}`. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : MultiquadraticPoly L (ℓ' - Fin.last ℓ'))
    (h_cons : sumcheckConsistencyProp (sumcheckTarget := target)
      (H := (H : CPoly.CMvPolynomial (ℓ' - Fin.last ℓ') L))) :
    target = H.val.eval (fun _ => (0 : L)) := by
  sorry

/-- The honest prover's message in the final sumcheck step equals `t'(challenges)`. -/
lemma finalSumcheck_honest_message_eq_t'_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges) :
    let step := finalSumcheckStepLogic
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = CPoly.CMvPolynomial.eval stmtIn.challenges witIn.t' := by
  sorry

/-- **Main helper lemma**: The verifier check passes in the final sumcheck step.

**Proof Structure** (following Binary Basefold's `finalSumcheckStep_verifierCheck_passed`):
1. From `sumcheckConsistencyProp`:
   - `stmtIn.sumcheck_target = ∑ x ∈ 𝓑^ᶠ(0), witIn.H.val.eval x`
   - Since `𝓑^ᶠ(0) = {∅}`, this simplifies to `witIn.H.val.eval (fun _ => 0)`

2. From `witnessStructuralInvariant`:
   - `witIn.H = projectToMidSumcheckPoly t' (m := A_MLE) (Fin.last ℓ') challenges`
   - Using `projectToMidSumcheckPoly_at_last_eval`:
   - `witIn.H.val.eval (fun _ => 0) = A_MLE.eval(challenges) * t'.eval(challenges)`

3. `A_MLE.eval(challenges) = compute_final_eq_value ...` by definition.

4. Combining gives: `target = compute_final_eq_value * t'(challenges) = compute_final_eq_value * s'`
-/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp
      (sumcheckTarget := stmtIn.sumcheck_target) (H := witIn.H))
    (h_wit_struct : witnessStructuralInvariant κ L K ℓ ℓ' stmtIn witIn) :
    let step := finalSumcheckStepLogic
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  sorry

/-! ## Strong Completeness Theorem -/

/-- Final sumcheck step logic is strongly complete.
**Key Proof Obligations:**
1. **Verifier Check**: Show that `stmtIn.sumcheck_target = eq_tilde_eval * s'` where
  `s' = witIn.t'.val.eval stmtIn.challenges`
   - This should follow from `h_relIn` (sumcheckRoundRelation) which includes `masterKStateProp`
   - The `masterKStateProp` includes:
     * `witnessStructuralInvariant`: `wit.H = projectToMidSumcheckPoly ...`
     * `sumcheckConsistencyProp`: `stmt.sumcheck_target =`
                                    `∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - Fin.last ℓ'), wit.H.val.eval x`
       For `i = Fin.last ℓ'`, we have `ℓ' - Fin.last ℓ' = 0`, so this is a sum over 0 variables
        (a constant)
   - Need to connect these properties to show the verifier check passes

2. **Relation Out**: Show that the output satisfies `aOStmtIn.toStrictRelInput`
   - This involves showing `MLPEvalRelation` and `strictInitialCompatibility` hold for the output
-/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn)).IsStronglyComplete := by
  sorry

/-! ## Prover and Verifier Implementation -/

/-- The prover for the final sumcheck step -/
def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' := finalSumcheckProverComputeMsg
      (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') witIn stmtIn
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn)
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The verifier for the final sumcheck step -/
def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    let s' : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) s'
    let logic := finalSumcheckStepLogic
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn)
    have : Decidable (logic.verifierCheck stmtIn t) := by
      change Decidable (finalSumcheckVerifierCheck
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) stmtIn s')
      infer_instance
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := (finalSumcheckStepLogic
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (aOStmtIn := aOStmtIn)).embed
  hEq := (finalSumcheckStepLogic
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (aOStmtIn := aOStmtIn)).hEq

/-- The oracle reduction for the final sumcheck step -/
def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (aOStmtIn := aOStmtIn)
  verifier := finalSumcheckVerifier κ L K β ℓ ℓ' h_l aOStmtIn

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (relIn := strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toStrictRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K β ℓ ℓ' h_l aOStmtIn)
      (init := init) (impl := impl) := by sorry
  /- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
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
      change vStmtOut ∈ support (Bind.bind (m := (OracleComp []ₒ)) _ _)
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
    simp only [ChallengeIdx, Challenge, liftComp_eq_liftM, liftM_pure, liftComp_id, support_pure,
      Set.mem_singleton_iff, MessageIdx, Message, Fin.isValue] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    rcases hx_mem_support with ⟨h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support =>
      dsimp only [finalSumcheckStepLogic]
      simp only [Fin.val_last, Fin.isValue, Prod.mk.injEq, and_true]
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      simp only [Set.mem_singleton_iff]
      -- change (some (verStmtOut, verOStmtOut)) ∈ support (liftComp _ _)
      erw [support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      simp only [Fin.isValue, Fin.val_last, OptionT.simulateQ_simOracle2_liftM_query_T2, pure_bind,
        OptionT.simulateQ_bind, toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
        Set.mem_iUnion, exists_prop]
      rw [simulateQ_ite]; erw [simulateQ_pure]
      simp only [OptionT.simulateQ_failure]
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
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_mem_support
    constructor
    · rw [verStmtOut_eq, verOStmtOut_eq, prvWitOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2
  -/

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

/-- The round-by-round extractor for the final sumcheck step.
  We do not collapse the witness away (unlike BBF): WitMid stays as full SumcheckWitness,
  and we pass the polynomial t' (WitMLP) plus MLPEvalStatement to a final PCS invocation. -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc
  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPoly (κ := κ)
      (L := L) (ℓ := ℓ) (ℓ' := ℓ') (t := witOut.t)
      (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/-- KState for the final sumcheck step, in the same style as BBF `finalSumcheckKStateProp`:
  m=0: same as relIn (masterKStateProp with sumcheckConsistencyProp).
  m=1: name prover message as `c`, build output statement `stmtOut`, then
  sumcheckFinalCheck ∧ finalEvalCheck ∧ oracleCompatProp
    (no folding; RS has only sumcheck + oracle compat). -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    RingSwitching.masterKStateProp κ L K ℓ ℓ' aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmtIn) (oStmt := oStmtIn) (wit := witMid)
      (localChecks := sumcheckConsistencyProp
        (sumcheckTarget := stmtIn.sumcheck_target) (H := witMid.H))
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges,
      original_claim := c
    }
    let sumcheckFinalVCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value
        (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
      stmtIn.sumcheck_target = eq_tilde_eval * c
    let finalEvalCheck : Prop := CPoly.CMvPolynomial.eval stmtOut.t_eval_point witMid.t' = stmtOut.original_claim
    let oracleCompatProp : Prop := aOStmtIn.initialCompatibility ⟨witMid.t', oStmtIn⟩
    let witnessStructProp : Prop := witnessStructuralInvariant κ L K ℓ ℓ' stmtIn witMid
    sumcheckFinalVCheck ∧ finalEvalCheck ∧ oracleCompatProp ∧ witnessStructProp

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' h_l aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn)) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    finalSumcheckKStateProp κ L K β ℓ ℓ' h_l
      (aOStmtIn := aOStmtIn) (m := m) (tr := tr)
      (stmtIn := stmtMid) (witMid := witMid) (oStmtIn := oStmtMid)
  toFun_empty := by
    intro stmtIn witMid
    cases stmtIn
    rfl
  toFun_next := by
    sorry
  toFun_full := by
    sorry

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := finalSumcheckKnowledgeError (L := L)) := by
  sorry

end FinalSumcheckStep

section LargeFieldReduction

/-- Composed oracle verifier for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleVerifier :=
  OracleVerifier.seqCompose (m := ℓ') (oSpec := []ₒ)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ))
    (V := fun (i : Fin ℓ') =>
      iteratedSumcheckOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)

/-- Composed oracle reduction for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckLoop L ℓ')
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := SumcheckWitness L ℓ' (Fin.last ℓ')) :=
  OracleReduction.seqCompose (m:=ℓ') (oSpec:=[]ₒ)
    (OStmt := fun _ => (aOStmtIn.OStmtIn (L := L) (ℓ' := ℓ')))
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (Oₘ := fun _ j => instOracleInterfaceMessagePSpecSumcheckRound L j)
    (R := fun (i : Fin ℓ') =>
      iteratedSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K β ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheckStep (L := L))

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K β ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheckStep (L := L))

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (relIn := strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn 0)
    (relOut := aOStmtIn.toStrictRelInput)
    (init := init)
    (impl := impl) := by
  sorry

/-- standard sumcheck error -/
noncomputable def coreInteractionRbrKnowledgeError (_ : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  (2 : ℝ≥0) / (Fintype.card L) -- this terms comes from the sumcheck
    -- steps, i.e. iteratedSumcheckRoundKnowledgeError

/-- RBR knowledge soundness for the sumcheck loop (seqCompose over ℓ'). -/
theorem sumcheckLoopOracleVerifier_rbrKnowledgeSoundness :
  (sumcheckLoopOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (relIn := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn 0)
    (relOut := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn (Fin.last ℓ'))
    (rbrKnowledgeError := fun _ => (2 : ℝ≥0) / Fintype.card L) := by
  sorry

/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := coreInteractionOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (init := init)
    (impl := impl)
    (relIn := sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  sorry

end LargeFieldReduction
end
end Binius.RingSwitching.SumcheckPhase
