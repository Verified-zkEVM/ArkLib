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

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Module Binius.BinaryBasefold TensorProduct Nat Matrix
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
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
-/

namespace Binius.RingSwitching.SumcheckPhase
noncomputable section

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
def sumcheckVerifierCheck (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (h_i : L⦃≤ 2⦄[X]) : Prop :=
  h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtIn.sumcheck_target

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def sumcheckVerifierStmtOut (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (h_i : L⦃≤ 2⦄[X]) (r_i' : L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtIn.challenges r_i'
    }

/-- Pure prover message computation: computes h_i from the witness. -/
@[reducible]
def sumcheckProverComputeMsg (witIn : SumcheckWitness L ℓ' i.castSucc) : L⦃≤ 2⦄[X] :=
  getSumcheckRoundPoly ℓ' 𝓑 (i := i) witIn.H

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def sumcheckProverWitOut (_stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (witIn : SumcheckWitness L ℓ' i.castSucc) (r_i' : L) : SumcheckWitness L ℓ' i.succ :=
  {
      t' := witIn.t',
      H := projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
  }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the i-th round of Ring Switching Sumcheck. -/
def sumcheckStepLogic :
    Binius.BinaryBasefold.CoreInteraction.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
      (SumcheckWitness L ℓ' i.castSucc)
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
      (SumcheckWitness L ℓ' i.succ)
      (pSpecSumcheckRound L) where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i.castSucc
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i.succ

  verifierCheck := fun stmtIn transcript =>
    sumcheckVerifierCheck (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (𝓑:=𝓑) i stmtIn (transcript.messages ⟨0, rfl⟩)

  verifierOut := fun stmtIn transcript =>
    sumcheckVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn (transcript.messages ⟨0, rfl⟩) (transcript.challenges ⟨1, rfl⟩)

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl

  -- honestProverTranscript is the concatenation of sendMessage & receiveChallenge methods
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg := sumcheckProverComputeMsg (L:=L) (ℓ':=ℓ') (𝓑:=𝓑) i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)

  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let h_i := transcript.messages ⟨0, rfl⟩
    let r_i' := transcript.challenges ⟨1, rfl⟩
    let stmtOut := sumcheckVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn h_i r_i'
    let witOut := sumcheckProverWitOut (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn witIn r_i'
    ((stmtOut, oStmtIn), witOut)

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the sumcheck phase. -/
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc × L⦃≤ 2⦄[X]
  | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc ×
    (∀ j, aOStmtIn.OStmtIn j) ×
    SumcheckWitness L ℓ' i.castSucc × L⦃≤ 2⦄[X] × L

/-- The prover for the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleProver (i : Fin ℓ') :
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

  sendMessage -- There are 2 messages in the pSpec
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    let h_i := sumcheckProverComputeMsg (L:=L) (ℓ':=ℓ') (𝓑:=𝓑) i wit
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))

  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let logic := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i
    let t := FullTranscript.mk2 h_i r_i'
    pure (logic.proverOut stmt wit oStmt t)

open Classical in
/-- The oracle verifier for the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    -- next round
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript.
  verify := fun stmtIn pSpecChallenges => do
    -- Message 0 : Receive h_i(X) from prover
    let h_i : L⦃≤ 2⦄[X] ← query (spec := [(pSpecSumcheckRound L).Message]ₒ)
       ⟨⟨0, by rfl⟩, (by simpa using ())⟩
    -- Message 1 : Sample challenge r'_i and send to prover
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩
    let t := FullTranscript.mk2 h_i r_i'
    let logic := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction that is the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleReduction (i : Fin ℓ') :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  prover := iteratedSumcheckOracleProver κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i
  verifier := iteratedSumcheckOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i

/-! ## Strong Completeness Theorem -/

omit [NeZero κ] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] in
lemma sumcheckStep_is_logic_complete (i : Fin ℓ') :
    (sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ)
    (ℓ':=ℓ') (h_l:=h_l) (𝓑:=𝓑) (aOStmtIn:=aOStmtIn) i
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2

  dsimp only [sumcheckStepLogic, sumcheckRoundRelation,
    sumcheckRoundRelationProp, masterKStateProp] at h_relIn

  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H
    := h_relIn.2.2.1

  -- Fact 1: Verifier check passes
  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    simp only [sumcheckStepLogic, step, sumcheckVerifierCheck]
    rw [h_sumcheck_cons]
    apply getSumcheckRoundPoly_sum_eq (𝓑 := 𝓑) (i := i) (h := witIn.H)

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := rfl

  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    simp only [step, sumcheckStepLogic]
    -- Fact 4: Prover and verifier oracle statements agree
    unfold OracleVerifier.mkVerifierOStmtOut
    funext j
    split
    · rename_i j' heq
      simp only [MessageIdx, Function.Embedding.coeFn_mk, Sum.inl.injEq] at heq
      cases heq
      rfl
    · rename_i heq
      simp only [MessageIdx, Function.Embedding.coeFn_mk, reduceCtorEq] at heq

  -- Key fact: Oracle statements are unchanged in the fold step
  -- (all oracle indices map via Sum.inl in the embedding)
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, sumcheckStepLogic]

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (sumcheckRoundRelation)
    simp only [step, sumcheckStepLogic, sumcheckRoundRelation,
      sumcheckRoundRelationProp, masterKStateProp]
    let r_i' := challenges ⟨1, rfl⟩
    simp only [Fin.val_succ, true_and, Set.mem_setOf_eq]
    simp only [Fin.val_castSucc] at h_relIn
    have h_oracleWitConsistency_In := h_relIn.2
    rw [h_verifierOStmtOut_eq];
    dsimp only [strictOracleWitnessConsistency] at h_oracleWitConsistency_In ⊢
    -- Extract the three components from the input
    obtain ⟨h_wit_struct_In, ⟨h_sumcheck_cons_In, h_oStmtIn_compat⟩⟩ :=
      h_oracleWitConsistency_In

    constructor
    · -- Component 1: witnessStructuralInvariant
      unfold witnessStructuralInvariant at ⊢ h_wit_struct_In
      let h_H_In := h_wit_struct_In
      conv_lhs =>
        dsimp only [proverWitOut, proverOutput, step,
        sumcheckStepLogic]
      conv_lhs =>
        rw [h_H_In]
        rw [←projectToMidSumcheckPoly_succ]
      rfl
    · constructor
      · -- Part 2.1: sumcheckConsistencyProp
        unfold sumcheckConsistencyProp
        dsimp only [verifierStmtOut, proverWitOut, proverOutput]
        simp only [step, sumcheckStepLogic, transcript]
        apply projectToNextSumcheckPoly_sum_eq
      · --Part 2.2: initialCompatibility
        exact h_oStmtIn_compat

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ') (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (𝓑:=𝓑) (β := β) (h_l := h_l) aOStmtIn i)
      (init := init)
      (impl := impl) := by
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
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
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver, iteratedSumcheckOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk2]
  let step := (sumcheckStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)) (i := i)
  let strongly_complete : step.IsStronglyComplete := sumcheckStep_is_logic_complete (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i)

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
      change vStmtOut ∈ (Bind.bind (m := (OracleComp []ₒ)) _ _).support
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
        (msg1 := (FullTranscript.mk2 (sumcheckProverComputeMsg L ℓ' i witIn) r_i').challenges ⟨1, rfl⟩))
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
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (sumcheckProverComputeMsg L ℓ' i witIn) r1).challenges ⟨1, rfl⟩))
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

def iteratedSumcheckRoundKnowledgeError (_ : Fin ℓ') : ℝ≥0 := (2 : ℝ≥0) / (Fintype.card L)

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := fun _messageIdx => SumcheckWitness L ℓ' i.castSucc) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun ⟨stmtIn, oStmtIn⟩ fullTranscript witOut => by
    exact {
      t' := witOut.t',
      H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
        (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
        (i := i.castSucc) (challenges := stmtIn.challenges)
    }

/-- This follows the KState of `foldKStateProp` -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) i.castSucc)
    (witMid : SumcheckWitness L ℓ' i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  -- Ground-truth polynomial from witness
  let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' 𝓑 (i := i) (h := witMid.H)
  -- Checks available after message 1 (P -> V : hᵢ(X))
  let get_Hᵢ := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 1 ≤ m.val) =>
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le hm⟩, by simp [pSpecSumcheckRound]; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    h_i

  let get_rᵢ' := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 2 ≤ m.val) =>
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (Nat.le_trans (by decide) hm)⟩, by simp; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    let i_msg2 : ((pSpecSumcheckRound L).take m m.is_le).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le hm⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let r_i' : L := chalsUpTo i_msg2
    r_i'

  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑)
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, h1⟩ => -- P sends hᵢ(X)
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨1, h1⟩) (tr := tr) (hm := by simp only [le_refl])
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmt.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, h2⟩ => -- implied by (relOut + V's check)
    -- The bad-folding-event of `fᵢ` is also introduced internaly by `masterKStateProp`
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [Nat.one_le_ofNat])
        let r_i' := get_rᵢ' (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [le_refl])
        let localizedRoundPolyCheck := h_i = h_star
        let nextSumcheckTargetCheck := -- this presents sumcheck of next round (sᵢ = s^*ᵢ)
          h_i.val.eval r_i' = h_star.val.eval r_i'
        localizedRoundPolyCheck ∧ nextSumcheckTargetCheck
      ) -- this holds the  constraint for witOut in relOut

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun _ _ => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_castSucc, cast_eq,
      Set.mem_setOf_eq, iteratedSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmtIn tr msg witMid => by
    obtain ⟨stmt, oStmt⟩ := stmtIn
    fin_cases m
    · -- m = 0: succ = 1, castSucc = 0
      unfold iteratedSumcheckKStateProp
      simp only [masterKStateProp, iteratedSumcheckRbrExtractor, true_and]
      simp only [Fin.succ_mk, Fin.castSucc_mk, Fin.castAdd_mk]
      tauto
    · -- m = 1: dir 1 = V_to_P, contradicts hDir
      simp [pSpecSumcheckRound] at hDir
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut => by
    intro h_relOut
    simp at h_relOut
    rcases h_relOut with ⟨stmtOut, ⟨oStmtOut, h_conj⟩⟩
    have h_simulateQ := h_conj.1
    have h_SumcheckStepRelOut := h_conj.2
    set witLast := (iteratedSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn i).extractOut
      ⟨stmtLast, oStmtLast⟩ tr witOut
    simp only [Fin.reduceLast, Fin.isValue]
    -- ⊢ iteratedSumcheckKStateProp 𝔽q β 2 tr stmtLast witLast oStmtLast
    -- TODO : prove this via the relations between stmtLast & stmtOut,
      --  witLast & witOut, oStmtLast & oStmtOut
    sorry

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (𝓑:=𝓑) (β := β) (h_l := h_l) aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i.succ)
      (fun j => iteratedSumcheckRoundKnowledgeError L ℓ' i) := by
  use fun _ => SumcheckWitness L ℓ' i.castSucc
  use iteratedSumcheckRbrExtractor κ (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (β := β) (h_l := h_l) aOStmtIn i
  use iteratedSumcheckKnowledgeStateFunction (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ') (𝓑 := 𝓑) (β := β) (h_l := h_l) aOStmtIn i
  intro stmtIn witIn prover j
  sorry

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
  let eq_tilde_eval : L := compute_final_eq_value κ L K β ℓ ℓ' h_l
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
  witIn.t'.val.eval stmtIn.challenges

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def finalSumcheckProverWitOut (witIn : SumcheckWitness L ℓ' (Fin.last ℓ')) : WitMLP L ℓ' :=
    { t := witIn.t' }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the final sumcheck step.
This is a 1-message protocol where the prover sends the final constant s'. -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.CoreInteraction.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
      (SumcheckWitness L ℓ' (Fin.last ℓ'))
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (MLPEvalStatement L ℓ')
      (WitMLP L ℓ')
      (pSpecFinalSumcheck L) where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ')

  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ aOStmtIn.toRelInput

  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)

  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K ℓ ℓ' stmtIn (transcript.messages ⟨0, rfl⟩)

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

  honestProverTranscript := fun stmtIn witIn _oStmtIn _chal =>
    let s' : L := finalSumcheckProverComputeMsg κ L K ℓ ℓ' witIn stmtIn
    FullTranscript.mk1 s'

  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let s' : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K ℓ ℓ' stmtIn s'
    let witOut := finalSumcheckProverWitOut (L := L) (ℓ' := ℓ') witIn
    ((stmtOut, oStmtIn), witOut)

/-! ## Helper Lemmas for Strong Completeness -/

/-- At `Fin.last ℓ'`, the sumcheck consistency sum is over 0 variables, simplifying to a single evaluation.
This is analogous to Binary Basefold's simplification of `𝓑^ᶠ(0) = {∅}`. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - Fin.last ℓ')])
    (h_cons : sumcheckConsistencyProp (𝓑 := 𝓑) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  -- Since ℓ' - Fin.last ℓ' = 0, the sum is over Fin 0 which has only one element
  simp only [Fin.val_last, tsub_self] at H h_cons ⊢
  simp only [sumcheckConsistencyProp, Fin.val_last, tsub_self] at h_cons
  -- The piFinset over Fin 0 has only one element: fun _ => 0
  haveI : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso; apply hb_ne
      funext i;
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso; apply h_not_mem
      simp only [Fintype.mem_piFinset]
      intro i; simp only [tsub_self] at i; exact i.elim0)] at h_cons
  exact h_cons

/-- The honest prover's message in the final sumcheck step equals `t'(challenges)`. -/
lemma finalSumcheck_honest_message_eq_t'_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheck L).Challenges) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.t'.val.eval stmtIn.challenges := by
  -- Direct from the definition of honestProverTranscript
  simp only [finalSumcheckStepLogic, finalSumcheckProverComputeMsg]

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
    (challenges : (pSpecFinalSumcheck L).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : witnessStructuralInvariant κ L K β ℓ ℓ' h_l stmtIn witIn) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  intro step transcript
  -- Step 1: Simplify sumcheck consistency to single evaluation
  have h_target_eq_H_eval : stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => 0) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ' := ℓ') (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H h_sumcheck_cons

  -- Step 2: Use witnessStructuralInvariant to connect H to projected poly
  have h_H_eq : witIn.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t')
    (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx)
    (i := Fin.last ℓ') (challenges := stmtIn.challenges) := h_wit_struct

  -- Step 3: Apply projectToMidSumcheckPoly_at_last_eval
  have h_proj_eval : (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t')
    (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx)
    (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => 0) =
    ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval stmtIn.challenges *
    witIn.t'.val.eval stmtIn.challenges := by
      apply projectToMidSumcheckPoly_at_last_eval

  -- Step 4: Connect multiplier poly to compute_final_eq_value
  -- This requires showing that A_MLE.eval(challenges) = compute_final_eq_value
  have h_mult_eq_eq_value : ((RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval stmtIn.challenges =
    compute_final_eq_value κ L K β ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
      compute_A_MLE_eval_eq_final_eq_value κ L K β ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching

  -- Step 5: Get the honest message
  have h_msg_eq : transcript.messages ⟨0, rfl⟩ = witIn.t'.val.eval stmtIn.challenges :=
    finalSumcheck_honest_message_eq_t'_eval κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn stmtIn witIn oStmtIn challenges

  -- Step 6: Combine everything
  simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierCheck]
  rw [h_target_eq_H_eval, Subtype.val_inj.mpr h_H_eq, h_proj_eval, h_mult_eq_eq_value, h_msg_eq]

/-! ## Strong Completeness Theorem -/

/-- Final sumcheck step logic is strongly complete.
**Key Proof Obligations:**
1. **Verifier Check**: Show that `stmtIn.sumcheck_target = eq_tilde_eval * s'` where `s' = witIn.t'.val.eval stmtIn.challenges`
   - This should follow from `h_relIn` (sumcheckRoundRelation) which includes `masterKStateProp`
   - The `masterKStateProp` includes:
     * `witnessStructuralInvariant`: `wit.H = projectToMidSumcheckPoly ...`
     * `sumcheckConsistencyProp`: `stmt.sumcheck_target = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - Fin.last ℓ'), wit.H.val.eval x`
       For `i = Fin.last ℓ'`, we have `ℓ' - Fin.last ℓ' = 0`, so this is a sum over 0 variables (a constant)
   - Need to connect these properties to show the verifier check passes

2. **Relation Out**: Show that the output satisfies `aOStmtIn.toRelInput`
   - This involves showing `MLPEvalRelation` and `initialCompatibility` hold for the output
-/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  let s' := transcript.messages ⟨0, rfl⟩

  -- Extract properties from h_relIn BEFORE any simp changes its structure
  simp only [finalSumcheckStepLogic, sumcheckRoundRelation, sumcheckRoundRelationProp,
    Set.mem_setOf_eq, masterKStateProp] at h_relIn
  obtain ⟨_, h_wit_struct, h_sumcheck_cons, h_oStmtIn_compat⟩ := h_relIn

  -- Fact 1: Verifier check passes (using the helper lemma)
  let h_VCheck_passed : step.verifierCheck stmtIn transcript :=
    finalSumcheckStep_verifierCheck_passed κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
      stmtIn witIn oStmtIn challenges h_sumcheck_cons h_wit_struct

  -- Fact 2: Prover and verifier statements agree
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic,
      finalSumcheckVerifierStmtOut, finalSumcheckProverWitOut]

  -- Fact 3: Prover and verifier oracle statements agree (no new oracles added)
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl

  -- Fact 4: Output relation holds
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, finalSumcheckStepLogic]
    constructor
    · -- MLPEvalRelation: stmtOut.original_claim = witOut.t.val.eval stmtOut.t_eval_point
      rfl
    · -- initial Compatibility
      exact h_oStmtIn_compat

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

/-! ## Prover and Verifier Implementation -/

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' := finalSumcheckProverComputeMsg κ L K ℓ ℓ' witIn stmtIn
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheck L) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) where
  verify := fun stmtIn _ => do
    -- Get the final constant `s'` from the prover's message
    let s' : L ← query (spec := [(pSpecFinalSumcheck L).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by simpa using ())⟩
    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheck L) s'
    -- Get the logic instance
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
    -- Use guard for verifier check (fails if check doesn't pass)
    have : Decidable (logic.verifierCheck stmtIn t) := Classical.propDecidable _
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  embed := (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).embed
  hEq := (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).hEq

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  prover := finalSumcheckProver κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
  verifier := finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheck L)
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
      (init := init) (impl := impl) := by
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

  let step := (finalSumcheckStepLogic κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)

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
      change vStmtOut ∈ (Bind.bind (m := (OracleComp []ₒ)) _ _).support
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
      change some (verStmtOut, verOStmtOut) ∈ (liftComp _ _).support
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

    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_mem_support

    constructor
    · rw [verStmtOut_eq, verOStmtOut_eq, prvWitOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2


/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckRbrKnowledgeError : ℝ≥0 := (1 : ℝ≥0) / (Fintype.card L)

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L)
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc

  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t)
      (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/- This follows the KState of `finalSumcheckKStateProp` in `BinaryBasefold`.
though the multiplier poly is different. -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheck L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    RingSwitching.masterKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheck L).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheck L) tr).1 i_msg0

    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmt.challenges,
      original_claim := c
    }
    let sumcheckFinalLocalCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K β ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
      stmt.sumcheck_target = eq_tilde_eval * c

    let final_eval : Prop := witMid.t'.val.eval stmt.challenges = c
    sumcheckFinalLocalCheck ∧ final_eval
    ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K β ℓ ℓ' h_l (𝓑 := 𝓑)
    (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_last, cast_eq,
      Set.mem_setOf_eq, finalSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmt tr msg witMid h => by
    sorry
  toFun_full := fun stmt tr witOut h => by
    sorry

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) := by
  use (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
  use finalSumcheckRbrExtractor κ L K β ℓ ℓ' h_l aOStmtIn
  use finalSumcheckKnowledgeStateFunction κ L K β ℓ ℓ' h_l aOStmtIn init impl
  intro stmtIn witIn prover j
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
    (V := fun (i: Fin ℓ') => iteratedSumcheckOracleVerifier κ (𝓑 := 𝓑) L K β ℓ ℓ' h_l aOStmtIn i)

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
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (R := fun (i: Fin ℓ') => iteratedSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

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
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (init := init)
    (impl := impl) := by
  -- Follows from append_perfectCompleteness of interactionPhase and finalSumcheck
  apply OracleReduction.append_perfectCompleteness
    (rel₂ := (sumcheckRoundRelation κ L K β ℓ ℓ' h_l aOStmtIn (Fin.last ℓ')))
  · exact OracleReduction.seqCompose_perfectCompleteness
      (rel := fun i => sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i)
      (R := fun i => iteratedSumcheckOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn i)
      (h := fun i =>
        iteratedSumcheckOracleReduction_perfectCompleteness (hInit:=hInit) (κ:=κ) (L:=L) (K:=K)
          (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (𝓑:=𝓑) (aOStmtIn:=aOStmtIn)
          (init:=init) (impl:=impl) i
      )
  · exact finalSumcheckOracleReduction_perfectCompleteness (hInit:=hInit) (κ:=κ) (L:=L) (K:=K)
      (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)

/-- standard sumcheck error -/
def coreInteractionRbrKnowledgeError (_ : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  (2 : ℝ≥0) / (Fintype.card L)

-- TODO: iteratedSumcheckLoop_rbrKnowledgeSoundness

/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness:
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
    (relIn := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  sorry

end LargeFieldReduction
end
end Binius.RingSwitching.SumcheckPhase
