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

section RelayStep
/- the relay is just to place the conditional oracle message -/

def relayPrvState (i : Fin ℓ) : Fin (0 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-! The prover for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleProver (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
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
    (pSpec := pSpecRelay) where
  PrvState := relayPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage | ⟨x, h⟩ => by exact x.elim0
  receiveChallenge | ⟨x, h⟩ => by exact x.elim0
  output := fun ⟨stmt, oStmt, wit⟩ =>
    pure ⟨⟨stmt, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR oStmt⟩, wit⟩

lemma h_oracle_size_eq_relay (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  toOutCodewordsCount ℓ ϑ i.castSucc =
      toOutCodewordsCount ℓ ϑ i.succ := by
  simp only [toOutCodewordsCount_succ_eq, hNCR, ↓reduceIte]

def relayOracleVerifier_embed (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  Fin (toOutCodewordsCount ℓ ϑ i.succ) →
    Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ pSpecRelay.MessageIdx
  := fun j => Sum.inl ⟨j.val, by rw [h_oracle_size_eq_relay i hNCR]; omega⟩

/-! The oracle verifier for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleVerifier (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleVerifier.{0, 0}
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay) where
  verify := fun stmtIn _ => pure stmtIn
  embed := ⟨relayOracleVerifier_embed (r := r) (𝓡 := 𝓡) i hNCR, by
    intro a b h_ab_eq
    simp only [relayOracleVerifier_embed, MessageIdx, Sum.inl.injEq, Fin.mk.injEq] at h_ab_eq
    exact Fin.ext h_ab_eq
  ⟩
  hEq := fun oracleIdx => by simp only [MessageIdx, Function.Embedding.coeFn_mk,
    relayOracleVerifier_embed]

/-! The oracle reduction that is the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleReduction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay) where
  prover := relayOracleProver 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
  verifier := relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] h_β₀_eq_1 [CharP L 2] [SampleableType L] in
lemma strictRoundRelation_relay_preserved (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement Context i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (witIn : Witness 𝔽q β i.succ)
    (h_relIn : ((stmtIn, oStmtIn), witIn) ∈ strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i) :
    ((stmtIn, fun (j : Fin (toOutCodewordsCount ℓ ϑ i.succ)) ↦
      oStmtIn ⟨j.val, by rw [h_oracle_size_eq_relay i hNCR]; omega⟩), witIn)
      ∈ strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i.succ := by
  dsimp only [strictRoundRelation, strictRoundRelationProp,
    strictFoldStepRelOut, strictFoldStepRelOutProp, Fin.val_succ, Set.mem_setOf_eq] at ⊢ h_relIn
  dsimp only [strictOracleWitnessConsistency, strictOracleFoldingConsistencyProp] at h_relIn ⊢
  constructor
  · exact h_relIn.1
  · constructor
    · exact h_relIn.2.1
    · dsimp only [OracleFrontierIndex.mkFromStmtIdx]
      dsimp only [OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc] at h_relIn
      intro (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
      have h_toOutCodewordsCount_eq : toOutCodewordsCount ℓ ϑ i.succ =
        toOutCodewordsCount ℓ ϑ i.castSucc := (h_oracle_size_eq_relay i hNCR).symm
      exact h_relIn.2.2 ⟨j, by omega⟩

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
theorem relayOracleReduction_perfectCompleteness (hInit : NeverFail init) (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecRelay)
      (relIn := strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (oracleReduction := relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR)
      (init := init)
      (impl := impl) := by
  -- must use `ProtocolSpec.challengeOracleInterface`
  rw [OracleReduction.unroll_0_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecRelay) (init := init) (impl := impl) (hInit := hInit)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [relayOracleReduction, relayOracleProver, relayOracleVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk2]
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    erw [simulateQ_pure];
    -- erw [OptionT.probFailure_mk]
    simp only [ liftComp_eq_liftM, ChallengeIdx, Challenge,
      OptionT.mem_support_iff, toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run,
      Prod.mk.eta, probFailure_eq_zero, implies_true, and_true]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    conv at h_vStmtOut_mem_support =>
      simp only [support_pure, Set.mem_singleton_iff]
    rw [h_vStmtOut_mem_support]
    simp only [MessageIdx, OptionT.run_pure, probOutput_eq_zero_iff, support_pure,
      Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true]
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
    simp only [Challenge,ChallengeIdx,
      liftComp_eq_liftM, MessageIdx, Message] at hx_mem_support
    obtain ⟨h_verOut_mem_support, h_prvOut_mem_support⟩ := hx_mem_support
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [support_liftComp]
      erw [simulateQ_pure]
      -- dsimp only [Functor.map]
      erw [support_bind]
      simp only [support_pure, Set.mem_singleton_iff, Function.comp_apply,
        Set.iUnion_iUnion_eq_left, OptionT.support_OptionT_pure_run, Option.some.injEq,
        Prod.mk.injEq]
    rcases h_verOut_mem_support with ⟨verStmtOut_eq, verOStmtOut_eq⟩
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_mem_support
    constructor
    · rw [prvWitOut_eq, verStmtOut_eq, verOStmtOut_eq];
      exact (strictRoundRelation_relay_preserved (i := i) (hNCR := hNCR) (stmtIn := stmtIn)
    (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn))
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq];
      · rw [verOStmtOut_eq, prvOStmtOut_eq]; rfl

def relayKnowledgeError (m : pSpecRelay.ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, _⟩ => j.elim0

/-! The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def relayRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

def relayKStateProp (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
  (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
  : Prop :=
  -- Relay step inherits sumcheckConsistency from foldStepRelOut (relIn) and preserves it
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H
  masterKStateProp (mp := mp) (ϑ := ϑ) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
    (stmt := stmtIn) (wit := witMid) (oStmt := mapOStmtOutRelayStep
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)
    (localChecks := sumCheckConsistency)

/-! The relay step oracle transformation equals mkVerifierOStmtOut.
This shows that mapOStmtOutRelayStep is exactly what the verifier produces. -/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma mapOStmtOut_eq_mkVerifierOStmtOut_relayStep
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (transcript : FullTranscript pSpecRelay) :
    let v := relayOracleVerifier (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
    mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn =
    OracleVerifier.mkVerifierOStmtOut v.embed v.hEq oStmtIn transcript := by
  intro v
  funext j
  simp only [mapOStmtOutRelayStep, OracleVerifier.mkVerifierOStmtOut, relayOracleVerifier, v]
  simp [relayOracleVerifier_embed]

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma getFirstOracle_mapOStmtOutRelayStep_eq (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn) =
    getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtIn := by
  funext y
  simp only [getFirstOracle, mapOStmtOutRelayStep]

/-! Knowledge state function (KState) for single round -/
def relayKnowledgeStateFunction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    relayKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp:=mp) -- (𝓑 := 𝓑)
      i hNCR stmtIn witMid oStmtIn
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witIn => by
    rw [cast_eq]
    simp only [foldStepRelOut, foldStepRelOutProp, Set.mem_setOf_eq, relayKStateProp]
    unfold masterKStateProp
    simp only [Fin.val_succ]
    constructor <;> intro h
    · -- Forward: castSuccOfSucc/original oStmt -> mkFromStmtIdx/mapped oStmt
      cases h with
      | inl hBad =>
        left
        exact (incrementalBadEventExistsProp_relay_preserved 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn stmtIn.challenges).1 hBad
      | inr hGood =>
        right
        refine ⟨hGood.1, hGood.2.1, ?_, ?_⟩
        · rw [getFirstOracle_mapOStmtOutRelayStep_eq (i := i) (hNCR := hNCR)
            (oStmtIn := oStmtIn)]
          exact hGood.2.2.1
        · have hFold' :
            oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc)
              (Fin.init stmtIn.challenges) oStmtIn := by
            exact hGood.2.2.2
          have hFold_map :=
            (oracleFoldingConsistencyProp_relay_preserved 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR stmtIn.challenges oStmtIn).1 hFold'
          exact hFold_map
    · -- Backward: mkFromStmtIdx/mapped oStmt -> castSuccOfSucc/original oStmt
      cases h with
      | inl hBad =>
        left
        exact (incrementalBadEventExistsProp_relay_preserved 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn stmtIn.challenges).2 hBad
      | inr hGood =>
        right
        refine ⟨hGood.1, hGood.2.1, ?_, ?_⟩
        · have hFirst := hGood.2.2.1
          rw [getFirstOracle_mapOStmtOutRelayStep_eq (i := i) (hNCR := hNCR)
            (oStmtIn := oStmtIn)] at hFirst
          exact hFirst
        · have hFold' :
            oracleFoldingConsistencyProp 𝔽q β (i := i.succ)
              stmtIn.challenges
              (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn) := by
            exact hGood.2.2.2
          have hFold_cast :=
            (oracleFoldingConsistencyProp_relay_preserved 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR stmtIn.challenges oStmtIn).2 hFold'
          exact hFold_cast
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => Fin.elim0 m
  toFun_full := by
    intro stmtOStmtIn tr witOut probEvent_relOut_gt_0
    rcases stmtOStmtIn with ⟨stmtIn, oStmtIn⟩
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    i hNCR).toVerifier)).run s).support := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  i hNCR).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [relayOracleVerifier]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      simp only [simulateQ_pure, pure_bind, Function.comp_apply]
      dsimp only [ProbComp] -- unfold ProbComp back to OracleComp
      simp only [MessageIdx, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, exists_eq_right,
        exists_and_right]
      ---
      erw [simulateQ_bind]
      erw [simulateQ_pure, support_pure]
      simp only [Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq]
    rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
    simp only [Nat.reduceAdd]
    let v := relayOracleVerifier (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
    -- Now h_relOut : ((stmtIn, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
    -- where oStmtOut = OracleVerifier.mkVerifierOStmtOut ...
    simp only [roundRelation, roundRelationProp, Set.mem_setOf_eq] at h_relOut
    unfold masterKStateProp at h_relOut
    -- The goal is relayKStateProp, which expands to masterKStateProp with sumcheckConsistency
    simp only [relayKStateProp]
    unfold masterKStateProp
    -- relayRbrExtractor.extractOut is identity
    rw [h_stmtOut_eq] at h_relOut
    -- Rewrite verifier-produced oracle statement to the relay map and conclude directly.
    have h_oStmt_eq_map : oStmtOut =
      mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn := by
      calc
        oStmtOut = OracleVerifier.mkVerifierOStmtOut v.embed v.hEq oStmtIn tr := h_oStmtOut_eq
        _ = mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn := by
          have h_map :=
            mapOStmtOut_eq_mkVerifierOStmtOut_relayStep
              (Context := Context) (i := i) (hNCR := hNCR) (oStmtIn := oStmtIn)
              (transcript := tr)
          dsimp only [v] at h_map
          exact h_map.symm
    rw [h_oStmt_eq_map] at h_relOut
    dsimp only [relayRbrExtractor] at h_relOut ⊢
    exact h_relOut

/-! RBR knowledge soundness for a single round oracle verifier -/
theorem relayOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (relayKnowledgeError) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  use relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use relayKnowledgeStateFunction (mp:=mp) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hNCR
  intro stmtIn witIn prover j
  exact Fin.elim0 j

end RelayStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
