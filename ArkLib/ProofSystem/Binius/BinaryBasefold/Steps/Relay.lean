/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold

/-!
# Binary Basefold Relay Step
-/

@[expose] public section

local instance relayEmptySpecInhabited : OracleSpec.Inhabited []ₒ where
  inhabitedB j := PEmpty.elim j


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
      Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ pSpecRelay.MessageIdx :=
  fun j => Sum.inl ⟨j.val, by rw [h_oracle_size_eq_relay i hNCR]; omega⟩

/-! The oracle verifier for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleVerifier (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleVerifier
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
  outputOracle := .inl {
    embed := ⟨relayOracleVerifier_embed (r := r) (𝓡 := 𝓡) i hNCR, by
      intro a b h_ab_eq
      simp only [relayOracleVerifier_embed, MessageIdx, Sum.inl.injEq, Fin.mk.injEq] at h_ab_eq
      exact Fin.ext h_ab_eq
    ⟩
    hEq := fun oracleIdx => by simp only [MessageIdx, Function.Embedding.coeFn_mk,
      relayOracleVerifier_embed]
    outputInterface_heq := by
      intro oracleIdx
      simp only [relayOracleVerifier_embed, Function.Embedding.coeFn_mk]
      rfl }

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
    strictFoldStepRelOut, strictFoldStepRelOutProp, Fin.val_succ, Set.mem_ofPred_eq] at ⊢ h_relIn
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
  let : (j : pSpecRelay.ChallengeIdx) → OracleInterface (pSpecRelay.Challenge j) :=
    ProtocolSpec.challengeOracleInterface
  let : OracleSpec.Fintype [pSpecRelay.Challenge]ₒ :=
    { fintypeB := fun j => j.1.1.elim0 }
  let : OracleSpec.Inhabited [pSpecRelay.Challenge]ₒ :=
    { inhabitedB := fun j => j.1.1.elim0 }
  rw [OracleReduction.unroll_0_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecRelay) (init := init) (impl := impl) (hInit := hInit)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro output h_output
  dsimp only [relayOracleReduction, relayOracleProver, relayOracleVerifier,
    OracleVerifier.toVerifier] at h_output
  simp only [liftComp_pure, liftM_pure, pure_bind, OptionT.run_bind,
    OptionT.run_pure, Option.elimM, map_pure, simulateQ_pure] at h_output
  refine ⟨_, h_output, ?_⟩
  have h_preserved := strictRoundRelation_relay_preserved
    (i := i) (hNCR := hNCR) (stmtIn := stmtIn)
    (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn)
  refine ⟨?_, rfl, ?_⟩
  · simpa [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
      relayOracleVerifier, relayOracleVerifier_embed] using h_preserved
  · funext j
    rfl

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
    (oStmtIn : (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) : Prop :=
  -- Relay step inherits sumcheckConsistency from foldStepRelOut (relIn) and preserves it
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H
  masterKStateProp (mp := mp) (ϑ := ϑ) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
    (stmt := stmtIn) (wit := witMid) (oStmt := mapOStmtOutRelayStep
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)
    (localChecks := sumCheckConsistency)

/-! The relay step oracle transformation equals the verifier's materialized output.
This shows that mapOStmtOutRelayStep is exactly what the verifier produces. -/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma mapOStmtOut_eq_materializeOutput_relayStep
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (transcript : FullTranscript pSpecRelay) :
    let v := relayOracleVerifier (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
    mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn =
    OracleVerifier.materializeOutput v transcript.challenges oStmtIn transcript.messages := by
  intro v
  funext j
  simp only [mapOStmtOutRelayStep, OracleVerifier.materializeOutput,
    OracleVerifier.materializeOutputOracle, relayOracleVerifier, v]
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
set_option backward.isDefEq.respectTransparency false in
def relayKnowledgeStateFunction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    relayKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) (𝓑 := 𝓑)
      i hNCR stmtIn witMid oStmtIn
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witIn => by
    rw [cast_eq]
    simp only [foldStepRelOut, foldStepRelOutProp, Set.mem_ofPred_eq, relayKStateProp]
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
          support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (OracleVerifier.toVerifier (pSpec := pSpecRelay)
                    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                      i hNCR)))).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (OracleVerifier.toVerifier (pSpec := pSpecRelay)
                  (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    i hNCR)))).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    have h_output_mem_V_run_support :=
      OracleComp.support_simulateQ_run'_subset impl _ s h_output_mem_V_run_support
    dsimp only [Verifier.run, OracleVerifier.toVerifier, relayOracleVerifier]
      at h_output_mem_V_run_support
    simp only [OptionT.run_pure] at h_output_mem_V_run_support
    cases h_output_mem_V_run_support
    simp only [roundRelation, roundRelationProp, Set.mem_ofPred_eq, relayKStateProp,
      relayRbrExtractor,
      OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle] at h_relOut ⊢
    convert h_relOut using 1
    rfl

/-! RBR knowledge soundness for a single round oracle verifier -/
omit [SampleableType L] in
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
