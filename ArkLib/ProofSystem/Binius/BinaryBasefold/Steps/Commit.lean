/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold

/-!
# Binary Basefold Commitment Step
-/

@[expose] public section

local instance commitEmptySpecInhabited : OracleSpec.Inhabited []ₒ where
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
noncomputable def commitOutputSimulation (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    OracleOutputSimulation []ₒ
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  materializeOutput := fun _ oStmt messages =>
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_destIdx := by rfl) oStmt (messages ⟨0, by rfl⟩)
  simulateOutputQuery := fun _ q => by
    rcases q with ⟨j, x⟩
    by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · exact liftM <| OracleSpec.query
        (show ([]ₒ +
            ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              i.castSucc]ₒ +
              [(pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message]ₒ)).Domain from
          Sum.inr (Sum.inl ⟨⟨j.val, hj⟩, x⟩))
    · exact do
      let f ← liftM <| OracleSpec.query
        (show ([]ₒ +
            ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              i.castSucc]ₒ +
              [(pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message]ₒ)).Domain from
          Sum.inr (Sum.inr ⟨⟨0, by rfl⟩, ()⟩))
      let h_eq := snoc_oracle_dest_eq_j
        (r := r) (𝓡 := 𝓡) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩)
        (h_destIdx := by rfl) j hj hCR
      pure (f (cast (by rw [h_eq]; rfl) x))
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rcases q with ⟨j, x⟩
    by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · dsimp only
      simp only [dif_pos hj]
      simp only [OracleInterface.simOracle2, snoc_oracle, hj, ↓reduceDIte]
      rfl
    · simp only [simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, OracleInterface.simOracle2,
        snoc_oracle, hj, ↓reduceDIte, hCR]
      rfl

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
  outputOracle := .inr (commitOutputSimulation 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

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
    i hCR

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
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
      (init := init)
      (impl := impl) := by
  -- Step 1: Unroll the 1-message reduction
  let p := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let : OracleSpec.Fintype [p.Challenge]ₒ :=
    { fintypeB := fun j => by
        have h := j.1.2
        simp [p, pSpecCommit] at h }
  let : OracleSpec.Inhabited [p.Challenge]ₒ :=
    { inhabitedB := fun j => by
        have h := j.1.2
        simp [p, pSpecCommit] at h }
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (oSpec := []ₒ)
    (hInit := hInit) (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro output h_output
  dsimp only [commitOracleReduction, commitOracleProver, commitOracleVerifier,
    OracleVerifier.toVerifier, getCommitProverFinalOutput] at h_output
  simp only [OptionT.run_bind, OptionT.run_pure,
    Option.elimM, map_pure, simulateQ_pure] at h_output
  refine ⟨_, h_output, ?_⟩
  have h_complete := commitStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i hCR
      stmtIn witIn oStmtIn
      (fun j => by have h := j.2; simp [pSpecCommit] at h) h_relIn
  obtain ⟨_, h_rel, h_stmt, h_oracles⟩ := h_complete
  rw [← h_oracles] at h_rel
  refine ⟨?_, rfl, ?_⟩
  · simpa [commitStepLogic, OracleVerifier.materializeOutput,
      OracleVerifier.materializeOutputOracle,
      commitOutputSimulation, FullTranscript.mk1, FullTranscript.messages] using h_rel
  · rfl

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
    (tr : Transcript m (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) : Prop :=
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
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
    simp only [foldStepRelOut, foldStepRelOutProp, Set.mem_ofPred_eq, commitKStateProp]
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
                    i hCR).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  i hCR).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    have h_output_mem_V_run_support :=
      OracleComp.support_simulateQ_run'_subset impl _ s h_output_mem_V_run_support
    dsimp only [Verifier.run, OracleVerifier.toVerifier, commitOracleVerifier]
      at h_output_mem_V_run_support
    simp only [OptionT.run_pure] at h_output_mem_V_run_support
    cases h_output_mem_V_run_support
    simpa [roundRelation, roundRelationProp, commitKStateProp, commitRbrExtractor,
      OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
      commitOutputSimulation] using h_relOut

/-! RBR knowledge soundness for a single round oracle verifier -/
omit [SampleableType L] in
theorem commitOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).rbrKnowledgeSoundness init impl
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
