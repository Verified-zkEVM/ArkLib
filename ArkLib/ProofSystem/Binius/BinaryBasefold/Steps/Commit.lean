/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold

/-!
# Binary Basefold: the commit step

At a commitment round `i` (`ϑ ∣ i + 1`, `i + 1 < ℓ`), the prover sends its folded word
`f⁽ⁱ⁺¹⁾` as a new oracle. The verifier never rejects: it keeps the statement and appends the sent
oracle to the oracle statements. The step sends no challenge.

## Main definitions and statements

* `commitOracleProver`, `commitOracleVerifier`, `commitOracleReduction`: the step.
* `commitOracleVerifierGuardedForm`: the verifier's trivially-true guard and its verdict as data,
  from its pure form `commitOracleVerifierPureForm`.
* `commitOracleReduction_perfectCompleteness`: perfect completeness from the strict fold-step
  output relation to the strict round relation at `i + 1`, through `commitStepLogic`.
* `commitKnowledgeStateFunction`: before the message, the fold-step output relation; after it,
  the round relation at `i + 1` with the sent oracle appended. Its backward step across the message
  is the content of the step's knowledge soundness
  (`hasIncrementalBadEvent_commit_step_backward`,
  `oracleFoldingConsistent_commit_step_backward`).
* `commitOracleVerifier_rbrKnowledgeSoundnessWith`: round-by-round knowledge
  soundness at `commitRbrExtractor` and `commitKnowledgeStateFunction`, with an existential
  form.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The step is line 6 of the loop of the evaluation IOP of Construction 4.12.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

omit [Fintype 𝔽q] in
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩

variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SingleIteratedSteps
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

section CommitStep

/-- The prover states of the commit step: before the message, with the oracle statements at round
`i`; after it, with the sent oracle appended. -/
def CommitProverState (i : Fin ℓ) : Fin (1 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  | ⟨1, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- The commit prover's message, its folded word, and its state with that word appended to the
oracle statements. -/
def getCommitProverFinalOutput (i : Fin ℓ)
    (inputPrvState : CommitProverState (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 0) :
  (↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩) → L) ×
  CommitProverState (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 1 :=
  let (stmtIn, oStmtIn, witIn) := inputPrvState
  let fᵢ_succ := witIn.f
  let oStmtOut := snocOracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (oStmtIn := oStmtIn) (newOracleFn := fᵢ_succ) (h_destIdx := by rfl)
    -- The only thing the prover does is to sends f_{i+1} as an oracle
  (fᵢ_succ, (stmtIn, oStmtOut, witIn))

/-- The prover of the commit step: it sends its folded word as a new oracle. -/
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
  PrvState := CommitProverState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun inputPrvState => by
    let res := getCommitProverFinalOutput 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i inputPrvState
    exact pure res
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  output := fun ⟨stmt, oStmt, wit⟩ => by
    exact pure ⟨⟨stmt, oStmt⟩, wit⟩

/-- The verifier of the commit step at a commitment round: it keeps the statement and appends the
sent oracle to the oracle statements. -/
noncomputable def commitOracleVerifier (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
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

/-- The oracle reduction of the commit step at a commitment round. -/
noncomputable def commitOracleReduction (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
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

/-- The commit verifier's verdict as data: it accepts every transcript, keeps the statement, and
appends the sent oracle to the oracle statements. -/
def commitOracleVerifierPureForm (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.PureForm where
  verify s tr := (s.1, (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).materializeOutput tr.challenges s.2 tr.messages)
  verify_eq _ _ := rfl

/-- The commit verifier's guard and verdict as data: the trivially-true guard of its pure form. -/
def commitOracleVerifierGuardedForm (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.GuardedForm :=
  (commitOracleVerifierPureForm 𝔽q β i hCR).toGuardedForm

omit [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The commit verifier never rejects. -/
@[simp]
theorem commitOracleVerifierGuardedForm_check (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i)
    (s : Statement (L := L) Context i.succ × ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).FullTranscript) :
    (commitOracleVerifierGuardedForm (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).check s tr = true := rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Perfect completeness of the commit step, from the strict fold-step output relation to the
strict round relation at `i + 1`. -/
theorem commitOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hCR : IsCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := strictFoldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (oracleReduction := commitOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
      (init := init)
      (impl := impl) := by
  classical
  let step := commitStepLogic 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i hCR
  apply step.perfectCompleteness_of_isStronglyComplete
    (commitOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
    (commitOracleVerifierGuardedForm 𝔽q β i hCR)
    (commitStepLogic_isStronglyComplete 𝔽q β i hCR)
  · intro stmt wit oracles q hq
    have hp : (commitOracleProver (Context := Context) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).run (stmt, oracles) wit =
        pure (((default : (pSpecCommit 𝔽q β i).Transcript 0).concat (m := 0) wit.f),
          step.proverOut stmt wit oracles
            (step.honestProverTranscript stmt wit oracles isEmptyElim)) := rfl
    dsimp only [commitOracleReduction] at hq
    rw [hp] at hq
    replace hq := OracleComp.eq_of_mem_support_pure _ hq
    refine ⟨isEmptyElim, hq.trans ?_⟩
    refine Prod.ext ?_ rfl
    dsimp only [step, commitStepLogic]
    funext j
    fin_cases j
    rfl
  · intro stmt oracles tr
    exact (decide_eq_true (show step.verifierCheck stmt tr from trivial)).symm
  · intro stmt oracles tr
    rfl

/-- The commit step sends no challenge, so its round-by-round knowledge error is the empty
family. -/
def commitKnowledgeError {i : Fin ℓ}
    (m : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, hj⟩ => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_P_to_V_eq_V_to_P] at hj -- not a V challenge

/-- The round-by-round extractor of the commit step: the witness passes through unchanged. -/
noncomputable def commitRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

/-- The knowledge state of the commit step: before the message, the fold-step output relation;
after it, the round relation at `i + 1` with the sent oracle appended to the oracle statements. -/
def CommitKnowledgeState (i : Fin ℓ) (m : Fin (1 + 1))
    (stmtIn : Statement (L := L) Context i.succ)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmtIn : (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc i_1)
    (tr : Transcript m (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    KnowledgeInvariant (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
          witMid.H)
  | ⟨1, _⟩ => -- implied by relOut: use transcript message as oracle (what verifier sees)
    -- The verifier sees tr.messages ⟨0, rfl⟩ as the new oracle, not witMid.f
    let newOracle := tr.messages ⟨0, rfl⟩
    let oStmtOut := snocOracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (newOracleFn := newOracle) (h_destIdx := by rfl)
    KnowledgeInvariant (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtOut)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
          witMid.H)

/-- The knowledge-state function of the commit step, `CommitKnowledgeState`, with its
obligations. -/
def commitKnowledgeStateFunction (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    CommitKnowledgeState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
      (tr := tr) (multpoly := multpoly)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid h => h
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- For pSpecCommit, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    intro h_kState_round1
    unfold CommitKnowledgeState KnowledgeInvariant at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]
    -- The round-1 state is the bad-event disjunct or the good conjunction.
    cases h_kState_round1 with
    | inl hBad =>
      left
      have hBad_cast :=
        hasIncrementalBadEvent_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR oStmtIn
          _ _ hBad
      exact hBad_cast
    | inr hGood =>
      have h_sumcheck : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
          stmtIn.sumcheck_target witMid.H := hGood.1
      have h_struct : WitnessStructuralInvariant 𝔽q β (multpoly := multpoly)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn witMid := hGood.2.1
      have h_init : FirstOracleWitnessConsistent 𝔽q β witMid.t
          (getFirstOracle 𝔽q β
            (snocOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
              oStmtIn
              (msg : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (domainIdx := ⟨i.val + 1, by omega⟩)))) := hGood.2.2.1
      have h_fold : OracleFoldingConsistent 𝔽q β (i := i.succ) stmtIn.challenges
          (snocOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
            oStmtIn
            (msg : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (domainIdx := ⟨i.val + 1, by omega⟩))) := hGood.2.2.2
      have h_init_cast : FirstOracleWitnessConsistent 𝔽q β witMid.t
          (getFirstOracle 𝔽q β oStmtIn) :=
        getFirstOracle_snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i rfl oStmtIn msg ▸
          h_init
      have h_fold_cast :
          OracleFoldingConsistent 𝔽q β (i := i.castSucc) (Fin.init stmtIn.challenges)
            oStmtIn := by
        exact oracleFoldingConsistent_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR _ oStmtIn _ h_fold
      right
      exact ⟨h_sumcheck, h_struct, h_init_cast, h_fold_cast⟩
  toFun_full := fun s tr witOut h =>
    ((commitOracleVerifierGuardedForm (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).check_and_of_prEvent_pos h).2

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the commit step, at the extractor
`commitRbrExtractor`, the knowledge-state function `commitKnowledgeStateFunction` and the error
`commitKnowledgeError`. The step sends no challenge, so there is no extraction-failure event to
bound; the content is the knowledge-state function's obligations. -/
theorem commitOracleVerifier_rbrKnowledgeSoundnessWith (i : Fin ℓ)
    (hCR : IsCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.rbrKnowledgeSoundnessWith init impl
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (commitKnowledgeStateFunction (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i hCR)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  Verifier.rbrKnowledgeSoundnessWith_of_isEmpty_challengeIdx _ _

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the commit step: the existential form of
`commitOracleVerifier_rbrKnowledgeSoundnessWith`. -/
theorem commitOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hCR : IsCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.rbrKnowledgeSoundness init impl
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, commitOracleVerifier_rbrKnowledgeSoundnessWith (multpoly := multpoly)
      (𝓑 := 𝓑) 𝔽q β i hCR⟩

end CommitStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
