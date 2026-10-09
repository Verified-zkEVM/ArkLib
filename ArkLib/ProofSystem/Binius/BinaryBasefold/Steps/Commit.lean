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
  (`incrementalBadEventExistsProp_commit_step_backward`,
  `oracleFoldingConsistencyProp_commit_step_backward`).
* `commitOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`: worst-case round-by-round knowledge
  soundness at `commitRbrExtractor` and `commitKnowledgeStateFunction`, with existential and
  averaged forms.

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
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
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
def commitPrvState (i : Fin ℓ) : Fin (1 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  | ⟨1, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- The commit prover's message, its folded word, and its state with that word appended to the
oracle statements. -/
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

/-- The output oracles of the commit verifier as a simulation: the old oracles are queried as
themselves, and the last one is answered by the sent oracle. -/
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
    · have h_eq := snoc_oracle_dest_eq_j
        (r := r) (𝓡 := 𝓡) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩)
        (h_destIdx := by rfl) j hj hCR
      exact liftM <| OracleSpec.query
        (show ([]ₒ +
            ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              i.castSucc]ₒ +
              [(pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message]ₒ)).Domain from
          Sum.inr (Sum.inr ⟨⟨0, by rfl⟩, cast (by
            change ↥(sDomain 𝔽q β h_ℓ_add_R_rate _) = ↥(sDomain 𝔽q β h_ℓ_add_R_rate _)
            rw [h_eq]) x⟩))
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rcases q with ⟨j, x⟩
    by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · dsimp only
      simp only [dite_eq_left hj]
      simp only [OracleInterface.simOracle2, snoc_oracle, hj, ↓reduceDIte]
      rfl
    · simp only [OracleInterface.simOracle2, snoc_oracle, hj, ↓reduceDIte, hCR]
      rfl

/-- The verifier of the commit step at a commitment round: it keeps the statement and appends the
sent oracle to the oracle statements. -/
noncomputable def commitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
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

/-- The commit verifier's verdict as data: it accepts every transcript, keeps the statement, and
appends the sent oracle to the oracle statements. -/
def commitOracleVerifierPureForm (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.PureForm where
  verify s tr := (s.1, (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).materializeOutput tr.challenges s.2 tr.messages)
  verify_eq _ _ := rfl

/-- The commit verifier's guard and verdict as data: the trivially-true guard of its pure form. -/
def commitOracleVerifierGuardedForm (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.GuardedForm :=
  (commitOracleVerifierPureForm 𝔽q β i hCR).toGuardedForm

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The commit verifier never rejects. -/
@[simp]
theorem commitOracleVerifierGuardedForm_check (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (s : Statement (L := L) Context i.succ × ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).FullTranscript) :
    (commitOracleVerifierGuardedForm (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).check s tr = true := rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Perfect completeness of the commit step, from the strict fold-step output relation to the
strict round relation at `i + 1`. -/
theorem commitOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
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
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  have hp : (commitOracleProver (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).run (stmt, oStmt) wit =
      pure (((default : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Transcript 0).concat
        (m := 0) wit.f), ((stmt, snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h_destIdx := by rfl) oStmt wit.f), wit)) := rfl
  let G := commitOracleVerifierGuardedForm (Context := Context) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  change x ∈ MonadAttach.support ((commitOracleProver (Context := Context) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).run (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  rw [hp] at hx
  simp only [G, commitOracleVerifierGuardedForm_check, ↓reduceIte] at hx
  subst x
  obtain ⟨-, hrel, -, horacle⟩ := commitStepLogic_isStronglyComplete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i hCR
      stmt wit oStmt isEmptyElim hIn
  rw [← horacle] at hrel
  exact ⟨_, rfl, hrel, rfl⟩

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
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

/-- The knowledge state of the commit step: before the message, the fold-step output relation;
after it, the round relation at `i + 1` with the sent oracle appended to the oracle statements. -/
def commitKStateProp (i : Fin ℓ) (m : Fin (1 + 1))
    (stmtIn : Statement (L := L) Context i.succ)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmtIn : (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc i_1)
    (tr : Transcript m (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
          witMid.H)
  | ⟨1, _⟩ => -- implied by relOut: use transcript message as oracle (what verifier sees)
    -- The verifier sees tr.messages ⟨0, rfl⟩ as the new oracle, not witMid.f
    let newOracle := tr.messages ⟨0, rfl⟩
    let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (newOracleFn := newOracle) (h_destIdx := by rfl)
    masterKStateProp (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtOut)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
          witMid.H)

/-- The knowledge-state function of the commit step, `commitKStateProp`, with its obligations. -/
def commitKnowledgeStateFunction (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    commitKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
      (tr := tr) (multpoly := multpoly)
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
    -- The round-1 state is the bad-event disjunct or the good conjunction.
    cases h_kState_round1 with
    | inl hBad =>
      left
      have hBad_cast :=
        incrementalBadEventExistsProp_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR oStmtIn
          _ _ hBad
      exact hBad_cast
    | inr hGood =>
      have h_sumcheck : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
          stmtIn.sumcheck_target witMid.H := hGood.1
      have h_struct : witnessStructuralInvariant 𝔽q β (multpoly := multpoly)
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
          (getFirstOracle 𝔽q β oStmtIn) :=
        getFirstOracle_snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i rfl oStmtIn msg ▸
          h_init
      have h_fold_cast :
          oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc) (Fin.init stmtIn.challenges)
            oStmtIn := by
        exact oracleFoldingConsistencyProp_commit_step_backward 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR _ oStmtIn _ h_fold
      right
      exact ⟨h_sumcheck, h_struct, h_init_cast, h_fold_cast⟩
  toFun_full := fun s tr witOut h =>
    ((commitOracleVerifierGuardedForm (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).check_and_of_prEvent_pos h).2

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- **Worst-case round-by-round knowledge soundness of the commit step**, at the extractor
`commitRbrExtractor`, the knowledge-state function `commitKnowledgeStateFunction` and the error
`commitKnowledgeError`. The step sends no challenge, so there is no extraction-failure event to
bound; the content is the knowledge-state function's obligations. -/
theorem commitOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
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
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_isEmpty_challengeIdx _ _

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the commit step: the existential form of
`commitOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`. -/
theorem commitOracleVerifier_rbrKnowledgeSoundnessWorstCase (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, commitOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith (multpoly := multpoly)
      (𝓑 := 𝓑) 𝔽q β i hCR⟩

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the commit step: the averaged form of
`commitOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem commitOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (commitOracleVerifier_rbrKnowledgeSoundnessWorstCase (multpoly := multpoly) (𝓑 := 𝓑)
      𝔽q β i hCR)

end CommitStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
