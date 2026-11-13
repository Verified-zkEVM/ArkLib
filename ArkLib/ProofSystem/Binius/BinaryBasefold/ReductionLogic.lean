/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas
public import ArkLib.OracleReduction.LogicStep

/-!
# Binary Basefold: the logic of a single step

An `OracleReduction.DeterministicLogicStep` records the deterministic content of one
interactive reduction step: the
verifier's check and output statement on a full transcript, the selection of its output oracles,
the honest prover's transcript as a function of the challenges and its output, and the relations
under which the step is complete. Its strong completeness
is the per-challenge statement that the honest transcript passes the check and lands in the output
relation. An oracle verifier that queries one prover message and runs a step's check and output
on the transcript rebuilt from the answer has a guarded form through
`Verifier.GuardedForm.ofQueryGuard`.

## Main definitions and statements

* `foldStepLogic`, `foldStepLogic_isStronglyComplete`: the fold step. The prover sends the
  univariate round polynomial `hᵢ`; the verifier checks `hᵢ(𝓑 0) + hᵢ(𝓑 1) = sᵢ` and sets
  `sᵢ₊₁ := hᵢ(r'ᵢ)`.
* `commitStepLogic`, `commitStepLogic_isStronglyComplete`: the commit step at a commitment round.
  The prover sends its folded word `f⁽ⁱ⁺¹⁾` as a new oracle.
* `finalSumcheckStepLogic`, `finalSumcheckStepLogic_isStronglyComplete`: the final sum-check
  step. The prover sends the constant `c` of `f⁽ˡ⁾`; the verifier checks `s_ℓ = eq̃(r, r') · c`.

The oracle reductions built from these steps are in `Steps/`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The fold step is lines 1–4 of the loop of the evaluation IOP of Construction 4.12, the commit
  step line 6, and the final sum-check step line 5 with step 3. Their completeness is part of
  Theorem 4.13, with the fold of the prover's word as in Lemma 4.14.
-/

@[expose] public section

namespace Binius.BinaryBasefold

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal

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
section FoldStep

/-- The logic of the `i`-th fold step. The prover sends the univariate round polynomial of its
current round polynomial; the verifier checks that its values at the two points of `𝓑` sum to the
sum-check target, and outputs the statement with target the round polynomial at the challenge and
the challenge appended. The oracle statements pass through. Completeness is stated for the strict
relations. -/
def foldStepLogic (i : Fin ℓ) :
    OracleReduction.DeterministicLogicStep []ₒ
      (Statement (L := L) Context i.castSucc)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecFold (L := L))
      where
  completeness_relIn := fun ((s, o), w) =>
    ((s, o), w) ∈ strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i.castSucc (multpoly := multpoly)
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (multpoly := multpoly)
  verifierCheck := fun s t =>
    foldVerifierCheck i s (𝓑 := 𝓑) (t.messages ⟨0, rfl⟩)
  verifierOut := fun s t =>
    foldVerifierStmtOut i s (t.messages ⟨0, rfl⟩) (t.challenges ⟨1, rfl⟩)
  outputInterfaces := inferInstance
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg : ↥L⦃≤ 2⦄[X] := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)
  proverOut := fun s w o t =>
    let h_i : (pSpecFold (L := L)).«Type» 0 := t ⟨0, by omega⟩
    let r_i' : (pSpecFold (L := L)).«Type» 1 := t ⟨1, by omega⟩
    getFoldProverFinalOutput 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
      (s, o, w, h_i, r_i')

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The fold step is strongly complete: from the strict round relation at `i`, the honest round
polynomial passes the check, and the honest output lies in the strict fold-step output relation,
for every challenge. -/
lemma foldStepLogic_isStronglyComplete (i : Fin ℓ) :
    (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).IsStronglyComplete := by
  classical
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn (strictRoundRelation)
  simp only [foldStepLogic, strictRoundRelation, StrictRoundRelated,
    Set.mem_ofPred_eq] at h_relIn
  have h_sumcheck_cons : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
      stmtIn.sumcheck_target witIn.H :=
    h_relIn.1
  have h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    simp only [step, foldStepLogic, foldVerifierCheck, foldProverComputeMsg]
    rw [h_sumcheck_cons]
    exact Sumcheck.Structured.eval_add_eval_getSumcheckRoundPoly ℓ 𝓑 i witIn.H
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, foldStepLogic]
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.val_succ]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = step.materializeOutput oStmtIn transcript
    simp only [step, foldStepLogic]
    funext j
    have hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := j.isLt
    rfl
  -- Key fact: Oracle statements are unchanged in the fold step
  -- (all oracle indices map via Sum.inl in the embedding)
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, foldStepLogic]
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, foldStepLogic, strictFoldStepRelOut, StrictFoldStepRelated,
      Set.mem_ofPred_eq]
    simp only [Fin.val_succ]
    constructor
    · -- Part 2.1: sumcheck consistency
      unfold sumcheckConsistencyProp
      dsimp only [verifierStmtOut, proverWitOut, proverOutput]
      simp only [step, foldStepLogic, foldVerifierStmtOut, getFoldProverFinalOutput, transcript]
      exact (Sumcheck.Structured.sum_projectToNextSumcheckPoly_uniform ℓ 𝓑 i _ _).symm
    · -- Part 2.2: StrictOracleWitnessConsistent
      simp only [Fin.val_castSucc] at h_relIn
      have h_oracleWitConsistency_In := h_relIn.2
      rw [h_verifierOStmtOut_eq];
      dsimp only [StrictOracleWitnessConsistent] at h_oracleWitConsistency_In ⊢
      obtain ⟨h_wit_struct_In, h_oracle_folding_In⟩ :=
        h_oracleWitConsistency_In
      refine ⟨?_, ?_⟩
      · -- Component 1: WitnessStructuralInvariant
        unfold WitnessStructuralInvariant
        obtain ⟨h_H_In, h_f_In⟩ := h_wit_struct_In
        dsimp only [Fin.val_succ, proverWitOut, proverOutput, step,
          foldStepLogic, verifierStmtOut]
        constructor
        · rw [h_H_In]
          exact (Sumcheck.Structured.fixPrefix_initial_succ ℓ witIn.t _ i _ _).symm
        · rw [h_f_In]
          exact (getMidCodewords_succ 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t i stmtIn.challenges
            (transcript.challenges ⟨1, by rfl⟩)).symm
      · -- Component 2: StrictOracleFoldingConsistent
        have h_oracleIdx_eq : (OracleFrontierIndex.mkFromStmtIdx i.castSucc).val
          = (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val := by rfl
        have h_challenges_eq : Fin.init verifierStmtOut.challenges = stmtIn.challenges :=
          Fin.init_snoc (α := fun _ => L) _ _
        rw! (castMode := .all) [h_oracleIdx_eq] at h_oracle_folding_In
        simp only [Fin.val_succ, OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
          Fin.val_castSucc, Fin.take_eq_self, Fin.take_eq_init] at h_oracle_folding_In ⊢
        rw [h_challenges_eq]
        exact h_oracle_folding_In
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FoldStep

section CommitStep

namespace CoreInteraction

/-- The output oracles of the commit verifier as a simulation: the old oracles are queried as
themselves, and the last one is answered by the sent oracle. -/
noncomputable def commitOutputSimulation (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
    OracleOutputSimulation []ₒ
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  materializeOutput := fun _ oStmt messages =>
    snocOracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
    · have h_eq := destIdx_eq_oraclePositionToDomainIndex_of_newOracle
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
      simp only [OracleInterface.simOracle2, snocOracle, hj, ↓reduceDIte]
      rfl
    · simp only [OracleInterface.simOracle2, snocOracle, hj, ↓reduceDIte, hCR]
      rfl

end CoreInteraction

/-- The logic of the commit step at a commitment round `i`. The prover sends its folded word as an
oracle; the verifier accepts and keeps the statement, and the sent oracle becomes the last oracle
statement. -/
def commitStepLogic (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
    OracleReduction.DeterministicLogicStep []ₒ
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictFoldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ
  -- No verification needed - just accept
  verifierCheck := fun _ _ => True
  -- Statement doesn't change
  verifierOut := fun stmt _ => stmt
  outputInterfaces := inferInstance
  outputOracle := .inr (CoreInteraction.commitOutputSimulation 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
  -- No challenges in 1-message protocol, so transcript is just the message
  honestProverTranscript := fun _stmt wit _oStmt _challenges =>
    fun ⟨0, _⟩ => wit.f
  -- Prover output: statement unchanged, oracle extended with new function
  proverOut := fun stmt wit oStmtIn transcript =>
    let oStmtOut :=
    snocOracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn (newOracleFn := wit.f)
    ((stmt, oStmtOut), wit)

omit [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- Appending an oracle does not change the first oracle. -/
lemma getFirstOracle_snoc_oracle
    (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx)) :
    getFirstOracle 𝔽q β
    (snocOracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx oStmtIn newOracleFn) =
    getFirstOracle 𝔽q β oStmtIn := by
  unfold getFirstOracle snocOracle
  have h_lt : 0 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h := (instNeZeroNatToOutCodewordsCount ℓ ϑ i.castSucc).out
    omega
  simp only [Fin.mk_zero', h_lt, ↓reduceDIte]
  rfl

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- At a commitment round, if the witness is structured and the oracle statements are the honest
folds of the witness's codeword, then so are the commit step's output oracles at the next oracle
frontier. -/
lemma strictOracleFoldingConsistent_commitStepLogic
    (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (witIn : Witness 𝔽q β i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (challenges : (pSpecCommit 𝔽q β i).Challenges)
    (h_wit_struct_In : WitnessStructuralInvariant 𝔽q β (multpoly := multpoly) stmtIn witIn)
    (h_oracle_folding_In : StrictOracleFoldingConsistent 𝔽q β (t := witIn.t) (i := i.castSucc)
      (challenges := Fin.take (m := i)
        (v := stmtIn.challenges) (h := by
          simp only [Fin.val_succ, le_add_iff_nonneg_right, zero_le]))
      (oStmt := oStmtIn)) :
    let step := (commitStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i (hCR := hCR))
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := step.materializeOutput oStmtIn transcript
    StrictOracleFoldingConsistent 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.succ)
      (challenges := Fin.take (m := i.val + 1)
        (v := verifierStmtOut.challenges) (h := by simp only [Fin.val_succ, le_refl]))
      (oStmt := verifierOStmtOut) (t := witIn.t) := by
  -- Key observations:
  --    (when IsCommitmentRound)
  -- Simplify the step definitions
  intro step transcript verifierStmtOut verifierOStmtOut
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_wit_f_eq : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_struct_In.2
  -- Oracle extension: verifierOStmtOut = snocOracle oStmtIn witIn.f
  have h_OStmtOut_eq : verifierOStmtOut = snocOracle 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl)
      oStmtIn (newOracleFn := witIn.f) := by
    rfl
  have h_challenges_eq : stmtIn.challenges = verifierStmtOut.challenges := by rfl
  -- Expand StrictOracleFoldingConsistent - goal is ∀ j, verifierOStmtOut j = iteratedFold ...
  simp only [StrictOracleFoldingConsistent]
  intro j
  -- The output oracle count is one more than input
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  -- Case analysis: old oracle vs new oracle
  have h_j_bound : j.val < toOutCodewordsCount ℓ ϑ i.succ := j.isLt
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · -- Case A: Old oracle (j < old count)
    -- verifierOStmtOut j = oStmtIn j (from snocOracle)
    have h_verifier_eq_old : verifierOStmtOut j = oStmtIn ⟨j.val, hj⟩ := by
      rw [h_OStmtOut_eq]
      dsimp only [snocOracle]
      simp only [hj, ↓reduceDIte]
    rw [h_verifier_eq_old]
    -- Use input hypothesis: oStmtIn j = iteratedFold ... (with challenges from i.castSucc)
    have h_old_eq := h_oracle_folding_In ⟨j.val, hj⟩
    rw [h_old_eq]
    -- Show that iteratedFold with challenges from i.castSucc equals iteratedFold with
    -- challenges from i.succ when j * ϑ < i.val (holds since j < toOutCodewordsCount i.castSucc)
    rfl
  · -- Case B: New oracle (j = toOutCodewordsCount i.castSucc)
    rw [h_OStmtOut_eq]
    dsimp only [snocOracle]
    simp only [hj, ↓reduceDIte, hCR]
    have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    -- verifierOStmtOut j is the cast version of witIn.f (from snocOracle)
    -- The domain indices match: oraclePositionToDomainIndex j = i.val + 1 when j is the new oracle
    have h_domain_idx_eq : (oraclePositionToDomainIndex (positionIdx := j)).val = i.val + 1 :=
      by simp only [h_j_eq]; exact toOutCodewordsCount_castSucc_mul_eq_succ_of_dvd ℓ ϑ i hCR.1
    -- Use witness structural invariant: witIn.f = getMidCodewords witIn.t stmtIn.challenges
    have h_steps_eq : (toOutCodewordsCount ℓ ϑ i.castSucc) * ϑ = i.val + 1 := by
      exact toOutCodewordsCount_castSucc_mul_eq_succ_of_dvd ℓ ϑ i hCR.1
    funext x
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    rw [h_wit_f_eq]
    simp only
    have h_cast_elim := iteratedFold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := i.succ)
      (destIdx := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)
      (destIdx' := ⟨i.succ, by simp only [Fin.val_succ]; omega⟩)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ, zero_add]
        exact h_domain_idx_eq)
      (h_destIdx_le := by simp only [oracle_index_le_ℓ])
      (h_destIdx_eq_destIdx' := by simp only [Fin.val_succ, Fin.mk.injEq]; exact h_domain_idx_eq)
      (f := f₀) (r_challenges := stmtIn.challenges)
    dsimp only [f₀, P₀] at h_cast_elim
    unfold polyToOracleFunc at h_cast_elim
    rw [← h_cast_elim]
    unfold getFoldingChallenges
    rw [←h_challenges_eq]
    unfold polyToOracleFunc
    have h_cast_elim2 := iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := i.succ) (steps' := j.val * ϑ)
      (destIdx := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)
      (h_steps_eq_steps' := by exact h_domain_idx_eq.symm)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ, zero_add]
        exact h_domain_idx_eq)
      (h_destIdx_le := by simp only [oracle_index_le_ℓ])
      (f := f₀) (r_challenges := stmtIn.challenges)
    dsimp only [f₀, P₀] at h_cast_elim2
    unfold polyToOracleFunc at h_cast_elim2
    rw [h_cast_elim2]
    dsimp only [Fin.val_succ, Fin.take_apply, Fin.castLE_refl]
    congr 1
    dsimp only [oraclePositionToDomainIndex] at h_domain_idx_eq
    have h_challenges_eq_take : (fun cIdx : Fin (j.val * ϑ) => stmtIn.challenges ⟨cIdx.val, by
      simp only [Fin.val_succ]; rw [h_domain_idx_eq.symm]; exact cIdx.isLt⟩) =
      (fun cIdx : Fin (j.val * ϑ) => stmtIn.challenges ⟨0 + cIdx.val, by
        simp only [zero_add, Fin.val_succ]; rw [h_domain_idx_eq.symm]; exact cIdx.isLt⟩) := by
      funext cId
      simp only [Fin.val_succ, zero_add]
    exact h_challenges_eq_take

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The commit step is strongly complete: from the strict fold-step output relation, the honest
output lies in the strict round relation at `i + 1`. -/
lemma commitStepLogic_isStronglyComplete (i : Fin ℓ) (hCR : IsCommitmentRound ℓ ϑ i) :
    (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (hCR := hCR)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (commitStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (multpoly := multpoly) i (hCR := hCR))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn (strictFoldStepRelOut)
  dsimp only [commitStepLogic, strictFoldStepRelOut, StrictFoldStepRelated,
    strictRoundRelation, StrictRoundRelated, Set.mem_ofPred_eq] at h_relIn
  dsimp only [StrictFoldStepRelated, StrictRoundRelated, Fin.val_succ] at h_relIn
  have h_sumcheck_cons : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
      stmtIn.sumcheck_target witIn.H :=
    h_relIn.1
  have h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    dsimp only [commitStepLogic, Prod.mk.eta, step]
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    dsimp only [step, commitStepLogic]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = step.materializeOutput oStmtIn transcript
    rfl
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    dsimp only [step, commitStepLogic, strictRoundRelation, StrictRoundRelated,
      Set.mem_ofPred_eq]
    simp only [Fin.val_succ]
    constructor
    · -- Part 2.1: sumcheck consistency
      exact h_sumcheck_cons
    · -- Part 2.2: StrictOracleWitnessConsistent
      have h_strictOracleWitConsistency_In := h_relIn.2
      dsimp only [StrictOracleWitnessConsistent] at h_strictOracleWitConsistency_In ⊢
      obtain ⟨h_wit_struct_In, h_strict_oracle_folding_In⟩ := h_strictOracleWitConsistency_In
      refine ⟨?_, ?_⟩
      · -- Component 1: WitnessStructuralInvariant
        exact h_wit_struct_In
      · -- Component 2: StrictOracleFoldingConsistent
        exact strictOracleFoldingConsistent_commitStepLogic 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (witIn := witIn)
          (stmtIn := stmtIn) (hCR := hCR) (h_wit_struct_In := h_wit_struct_In)
          (h_oracle_folding_In := h_strict_oracle_folding_In) (challenges := challenges)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end CommitStep

section FinalSumcheckStep

/-- The logic of the final sum-check step. The prover sends the constant `c` of its fully folded
word; the verifier checks the closing sum-check equation `s_ℓ = eq̃(r, r') · c` and outputs the
statement extended by `c`. The oracle statements pass through. -/
def finalSumcheckStepLogic :
    OracleReduction.DeterministicLogicStep []ₒ
      (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (Unit)
      (pSpecFinalSumcheckStep (L := L))
      where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multiplier)
      (Fin.last ℓ)
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    -- For strict relations, we need t from the input witness
    -- In completeness proofs, extracted from h_relIn via StrictOracleWitnessConsistent
    ((stmtOut, oStmtOut), witOut) ∈ strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifierCheck := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let eq_tilde_eval := eqTilde (r := stmtIn.ctx.t_eval_point) (r' := stmtIn.challenges)
    stmtIn.sumcheck_target = eq_tilde_eval * c
  verifierOut := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      finalConstant := c
    }
  honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    -- The honest prover sends c = f^(ℓ)(0, ..., 0)
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    FullTranscript.mk1 c
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      finalConstant := c
    }
    ((stmtOut, oStmtIn), ())
  outputInterfaces := inferInstance
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The source-domain index of the final folding block. -/
def lastBlockStart : Fin r :=
  ⟨getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ), by
    have h := (getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).isLt
    have hrate := h_ℓ_add_R_rate
    omega⟩

omit [NeZero r] [NeZero 𝓡] in
/-- The final block starts at the domain of the last committed oracle. -/
lemma lastBlockStart_val_eq_getLastOracleDomainIndex :
    (lastBlockStart (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).val =
      getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ) := rfl

omit [NeZero r] [NeZero 𝓡] in
/-- The final block begins `ϑ` rounds before the last round. -/
lemma lastBlockStart_val :
    (lastBlockStart (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).val = ℓ - ϑ := by
  dsimp only [lastBlockStart, getLastOracleDomainIndex]
  rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
    Nat.div_mul_cancel hdiv.out]

/-- The destination-domain index after folding the final block. -/
def lastBlockEnd : Fin r :=
  ⟨(lastBlockStart (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).val + ϑ, by
    rw [lastBlockStart_val]
    have hle := blockSize_le_rounds ℓ ϑ
    omega⟩

omit [NeZero r] [NeZero 𝓡] in
/-- The final block ends at the last round. -/
lemma lastBlockEnd_val :
    (lastBlockEnd (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).val = ℓ := by
  dsimp only [lastBlockEnd]
  rw [lastBlockStart_val, Nat.sub_add_cancel (blockSize_le_rounds ℓ ϑ)]

/-- The challenge family restricted to the final folding block. -/
def lastBlockChallenges (challenges : Fin ℓ → L) : Fin ϑ → L := fun j =>
  challenges ⟨(lastBlockStart (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).val + j.val, by
    rw [lastBlockStart_val]
    have hj := j.isLt
    have hle := blockSize_le_rounds ℓ ϑ
    omega⟩

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- If the committed oracles and final witness word are honest folds of the same polynomial,
folding the final oracle block gives the witness word's constant value. -/
lemma iteratedFold_lastOracle_eq_finalConstant
    (stmtIn : Statement (L := L) Context (Fin.last ℓ))
    (witIn : Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_witness : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges)
    (h_oracles : StrictOracleFoldingConsistent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := Fin.last ℓ) (t := witIn.t)
      (challenges := stmtIn.challenges) (oStmt := oStmtIn)) :
    ∀ y, iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := lastBlockStart (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (steps := ϑ)
      (destIdx := lastBlockEnd (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (h_destIdx := rfl) (h_destIdx_le := by rw [lastBlockEnd_val])
      (getLastOracle 𝔽q β (h_destIdx := lastBlockStart_val_eq_getLastOracleDomainIndex) oStmtIn)
      (lastBlockChallenges (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn.challenges) y =
      witIn.f ⟨0, by simp only [zero_mem]⟩ := by
  let start : Fin r := lastBlockStart (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let dest : Fin r := lastBlockEnd (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let k := start.val
  have hsteps : k + ϑ = ℓ := lastBlockEnd_val
    (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let P₀ : L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := 0) P₀
  have hlast : getLastOracle 𝔽q β (ϑ := ϑ) (destIdx := start)
      (h_destIdx := lastBlockStart_val_eq_getLastOracleDomainIndex) oStmtIn =
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k) (destIdx := start)
        (h_destIdx := by simp [k])
        (h_destIdx_le := by dsimp [start]; rw [lastBlockStart_val]; omega)
        f₀ (Fin.take k (by change k ≤ ℓ; omega) stmtIn.challenges) := by
    have h := h_oracles (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ))
    have hpfx : getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := k)
        (Fin.last ℓ) stmtIn.challenges 0 (by change 0 + k ≤ ℓ; omega) =
        Fin.take k (by change k ≤ ℓ; omega) stmtIn.challenges := by
      funext c
      simp only [getFoldingChallenges, zero_add, Fin.take_apply]
      congr 1
    funext x
    dsimp only [getLastOracle]
    refine (congr_fun h _).trans ?_
    exact congrArg (fun rs : Fin k → L =>
      iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := 0) (steps := k) (destIdx := start) (h_destIdx := by simp [k])
        (h_destIdx_le := by dsimp [start]; rw [lastBlockStart_val]; omega) f₀ rs x) hpfx
  intro y
  rw [hlast]
  have hsplit := iteratedFold_take_suffix_of_add_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) k ϑ hsteps
    (midIdx := start) (destIdx := dest) (hmid := by simp [k])
    (hdest := by simpa only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add] using lastBlockEnd_val)
    (hle := by dsimp [dest]; rw [lastBlockEnd_val]) f₀ stmtIn.challenges
  change iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := start) (steps := ϑ) (destIdx := dest)
    (h_destIdx := rfl) (h_destIdx_le := by dsimp [dest]; rw [lastBlockEnd_val])
    (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k) (destIdx := start)
      (h_destIdx := by simp [k]) (h_destIdx_le := by dsimp [start]; rw [lastBlockStart_val]; omega)
      f₀ (Fin.take k (by change k ≤ ℓ; omega) stmtIn.challenges))
    (fun j => stmtIn.challenges ⟨k + j.val, by change k + j.val < ℓ; omega⟩) y = _
  rw [hsplit, iteratedFold_to_level_ℓ_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := witIn.t)
    (h_destIdx := by dsimp [dest]; rw [lastBlockEnd_val])]
  rw [h_witness]
  dsimp only [getMidCodewords]
  have hconstant := iteratedFold_to_level_ℓ_eval 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t ⟨ℓ, by omega⟩ rfl stmtIn.challenges
  dsimp only at hconstant
  unfold polyToOracleFunc at hconstant
  exact (congr_fun hconstant ⟨0, by simp only [zero_mem]⟩).symm

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- Under sum-check consistency and the strict oracle-witness consistency at round `ℓ`, the honest
final constant passes the closing sum-check equation. -/
lemma finalSumcheckStepLogic_verifierCheck_honest
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
        witIn.H)
    (h_strictOracleWitConsistency_In : StrictOracleWitnessConsistent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (multpoly := multiplier) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)) (stmt := stmtIn)
      (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  classical
  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  -- Simplify the verifier check to the equality we need to prove
  change (finalSumcheckStepLogic 𝔽q β).verifierCheck stmtIn transcript
  simp only [finalSumcheckStepLogic]
  dsimp only [sumcheckConsistencyProp] at h_sumcheck_cons
  simp only [Fin.val_last] at h_sumcheck_cons
  rw [Finset.sum_eq_single_of_mem (a := fun _ => 0)
    (by
      simp only [SumcheckDomain.mem_cube]
      intro i
      have hi := i.isLt
      omega)
    (fun b _ hb => (hb (by funext i; have hi := i.isLt; omega)).elim)] at h_sumcheck_cons
  have h_wit_structural_invariant := h_strictOracleWitConsistency_In.1
  have h_f_eq_getMidCodewords_t : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_structural_invariant.2
  have h_witIn_f_0_eq_c : witIn.f ⟨0, by simp only [zero_mem]⟩ = transcript.messages ⟨0, rfl⟩ := by
    rfl
  have h_c_eq : (transcript.messages ⟨0, rfl⟩) = witIn.t.val.eval stmtIn.challenges := by
    change witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges
    dsimp only [getMidCodewords, Fin.coe_ofNat_eq_mod] at h_f_eq_getMidCodewords_t
    rw [congr_fun h_f_eq_getMidCodewords_t ⟨0, by simp only [zero_mem]⟩]
    have h_eval := iteratedFold_to_level_ℓ_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := witIn.t) (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
    exact congr_fun (h := h_eval) ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  -- Apply `eval_fixPrefix_initial_last` to connect H.eval with eqTilde * f(0)
  have h_H_eval_at_zero_eq_mul : witIn.H.val.eval (fun _ => (0 : L)) =
      eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
      (witIn.f ⟨0, by simp only [zero_mem]⟩) := by
    rw [h_wit_structural_invariant.1]
    rw [Sumcheck.Structured.eval_fixPrefix_initial_last]
    -- ↑witIn.t = witIn.f ⟨0, ⋯⟩
    rw [h_witIn_f_0_eq_c, h_c_eq]; rfl
  -- Combine to finish the proof
  change stmtIn.sumcheck_target = eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
    witIn.f ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  rw [←h_H_eval_at_zero_eq_mul]
  exact h_sumcheck_cons

omit [DecidableEq 𝔽q] [SampleableType L] in
/-- The final sum-check step is strongly complete: from the strict round relation at `ℓ`, the
honest constant passes the check and the output lies in the strict final sum-check output
relation. -/
lemma finalSumcheckStepLogic_isStronglyComplete :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn BEFORE any simp changes its structure
  simp only [finalSumcheckStepLogic, strictRoundRelation, StrictRoundRelated,
    Set.mem_ofPred_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOracleWitConsistency_In⟩ := h_relIn
  -- The multilinear polynomial of the witness
  let t := witIn.t
  have h_VCheck_passed := finalSumcheckStepLogic_verifierCheck_honest 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
    (oStmtIn := oStmtIn) (challenges := challenges)
    (h_sumcheck_cons := h_sumcheck_cons)
    (h_strictOracleWitConsistency_In := by exact h_strictOracleWitConsistency_In)
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl -- not new oracles added
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- The output satisfies the strict final relation
    simp only [finalSumcheckStepLogic, strictRoundRelation, StrictRoundRelated, Fin.val_last,
      Prod.mk.eta, Set.mem_ofPred_eq, strictFinalSumcheckRelOut, StrictFinalSumcheckRelated,
      StrictFinalSumcheckFoldingState, exists_and_right, Subtype.exists,
        Fin.isValue, MessageIdx, step]
    dsimp only [StrictOracleWitnessConsistent, Fin.val_last, OracleFrontierIndex.mkFromStmtIdx,
      StrictOracleFoldingConsistent, Fin.eta, ↓dreduceIte,
    Bool.false_eq_true] at h_strictOracleWitConsistency_In ⊢
    have h_oracle_folding_In := h_strictOracleWitConsistency_In.2
    refine ⟨?_, ?_⟩
    · -- Component 1: OracleFoldingConsistent
      use t
      simp only [SetLike.coe_mem, exists_const]
      exact h_oracle_folding_In
    · -- Component 2: finalOracleFoldingConsistency
      funext y
      classical
      have res := iteratedFold_lastOracle_eq_finalConstant 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
        (oStmtIn := oStmtIn)
        (h_witness := h_strictOracleWitConsistency_In.1.2)
        (h_oracles := h_strictOracleWitConsistency_In.2)
      dsimp only [lastBlockStart, lastBlockEnd, lastBlockChallenges,
        getLastOracleDomainIndex] at res
      exact res y
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold
