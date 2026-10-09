/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold

/-!
# Binary Basefold: the relay step

Outside a commitment round no oracle is sent. The relay step is the zero-round step that moves
the oracle statements from round `i` to round `i + 1` (the oracle counts are equal), so that a fold
step followed by a relay step lands in the round relation at `i + 1`, as a fold step followed by
a commit step does. It is a formalization device and has no counterpart in [DP24].

## Main definitions and statements

* `relayOracleProver`, `relayOracleVerifier`, `relayOracleReduction`: the step.
* `relayOracleVerifierGuardedForm`: the verifier's trivially-true guard and its verdict as data,
  from its pure form `relayOracleVerifierPureForm`.
* `relayOracleReduction_perfectCompleteness`: perfect completeness from the strict fold-step output
  relation to the strict round relation at `i + 1`.
* `relayKnowledgeStateFunction`: the round relation at `i + 1` on the reindexed oracle statements;
  that it is the fold-step output relation is the content of the step's knowledge soundness.
* `relayOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`: worst-case round-by-round knowledge
  soundness at `relayRbrExtractor` and `relayKnowledgeStateFunction`, with existential and averaged
  forms.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
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

section RelayStep

/-- The prover state of the relay step. -/
def relayPrvState (i : Fin ℓ) : Fin (0 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- The prover of the relay step: it sends nothing and reindexes its oracle statements to round
`i + 1`. -/
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

/-- Outside a commitment round the number of oracle statements does not change. -/
lemma toOutCodewordsCount_castSucc_eq_succ_of_not_isCommitmentRound (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
  simp only [toOutCodewordsCount_succ_eq, hNCR, ↓reduceIte]

/-- The output oracles of the relay step: the input oracles, reindexed. -/
def relayOracleVerifier_embed (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    Fin (toOutCodewordsCount ℓ ϑ i.succ) →
      Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ pSpecRelay.MessageIdx :=
  fun j => Sum.inl ⟨j.val, by
    rw [toOutCodewordsCount_castSucc_eq_succ_of_not_isCommitmentRound i hNCR]; omega⟩

/-- The verifier of the relay step outside a commitment round: it keeps the statement and reindexes
the oracle statements to round `i + 1`. -/
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

/-- The oracle reduction of the relay step outside a commitment round. -/
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

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The relay verifier's output oracles are the input oracles reindexed along the equal oracle
counts, `mapOStmtOutRelayStep`. -/
lemma mapOStmtOutRelayStep_eq_materializeOutput
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

/-- The relay verifier's verdict as data: it accepts every transcript, keeps the statement, and
reindexes the oracle statements (`mapOStmtOutRelayStep`). -/
def relayOracleVerifierPureForm (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR).toVerifier.PureForm where
  verify s tr := (s.1, (relayOracleVerifier (Context := Context) 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).materializeOutput tr.challenges s.2 tr.messages)
  verify_eq _ _ := rfl

/-- The relay verifier's guard and verdict as data: the trivially-true guard of its pure form. -/
def relayOracleVerifierGuardedForm (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR).toVerifier.GuardedForm :=
  (relayOracleVerifierPureForm 𝔽q β i hNCR).toGuardedForm

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The relay verifier never rejects. -/
@[simp]
theorem relayOracleVerifierGuardedForm_check (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (s : Statement (L := L) Context i.succ × ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : pSpecRelay.FullTranscript) :
    (relayOracleVerifierGuardedForm (Context := Context) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).check s tr = true := rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The relay verifier keeps the statement and reindexes the oracle statements. -/
@[simp]
theorem relayOracleVerifierGuardedForm_out (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (s : Statement (L := L) Context i.succ × ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : pSpecRelay.FullTranscript) :
    (relayOracleVerifierGuardedForm (Context := Context) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).out s tr =
      (s.1, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR s.2) :=
  Prod.ext rfl
    (mapOStmtOutRelayStep_eq_materializeOutput (Context := Context) 𝔽q β i hNCR s.2 tr).symm

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [DecidableEq 𝔽q] h_β₀_eq_1 [CharP L 2] [SampleableType L] in
/-- Outside a commitment round, reindexing the oracle statements takes the strict fold-step output
relation to the strict round relation at `i + 1`. -/
lemma mapOStmtOutRelayStep_mem_strictRoundRelation (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement Context i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (witIn : Witness 𝔽q β i.succ)
    (h_relIn : ((stmtIn, oStmtIn), witIn) ∈ strictFoldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ :=
        ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i) :
    ((stmtIn, fun (j : Fin (toOutCodewordsCount ℓ ϑ i.succ)) ↦
      oStmtIn ⟨j.val, by
        rw [toOutCodewordsCount_castSucc_eq_succ_of_not_isCommitmentRound i hNCR]; omega⟩), witIn)
      ∈ strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
        toOutCodewordsCount ℓ ϑ i.castSucc :=
        (toOutCodewordsCount_castSucc_eq_succ_of_not_isCommitmentRound i hNCR).symm
      exact h_relIn.2.2 ⟨j, by omega⟩

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Perfect completeness of the relay step, from the strict fold-step output relation to the strict
round relation at `i + 1`. -/
theorem relayOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecRelay)
      (relIn := strictFoldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      (relOut := strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      (oracleReduction := relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR)
      (init := init)
      (impl := impl) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  let G := relayOracleVerifierGuardedForm (Context := Context) 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  have hp : (relayOracleProver (Context := Context) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR).run (stmt, oStmt) wit =
      pure (default, ((stmt, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR oStmt), wit)) := rfl
  change x ∈ MonadAttach.support ((relayOracleProver (Context := Context) 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).run (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  rw [hp] at hx
  simp only [G, relayOracleVerifierGuardedForm_check, ↓reduceIte] at hx
  subst x
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [relayOracleVerifierGuardedForm_out]
    exact mapOStmtOutRelayStep_mem_strictRoundRelation 𝔽q β i hNCR stmt oStmt wit hIn
  · exact (relayOracleVerifierGuardedForm_out (Context := Context) 𝔽q β i hNCR (stmt, oStmt)
      default).symm

/-- The relay step has no rounds, so its round-by-round knowledge error is the empty family. -/
def relayKnowledgeError (m : pSpecRelay.ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, _⟩ => j.elim0

/-- The round-by-round extractor of the relay step: the witness passes through unchanged. -/
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

/-- The knowledge state of the relay step: the round relation at `i + 1` with the oracle statements
reindexed, which is the fold-step output relation (`incrementalBadEventExistsProp_relay_preserved`,
`oracleFoldingConsistencyProp_relay_preserved`). -/
def relayKStateProp (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmtIn : (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) : Prop :=
  -- Relay step inherits sumcheckConsistency from foldStepRelOut (relIn) and preserves it
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
      stmtIn.sumcheck_target witMid.H
  masterKStateProp (multpoly := multpoly) (ϑ := ϑ) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ)
    (stmt := stmtIn) (wit := witMid) (oStmt := mapOStmtOutRelayStep
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)
    (localChecks := sumCheckConsistency)

/-- The knowledge-state function of the relay step, `relayKStateProp`, with its obligations. -/
def relayKnowledgeStateFunction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)  i.succ)
      (extractor := relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    relayKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (multpoly := multpoly) (𝓑 := 𝓑)
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
        · exact hGood.2.2.1
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
        · exact hGood.2.2.1
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
  toFun_full := fun s tr witOut h => by
    have hrel := ((relayOracleVerifierGuardedForm (Context := Context) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).check_and_of_prEvent_pos h).2
    rwa [relayOracleVerifierGuardedForm_out 𝔽q β i hNCR s tr] at hrel

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- **Worst-case round-by-round knowledge soundness of the relay step**, at the extractor
`relayRbrExtractor`, the knowledge-state function `relayKnowledgeStateFunction` and the error
`relayKnowledgeError`. The step has no rounds, so there is no extraction-failure event to bound;
the content is the knowledge-state function's obligations. -/
theorem relayOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      (fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relayKnowledgeStateFunction (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hNCR)
      relayKnowledgeError :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_isEmpty_challengeIdx _ _

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- Worst-case round-by-round knowledge soundness of the relay step: the existential form of
`relayOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`. -/
theorem relayOracleVerifier_rbrKnowledgeSoundnessWorstCase (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.succ)
      relayKnowledgeError :=
  (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, relayOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith (multpoly := multpoly)
      (𝓑 := 𝓑) 𝔽q β i hNCR⟩

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the relay step: the averaged form of
`relayOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem relayOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
      (relOut := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ)
      relayKnowledgeError :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (relayOracleVerifier_rbrKnowledgeSoundnessWorstCase (multpoly := multpoly) (𝓑 := 𝓑)
      𝔽q β i hNCR)

end RelayStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
