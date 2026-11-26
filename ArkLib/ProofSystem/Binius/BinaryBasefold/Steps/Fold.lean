/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold.Protocol
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Binary Basefold: round-by-round knowledge soundness of the fold step

The fold step's extractor, knowledge-state function and error, and its round-by-round knowledge
soundness. The knowledge state before the challenge is the round relation at `i` with the local
checks of the sent round polynomial; after the challenge it is the fold-step output relation. An
extraction failure at the challenge is a fresh incremental folding bad event of the last oracle
block, or a bad sum-check event: the sent round polynomial differs from the honest one of the
unique witness consistent with the first oracle, but agrees with it at the challenge.

## Main statements

* `prob_foldStep_rbrExtractionFailureEvent_le`: for every input statement and every sent round
  polynomial, the extraction failure probability over the challenge alone is at most
  `foldKnowledgeError`, the Schwartz–Zippel term `2 / |L|` plus the bound of
  `prob_incrementalFoldingBadEvent_fresh_le` on the fresh incremental folding bad event.
* `foldOracleVerifier_rbrKnowledgeSoundnessWith`: round-by-round knowledge
  soundness at `foldRbrExtractor`, `foldKnowledgeStateFunction` and `foldKnowledgeError`;
  the existential form is `foldOracleVerifier_rbrKnowledgeSoundness`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The fold step is lines 1–4 of the loop of the evaluation IOP of Construction 4.12. Its bad
  events are the per-challenge form of the sum-check and folding bad events of the proof of
  Theorem 4.17 (Definition 4.20, Proposition 4.21).
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

section FoldStep

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- The domain level of the oracle committed at the start of round `i`'s block. -/
@[reducible]
def foldStepBlockStart (i : Fin ℓ) : Fin r :=
  ⟨(getLastOracleDomainIndex ℓ ϑ i.castSucc).val,
    lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (getLastOracleDomainIndex ℓ ϑ i.castSucc).isLt⟩

/-- The domain level at the end of round `i`'s folding block. -/
@[reducible]
def foldStepBlockEnd (i : Fin ℓ) : Fin r :=
  ⟨(foldStepBlockStart (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i).val + ϑ,
    lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc)⟩

open Classical in
/-- The round-by-round knowledge error of the `i`-th fold step at its challenge: the
Schwartz–Zippel term `2 / |L|` for the degree-two round polynomial, plus the fresh incremental
folding bad-event term `|S⁽ʲ⁺ᶿ⁾| / |L|`, where `j` is the domain index of the last oracle at round
`i`. -/
def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
  let err_SC := (2 : ℝ≥0) / (Fintype.card L)
  let err_BE :=
    (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate
      (foldStepBlockEnd (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i)) : ℝ≥0) /
      (Fintype.card L)
  err_SC + err_BE

/-- The intermediate witness types of the fold step: the round-`i` witness before the challenge
and the round-`(i + 1)` witness after it, the type of the output witness. -/
def FoldIntermediateWitness (i : Fin ℓ) : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨1, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨2, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- Re-project a witness to the input statement's challenges. -/
@[reducible]
def foldStepWitBeforeFromWitMid (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc where
  t := witMid.t
  H := MvPolynomial.fixPrefix ℓ i.castSucc
    (computeInitialSumcheckPoly ℓ witMid.t (multpoly stmtIn.ctx))
    (challenges := stmtIn.challenges)
  f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witMid.t
    (challenges := stmtIn.challenges)

/-- The round-by-round extractor of the fold step. Across the challenge it recovers the round-`i`
witness from a round-`(i + 1)` witness by re-projecting the round polynomial and the folded word
of its multilinear polynomial to the input statement's challenges; across the message it keeps
the witness. The output witness is extracted as itself. -/
noncomputable def foldRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L))
    (WitMid := FoldIntermediateWitness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  extractIn := fun _ w => w
  extractMid := fun m ⟨stmtIn, _oStmtIn⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both are Witness i.castSucc
    | ⟨1, _⟩ =>
      foldStepWitBeforeFromWitMid (multpoly := multpoly) 𝔽q β i stmtIn witMidSucc
  -- extractOut is the identity: WitMid (Fin.last 2) = WitOut = Witness i.succ
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-- The knowledge state of the fold step after `m` messages: the round relation at `i` before the
message; after the message, the same state with the local check that the sent polynomial passes
the verifier's check and is the honest round polynomial; after the challenge, the state of the
fold-step output relation at the folded statement, with the verifier's check. -/
def FoldKnowledgeState {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : FoldIntermediateWitness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    KnowledgeInvariant (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtMid.sumcheck_target
          witMid.H)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h :=
        witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    KnowledgeInvariant (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := h_i.val.eval r_i'
    let stmtOut : Statement (L := L) Context i.succ := {
        -- same  as in Verifier's output & getFoldProverFinalOutput
      ctx := stmtMid.ctx,
      sumcheck_target := newSumcheckTarget,
      challenges := Fin.snoc stmtMid.challenges r_i'
    }
    let oStmtOut := oStmtMid
    let witOut := witMid
    -- Use OUTPUT state: stmtIdx advances to i.succ, oracleIdx stays at i.castSucc (no new oracle)
    KnowledgeInvariant (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        let explicitVCheck :=
          h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
          -- we also keep the output-state sumcheck consistency
          sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtOut.sumcheck_target witOut.H)

/-- The knowledge-state function of the fold step, `FoldKnowledgeState`, with its obligations. -/
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).KnowledgeStateFunction init impl
      (relIn := roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (extractor := foldRbrExtractor (multpoly := multpoly) (𝓡 := 𝓡) (ϑ := ϑ) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    FoldKnowledgeState (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmtMid := stmtMid) (witMid := witMid) (oStmtMid := oStmtMid)
  toFun_empty := fun _ _ h => h
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
    unfold FoldKnowledgeState at h_kState_round1 ⊢
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
      have h_struct : WitnessStructuralInvariant 𝔽q β (multpoly := multpoly)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtMid witMid := h_good.2.1
      have h_init : FirstOracleWitnessConsistent 𝔽q β witMid.t
          (getFirstOracle 𝔽q β oStmtMid) := h_good.2.2.1
      have h_fold := h_good.2.2.2
      have h_sumcheck : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
          stmtMid.sumcheck_target witMid.H := by
        simp_rw [h_localized] at h_explicit
        rw [h_explicit.symm]
        exact Sumcheck.Structured.eval_add_eval_getSumcheckRoundPoly ℓ 𝓑 i witMid.H
      exact Or.inr ⟨h_sumcheck, h_struct, h_init, h_fold⟩
  toFun_full := fun s tr witOut h => by
    obtain ⟨hcheck, hrel⟩ := (foldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly)
          i).check_and_of_prEvent_pos h
    rw [foldOracleVerifierGuardedForm_check 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multpoly) i s tr] at hcheck
    rw [foldOracleVerifierGuardedForm_out 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multpoly) i s tr, foldOracleVerifier_materializeOutput] at hrel
    rcases hrel with hbad | ⟨hsc, hrest⟩
    · exact Or.inl hbad
    · exact Or.inr ⟨⟨of_decide_eq_true hcheck, hsc⟩, hrest⟩

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- The multilinear polynomial whose codeword is unique-decoding close to the first oracle is
unique. -/
lemma firstOracleWitnessConsistency_unique (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {t₁ t₂ : MultilinearPoly L ℓ}
    (h₁ : FirstOracleWitnessConsistent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : FirstOracleWitnessConsistent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  classical
  have h₁_some :
      extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₁ :=
    (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) (tpoly := t₁)).2 h₁
  have h₂_some :
      extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₂ :=
    (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) (tpoly := t₂)).2 h₂
  rw [h₁_some] at h₂_some
  injection h₂_some with h_t

/-- The honest round polynomial of the witness extracted from a round-`(i + 1)` witness. -/
@[reducible]
def foldStepHStarFromWitMid (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    L⦃≤ 2⦄[X] :=
  let witBefore := foldStepWitBeforeFromWitMid
    (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i stmtIn witMid
  getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h := witBefore.H)

/-- The number of challenges already received in the current folding block. -/
def foldStepPrefixLen (i : Fin ℓ) : ℕ :=
  min ϑ (i.val - (getLastOracleDomainIndex ℓ ϑ i.castSucc).val)

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- The current block prefix is shorter than a full block. -/
lemma foldStepPrefixLen_lt (i : Fin ℓ) : foldStepPrefixLen (ϑ := ϑ) i < ϑ := by
  unfold foldStepPrefixLen
  rw [sub_getLastOracleDomainIndex_castSucc_val]
  exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.mod_lt _ (NeZero.pos ϑ))

/-- The challenges received since the last committed oracle. -/
def foldStepPrefix (i : Fin ℓ) (challenges : Fin i.val → L) :
    Fin (foldStepPrefixLen (ϑ := ϑ) i) → L := fun j =>
  challenges ⟨(getLastOracleDomainIndex ℓ ϑ i.castSucc).val + j.val, by
    clear h_ℓ_add_R_rate
    have hprefix := Nat.min_le_right ϑ (i.val -
      (getLastOracleDomainIndex ℓ ϑ i.castSucc).val)
    have hlast : (getLastOracleDomainIndex ℓ ϑ i.castSucc).val ≤ i.val := by
      rw [getLastOracleDomainIndex_castSucc_val]
      exact Nat.div_mul_le_self _ _
    have hj := j.isLt
    change j.val < min ϑ (i.val - (getLastOracleDomainIndex ℓ ϑ i.castSucc).val) at hj
    omega⟩

/-- The fresh incremental folding bad event of the fold step's challenge: the incremental bad event
of the last oracle block does not hold for the challenges received before and holds once the
challenge is appended. -/
@[reducible]
def FoldStepFreshBadEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L) : Prop :=
  let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
  let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
  let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
  let curOracleDomainIdx := foldStepBlockStart (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (ϑ := ϑ) i
  let kBefore : ℕ := foldStepPrefixLen (ϑ := ϑ) i
  -- `kBefore < ϑ`, so `kBefore + 1 ≤ ϑ`
  have h_kBefore_lt : kBefore < ϑ := foldStepPrefixLen_lt i
  let destIdx := foldStepBlockEnd (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i
  let r_prefix : Fin kBefore → L := foldStepPrefix i challengesBefore
  let E_before :=
    Binius.BinaryBasefold.IncrementalFoldingBadEvent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
      (h_k_le := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val))
      (h_midIdx := by simp only)
      (h_destIdx := rfl)
      (h_destIdx_le := getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc)
      (f_block_start := stmtOStmtIn.2 j)
      (r_challenges := r_prefix)
  let E_after :=
    Binius.BinaryBasefold.IncrementalFoldingBadEvent 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (block_start_idx := curOracleDomainIdx)
    (midIdx := ⟨curOracleDomainIdx.val + (kBefore + 1), by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
        oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      omega
    ⟩)
    (destIdx := destIdx) (k := kBefore + 1)
    (h_k_le := Nat.succ_le_of_lt h_kBefore_lt)
    (h_midIdx := by simp only)
    (h_destIdx := rfl)
    (h_destIdx_le := getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc)
    (f_block_start := stmtOStmtIn.2 j)
    (r_challenges := Fin.snoc r_prefix r_i')
  ¬ E_before ∧ E_after

/-- A candidate round-`(i + 1)` witness is structured for the folded statement and consistent with
the first oracle. -/
@[reducible]
def FoldStepWitnessConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt : Statement (L := L) Context i.succ := {
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
      ctx := stmtOStmtIn.1.ctx
  }
  let structural := WitnessStructuralInvariant 𝔽q β (multpoly := multpoly)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt witMid
  let initial := FirstOracleWitnessConsistent 𝔽q β witMid.t (getFirstOracle 𝔽q β stmtOStmtIn.2)
  structural ∧ initial

omit [Field L] [Fintype L] [DecidableEq L] [SampleableType L] in
private theorem fin_fun_heq_of_cast {m n : ℕ} (h : m = n)
    (f : Fin m → L) (g : Fin n → L)
    (hfg : ∀ i : Fin m, f i = g (Fin.cast h i)) :
    HEq f g := by
  subst h
  apply heq_of_eq
  funext i
  simpa using hfg i

omit [SampleableType L] in
omit [DecidableEq 𝔽q] in
/-- If the incremental bad event exists after the fold step's challenge but the challenge did not
cause a fresh bad event, it already existed before the challenge. -/
lemma hasIncrementalBadEvent_of_not_foldStepFreshBadEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L)
    (h_bad_after : HasIncrementalBadEvent 𝔽q β i.succ
      (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) stmtOStmtIn.2
      (Fin.snoc stmtOStmtIn.1.challenges r_i'))
    (h_not_fresh : ¬ FoldStepFreshBadEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i') :
  HasIncrementalBadEvent 𝔽q β i.castSucc
      (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
      stmtOStmtIn.1.challenges := by
  classical
  unfold HasIncrementalBadEvent at h_bad_after ⊢
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
        IncrementalFoldingBadEvent 𝔽q β
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
      refine (incrementalFoldingBadEvent_congr 𝔽q β blockStart
        (hmid := by apply Fin.ext; dsimp [blockDest]; omega) (hk := hk_after)
        (h_k_le := Nat.min_le_left _ _) (h_k_le' := le_rfl)
        (h_midIdx := _) (h_midIdx' := _)
        (h_destIdx := _) (h_destIdx_le := _) (f := _) (rs := _) (rs' := _)
        (hrs := ?_)).mp hj_copy
      apply fin_fun_heq_of_cast hk_after
      intro cId
      dsimp [afterSlice]
    have hj_before_full := hj_after_full
    rw [h_challenges] at hj_before_full
    refine (incrementalFoldingBadEvent_congr 𝔽q β blockStart
      (hmid := by apply Fin.ext; dsimp [blockDest]; omega) (hk := hk_before)
      (h_k_le := Nat.min_le_left _ _) (h_k_le' := le_rfl)
        (h_midIdx := _) (h_midIdx' := _)
      (h_destIdx := _) (h_destIdx_le := _) (f := _) (rs := _) (rs' := _)
      (hrs := ?_)).mpr hj_before_full
    apply fin_fun_heq_of_cast hk_before
    intro cId
    dsimp [beforeSlice]
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
        omega
      dsimp [getLastOraclePositionIndex]
      exact h_val
    subst j
    dsimp [FoldStepFreshBadEvent] at h_not_fresh
    have h_j_val : (getLastOraclePositionIndex ℓ ϑ i.castSucc).val = i.val / ϑ :=
      getLastOraclePositionIndex_castSucc_val ℓ ϑ i
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
      omega
    let kBefore : ℕ := min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)
    let prefixSlice : Fin kBefore → L := fun cId =>
      stmtOStmtIn.1.challenges
        ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
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
        exact (Fin.snoc_castSucc (α := fun _ => L) (p := stmtOStmtIn.1.challenges)
          (x := r_i') ⟨_, h_idx_lt⟩).trans
          (Fin.snoc_castSucc (α := fun _ => L) (p := prefixSlice) (x := r_i') ⟨cId.val, h_lt⟩).symm
      · have h_eq_last :
            cId.val = kBefore := by
          omega
        have h_idx_eq :
            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val = i.val := by
          rw [h_eq_last]
          dsimp [kBefore]
          omega
        obtain rfl : cId = Fin.last kBefore := Fin.ext h_eq_last
        exact ((congrArg (Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i')
          (Fin.ext h_idx_eq : (_ : Fin (↑i.castSucc + 1)) = Fin.last _)).trans
          (Fin.snoc_last (α := fun _ => L) _ _)).trans
          (Fin.snoc_last (α := fun _ => L) (p := prefixSlice) r_i').symm
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
        IncrementalFoldingBadEvent 𝔽q β
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
      refine (incrementalFoldingBadEvent_congr 𝔽q β blockStart
        (hmid := by apply Fin.ext; dsimp [blockStart, blockMidAfter, kBefore]; omega)
        (hk := hk_after_last) (h_k_le := Nat.min_le_left _ _)
        (h_k_le' := by omega) (h_midIdx := _)
        (h_midIdx' := _) (h_destIdx := _) (h_destIdx_le := _) (f := _)
        (rs := _) (rs' := _) (hrs := ?_)).mp hj_copy
      apply fin_fun_heq_of_cast hk_after_last
      intro cId
      dsimp [afterSlice]
    have h_after_last' := h_after_last_afterSlice
    rw [h_after_challenges] at h_after_last'
    by_contra h_before_false
    exact h_not_fresh ⟨h_before_false, h_after_last'⟩

omit [SampleableType L] in
omit [DecidableEq 𝔽q] in
/-- An extraction failure at the fold step's challenge is either a fresh incremental folding bad
event, or, failing that, a bad sum-check event for a witness consistent with the first oracle:
the sent round polynomial differs from the honest one but agrees with it at the challenge. -/
lemma foldStepFreshBadEvent_or_of_rbrExtractionFailureEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (hfail : rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (multpoly := multpoly) (𝓑 := 𝓑) (init := init)
        (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (multpoly := multpoly) 𝔽q β i) (i := ⟨1, rfl⟩) (stmtIn :=
          stmtOStmtIn)
    (transcript := FullTranscript.mk1 h_i) (challenge := r_i')) :
    let IncrementalFoldingBadEvent :=
      FoldStepFreshBadEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
    IncrementalFoldingBadEvent ∨ (
      ¬IncrementalFoldingBadEvent ∧
      (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (FoldStepWitnessConsistency (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate :=
            h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i r_i' witMid)
        ∧ (BadSumcheckChallenge r_i' h_i
            (foldStepHStarFromWitMid (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn.1 witMid))
      )
    ) := by
  classical
  let IncrementalFoldingBadEvent : Prop :=
    FoldStepFreshBadEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
  unfold rbrExtractionFailureEvent at hfail
  rcases hfail with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [foldKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold FoldKnowledgeState at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    Transcript.concat] at h_kState_before_false h_kState_after_true
  by_cases h_bad : IncrementalFoldingBadEvent
  · left
    exact h_bad
  · right
    refine ⟨h_bad, ?_⟩
    -- Under ¬ fresh bad-event, the m=2 KState cannot be on the bad branch.
    have h_after_good_exists : ∃ h_after_good, h_kState_after_true = Or.inr h_after_good := by
      cases h_kState_after_true with
      | inl h_bad_after =>
        exfalso
        have h_bad_before : HasIncrementalBadEvent 𝔽q β i.castSucc
          (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
          stmtOStmtIn.1.challenges :=
          hasIncrementalBadEvent_of_not_foldStepFreshBadEvent 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            i stmtOStmtIn r_i' h_bad_after h_bad
        exact h_kState_before_false (Or.inl h_bad_before)
      | inr h_after_good =>
        exact ⟨h_after_good, rfl⟩
    rcases h_after_good_exists with ⟨h_after_good, rfl⟩
    have h_explicit_after :
        h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtOStmtIn.1.sumcheck_target := by
      exact h_after_good.1.1
    have h_sumcheck_after :
        sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) (Polynomial.eval r_i' h_i.val)
            witMid.H := by
      exact h_after_good.1.2
    have h_consistency : FoldStepWitnessConsistency 𝔽q β i stmtOStmtIn h_i r_i' witMid :=
      ⟨h_after_good.2.1, h_after_good.2.2.1⟩
    have h_left_from_consistency :
        BadSumcheckChallenge r_i' h_i
          (foldStepHStarFromWitMid (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := 𝓑) i stmtOStmtIn.1 witMid) := by
      have h_wit_struct_after :
          witMid.H = MvPolynomial.fixPrefix ℓ i.succ
            (computeInitialSumcheckPoly ℓ witMid.t (multpoly stmtOStmtIn.1.ctx))
            (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i') := by
        exact h_consistency.1.1
      let H_before : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        MvPolynomial.fixPrefix ℓ i.castSucc
          (computeInitialSumcheckPoly ℓ witMid.t (multpoly stmtOStmtIn.1.ctx))
          (challenges := stmtOStmtIn.1.challenges)
      let h_star_extracted : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ)
          (i := i) (h := H_before)
      have h_eval_eq_extracted :
          Polynomial.eval r_i' h_i.val = Polynomial.eval r_i' h_star_extracted.val := by
        unfold sumcheckConsistencyProp at h_sumcheck_after
        rw [h_wit_struct_after] at h_sumcheck_after
        rw [Sumcheck.Structured.fixPrefix_initial_succ ℓ witMid.t
          (multpoly stmtOStmtIn.1.ctx) i stmtOStmtIn.1.challenges r_i'] at h_sumcheck_after
        exact h_sumcheck_after.trans
          (Sumcheck.Structured.sum_projectToNextSumcheckPoly_uniform ℓ 𝓑 i H_before r_i')
      have h_hi_ne_extracted : h_i ≠ h_star_extracted := by
        intro h_eq
        apply h_kState_before_false
        right
        refine ⟨?_, ?_, ?_, ?_⟩
        · constructor
          · exact h_explicit_after
          · have h_eq' := h_eq
            simp only [h_star_extracted, H_before, foldRbrExtractor, Fin.isValue] at h_eq' ⊢
            exact h_eq'
        · unfold WitnessStructuralInvariant
          simp only [Fin.val_castSucc, foldRbrExtractor, Fin.zero_eta, Fin.isValue,
            Fin.succ_zero_eq_one, Fin.mk_one, Fin.succ_one_eq_two,
            Fin.coe_ofNat_eq_mod, Nat.reduceMod, and_self]
        · exact h_consistency.2
        · have h_folding_after := h_after_good.2.2.2
          unfold OracleFoldingConsistent at h_folding_after ⊢
          intro j hj
          have h_fold_j := h_folding_after j hj
          unfold IsCompliant at h_fold_j ⊢
          rcases h_fold_j with ⟨h_fw_close, h_next_close, h_iter⟩
          refine ⟨h_fw_close, h_next_close, ?_⟩
          have h_gc (y : L) :
              getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
                (Fin.take ↑i.castSucc (Nat.le_succ ↑i.castSucc)
                  (Fin.snoc (α := fun _ : Fin i.succ => L) stmtOStmtIn.1.challenges y))
                (↑j * ϑ) (h := by
                  exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc)
                    (j := j) (hj := hj)) =
              getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
                stmtOStmtIn.1.challenges
                (↑j * ϑ) (h := by
                  exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc)
                    (j := j) (hj := hj)) := by
            ext cId
            dsimp [getFoldingChallenges]
            simp only [Fin.init_snoc]
          refine Eq.trans ?_ h_iter
          congr 1
          exact (h_gc _).symm
      change BadSumcheckChallenge r_i' h_i h_star_extracted
      exact ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
    exact ⟨witMid, h_consistency, h_left_from_consistency⟩

omit [DecidableEq 𝔽q] in
/-- For every input statement and every sent round polynomial, the probability over the challenge
alone of an extraction failure at the fold step is at most `foldKnowledgeError`: a union bound
over the bad sum-check event (Schwartz–Zippel, `Probability.prob_degreeLE_eval_eq_le`) and the
fresh incremental folding bad event (`prob_incrementalFoldingBadEvent_fresh_le`). -/
lemma prob_foldStep_rbrExtractionFailureEvent_le (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) :
    Pr{ let y ← $ᵗ L }[
      rbrExtractionFailureEvent
        (kSF := foldKnowledgeStateFunction (multpoly := multpoly) (𝓑 := 𝓑)
          (init := init) (impl := impl) (σ := σ) 𝔽q β i)
        (extractor := foldRbrExtractor (multpoly := multpoly) 𝔽q β i) ⟨1, rfl⟩
          stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, by rfl⟩ := by
  classical
  let failureEvent := fun y : L =>
    rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (multpoly := multpoly) (𝓑 := 𝓑)
        (init := init) (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (multpoly := multpoly) 𝔽q β i) ⟨1, rfl⟩
      stmtOStmtIn (FullTranscript.mk1 h_i) y
  let sumcheckBadEvent : L → Prop := fun y =>
    let IncrementalFoldingBadEvent :=
      FoldStepFreshBadEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
    (¬IncrementalFoldingBadEvent ∧
        (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (FoldStepWitnessConsistency (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate :=
            h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i y witMid)
        ∧ (BadSumcheckChallenge y h_i
            (foldStepHStarFromWitMid (multpoly := multpoly) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn.1 witMid))
      ))
  let incrementalBadFoldEvent := fun y : L =>
    FoldStepFreshBadEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
  let incrementalBadFoldEvent_or_sumcheckBadEvent := fun y : L =>
    (incrementalBadFoldEvent y) ∨ (sumcheckBadEvent y)
  have h_prob_mono := prEvent_mono ($ᵗ L)
    failureEvent incrementalBadFoldEvent_or_sumcheckBadEvent
    (by
      intro y h_hfail
      have h_imp := (foldStepFreshBadEvent_or_of_rbrExtractionFailureEvent
          (multpoly := multpoly) (𝓑 := 𝓑) (init := init) (impl := impl) 𝔽q β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i)
          (r_i' := y) (hfail := h_hfail))
      dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, sumcheckBadEvent,
        incrementalBadFoldEvent]
      by_cases h_bad : FoldStepFreshBadEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
      · exact Or.inl h_bad
      · cases h_imp with
        | inl h_bad' => exact False.elim (h_bad h_bad')
        | inr h_sum => exact Or.inr h_sum
    )
  refine le_trans h_prob_mono ?_
  dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, foldKnowledgeError]
  apply le_trans (
      prEvent_or_le ($ᵗ L) incrementalBadFoldEvent sumcheckBadEvent
  )
  conv_rhs => simp only [ENNReal.coe_add]; rw [add_comm]
  apply add_le_add
  · dsimp only [incrementalBadFoldEvent, FoldStepFreshBadEvent]
    let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
    let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
    let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
    let curOracleDomainIdx := foldStepBlockStart (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) i
    let kBefore : ℕ := foldStepPrefixLen (ϑ := ϑ) i
    have h_kBefore_lt : kBefore < ϑ := foldStepPrefixLen_lt i
    let destIdx := foldStepBlockEnd (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i
    let r_prefix : Fin kBefore → L := foldStepPrefix i challengesBefore
    have h_res := prob_incrementalFoldingBadEvent_fresh_le 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx_i := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (midIdx_i_succ := ⟨curOracleDomainIdx.val + kBefore + 1, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
        (h_k_lt := h_kBefore_lt)
        (h_midIdx_i := by simp only)
        (h_midIdx_i_succ := by simp only)
        (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
        (f_block_start := stmtOStmtIn.2 j)
      (r_prefix := r_prefix)
    dsimp only [destIdx, curOracleDomainIdx, j, kBefore, r_prefix, stmtIdxBefore, challengesBefore]
      at h_res
    conv_rhs => simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      ENNReal.coe_div, ENNReal.coe_natCast]
    exact h_res
  · dsimp only [sumcheckBadEvent]
    -- Strategy: ignore the `FoldStepFreshBadEvent`; `firstOracleWitnessConsistency_unique`
    -- makes the witness consistent with the first oracle unique, so the bound is
    -- `Probability.prob_degreeLE_eval_eq_le` at that witness's honest round polynomial.
    let compatPred : MultilinearPoly L ℓ → Prop := fun t =>
      FirstOracleWitnessConsistent 𝔽q β t (getFirstOracle 𝔽q β stmtOStmtIn.2)
    by_cases hCompat : ∃ t : MultilinearPoly L ℓ, compatPred t
    · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
      let H_fixed : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        MvPolynomial.fixPrefix ℓ i.castSucc
          (computeInitialSumcheckPoly ℓ t_fixed (multpoly stmtOStmtIn.1.ctx))
          (challenges := stmtOStmtIn.1.challenges)
      let h_star_fixed : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i)
          (h := H_fixed)
      have h_prob_mono_sum := prEvent_mono ($ᵗ L)
        (fun y => sumcheckBadEvent y)
        (fun y => BadSumcheckChallenge y h_i h_star_fixed)
        (by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, h_bad⟩
          have h_t_eq : witMid.t = t_fixed :=
            firstOracleWitnessConsistency_unique 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := i)
              (oStmt := stmtOStmtIn.2) (h₁ := h_cons.2) (h₂ := h_t_fixed_compat)
          have h_bad' := h_bad
          simp only [h_star_fixed, H_fixed, foldStepHStarFromWitMid, h_t_eq] at h_bad' ⊢
          exact h_bad'
        )
      refine le_trans h_prob_mono_sum ?_
      by_cases hne : h_i = h_star_fixed
      · rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hne]
        exact _root_.zero_le
      · refine (prEvent_mono _ _ _ fun _ h => h.2).trans ?_
        have h_sz := Probability.prob_degreeLE_eval_eq_le (R := L) hne
        rw [ENNReal.coe_div (by simp)] at h_sz ⊢
        simpa using h_sz
    · have h_prob_mono_false := prEvent_mono ($ᵗ L)
        (fun y => sumcheckBadEvent y)
        (fun _ => False)
        (by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, _h_bad⟩
          exact (hCompat ⟨witMid.t, h_cons.2⟩).elim
        )
      refine le_trans h_prob_mono_false ?_
      simp

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the fold step, at the extractor
`foldRbrExtractor`, the knowledge-state function `foldKnowledgeStateFunction` and the error
`foldKnowledgeError`: for every input statement and every sent round polynomial, the extraction
failure probability over the challenge alone is at most the Schwartz–Zippel term plus the fresh
incremental folding bad-event term. -/
theorem foldOracleVerifier_rbrKnowledgeSoundnessWith (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).toVerifier.rbrKnowledgeSoundnessWith init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc)
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (FoldIntermediateWitness 𝔽q β i) (foldRbrExtractor (multpoly := multpoly) 𝔽q β i)
      (foldKnowledgeStateFunction (multpoly := multpoly) (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (init := init) (impl := impl) 𝔽q β i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  refine Verifier.rbrKnowledgeSoundnessWith_of_two_message rfl rfl _ _ ?_
  intro stmtIn transcript
  have htr : transcript = FullTranscript.mk1 (transcript ⟨0, by change 0 < 1; omega⟩) := by
    funext k
    fin_cases k
    rfl
  rw [htr]
  exact prob_foldStep_rbrExtractionFailureEvent_le 𝔽q β (i := i) (stmtOStmtIn := stmtIn)
    (h_i := _) (init := init) (impl := impl) (multpoly := multpoly) (𝓑 := 𝓑) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the fold step, with error
`foldKnowledgeError`: the existential form of
`foldOracleVerifier_rbrKnowledgeSoundnessWith`. -/
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).toVerifier.rbrKnowledgeSoundness init impl
      (roundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc)
      (foldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, foldOracleVerifier_rbrKnowledgeSoundnessWith 𝔽q β i⟩

end FoldStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
