/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck.Extraction
public import ArkLib.ToVCVio.Simulation
public import ArkLib.OracleReduction.Completeness

/-!
# Binary Basefold Final Sumcheck Step
-/

@[expose] public section


namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
-- open scoped Binius.BinaryBasefold
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

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

open Classical in
/-! The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    -- Compute the message using the honest transcript from logic
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    -- Construct the transcript from the message and challenges (no challenges in this step)
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Delegate to the logic instance for prover output
    pure ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).proverOut stmtIn witIn oStmtIn t)

/-! The verifier for the final sumcheck step -/
open Classical in
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Get the logic instance
    let logic := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    -- Use guard for verifier check (fails if check doesn't pass)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  outputOracle := .inl {
    embed := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)).embed
    hEq := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)).hEq
    outputInterface_heq := by
      intro _
      rfl }

/-! The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

open Classical in
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The final verifier has no external queries: after routing its sole message query through a
transcript, it is the deterministic guarded logic step. -/
lemma finalSumcheckVerifier_run_eq_guarded
    (stmtIn : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (oStmtIn : ∀ i, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) i)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    Verifier.run (stmtIn, oStmtIn) tr
      (finalSumcheckVerifier 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toVerifier =
      let messageIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨0, by rfl⟩
      let c : L := @OracleInterface.answer _
        (Binius.BinaryBasefold.instFinalSumcheckMessageInterface messageIdx)
        (tr.messages messageIdx) ()
      let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
      let logic := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      if logic.verifierCheck stmtIn t then
        pure (logic.verifierOut stmtIn t,
          (finalSumcheckVerifier 𝔽q β (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).materializeOutput
              tr.challenges oStmtIn tr.messages)
      else failure := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, finalSumcheckVerifier]
  erw [simulateQ_bind]
  erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
  erw [_root_.bind_pure_simulateQ_comp]
  simp only [guard_eq]
  erw [simulateQ_bind]
  erw [simulateQ_ite]
  simp only [OptionT.simulateQ_failure]
  split
  · erw [simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    rfl
  · rfl

/-! Perfect completeness for the final sumcheck step -/
omit [DecidableEq 𝔽q] in
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (hInit : NeverFail init)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFinalSumcheckStep (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  let : ([]ₒ).Inhabited := { inhabitedB := fun t => nomatch t }
  have h_no_challenge : IsEmpty (ChallengeIdx (pSpecFinalSumcheckStep (L := L))) := by
    constructor
    rintro ⟨i, hdir⟩
    have hdir' : (pSpecFinalSumcheckStep (L := L)).dir i = Direction.P_to_V := by
      fin_cases i; simp [pSpecFinalSumcheckStep]
    rw [hdir'] at hdir
    exact absurd hdir (by decide : Direction.P_to_V ≠ Direction.V_to_P)
  let : [(pSpecFinalSumcheckStep (L := L)).Challenge]ₒ.Fintype := {
    fintypeB := fun ⟨i, _⟩ => False.elim (h_no_challenge.false i) }
  let : [(pSpecFinalSumcheckStep (L := L)).Challenge]ₒ.Inhabited := {
    inhabitedB := fun ⟨i, _⟩ => False.elim (h_no_challenge.false i) }
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (oSpec := []ₒ)
    (pSpec := pSpecFinalSumcheckStep (L := L)) (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro x hx_mem_support
  · obtain ⟨sendResult, h_send, hx_mem_support⟩ :=
      OptionT.mem_support_run_lift_bind _ _ hx_mem_support
    rw [show (monadLift : OracleComp ([]ₒ + [pSpecFinalSumcheckStep (L := L).Challenge]ₒ) _ →
        OracleComp ([]ₒ + [pSpecFinalSumcheckStep (L := L).Challenge]ₒ) _) = id from rfl,
      id_eq] at h_send
    have h_send_eq := OracleComp.eq_of_mem_support_pure _ h_send
    subst sendResult
    obtain ⟨proverOutput, h_proverOutput, hx_mem_support⟩ :=
      OptionT.mem_support_run_lift_bind _ _ hx_mem_support
    rw [show (monadLift : OracleComp ([]ₒ + [pSpecFinalSumcheckStep (L := L).Challenge]ₒ) _ →
        OracleComp ([]ₒ + [pSpecFinalSumcheckStep (L := L).Challenge]ₒ) _) = id from rfl,
      id_eq] at h_proverOutput
    have h_proverOutput_eq := OracleComp.eq_of_mem_support_pure _ h_proverOutput
    subst proverOutput
    obtain ⟨h_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun i => False.elim (h_no_challenge.false i))
    set V_check := step.verifierCheck stmtIn (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    have h_V_check : V_check := h_check
    have h_logic_check : (finalSumcheckStepLogic 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).verifierCheck stmtIn
        (FullTranscript.mk1 (witIn.f ⟨0, by simp only [zero_mem]⟩)) := by
      exact h_check
    let messageIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨0, by rfl⟩
    have h_message : @OracleInterface.answer _
        (Binius.BinaryBasefold.instFinalSumcheckMessageInterface messageIdx)
        ((FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L))
          (witIn.f ⟨0, by simp only [zero_mem]⟩)).messages messageIdx) () =
        witIn.f ⟨0, by simp only [zero_mem]⟩ := by
      rfl
    rcases OptionT.mem_support_run_bind _ _ hx_mem_support with
      ⟨h_verifier_none, _⟩ | ⟨verifierResult, h_verifierResult, hx_mem_support⟩
    · change none ∈ _root_.support (liftComp _ _) at h_verifier_none
      rw [OracleComp.support_liftComp] at h_verifier_none
      conv at h_verifier_none =>
        erw [simulateQ_bind]
        erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
        erw [_root_.bind_pure_simulateQ_comp]
        simp only [Matrix.cons_val_zero, guard_eq]
        erw [simulateQ_bind]
        simp only [show OptionT.pure (m := (OracleComp
          ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
            [pSpecFinalSumcheckStep.Message]ₒ)))) = pure by rfl]
        erw [simulateQ_ite]
        simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx,
          toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
          OptionT.simulateQ_failure, _root_.map_pure, support_ite, support_pure]
        erw [_root_.simulateQ_pure]
      rw [h_message] at h_verifier_none
      rw [if_pos h_logic_check] at h_verifier_none
      simp only [pure_bind] at h_verifier_none
      erw [simulateQ_pure] at h_verifier_none
      change none ∈ _root_.support (pure (some _) : OracleComp _ _) at h_verifier_none
      exact absurd (OracleComp.eq_of_mem_support_pure _ h_verifier_none) (by simp)
    · change some verifierResult ∈ _root_.support (liftComp _ _) at h_verifierResult
      rw [OracleComp.support_liftComp] at h_verifierResult
      conv at h_verifierResult =>
        erw [simulateQ_bind]
        erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
        erw [_root_.bind_pure_simulateQ_comp]
        simp only [Matrix.cons_val_zero, guard_eq]
        erw [simulateQ_bind]
        simp only [show OptionT.pure (m := (OracleComp
          ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
            [pSpecFinalSumcheckStep.Message]ₒ)))) = pure by rfl]
        erw [simulateQ_ite]
        simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx,
          toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
          OptionT.simulateQ_failure, _root_.map_pure, support_ite, support_pure]
        erw [_root_.simulateQ_pure]
      rw [h_message] at h_verifierResult
      rw [if_pos h_logic_check] at h_verifierResult
      simp only [pure_bind] at h_verifierResult
      erw [simulateQ_pure] at h_verifierResult
      change some verifierResult ∈ _root_.support (pure (some _) : OracleComp _ _)
        at h_verifierResult
      have h_verifierResult_eq := OracleComp.eq_of_mem_support_pure _ h_verifierResult
      rw [Option.some.injEq] at h_verifierResult_eq
      subst verifierResult
      have hx_eq := OracleComp.eq_of_mem_support_pure _ hx_mem_support
      subst x
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · exact h_rel
      · exact h_agree.1
      · exact h_agree.2

/-! RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0


def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
 | ⟨1, _⟩ => Unit

/-! The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ)) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl -- witMidSucc is of type Unit
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle 𝔽q β oStmtMid
    let polyOpt := extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ⟩) (f := f0)
    have h_C_mem : MvPolynomial.C stmtMid.sumcheck_target ∈
        L⦃≤ 2⦄[X Fin (ℓ - ↑(Fin.last ℓ))] := by
      rw [mem_restrictDegree_iff_degreeOf_le]
      intro n
      exact le_trans (by rw [MvPolynomial.degreeOf_C]) (Nat.zero_le _)
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ - ↑(Fin.last ℓ))] :=
      ⟨MvPolynomial.C stmtMid.sumcheck_target, h_C_mem⟩
    match polyOpt with
    | none =>
      -- Extraction failed - use constant H to satisfy sumcheckConsistencyProp trivially
      exact {
        t := ⟨0, by apply zero_mem⟩,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      -- Build H_ℓ from t and challenges r'
      exact {
        t := tpoly,
        -- projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := tpoly)
          -- (m := BBF_SumcheckMultiplierParam.multpoly stmtMid.ctx)
          -- (i := Fin.last ℓ) (challenges := stmtMid.challenges),
        H := H_constant,
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) -- (𝓑 := 𝓑)
      (mp := BBF_SumcheckMultiplierParam)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    let sumcheckFinalCheck : Prop := stmtIn.sumcheck_target
      = eqTilde (stmtIn.ctx.t_eval_point) stmtIn.challenges * c
    let finalFoldingProp := finalSumcheckStepFoldingStateProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ
        · exact hdiv.out) (input := ⟨stmtOut, oStmtIn⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-! The knowledge state function for the final sumcheck step -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) )
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    finalSumcheckKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (tr := tr) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- toFun_next is impacted by how we build extractMid
    -- For pSpecCommit, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- declare c and stmtOut as in KState (m=1), as well as in honest verifier
    -- For the final sumcheck step, there is a single P→V message carrying the final constant,
    -- so we can read it directly from `msg` without reconstructing a truncated transcript.
    let c : L := msg
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    intro h_kState_round1
    unfold finalSumcheckKStateProp finalSumcheckStepFoldingStateProp
      masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    -- At m=1 we have local final-check and (oracle-consistency ∨ block-bad-event).
    -- At m=0 the target is Option-B masterKState:
    -- incremental-bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    obtain ⟨h_V_check, h_core⟩ := h_kState_round1
    -- Case split on the m=1 final-folding state: consistency or block bad-event.
    cases h_core with
    | inl hConsistent =>
      -- When we have finalSumcheckStepOracleConsistencyProp, extractMLP must succeed.
      have ⟨tpoly, h_extractMLP⟩ := extractMLP_some_of_oracleFoldingConsistency 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) (h_oracle_consistency := hConsistent)
      refine Or.inr ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local check at m=0
        unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod]
        symm
        calc ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ), (MvPolynomial.eval x)
                (MvPolynomial.C stmtIn.sumcheck_target)
            = ∑ _x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ), stmtIn.sumcheck_target :=
              Finset.sum_congr rfl (fun x _ => MvPolynomial.eval_C (f := x) stmtIn.sumcheck_target)
          _ = stmtIn.sumcheck_target := by
              simp only [Finset.sum_const, Fintype.card_piFinset, Finset.card_map,
                Finset.card_univ, Fintype.card_fin, Finset.prod_const, tsub_self, pow_zero,
                one_smul]
      · -- witnessStructuralInvariant
        unfold finalSumcheckRbrExtractor witnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [projectToMidSumcheckPoly_at_last_eq]
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            (BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          rw [h_V_check]
          congr 1
          change c = tpoly.val.eval stmtIn.challenges
          exact extracted_t_poly_eval_eq_final_constant 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly)
            (h_extractMLP := h_extractMLP) (h_finalSumcheckStepOracleConsistency := hConsistent)
        simp only
          [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
      · -- firstOracleWitnessConsistencyProp
        dsimp only [finalSumcheckRbrExtractor, firstOracleWitnessConsistencyProp]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle 𝔽q β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- Hybrid plan: map terminal block bad-event to incremental bad-event at m=0.
      exact Or.inl (
        (badEventExistsProp_iff_incrementalBadEventExistsProp_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
  -- Same pattern as relay: verifier output (stmtOut, oStmtOut) + h_relOut ⇒ commitKStateProp 1
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    rw [finalSumcheckVerifier_run_eq_guarded] at h_output_mem_V_run_support
    rw [OptionT.mem_support_iff] at h_output_mem_V_run_support
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion, exists_prop]
      at h_output_mem_V_run_support
    rcases h_output_mem_V_run_support with ⟨s, hs_init, h_output_mem_V_run_support⟩
    let messageIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨0, by rfl⟩
    let c : L := @OracleInterface.answer _
      (Binius.BinaryBasefold.instFinalSumcheckMessageInterface messageIdx)
      (tr.messages messageIdx) ()
    by_cases h_V_check : (finalSumcheckStepLogic 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).verifierCheck stmtIn
        (FullTranscript.mk1 c)
    · rw [if_pos h_V_check] at h_output_mem_V_run_support
      change some (stmtOut, oStmtOut) ∈ _root_.support
        ((simulateQ impl (pure (some _) : OracleComp []ₒ (Option _))).run' s)
        at h_output_mem_V_run_support
      rw [simulateQ_pure] at h_output_mem_V_run_support
      change some (stmtOut, oStmtOut) ∈ _root_.support
        (Prod.fst <$> (pure (some _) : StateT σ ProbComp _).run s)
        at h_output_mem_V_run_support
      rw [StateT.run_pure] at h_output_mem_V_run_support
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq]
        at h_output_mem_V_run_support
      have h_stmtOut_eq := congrArg Prod.fst h_output_mem_V_run_support
      have h_oStmtOut_eq := congrArg Prod.snd h_output_mem_V_run_support
      simp only [Fin.reduceLast, Fin.isValue]
      simp only [finalSumcheckRelOut, finalSumcheckRelOutProp, Set.mem_ofPred_eq] at h_relOut
      unfold finalSumcheckKStateProp
      dsimp only
      change stmtOut = _ at h_stmtOut_eq
      rw [h_stmtOut_eq] at h_relOut
      change oStmtOut = _ at h_oStmtOut_eq
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
      constructor
      · exact h_V_check
      · rw [h_oStmtOut_eq_oStmtIn] at h_relOut
        exact h_relOut
    · rw [if_neg h_V_check] at h_output_mem_V_run_support
      change some (stmtOut, oStmtOut) ∈ _root_.support
        ((simulateQ impl (pure none : OracleComp []ₒ (Option _))).run' s)
        at h_output_mem_V_run_support
      rw [simulateQ_pure] at h_output_mem_V_run_support
      change some (stmtOut, oStmtOut) ∈ _root_.support
        (Prod.fst <$> (pure none : StateT σ ProbComp _).run s)
        at h_output_mem_V_run_support
      rw [StateT.run_pure] at h_output_mem_V_run_support
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq]
        at h_output_mem_V_run_support

omit [Fintype L] [CharP L 2] in
/-! Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑)
        (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) )
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
      (rbrKnowledgeError := finalSumcheckKnowledgeError) := by
  use FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
  use finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckKnowledgeStateFunction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) init impl
  intro stmtIn witIn prover ⟨j, hj⟩
  -- pSpecFinalSumcheckStep has 1 message (ChallengeIdx = Fin 1); same pattern as commit
  cases j using Fin.cases with
  | zero => simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
    Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
    -- bound for challenge index 0 (P→V only, no V challenge)
  | succ j' => exact Fin.elim0 j'

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
