/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase.SumcheckFold

/-!
# FRI-Binius final sumcheck and core composition

The sumcheck-fold adapters and their security proofs are re-exported from `SumcheckFold`.
This module checks the final tensor equality and composes the full interaction phase.
-/

@[expose] public section

-- The inferred composed protocol types contain public inline bounds proofs.
set_option backward.proofsInPublic true

namespace Binius.FRIBinius.CoreInteractionPhase
noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold _root_.RingSwitching
open scoped NNReal

-- TODO: how to make params cleaner while can explicitly reuse across sections?
variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable [hdiv : Fact (ϑ ∣ ℓ')]

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckVerifierCheck
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (c : L) : Prop :=
  let eq_tilde_eval : L := RingSwitching.compute_final_eq_value κ L K
    (biniusProfile κ L K β) ℓ ℓ' h_l
    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  stmtIn.sumcheck_target = eq_tilde_eval * c

/-- Pure verifier output for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckVerifierStmtOut
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (c : L) : BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ') := {
      ctx := {
        t_eval_point := getEvaluationPointSuffix κ L ℓ ℓ' h_l stmtIn.ctx.t_eval_point
        original_claim := stmtIn.ctx.original_claim
      }
      sumcheck_target := stmtIn.sumcheck_target
      challenges := stmtIn.challenges
      final_constant := c
    }

/-- Pure prover message computation for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckProverComputeMsg
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')) : L :=
  witIn.f ⟨0, by simp only [zero_mem]⟩

/-- Pure prover output witness for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckProverWitOut : Unit := ()

/-! ## ReductionLogicStep Instance -/

/-- The logic instance for the FRI final sumcheck step. -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
      (BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      Unit
      (BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ BinaryBasefold.strictRoundRelation
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ')
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ BinaryBasefold.strictFinalSumcheckRelOut K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl
  honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
    FullTranscript.mk1 c
  proverOut := fun stmtIn _witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn c
    ((stmtOut, oStmtIn), ())

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ') ×
      (∀ j, BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  verify := fun stmtIn _ => do
    let s' : L ← query (spec := [(BinaryBasefold.pSpecFinalSumcheckStep
      (L:=L)).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    -- 8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    -- decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
    -- Then `V` computes the final eq value: `(Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1},`
      -- `r''_0, ..., r''_{κ-1}) ⋅ e_u)`
    let eq_tilde_eval : L := RingSwitching.compute_final_eq_value κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
    -- 9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1},`
      -- `r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
    guard (stmtIn.sumcheck_target = eq_tilde_eval * s')
    -- Return the final sumcheck statement with the constant
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      ctx := {
        t_eval_point := getEvaluationPointSuffix κ L ℓ ℓ' h_l stmtIn.ctx.t_eval_point,
        original_claim := stmtIn.ctx.original_claim,
      },
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := s',
    }
    pure stmtOut

  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun _ => rfl
    outputInterface_heq := by
      intro oracleIdx
      rfl }

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  prover := finalSumcheckProver κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
  verifier := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l

omit [SampleableType L] h_β₀_eq_1 in
open Classical in
/-- Routing the sole message query yields the exact final equality guard. In particular,
a failed check produces failure, not an ordinary dummy output statement. -/
lemma finalSumcheckVerifier_run_eq_guarded
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (oStmtIn : ∀ i, OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') i)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    Verifier.run (stmtIn, oStmtIn) tr
      (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).toVerifier =
      let messageIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨0, by rfl⟩
      let c : L := @OracleInterface.answer _
        (Binius.BinaryBasefold.instFinalSumcheckMessageInterface messageIdx)
        (tr.messages messageIdx) ()
      let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
      let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      if logic.verifierCheck stmtIn t then
        pure (logic.verifierOut stmtIn t,
          (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).materializeOutput
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
  dsimp only [finalSumcheckStepLogic, finalSumcheckVerifierCheck, finalSumcheckVerifierStmtOut]
  split
  · rename_i h_check
    erw [ite_eq_left h_check]
    erw [simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    simp only [_root_.map_pure]
    rfl
  · rename_i h_check
    erw [ite_eq_right h_check]
    rfl

omit [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] [NeZero ℓ'] in
/-- At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - Fin.last ℓ')])
    (h_cons : BinaryBasefold.sumcheckConsistencyProp (𝓑 := boolEmbedding L) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [BinaryBasefold.sumcheckConsistencyProp] at h_cons
  have : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso
      apply hb_ne
      funext i
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso
      apply h_not_mem
      simp only [Fintype.mem_piFinset]
      intro i
      simp only [tsub_self] at i
      exact i.elim0)] at h_cons
  exact h_cons

omit [SampleableType L] in
/-- The final codeword value at `0` equals `t(challenges)`. -/
lemma finalCodeword_zero_eq_t_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (h_wit_struct : BinaryBasefold.witnessStructuralInvariant K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmt := stmtIn) (wit := witIn)) :
    witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
  have h_f_eq_getMidCodewords_t :
      witIn.f = BinaryBasefold.getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := Fin.last ℓ') witIn.t stmtIn.challenges := h_wit_struct.2
  dsimp only [BinaryBasefold.getMidCodewords, Fin.coe_ofNat_eq_mod] at h_f_eq_getMidCodewords_t
  rw [congr_fun h_f_eq_getMidCodewords_t ⟨0, by simp only [zero_mem]⟩]
  let h_eval := BinaryBasefold.iterated_fold_to_level_ℓ_eval K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := witIn.t)
    (destIdx := ⟨Fin.last ℓ', by
      simp only [Fin.val_last]
      omega⟩)
    (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
  exact congr_fun h_eval ⟨0, by simp only [Fin.val_last, zero_mem]⟩

omit [SampleableType L] in
/-- Strict helper: folding the last oracle block in the final sumcheck step yields
the constant function equal to the prover message `witIn.f(0)`. -/
lemma iterated_fold_to_const_strict
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (h_strictOracleWitConsistency_In : BinaryBasefold.strictOracleWitnessConsistency K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Context := RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β))
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmtIdx := Fin.last ℓ')
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ'))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    let lastDomainIdx := getLastOracleDomainIndex ℓ' ϑ (Fin.last ℓ')
    let k := lastDomainIdx.val
    have h_k : k = ℓ' - ϑ := by
      dsimp only [k, lastDomainIdx]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
        Nat.div_mul_cancel (hdiv.out)]
    let curDomainIdx : Fin (2 ^ κ) := ⟨k, by
      rw [h_k]
      omega
    ⟩
    have h_destIdx_eq : curDomainIdx.val = lastDomainIdx.val := rfl
    let f_k : OracleFunction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
      getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ')
        K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
    let finalChallenges : Fin ϑ → L := fun cId => stmtIn.challenges ⟨k + cId, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ' := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ').val = ℓ' := by simp only [Fin.val_last]
      omega
    ⟩
    let destDomainIdx : Fin (2 ^ κ) := ⟨k + ϑ, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ' := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
      omega
    ⟩
    let folded := iterated_fold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (steps := ϑ) (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by
        dsimp only [destDomainIdx, k, lastDomainIdx]
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      ) (f := f_k)
      (r_challenges := finalChallenges)
    ∀ y, folded y = c := by
  have h_ϑ_le_ℓ' : ϑ ≤ ℓ' := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
  intro c lastDomainIdx k h_k curDomainIdx h_destIdx_eq f_k finalChallenges destDomainIdx folded
  let P₀ : L[X]_(2 ^ ℓ') := polynomialFromNovelCoeffsF₂ K β ℓ' (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_wit_struct := h_strictOracleWitConsistency_In.1
  have h_strict_oracle_folding := h_strictOracleWitConsistency_In.2
  dsimp only [Fin.val_last, OracleFrontierIndex.val_mkFromStmtIdx,
    strictOracleFoldingConsistencyProp] at h_strict_oracle_folding
  have h_eq : folded = fun x => c := by
    dsimp only [folded, f_k]
    have h_f_last_consistency := h_strict_oracle_folding
      (j := (getLastOraclePositionIndex ℓ' ϑ (Fin.last ℓ')))
    have h_wit_f_eq : witIn.f = getMidCodewords K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t stmtIn.challenges := h_wit_struct.2
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    dsimp only [c]
    conv_rhs =>
      rw [h_wit_f_eq]
      simp only [Fin.val_last]
    have h_curDomainIdx_eq : curDomainIdx = ⟨ℓ' - ϑ, by omega⟩ := by
      dsimp [curDomainIdx, k, lastDomainIdx]
      simp only [Fin.mk.injEq]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.div_mul_cancel (hdiv.out)]
      simp only [one_mul]
    let res := iterated_fold_congr_source_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (i' := ⟨ℓ' - ϑ, by omega⟩) (h := h_curDomainIdx_eq) (steps := ϑ)
      (destIdx := destDomainIdx)
      (h_destIdx := by rfl) (h_destIdx' := by simp only [destDomainIdx, h_k])
      (h_destIdx_le := by
        dsimp only [destDomainIdx]
        rw [h_k]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      ) (f := (getLastOracle K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx_eq oStmtIn))
      (r_challenges := finalChallenges)
    rw [res]
    dsimp only [getLastOracle, finalChallenges]
    rw [h_f_last_consistency]
    simp only [Fin.take_eq_self]
    let k_pos_idx := getLastOraclePositionIndex ℓ' ϑ (Fin.last ℓ')
    let k_steps := k_pos_idx.val * ϑ
    have h_k_steps_eq : k_steps = k := by
      dsimp only [k_steps, k_pos_idx, k, lastDomainIdx]
    have h_cast_elim := iterated_fold_congr_dest_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps) (destIdx := curDomainIdx) (destIdx' := ⟨k_steps, by
        rw [h_k_steps_eq]
        exact curDomainIdx.isLt⟩)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
        exact h_k_steps_eq.symm)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]
        simp only [h_k, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      ) (h_destIdx_eq_destIdx' := by rfl)
      (f := f₀)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (Fin.last ℓ')
        stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    have h_cast_elim2 := iterated_fold_congr_dest_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps) (destIdx := ⟨ℓ' - ϑ, by omega⟩) (destIdx' := curDomainIdx)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
        rw [h_k_steps_eq, h_k])
      (h_destIdx_le := by
        dsimp only [curDomainIdx]
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      )
      (h_destIdx_eq_destIdx' := by
        dsimp only [curDomainIdx]
        simp only [Fin.mk.injEq]; omega
      )
      (f := f₀)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (Fin.last ℓ')
        stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim2
    conv_lhs =>
      simp only [← h_cast_elim]
      simp only [← h_cast_elim2]
      simp only [← fun_eta_expansion]
    have h_transitivity := iterated_fold_transitivity K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (midIdx := ⟨ℓ' - ϑ, by omega⟩) (destIdx := destDomainIdx)
      (steps₁ := k_steps) (steps₂ := ϑ)
      (h_midIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, h_k_steps_eq, h_k, zero_add]
      )
      (h_destIdx := by
        dsimp only [destDomainIdx, k_steps, k_pos_idx]
        rw [h_k]
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff]
        rw [getLastOraclePositionIndex_last]
        simp only
        rw [Nat.sub_mul, Nat.div_mul_cancel (hdiv.out)]
        simp only [one_mul]
      )
      (h_destIdx_le := by
        dsimp only [destDomainIdx]
        rw [h_k]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      )
      (f := f₀)
      (r_challenges₁ := getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (Fin.last ℓ')
        stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
      (r_challenges₂ := finalChallenges)
    have h_finalChallenges_eq : finalChallenges = fun cId : Fin ϑ => stmtIn.challenges
      ⟨k + cId.val, by
        rw [h_k]
        have h_le : ϑ ≤ ℓ' := by
          apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
        have h_cId : cId.val < ϑ := cId.isLt
        have h_last : (Fin.last ℓ').val = ℓ' := by simp only [Fin.val_last]
        omega
      ⟩ := by
      rfl
    rw [h_finalChallenges_eq] at h_transitivity
    rw [h_transitivity]
    have h_steps_eq : k_steps + ϑ = ℓ' := by
      dsimp only [k_steps, k_pos_idx, h_k_steps_eq, h_k]
      rw [getLastOraclePositionIndex_last]
      simp only [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
      rw [Nat.sub_add_cancel (by
        exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
    have h_concat_challenges_eq :
        Fin.append
          (getFoldingChallenges (𝓡 := 𝓡) (r := 2 ^ κ) (ϑ := k_steps)
            (Fin.last ℓ') stmtIn.challenges 0
            (by simp only [zero_add, Fin.val_last]; omega))
          finalChallenges =
        fun (cIdx : Fin (k_steps + ϑ)) => stmtIn.challenges ⟨cIdx, by
          simp only [Fin.val_last]
          omega
        ⟩ := by
      funext cId
      dsimp only [getFoldingChallenges, finalChallenges]
      by_cases h : cId.val < k_steps
      · simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.val_castLT, zero_add]
      · simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp only [h, ↓reduceDIte, Fin.val_subNat, Fin.val_cast, eq_rec_constant]
        congr 1
        simp only [Fin.val_last, Fin.mk.injEq]
        rw [add_comm, ←h_k_steps_eq]
        omega
    dsimp only [finalChallenges] at h_concat_challenges_eq
    simp only [h_concat_challenges_eq]
    funext y
    have h_cast_elim3 := iterated_fold_congr_dest_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps + ϑ) (destIdx := destDomainIdx)
      (destIdx' := ⟨Fin.last ℓ', by
        simp only [Fin.val_last]
        omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega)
      (h_destIdx_eq_destIdx' := by
        dsimp only [destDomainIdx]
        simp only [Fin.val_last, Fin.mk.injEq]
        omega
      )
      (f := f₀)
      (r_challenges := fun (cIdx : Fin (k_steps + ϑ)) => stmtIn.challenges ⟨cIdx, by
        simp only [Fin.val_last]
        omega
      ⟩)
    rw [h_cast_elim3]
    have h_cast_elim4 := iterated_fold_congr_steps_index K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := ℓ') (steps' := k_steps + ϑ)
      (destIdx := ⟨Fin.last ℓ', by
        simp only [Fin.val_last]
        omega⟩)
      (h_steps_eq_steps' := by simp only [h_steps_eq])
      (h_destIdx := by
        dsimp only [destDomainIdx]
        simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
      )
      (h_destIdx_le := by simp only [Fin.val_last, le_refl])
      (f := f₀) (r_challenges := stmtIn.challenges)
    erw [←h_cast_elim4]
    set f_last := iterated_fold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ℓ'
      (destIdx := ⟨Fin.last ℓ', by
        simp only [Fin.val_last]
        omega⟩)
      (h_destIdx := by
        simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
      )
      (h_destIdx_le := by simp only [Fin.val_last, le_refl]) (f := f₀)
      (r_challenges := stmtIn.challenges)
    have h_eval_eq : ∀ x, f_last x = f_last ⟨0, by simp only [zero_mem]⟩ := by
      intro x
      apply iterated_fold_to_level_ℓ_is_constant K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t := witIn.t) (destIdx := ⟨Fin.last ℓ', by
          simp only [Fin.val_last]
          omega⟩)
        (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
        (x := x) (y := 0)
    rw [h_eval_eq]
    rfl
  rw [h_eq]
  intro y
  rfl

omit [SampleableType L] h_β₀_eq_1 in
/-- Honest prover message in final sumcheck equals `witIn.f(0)`. -/
lemma finalSumcheck_honest_message_eq_f_zero
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (challenges : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).Challenges) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ := by
  simp only [finalSumcheckStepLogic, finalSumcheckProverComputeMsg]

omit [SampleableType L] in
/-- Verifier check passes in the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (challenges : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : BinaryBasefold.sumcheckConsistencyProp
      (𝓑 := boolEmbedding L) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : BinaryBasefold.witnessStructuralInvariant K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmt := stmtIn) (wit := witIn)) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  intro step transcript
  have h_target_eq_H_eval :
      stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => (0 : L)) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ' := ℓ')
      stmtIn.sumcheck_target witIn.H h_sumcheck_cons
  have h_proj_eval :
      (BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t)
        (m := (RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx)
        (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => (0 : L)) =
      ((RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := by
    apply BinaryBasefold.projectToMidSumcheckPoly_at_last_eval
  have h_mult_eq_eq_value :
      ((RingSwitching_BBFSumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges =
      RingSwitching.compute_final_eq_value κ L K
        (biniusProfile κ L K β) ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
    RingSwitching.compute_A_MLE_eval_eq_final_eq_value_tensor κ L K
      (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  have h_c_eq : witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
    exact finalCodeword_zero_eq_t_eval (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      stmtIn witIn h_wit_struct
  let cmsg : L := transcript.messages ⟨0, rfl⟩
  have h_msg_eq : cmsg = witIn.f ⟨0, by simp only [zero_mem]⟩ :=
    finalSumcheck_honest_message_eq_f_zero (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
       stmtIn witIn oStmtIn challenges
  have h_eq : stmtIn.sumcheck_target = RingSwitching.compute_final_eq_value κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
      cmsg := by
    calc
      stmtIn.sumcheck_target
          = witIn.H.val.eval (fun _ => (0 : L)) := h_target_eq_H_eval
      _ = (BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t)
            (m := (RingSwitching_BBFSumcheckMultParam κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx)
            (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => (0 : L)) := by
            rw [h_wit_struct.1]
      _ = ((RingSwitching_BBFSumcheckMultParam κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
            stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := h_proj_eval
      _ = RingSwitching.compute_final_eq_value κ L K
            (biniusProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            witIn.t.val.eval stmtIn.challenges := by
            rw [h_mult_eq_eq_value]
      _ = RingSwitching.compute_final_eq_value κ L K
            (biniusProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            witIn.f ⟨0, by simp only [zero_mem]⟩ := by
            rw [h_c_eq]
      _ = RingSwitching.compute_final_eq_value κ L K
            (biniusProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            cmsg := by
            rw [←h_msg_eq]
  dsimp [step, finalSumcheckStepLogic, finalSumcheckVerifierCheck, cmsg] at h_eq ⊢
  exact h_eq

omit [SampleableType L] in
/-- Strong completeness of the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      ).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  simp only [finalSumcheckStepLogic, BinaryBasefold.strictRoundRelation,
    BinaryBasefold.strictRoundRelationProp] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOracleWitConsistency⟩ := h_relIn
  have h_wit_struct := h_strictOracleWitConsistency.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript :=
    finalSumcheckStep_verifierCheck_passed (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) stmtIn witIn oStmtIn challenges h_sumcheck_cons h_wit_struct
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierStmtOut]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, finalSumcheckStepLogic]
    refine ⟨witIn.t, ?_⟩
    unfold BinaryBasefold.strictfinalSumcheckStepFoldingStateProp
    dsimp only [finalSumcheckVerifierStmtOut]
    constructor
    · exact h_strictOracleWitConsistency.2
    · funext y
      have h_const := iterated_fold_to_const_strict (κ := κ) (L := L) (K := K) (β := β)
        (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (h_l := h_l) (stmtIn := stmtIn) (witIn := witIn) (oStmtIn := oStmtIn)
        (h_strictOracleWitConsistency_In := h_strictOracleWitConsistency) y
      have h_msg_eq : transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ :=
        finalSumcheck_honest_message_eq_f_zero (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
           stmtIn witIn oStmtIn challenges
      dsimp [verifierStmtOut, verifierOStmtOut, transcript, step, finalSumcheckStepLogic,
        finalSumcheckVerifierStmtOut] at h_const ⊢
      dsimp [transcript, step, finalSumcheckStepLogic] at h_msg_eq
      rw [h_msg_eq]
      exact h_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (relIn := BinaryBasefold.strictRoundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := boolEmbedding L) (Fin.last ℓ'))
    (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init) (impl := impl) := by
  have h_no_challenge : IsEmpty (ChallengeIdx (pSpecFinalSumcheckStep (L := L))) := by
    constructor
    rintro ⟨i, hdir⟩
    have hdir' : (pSpecFinalSumcheckStep (L := L)).dir i = Direction.P_to_V := by
      fin_cases i
      simp [pSpecFinalSumcheckStep]
    rw [hdir'] at hdir
    exact absurd hdir (by decide : Direction.P_to_V ≠ Direction.V_to_P)
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V
    (oSpec := []ₒ) (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L))
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
  apply OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support
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
    have h_logic_check :
        (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).verifierCheck stmtIn
        (FullTranscript.mk1 (witIn.f ⟨0, by simp only [zero_mem]⟩)) := by
      exact h_check
    let messageIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨0, by rfl⟩
    have h_message : @OracleInterface.answer _
        (Binius.BinaryBasefold.instFinalSumcheckMessageInterface messageIdx)
        ((FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L))
          (witIn.f ⟨0, by simp only [zero_mem]⟩)).messages messageIdx) () =
        witIn.f ⟨0, by simp only [zero_mem]⟩ := by
      rfl
    dsimp only [finalSumcheckStepLogic, finalSumcheckVerifierCheck,
      finalSumcheckProverComputeMsg, FullTranscript.mk1, FullTranscript.messages] at h_logic_check
    rcases OptionT.mem_support_run_bind _ _ hx_mem_support with
      ⟨h_verifier_none, _⟩ | ⟨verifierResult, h_verifierResult, hx_mem_support⟩
    · change none ∈ MonadAttach.support (liftComp _ _) at h_verifier_none
      rw [OracleComp.support_liftComp] at h_verifier_none
      conv at h_verifier_none =>
        erw [simulateQ_bind]
        erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
        erw [_root_.bind_pure_simulateQ_comp]
        simp only [Matrix.cons_val_zero, guard_eq]
        erw [simulateQ_bind]
        simp only [show OptionT.pure (m := (OracleComp
          ([]ₒ + ([OracleStatement K β ϑ (Fin.last ℓ')]ₒ +
            [pSpecFinalSumcheckStep.Message]ₒ)))) = pure by rfl]
        erw [simulateQ_ite]
        simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx,
          toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
          OptionT.simulateQ_failure, _root_.map_pure, support_ite, support_pure]
        erw [_root_.simulateQ_pure]
      rw [h_message] at h_verifier_none
      rw [ite_eq_left h_logic_check] at h_verifier_none
      simp only [pure_bind] at h_verifier_none
      erw [simulateQ_pure] at h_verifier_none
      change none ∈ MonadAttach.support (pure (some _) : OracleComp _ _) at h_verifier_none
      exact absurd (OracleComp.eq_of_mem_support_pure _ h_verifier_none) (by simp)
    · change some verifierResult ∈ MonadAttach.support (liftComp _ _) at h_verifierResult
      rw [OracleComp.support_liftComp] at h_verifierResult
      conv at h_verifierResult =>
        erw [simulateQ_bind]
        erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
        erw [_root_.bind_pure_simulateQ_comp]
        simp only [Matrix.cons_val_zero, guard_eq]
        erw [simulateQ_bind]
        simp only [show OptionT.pure (m := (OracleComp
          ([]ₒ + ([OracleStatement K β ϑ (Fin.last ℓ')]ₒ +
            [pSpecFinalSumcheckStep.Message]ₒ)))) = pure by rfl]
        erw [simulateQ_ite]
        simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx,
          toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
          OptionT.simulateQ_failure, _root_.map_pure, support_ite, support_pure]
        erw [_root_.simulateQ_pure]
      rw [h_message] at h_verifierResult
      rw [ite_eq_left h_logic_check] at h_verifierResult
      simp only [pure_bind] at h_verifierResult
      erw [simulateQ_pure] at h_verifierResult
      change some verifierResult ∈ MonadAttach.support (pure (some _) : OracleComp _ _)
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

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ') ×
      (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (WitMid := FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle K β oStmtMid
    let polyOpt := extractMLP K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ'⟩) (f := f0)
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ' - ↑(Fin.last ℓ'))] := ⟨MvPolynomial.C stmtMid.sumcheck_target,
      by
        rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
        intro i
        simp only [MvPolynomial.degreeOf_C, zero_le]⟩
    match polyOpt with
    | none =>
      exact {
        t := ⟨0, by apply zero_mem⟩,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      exact {
        t := tpoly,
        H := H_constant,
        f := getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

def finalSumcheckKStateProp {m : Fin (1 + 1)}
    (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmt : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (witMid : FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate) m)
    (oStmt : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    BinaryBasefold.masterKStateProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
      (stmtIdx := Fin.last ℓ') (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ'))
      (stmt := stmt) (wit := witMid) (oStmt := oStmt)
      (localChecks := sumcheckConsistencyProp (𝓑 := boolEmbedding L) stmt.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheckStep (L := L)).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let s' : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheckStep (L := L)) tr).1 i_msg0
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      -- **Dummy UNUSED values**
      ctx := {
        t_eval_point := 0,
        original_claim := 0
      },
      sumcheck_target := 0,
      -- **ONLY the last two fields are used in finalSumcheckStepFoldingStateProp**
      challenges := stmt.challenges,
      final_constant := s'
    }
    let sumcheckFinalCheck : Prop := stmt.sumcheck_target = compute_final_eq_value κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching * s'
    let finalFoldingProp := finalSumcheckStepFoldingStateProp K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ'
        · exact hdiv.out) (input := ⟨stmtOut, oStmt⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

-- At the last frontier, the transcript's take-spec reduces to the full protocol specification.
set_option backward.isDefEq.respectTransparency false in
/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate h_l).KnowledgeStateFunction init impl
    (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (𝓑 := boolEmbedding L)
       (mp := RingSwitching_BBFSumcheckMultParam κ L K
        (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
    (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- In the single-message final sumcheck step, the new message `msg` *is* the final constant.
    -- We use it directly rather than reconstructing a truncated transcript.
    let s' : L := msg
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      ctx := {
        t_eval_point := 0,
        original_claim := 0
      },
      sumcheck_target := 0,
      challenges := stmtIn.challenges,
      final_constant := s'
    }
    intro h_kState_round1
    unfold finalSumcheckKStateProp BinaryBasefold.finalSumcheckStepFoldingStateProp
      BinaryBasefold.masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue] at h_kState_round1
    obtain ⟨h_sumcheckFinalCheck, h_core⟩ := h_kState_round1
    -- Option-B shape at m=0:
    -- incremental bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    cases h_core with
    | inl hConsistent =>
      have ⟨tpoly, h_extractMLP⟩ :=
        BinaryBasefold.CoreInteraction.extractMLP_some_of_oracleFoldingConsistency K β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtIn hConsistent
      refine Or.inr ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local sumcheck consistency at m=0
        unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', Fin.coe_ofNat_eq_mod]
        simp only [h_extractMLP]
        symm
        refine (Finset.sum_congr rfl fun x _ =>
          MvPolynomial.eval_C (f := x) stmtIn.sumcheck_target).trans ?_
        simp only [Finset.sum_const, Fintype.card_piFinset,
          card_map, card_univ, Fintype.card_fin, prod_const, tsub_self, pow_zero, one_smul]
      · -- witnessStructuralInvariant for extracted witness
        unfold finalSumcheckRbrExtractor BinaryBasefold.witnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [BinaryBasefold.projectToMidSumcheckPoly_at_last_eq
          (ℓ := ℓ') (t := tpoly) (challenges := stmtIn.challenges)]
        have h_s'_eq : s' = tpoly.val.eval stmtIn.challenges := by
          exact BinaryBasefold.CoreInteraction.extracted_t_poly_eval_eq_final_constant K β
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly) (h_extractMLP := h_extractMLP)
            (h_finalSumcheckStepOracleConsistency := hConsistent)
        have h_mult_eq : (MvPolynomial.eval stmtIn.challenges
          ((RingSwitching_BBFSumcheckMultParam κ L K
            (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) =
          compute_final_eq_value κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
          compute_A_MLE_eval_eq_final_eq_value_tensor κ L K (booleanHypercubeBasis κ L K β)
            ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            ((RingSwitching_BBFSumcheckMultParam κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          calc
            stmtIn.sumcheck_target
                = compute_final_eq_value κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
                    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching * s' :=
                  h_sumcheckFinalCheck
            _ = compute_final_eq_value κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
                  stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
                  (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
                    rw [h_s'_eq]
            _ = (MvPolynomial.eval stmtIn.challenges
                  ((RingSwitching_BBFSumcheckMultParam κ L K
                    (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
                  (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
                    rw [h_mult_eq]
        exact congrArg MvPolynomial.C h_sumcheck_target_eq
      · -- initial compatibility via first-oracle consistency
        dsimp only [finalSumcheckRbrExtractor, BinaryBasefold.firstOracleWitnessConsistencyProp]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMLP_eq_some_iff_pair_UDRClose K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle K β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- Convert terminal block bad-event to incremental bad-event.
      exact Or.inl (
        (BinaryBasefold.badEventExistsProp_iff_incrementalBadEventExistsProp_last K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    simp only [StateT.run'_eq, gt_iff_lt, OptionT.prEvent_mk_pos_iff, Prod.exists]
      at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output, h_relOut⟩
    rw [finalSumcheckVerifier_run_eq_guarded] at h_output
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output
    rcases h_output with ⟨s, _hs_init, h_output⟩
    let messageIdx : (pSpecFinalSumcheckStep (L := L)).MessageIdx := ⟨0, by rfl⟩
    let c : L := @OracleInterface.answer _
      (Binius.BinaryBasefold.instFinalSumcheckMessageInterface messageIdx)
      (tr.messages messageIdx) ()
    by_cases h_check : (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).verifierCheck
        stmtIn (FullTranscript.mk1 c)
    · rw [ite_eq_left h_check] at h_output
      change some (stmtOut, oStmtOut) ∈ MonadAttach.support
        ((simulateQ impl (pure (some _) : OracleComp []ₒ (Option _))).run' s) at h_output
      rw [simulateQ_pure] at h_output
      change some (stmtOut, oStmtOut) ∈ MonadAttach.support
        (Prod.fst <$> (pure (some _) : StateT σ ProbComp _).run s) at h_output
      rw [StateT.run_pure] at h_output
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at h_output
      have h_stmtOut_eq := congrArg Prod.fst h_output
      have h_oStmtOut_eq := congrArg Prod.snd h_output
      simp only [Fin.reduceLast, Fin.isValue]
      simp only [finalSumcheckRelOut, finalSumcheckRelOutProp, Set.mem_ofPred_eq] at h_relOut
      unfold finalSumcheckKStateProp
      dsimp only
      change stmtOut = _ at h_stmtOut_eq
      rw [h_stmtOut_eq] at h_relOut
      change oStmtOut = _ at h_oStmtOut_eq
      have h_oracle : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
      constructor
      · exact h_check
      · rw [h_oracle] at h_relOut
        exact h_relOut
    · rw [ite_eq_right h_check] at h_output
      change some (stmtOut, oStmtOut) ∈ MonadAttach.support
        ((simulateQ impl (pure none : OracleComp []ₒ (Option _))).run' s) at h_output
      rw [simulateQ_pure] at h_output
      change some (stmtOut, oStmtOut) ∈ MonadAttach.support
        (Prod.fst <$> (pure none : StateT σ ProbComp _).run s) at h_output
      rw [StateT.run_pure] at h_output
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at h_output

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate h_l).rbrKnowledgeSoundness init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         (𝓑 := boolEmbedding L)
         (mp := RingSwitching_BBFSumcheckMultParam κ L K
          (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError L) := by
  use FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate
  use finalSumcheckKnowledgeStateFunction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l init impl
  intro stmtIn witIn prover j
  rcases j with ⟨j, hj⟩
  cases j using Fin.cases with
  | zero =>
    simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
      Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' =>
    exact Fin.elim0 j'

end FinalSumcheckStep

section CoreInteractionPhaseReduction

/-- The final oracle verifier that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Sumcheck.Structured.Statement (L := L) (ℓ:=ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (V₁ := sumcheckFoldOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l)
       (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)

/-- The final oracle reduction that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Sumcheck.Structured.Statement (L := L) (ℓ:=ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ')
      (RingSwitchingBaseContext κ L K ℓ (biniusProfile κ L K β)) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Wit₁ := RingSwitching.SumcheckWitness L ℓ' 0)
    (Wit₂ := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (Wit₃ := Unit)
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (R₁ := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (R₂ := finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (oSpec := []ₒ)
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (relIn := RingSwitching.strictSumcheckRoundRelation κ (L := L) (K := K)
        (biniusProfile κ L K β) ℓ ℓ' h_l
        (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
      (init := init)
      (impl := impl) := by
  unfold coreInteractionOracleReduction BinaryBasefold.pSpecCoreInteraction
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨⟨0, input.1.challenges, ⟨0, 0⟩⟩, 0⟩, input.2)))
    (fun _ => Or.inl inferInstance)
    (rel₂ := strictRoundRelation K (β := β) (i := Fin.last ℓ'))
  · exact sumcheckFoldOracleReduction_perfectCompleteness κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (init := init) (impl := impl)
  · intro s
    exact finalSumcheckOracleReduction_perfectCompleteness κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (pure s) impl

def coreInteractionOracleRbrKnowledgeError (j : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ).rbrKnowledgeSoundness init impl
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  let res := OracleVerifier.append_rbrKnowledgeSoundness
    (oSpec := []ₒ)
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (init := init) (impl:=impl)
    (Wit₁ := (SumcheckWitness L ℓ' 0))
    (Wit₂ := (Witness K (β := β) (i := Fin.last ℓ')))
    (Wit₃ := Unit)
    (rel₁ := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
    (rel₂ :=  BinaryBasefold.roundRelation (mp := RingSwitching_BBFSumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ'))
    (rel₃ := finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := sumcheckFoldOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
      (V₂ := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
      (rbrKnowledgeError₁ := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ))
    (rbrKnowledgeError₂ := finalSumcheckKnowledgeError (L := L))
    (h₁ := by apply sumcheckFoldOracleVerifier_rbrKnowledgeSoundness)
    (h₂ := by apply finalSumcheckOracleVerifier_rbrKnowledgeSoundness)
  exact res

end CoreInteractionPhaseReduction

omit [NeZero κ] [CharP L 2] [DecidableEq K] h_β₀_eq_1 [SampleableType L] in
/-- Sum of the per-round RBR knowledge error over core interaction challenges is **at most**
`2 * ℓ' / |L| + 2^(ℓ' + 𝓡) / |L|`
(see `BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le`). -/
theorem coreInteractionOracleRbrKnowledgeError_le :
    (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
      coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
    ≤ 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
      + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  classical
  unfold coreInteractionOracleRbrKnowledgeError
  rw [Equiv.sum_comp (Equiv.symm ChallengeIdx.sumEquiv)]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hb : (∑ i : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).ChallengeIdx,
      finalSumcheckKnowledgeError (L := L) i) = 0 := by
    have hu : (Finset.univ : Finset (ChallengeIdx (BinaryBasefold.pSpecFinalSumcheckStep
        (L := L)))) = ∅ := by
      ext x
      exact False.elim
        (BinaryBasefold.CoreInteraction.challengeIdx_pSpecFinalSumcheckStep_isEmpty.false x)
    simp [hu]
  rw [hb, add_zero]
  exact BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le (𝔽q := K) (L := L) (β := β)
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')


end
end Binius.FRIBinius.CoreInteractionPhase
