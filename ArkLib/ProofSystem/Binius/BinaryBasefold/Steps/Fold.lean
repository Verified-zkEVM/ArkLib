/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold.Protocol


/-!
# Binary Basefold Fold-Step Knowledge Soundness
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
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

section FoldStep

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}


open scoped NNReal

open Classical in
/-! Definition of the per-round RBR KS error for Binary FoldFold.
This combines the Sumcheck error (2/|L|) and the LDT Bad Event probability.
For round i : rbrKnowledgeError(i) = err_SC + err_BE where
- err_SC = 2/|L| (Schwartz-Zippel for degree 2)
- err_BE = |S^(last_oracle_domain_index_of_i + ϑ)| / |L|
-/
def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
  let err_SC := (2 : ℝ≥0) / (Fintype.card L)
  -- Distributed fold-error budget: one incremental bad-event charge per fold round.
  let err_BE :=
    let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ i.castSucc
    (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨lastDomainIdx.val + ϑ, by
        have h_le := getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc
        omega⟩) : ℝ≥0) / (Fintype.card L)
  err_SC + err_BE

/-! WitMid type for fold step: Witness i.succ at final round, Witness i.castSucc otherwise.
This allows the extractor to work with the actual output witness type at the final round. -/
def foldWitMid (i : Fin ℓ) : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨1, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨2, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-! The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly.

Key design: WitMid at the final round (m=2) is Witness i.succ, matching WitOut.
This allows extractOut to be identity and simplifies toFun_full proofs. -/
noncomputable def foldRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L))
    (WitMid := foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _oStmtIn⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both are Witness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1, i.e., Witness i.succ → Witness i.castSucc
      -- Extract backward using the transcript
      {
        t := witMidSucc.t,
        H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ)
          (t := witMidSucc.t) (m := mp.multpoly stmtIn.ctx)
          (i := i.castSucc) (challenges := stmtIn.challenges),
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witMidSucc.t
          (challenges := stmtIn.challenges)
      }
  -- extractOut is now identity since WitMid (Fin.last 2) = WitOut = Witness i.succ
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-! This follows the KState of sum-check -/
def foldKStateProp {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc)
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks := sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        let explicitVCheck :=
          h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
          -- we also keep the output-state sumcheck consistency
          sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

-- Note: this fold step couldn't carry bad-event errors, because we don't have oracles yet.

/-! Knowledge state function (KState) for single round -/
set_option backward.isDefEq.respectTransparency false in
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).KnowledgeStateFunction init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (extractor := foldRbrExtractor (mp:=mp) (𝓡 := 𝓡) (ϑ := ϑ) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    foldKStateProp (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmtMid := stmtMid) (witMid := witMid) (oStmtMid := oStmtMid)
  toFun_empty := fun _ _ => by rfl
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
    unfold foldKStateProp at h_kState_round1 ⊢
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
      have h_struct : witnessStructuralInvariant 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtMid witMid := h_good.2.1
      have h_init : firstOracleWitnessConsistencyProp 𝔽q β witMid.t
          (getFirstOracle 𝔽q β oStmtMid) := h_good.2.2.1
      have h_fold := h_good.2.2.2
      have h_sumcheck : sumcheckConsistencyProp (𝓑 := 𝓑) stmtMid.sumcheck_target witMid.H := by
        simp_rw [h_localized] at h_explicit
        rw [h_explicit.symm]
        exact getSumcheckRoundPoly_sum_eq (L := L) (ℓ := ℓ) (𝓑 := 𝓑) (i := i) (h := witMid.H)
      exact Or.inr ⟨h_sumcheck, h_struct, h_init, h_fold⟩
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          _root_.support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (𝓑 := 𝓑) (mp := mp) i).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (𝓑 := 𝓑) (mp := mp) i).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    have h_output_mem_V_run_support :=
      support_simulateQ_run'_subset impl _ s h_output_mem_V_run_support
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [foldOracleVerifier]
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        OptionT.simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
        bind_map_left, Function.comp_apply]
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2, pure_bind]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    let step := (foldStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2 (msg0 := tr.messages ⟨⟨0, by decide⟩, rfl⟩)
        (msg1 := tr.challenges ⟨⟨1, by decide⟩, rfl⟩)) with h_V_check_def
    have h_answer : @OracleInterface.answer _
        (instOracleInterfaceMessagePSpecFold (L := L) ⟨0, rfl⟩)
        (tr.messages ⟨⟨0, by decide⟩, rfl⟩) () =
        tr.messages ⟨⟨0, by decide⟩, rfl⟩ := rfl
    erw [h_answer] at h_output_mem_V_run_support
    by_cases h_V_check : V_check
    · erw [if_pos h_V_check] at h_output_mem_V_run_support
      erw [OptionT.run_pure, simulateQ_pure] at h_output_mem_V_run_support
      erw [_root_.map_pure] at h_output_mem_V_run_support
      simp only [OptionT.mk,
        support_pure, Set.mem_singleton_iff, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue] -- simp the `match`
      dsimp only [foldStepRelOut, foldStepRelOutProp, masterKStateProp] at h_relOut
      simp only [Fin.val_succ, Set.mem_ofPred_eq] at h_relOut
      dsimp only [foldKStateProp]
      set h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨⟨0, by simp only [Nat.reduceAdd,
        Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.ofNat_pos]⟩, rfl⟩ with h_i_def
      set r_i' : L := tr.challenges ⟨⟨1, by simp only [Nat.reduceAdd, Fin.reduceLast,
        Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.one_lt_ofNat]⟩, rfl⟩ with h_i_def
      set extractedWitLast : Witness (L := L) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ :=
        (foldRbrExtractor 𝔽q β i).extractOut (stmtIn, oStmtIn) tr witOut
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by
        rw [h_oStmtOut_eq]
        funext j
        simp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
          MessageIdx, foldStepLogic, Fin.isValue, Fin.eta, Lean.Elab.WF.paramLet,
          Nat.cast_ofNat, Matrix.cons_val_zero, Fin.zero_eta, Matrix.cons_val_one,
          Fin.mk_one, Function.Embedding.coeFn_mk, Message]
        split <;> rename_i k hk
        · have hk' : j = k := by simpa only [dif_pos j.is_lt, Sum.inl.injEq] using hk
          subst k
          apply eq_of_heq
          simp only [eqRec_heq_iff]
          rfl
        · simp only [dif_pos j.is_lt, Sum.inl_ne_inr] at hk
      have h_stmtOut_challenges_eq :
        ((Fin.snoc stmtIn.challenges r_i') : Fin (↑i + 1) → L) = stmtOut.challenges := by
        -- use the h_stmtOut_eq to prove this
        rw [h_stmtOut_eq]
        unfold foldStepLogic foldVerifierStmtOut
        simp only [Fin.val_succ, Fin.isValue, Fin.snoc_inj, true_and]
        rfl
      rw [h_oStmtOut_eq_oStmtIn] at h_relOut
      have h_stmtOut_sumcheck_target_eq :
          stmtOut.sumcheck_target = (Polynomial.eval r_i' ↑h_i) := by
        rw [h_stmtOut_eq]; rfl
      dsimp only [masterKStateProp]
      rw [h_stmtOut_sumcheck_target_eq] at h_relOut
      have h_explicit : h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtIn.sumcheck_target := by
        have h_explicit' := h_V_check
        exact h_explicit'
      cases h_relOut with
      | inl h_bad =>
        have h_bad' : incrementalBadEventExistsProp 𝔽q β i.succ
            (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) oStmtIn
            (Fin.snoc stmtIn.challenges r_i') := by
          have h_bad'' := h_bad
          exact h_stmtOut_challenges_eq ▸ h_bad''
        exact Or.inl h_bad'
      | inr h_good =>
        refine Or.inr ?_
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact ⟨h_explicit, h_good.1⟩
        · have h_struct := h_good.2.1
          simp only [h_stmtOut_eq] at h_struct ⊢
          exact h_struct
        · have h_init := h_good.2.2.1
          exact h_init
        · have h_res := h_good.2.2.2
          simp only [h_stmtOut_eq] at ⊢ h_res
          exact h_res
    · erw [if_neg h_V_check, OptionT.run_failure, simulateQ_pure] at h_output_mem_V_run_support
      erw [map_failure] at h_output_mem_V_run_support
      erw [_root_.map_pure] at h_output_mem_V_run_support
      simp only [OptionT.mk, Option.map_none, support_pure,
        Set.mem_singleton_iff, reduceCtorEq] at h_output_mem_V_run_support

/-
The fold-step extraction failure event implies either:
1. a sumcheck bad event at the sampled challenge, or
2. an incremental folding bad event at the current oracle frontier.

More precisely:
- **Sumcheck bad**: `h_i ≠ h_star ∧ h_i.eval r_i' = h_star.eval r_i'`,
  where `h_star = getSumcheckRoundPoly ℓ 𝓑 i witIn.H`.
- **Folding bad**: an incremental bad-event witness exists at frontier `i.castSucc`
  using challenges extended by `r_i'`.

Proof plan for `foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent`:

Goal shape:
  Doom-escape at challenge round `⟨1, rfl⟩` gives an existential `witMid` with
  `¬kSF@castSucc` and `kSF@succ`; we must derive:
  `badSumcheckEventProp r_i' h_i h_star(witIn) ∨ incrementalFoldingBadEvent`.

Plan:
1. Unfold the doom-escape witness:
   Expand `rbrExtractionFailureEvent`, `foldKnowledgeStateFunction`, and `foldKStateProp`
   at rounds `m=1` and `m=2`, obtaining the two KState facts carried by `witMid`.

2. Isolate the KState core:
   From `masterKStateProp`, separate local checks from the core disjunction
   `incrementalBadEventExistsProp ∨ oracleWitnessConsistency`.

3. Split by the incremental bad event:
   Case A: `incrementalFoldingBadEvent` holds; finish by `Or.inr`.
   Case B: `¬ incrementalFoldingBadEvent`; show this forces the KState-2 core to use
   `oracleWitnessConsistency` (good branch).

4. Overlap-cancellation for bad events:
   In Case B, any bad event witnessed at round 2 must already be present at round 1.
   Old events are preserved backward to round 1 (same oracle frontier / challenge prefix),
   contradicting `¬kSF@round1`. Hence no bad-event branch remains.

5. Fix the round polynomial on the good branch:
   Use the good branch (`oracleWitnessConsistency`, plus local checks) to identify the
   witness-derived round polynomial and compare it with `h_i`.
   Then combine with `¬kSF@round1` to obtain:
   `h_i ≠ h_star` and `h_i(r_i') = h_star(r_i')`.

6. Conclude sumcheck bad:
   Package Step 5 as `badSumcheckEventProp r_i' h_i h_star(witIn)` and finish by `Or.inl`.

Expected helper lemmas:
- backward preservation of incremental bad events from round-2 to round-1 view;
- extraction of localized round-poly equalities from fold-step local checks.
-/
omit [SampleableType L] [DecidableEq 𝔽q] in
omit [CharP L 2] in
lemma firstOracleWitnessConsistency_unique (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {t₁ t₂ : MultilinearPoly L ℓ}
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  classical
  have h₁_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₁ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) (tpoly := t₁)).2 h₁
  have h₂_some :
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) = some t₂ :=
    (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (f := getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) (tpoly := t₂)).2 h₂
  rw [h₁_some] at h₂_some
  injection h₂_some with h_t

/-! Extract the round-`i` witness (before the verifier challenge) from a fold-step output
witness. -/
@[reducible]
def foldStepWitBeforeFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc :=
  (foldRbrExtractor.{0} (mp := mp) 𝔽q β i).extractMid
    (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid

/-! Canonical fold-step round polynomial extracted from a specific `witMid`. -/
@[reducible]
def foldStepHStarFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    L⦃≤ 2⦄[X] :=
  let witBefore := foldStepWitBeforeFromWitMid
    (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i stmtOStmtIn h_i r_i' witMid
  getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := witBefore.H)

/-! At the same fold-step output state, `witnessStructuralInvariant`
and `firstOracleWitnessConsistencyProp` determine a unique witness.
Consequently, any witness-dependent extracted `h_star` is canonical. -/
omit [SampleableType L] [DecidableEq 𝔽q] in
omit [CharP L 2] in
lemma foldStep_oracleWitnessConsistency_unique_witMid (i : Fin ℓ)
    (stmtOut : Statement (L := L) Context i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut witMid₂)
    (h_init₁ : firstOracleWitnessConsistencyProp 𝔽q β witMid₁.t
      (getFirstOracle 𝔽q β oStmt))
    (h_init₂ : firstOracleWitnessConsistencyProp 𝔽q β witMid₂.t
      (getFirstOracle 𝔽q β oStmt)) :
    witMid₁ = witMid₂ := by
  classical
  have h_t : witMid₁.t = witMid₂.t := by
    exact firstOracleWitnessConsistency_unique 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := i) (oStmt := oStmt) (h₁ := h_init₁) (h₂ := h_init₂)
  have h_H : witMid₁.H = witMid₂.H := by
    calc
      witMid₁.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid₁.t)
        (m := mp.multpoly stmtOut.ctx) (i := i.succ)
        (challenges := stmtOut.challenges) := h_struct₁.1
      _ = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid₂.t)
        (m := mp.multpoly stmtOut.ctx) (i := i.succ)
        (challenges := stmtOut.challenges) := by simp only [Fin.val_succ, h_t]
      _ = witMid₂.H := h_struct₂.1.symm
  have h_f : witMid₁.f = witMid₂.f := by
    calc
      witMid₁.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i.succ) (t := witMid₁.t) (challenges := stmtOut.challenges) := h_struct₁.2
      _ = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i.succ) (t := witMid₂.t)
        (challenges := stmtOut.challenges) := by simp only [Fin.val_succ, h_t]
      _ = witMid₂.f := h_struct₂.2.symm
  cases witMid₁
  cases witMid₂
  simp only [Fin.val_succ, Witness.mk.injEq] at h_t h_H h_f ⊢
  exact ⟨h_t, h_H, h_f⟩

omit [SampleableType L] [DecidableEq 𝔽q] in
omit [CharP L 2] in
lemma foldStepHStarFromWitMid_eq_of_oracleWitnessConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
        ctx := stmtOStmtIn.1.ctx
      } witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
        ctx := stmtOStmtIn.1.ctx
      } witMid₂)
    (h_init₁ : firstOracleWitnessConsistencyProp 𝔽q β witMid₁.t
      (getFirstOracle 𝔽q β stmtOStmtIn.2))
    (h_init₂ : firstOracleWitnessConsistencyProp 𝔽q β witMid₂.t
      (getFirstOracle 𝔽q β stmtOStmtIn.2)) :
    foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid₁ =
    foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid₂ := by
  have h_wit_eq :
      witMid₁ = witMid₂ := foldStep_oracleWitnessConsistency_unique_witMid
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) (ϑ := ϑ)
        (i := i)
        (stmtOut := {
          sumcheck_target := h_i.val.eval r_i',
          challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
          ctx := stmtOStmtIn.1.ctx
        })
        (oStmt := stmtOStmtIn.2) h_struct₁ h_struct₂ h_init₁ h_init₂
  subst h_wit_eq
  rfl

/-! Fresh incremental bad-event for the **latest oracle block** at the fold-step:
`¬ E_before ∧ E_after`, where `E_*` is `incrementalFoldingBadEvent` evaluated
before/after appending `r_i'`. -/
@[reducible]
def foldStepFreshDoomPreservationEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L) : Prop :=
  let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
  let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
  let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
  let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
  let kBefore : ℕ := min ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
  -- NOTE: actually `kBefore` is always less than `ϑ`, so `kBefore + 1 ≤ ϑ`
  have h_j_val : j.val = i.val / ϑ := by
    have h_i_lt_ℓ : i.val < ℓ := i.isLt
    have h_i_cast_lt_ℓ : i.val < ℓ := by simp only [h_i_lt_ℓ]
    dsimp only [j, getLastOraclePositionIndex]
    unfold toOutCodewordsCount
    simp only [Fin.val_castSucc, h_i_lt_ℓ, ↓reduceIte, add_tsub_cancel_right]
  have h_cur_eq : curOracleDomainIdx.val = (i.val / ϑ) * ϑ := by
    dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
    simp only [h_j_val]
  have h_diff_lt : stmtIdxBefore.val - curOracleDomainIdx.val < ϑ := by
    have h_div_mod : (i.val / ϑ) * ϑ + i.val % ϑ = i.val := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i.val ϑ
    have h_cur_le : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
        _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
    have h_sum : curOracleDomainIdx.val + i.val % ϑ = stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val + i.val % ϑ = (i.val / ϑ) * ϑ + i.val % ϑ := by
          simp only [h_cur_eq]
        _ = i.val := h_div_mod
    have h_diff_eq : stmtIdxBefore.val - curOracleDomainIdx.val = i.val % ϑ := by omega
    rw [h_diff_eq]
    exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
  have h_kBefore_lt : kBefore < ϑ := by
    exact lt_of_le_of_lt
      (Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)) h_diff_lt
  let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
    have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := Nat.pos_of_neZero 𝓡
    dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]
    omega
  ⟩
  let r_prefix : Fin kBefore → L := fun cId => challengesBefore
    ⟨curOracleDomainIdx.val + cId.val, by
      have h_k_le_stmt : kBefore ≤ stmtIdxBefore.val - curOracleDomainIdx.val :=
        Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
      have h_cId_lt_k : cId.val < kBefore := cId.isLt
      omega
    ⟩
  let E_before :=
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore ≤ ϑ := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
      (h_k_le := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val))
      (h_midIdx := by simp only)
      (h_destIdx := rfl)
      (h_destIdx_le := by
        simp only [(oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)), j, destIdx,
          curOracleDomainIdx])
      (f_block_start := stmtOStmtIn.2 j)
      (r_challenges := r_prefix)
  let E_after :=
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (block_start_idx := curOracleDomainIdx)
    (midIdx := ⟨curOracleDomainIdx.val + (kBefore + 1), by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      have h_k_le : kBefore + 1 ≤ ϑ := Nat.succ_le_of_lt h_kBefore_lt
      have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
        oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      omega
    ⟩)
    (destIdx := destIdx) (k := kBefore + 1)
    (h_k_le := Nat.succ_le_of_lt h_kBefore_lt)
    (h_midIdx := by simp only)
    (h_destIdx := rfl)
    (h_destIdx_le := by
      simp only [(oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)), j, destIdx,
        curOracleDomainIdx])
    (f_block_start := stmtOStmtIn.2 j)
    (r_challenges := Fin.snoc r_prefix r_i')
  ¬ E_before ∧ E_after

/-! Oracle-witness consistency for a candidate fold-step output witness. -/
@[reducible]
def foldStepWitMidOracleConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt : Statement (L := L) Context i.succ := {
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtOStmtIn.1.challenges r_i',
      ctx := stmtOStmtIn.1.ctx
  }
  let structural := witnessStructuralInvariant 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt witMid
  let initial := firstOracleWitnessConsistencyProp 𝔽q β witMid.t (getFirstOracle 𝔽q β stmtOStmtIn.2)
  structural ∧ initial

/-! Proof sketch:
let `j` be the **oracle position index** of the last oracle at oracle frontier `i`.
Note that `k = i - j * ϑ < ϑ`, since if `k = ϑ`,
  then `i` must be an oracle domain, therefore `k = 0`, contradiction.
We have:
  h_bad_after =  `|__|__|...|__|__|j*ϑ|====i===(i+1)| ↔ exists_bad_until_j OR incBad(j -> i+1)`
  h_not_fresh = `¬(¬incBad(j -> i) ∧ incBad(j -> i+1)) ↔ incBad(j -> i) ∨ (¬incBad(j -> i+1))`
Goal: h_bad_before = `|__|__|...|__|__|j*ϑ|====i| = exists_bad_until_j OR incBad(j -> i)`
--------
We rcases on h_not_fresh:
  If `incBad(j -> i)` holds, then h_bad_before = true, Q.E.D.
  else we have `¬incBad(j -> i+1)`,
    which implies `exists_bad_until_j` to be true from `h_bad_after`
    => `h_bad_before = true` by definition
-/
omit [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] in
private theorem fin_fun_heq_of_cast {m n : ℕ} (h : m = n)
    (f : Fin m → L) (g : Fin n → L)
    (hfg : ∀ i : Fin m, f i = g (Fin.cast h i)) :
    HEq f g := by
  subst h
  apply heq_of_eq
  funext i
  simpa using hfg i

set_option maxHeartbeats 200000 in
-- This bad-event backward step expands several nested verifier definitions before omega closes.
omit [CharP L 2] [SampleableType L] in
omit [DecidableEq 𝔽q] in
lemma incrementalBadEventExistsProp_fold_step_backward (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L)
    (h_bad_after : incrementalBadEventExistsProp 𝔽q β i.succ
      (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) stmtOStmtIn.2
      (Fin.snoc stmtOStmtIn.1.challenges r_i'))
    (h_not_fresh : ¬ foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i') :
  incrementalBadEventExistsProp 𝔽q β i.castSucc
      (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
      stmtOStmtIn.1.challenges := by
  classical
  unfold incrementalBadEventExistsProp at h_bad_after ⊢
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
        incrementalFoldingBadEvent 𝔽q β
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
      convert hj_copy using 1
      · apply Fin.eq_of_val_eq
        dsimp [blockDest]
        omega
      · exact hk_after.symm
      · have h_afterSlice_heq :
            HEq
              (fun cId : Fin (min ϑ (i.val + 1 - j.val * ϑ)) =>
                Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i'
                  ⟨j.val * ϑ + cId.val, by
                    have h_cId_lt :
                        cId.val < i.val + 1 - j.val * ϑ := by
                      exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                    have h_block_le : j.val * ϑ ≤ i.val + 1 := by
                      omega
                    calc
                      j.val * ϑ + cId.val < j.val * ϑ + (i.val + 1 - j.val * ϑ) :=
                        Nat.add_lt_add_left h_cId_lt (j.val * ϑ)
                      _ = i.val + 1 := Nat.add_sub_of_le h_block_le⟩)
              afterSlice := by
          apply fin_fun_heq_of_cast hk_after
          intro cId
          dsimp [afterSlice]
        exact HEq.symm h_afterSlice_heq
    have h_bad_after_full :
        foldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := blockStart)
          (destIdx := blockDest)
          (steps := ϑ)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_i := stmtOStmtIn.2 j)
          (r_challenges := afterSlice) := by
      exact
        (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
          (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ)
          (block_start_idx := blockStart)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := by rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := afterSlice)).1 hj_after_full
    have h_bad_before_full := h_bad_after_full
    rw [h_challenges] at h_bad_before_full
    have hj_before_full :
        incrementalFoldingBadEvent 𝔽q β
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
          (r_challenges := beforeSlice) := by
      exact
        (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
          (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ)
          (block_start_idx := blockStart)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := by rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := beforeSlice)).2 h_bad_before_full
    convert hj_before_full using 1
    · apply Fin.eq_of_val_eq
      dsimp [blockDest]
      omega
    · have h_beforeSlice_heq :
          HEq
            (fun cId : Fin (min ϑ (i.val - j.val * ϑ)) =>
              stmtOStmtIn.1.challenges
                ⟨j.val * ϑ + cId.val, by
                  have h_cId_lt :
                      cId.val < i.val - j.val * ϑ := by
                    exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                  have h_block_le : j.val * ϑ ≤ i.val := by
                    exact le_trans (by omega) h_k_full
                  calc
                    j.val * ϑ + cId.val < j.val * ϑ + (i.val - j.val * ϑ) :=
                      Nat.add_lt_add_left h_cId_lt (j.val * ϑ)
                    _ = i.val := Nat.add_sub_of_le h_block_le⟩)
            beforeSlice := by
        apply fin_fun_heq_of_cast hk_before
        intro cId
        dsimp [beforeSlice]
      exact h_beforeSlice_heq
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
        have h_ge : toOutCodewordsCount ℓ ϑ i.castSucc ≤ j.val + 1 := by
          omega
        omega
      dsimp [getLastOraclePositionIndex]
      exact h_val
    subst j
    dsimp [foldStepFreshDoomPreservationEvent] at h_not_fresh
    have h_j_val : (getLastOraclePositionIndex ℓ ϑ i.castSucc).val = i.val / ϑ := by
      dsimp only [getLastOraclePositionIndex]
      unfold toOutCodewordsCount
      simp only [Fin.val_castSucc, i.isLt, ↓reduceIte, add_tsub_cancel_right]
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
      have h_mod_lt : i.val % ϑ < ϑ := by
        exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
      omega
    let kBefore : ℕ := min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)
    let prefixSlice : Fin kBefore → L := fun cId =>
      stmtOStmtIn.1.challenges
        ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
          have h_min_le :
              kBefore ≤ i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
            dsimp [kBefore]
            exact Nat.min_le_right ϑ _
          have h_cId_lt :
              cId.val < i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
            exact lt_of_lt_of_le cId.isLt h_min_le
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
            have h_min_le :
                min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) ≤
                  i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ :=
              Nat.min_le_right ϑ _
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
        simp [afterSlice, freshSlice, prefixSlice, Fin.snoc, h_lt, h_idx_lt]
      · have h_eq_last :
            cId.val = kBefore := by
          omega
        have h_idx_eq :
            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val = i.val := by
          rw [h_eq_last]
          dsimp [kBefore]
          omega
        have h_not_idx_lt :
            ¬ (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val < i.val := by
          omega
        simp [afterSlice, freshSlice, prefixSlice, Fin.snoc, h_lt, h_idx_eq]
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
        incrementalFoldingBadEvent 𝔽q β
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
      convert hj_copy using 1
      · apply Fin.eq_of_val_eq
        dsimp [blockStart, blockMidAfter, kBefore]
        omega
      · dsimp [kBefore]
        omega
      · have h_afterSlice_heq :
            HEq
              (fun cId : Fin
                  (min ϑ (i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)) =>
                Fin.snoc (α := fun _ => L) stmtOStmtIn.1.challenges r_i'
                  ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
                    have h_cId_lt :
                        cId.val <
                          i.val + 1 -
                            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
                      exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                    have h_block_le :
                        (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ ≤ i.val + 1 := by
                      omega
                    calc
                      (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val <
                          (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ +
                            (i.val + 1 -
                              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) :=
                        Nat.add_lt_add_left h_cId_lt _
                      _ = i.val + 1 := Nat.add_sub_of_le h_block_le⟩)
              afterSlice := by
          apply fin_fun_heq_of_cast hk_after_last
          intro cId
          dsimp [afterSlice]
        exact HEq.symm h_afterSlice_heq
    have h_after_last' := h_after_last_afterSlice
    rw [h_after_challenges] at h_after_last'
    by_contra h_before_false
    exact h_not_fresh ⟨h_before_false, h_after_last'⟩

omit [CharP L 2] [SampleableType L] in
omit [DecidableEq 𝔽q] in
lemma foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑) (init := init)
        (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn)
    (transcript := FullTranscript.mk1 h_i) (challenge := r_i')) :
    let incrementalFoldingBadEvent :=
      foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
    incrementalFoldingBadEvent ∨ (
      ¬incrementalFoldingBadEvent ∧
      (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (foldStepWitMidOracleConsistency (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i r_i' witMid)
        ∧ (badSumcheckEventProp r_i' h_i
            (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid))
      )
    ) := by
  classical
  let incrementalFoldingBadEvent : Prop :=
    foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [foldKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold foldKStateProp at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    Transcript.concat] at h_kState_before_false h_kState_after_true
  by_cases h_bad : incrementalFoldingBadEvent
  · left
    exact h_bad
  · right
    refine ⟨h_bad, ?_⟩
    -- Under ¬ fresh bad-event, the m=2 KState cannot be on the bad branch.
    have h_after_good_exists : ∃ h_after_good, h_kState_after_true = Or.inr h_after_good := by
      cases h_kState_after_true with
      | inl h_bad_after =>
        exfalso
        have h_bad_before : incrementalBadEventExistsProp 𝔽q β i.castSucc
          (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
          stmtOStmtIn.1.challenges :=
          incrementalBadEventExistsProp_fold_step_backward 𝔽q β
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
        sumcheckConsistencyProp (𝓑 := 𝓑) (Polynomial.eval r_i' h_i.val) witMid.H := by
      exact h_after_good.1.2
    have h_consistency : foldStepWitMidOracleConsistency 𝔽q β i stmtOStmtIn h_i r_i' witMid :=
      ⟨h_after_good.2.1, h_after_good.2.2.1⟩
    have h_left_from_consistency :
        badSumcheckEventProp r_i' h_i
          (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid) := by
      have h_wit_struct_after :
          witMid.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid.t)
            (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i.succ)
            (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i') := by
        exact h_consistency.1.1
      let H_before : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid.t)
          (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i.castSucc)
          (challenges := stmtOStmtIn.1.challenges)
      let h_star_extracted : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H_before)
      have h_eval_eq_extracted :
          Polynomial.eval r_i' h_i.val = Polynomial.eval r_i' h_star_extracted.val := by
        unfold sumcheckConsistencyProp at h_sumcheck_after
        rw [h_wit_struct_after] at h_sumcheck_after
        rw [projectToMidSumcheckPoly_succ (L := L) (ℓ := ℓ) (t := witMid.t)
          (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i)
          (challenges := stmtOStmtIn.1.challenges) (r_i' := r_i')] at h_sumcheck_after
        have h_sum_eq :=
          projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := 𝓑) (ℓ := ℓ)
            (i := i) (Hᵢ := H_before) (rᵢ := r_i')
        have h_sum_eq' :
            Polynomial.eval r_i' h_star_extracted.val =
              ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
                (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i)
                  (Hᵢ := H_before) (rᵢ := r_i')).val.eval x := by
          have h_sum_eq' := h_sum_eq
          dsimp only [h_star_extracted] at h_sum_eq' ⊢
          exact h_sum_eq'
        calc
          Polynomial.eval r_i' h_i.val
              = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
                  (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i)
                    (Hᵢ := H_before) (rᵢ := r_i')).val.eval x := h_sumcheck_after
          _ = Polynomial.eval r_i' h_star_extracted.val := by
            symm
            exact h_sum_eq'
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
        · unfold witnessStructuralInvariant
          simp only [Fin.val_castSucc, foldRbrExtractor, Fin.zero_eta, Fin.isValue,
            Fin.succ_zero_eq_one, Fin.mk_one, Fin.succ_one_eq_two,
            Fin.coe_ofNat_eq_mod, Nat.reduceMod, and_self]
        · exact h_consistency.2
        · have h_folding_after := h_after_good.2.2.2
          unfold oracleFoldingConsistencyProp at h_folding_after ⊢
          intro j hj
          have h_fold_j := h_folding_after j hj
          unfold isCompliant at h_fold_j ⊢
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
          erw [h_gc _] at h_iter
          exact h_iter
      change badSumcheckEventProp r_i' h_i h_star_extracted
      exact ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
    exact ⟨witMid, h_consistency, h_left_from_consistency⟩

/-! Per-transcript bound: for the first prover message `msg0`, the probability (over the verifier
  challenge `y`) that extraction fails is at most `foldKnowledgeError`. Stated for
  `P (FullTranscript.mk1 msg0)` so it matches the goal after `tsum_uniform_Pr_eq_Pr` in the main
  soundness proof.
  **Proof strategy:**
  1. **Implication**: Show that extraction failure `P(tr, y)` implies either
    - a SINGLE sumcheck “bad” event
    - or an incremental folding bad event (bad oracle / consistency failure)
  2. **Monotonicity**: Conclude `Pr[P] ≤ Pr[SZ ∨ BE]` via `prob_mono`.
  3. **Union bound**: Apply `Pr_or_le` to get `Pr[SZ ∨ BE] ≤ Pr[SZ] + Pr[BE]`.
  4. **Schwartz–Zippel**: Bound `Pr[SZ]` by `1/|L|` using univariate degree-1
    agreement (lemmas from Instances.lean)
  5. **Bad event**: Bound `Pr[BE]` using the incremental folding bad-event probability
    (`prop_4_21_2_incremental_bad_event_probability`).
  6. **Combine**: Add the two bounds and match the RHS to `foldKnowledgeError`. -/
omit [DecidableEq 𝔽q] in
lemma foldStep_doom_escape_probability_bound (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑)
          (init := init) (impl := impl) (σ := σ) 𝔽q β i)
        (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) ⟨1, rfl⟩
          stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, by rfl⟩ := by
  classical
  let doomEvent := fun y : L =>
    rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑)
        (init := init) (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) ⟨1, rfl⟩
      stmtOStmtIn (FullTranscript.mk1 h_i) y
  let sumcheckBadEvent : L → Prop := fun y =>
    let incrementalFoldingBadEvent :=
      foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
    (¬incrementalFoldingBadEvent ∧
        (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (foldStepWitMidOracleConsistency (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i y witMid)
        ∧ (badSumcheckEventProp y h_i
            (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn h_i y witMid))
      ))
  let incrementalBadFoldEvent := fun y : L =>
    foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
  let incrementalBadFoldEvent_or_sumcheckBadEvent := fun y : L =>
    (incrementalBadFoldEvent y) ∨ (sumcheckBadEvent y)
  have h_prob_mono := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
    (f := doomEvent) (g := incrementalBadFoldEvent_or_sumcheckBadEvent)
    (h_imp := by
      intro y h_doomEscape
      have h_imp := (foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent
          (mp := mp) (𝓑 := 𝓑) (init := init) (impl := impl) 𝔽q β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i)
          (r_i' := y) (doomEscape := h_doomEscape))
      dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, sumcheckBadEvent,
        incrementalBadFoldEvent]
      by_cases h_bad : foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
      · exact Or.inl h_bad
      · cases h_imp with
        | inl h_bad' => exact False.elim (h_bad h_bad')
        | inr h_sum => exact Or.inr h_sum
    )
  refine le_trans h_prob_mono ?_
  dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, foldKnowledgeError]
  apply le_trans (
      Probability.Pr_or_le ($ᵖ L) (f := incrementalBadFoldEvent) (g := sumcheckBadEvent)
  )
  conv_rhs => simp only [ENNReal.coe_add]; rw [add_comm]
  apply add_le_add
  · dsimp only [incrementalBadFoldEvent, foldStepFreshDoomPreservationEvent]
    let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
    let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
    let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
    let kBefore : ℕ := min ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
    have h_j_val : j.val = i.val / ϑ := by
      have h_i_lt_ℓ : i.val < ℓ := i.isLt
      have h_i_cast_lt_ℓ : i.val < ℓ := by
        simp only [h_i_lt_ℓ]
      dsimp only [j, getLastOraclePositionIndex]
      unfold toOutCodewordsCount
      simp only [Fin.val_castSucc, h_i_lt_ℓ, ↓reduceIte, add_tsub_cancel_right]
    have h_cur_eq : curOracleDomainIdx.val = (i.val / ϑ) * ϑ := by
      dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
      simp only [h_j_val]
    have h_diff_lt : stmtIdxBefore.val - curOracleDomainIdx.val < ϑ := by
      have h_div_mod : (i.val / ϑ) * ϑ + i.val % ϑ = i.val := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod i.val ϑ
      have h_cur_le : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
        dsimp only [stmtIdxBefore]
        calc
          curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
          _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
      have h_sum : curOracleDomainIdx.val + i.val % ϑ = stmtIdxBefore.val := by
        dsimp only [stmtIdxBefore]
        calc
          curOracleDomainIdx.val + i.val % ϑ = (i.val / ϑ) * ϑ + i.val % ϑ := by
            simp only [h_cur_eq]
          _ = i.val := h_div_mod
      have h_diff_eq : stmtIdxBefore.val - curOracleDomainIdx.val = i.val % ϑ := by omega
      rw [h_diff_eq]
      exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
    have h_kBefore_lt : kBefore < ϑ := by
      exact lt_of_le_of_lt
        (Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)) h_diff_lt
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
      have _ : 𝓡 > 0 := Nat.pos_of_neZero 𝓡
      dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]
      omega
    ⟩
    let r_prefix : Fin kBefore → L := fun cId => challengesBefore
      ⟨curOracleDomainIdx.val + cId.val, by
        have h_k_le_stmt : kBefore ≤ stmtIdxBefore.val - curOracleDomainIdx.val :=
          Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_cId_lt_k : cId.val < kBefore := cId.isLt
        omega
      ⟩
    have h_res := prop_4_21_2_incremental_bad_event_probability 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx_i := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore ≤ ϑ := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (midIdx_i_succ := ⟨curOracleDomainIdx.val + kBefore + 1, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore + 1 ≤ ϑ := Nat.succ_le_of_lt h_kBefore_lt
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
    have h_cur_le_stmt : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
        _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
    have h_kBefore_eq : kBefore = stmtIdxBefore.val - curOracleDomainIdx.val := by
      dsimp only [kBefore]
      exact Nat.min_eq_right (Nat.le_of_lt h_diff_lt)
    have h_kAfter_eq : min ϑ (i.succ.val - curOracleDomainIdx.val) = kBefore + 1 := by
      have h_cur_le_i : curOracleDomainIdx.val ≤ i.val := by
        have h_cur_le_i' := h_cur_le_stmt
        simp only [stmtIdxBefore] at h_cur_le_i'
        exact h_cur_le_i'
      have h_sub_succ : i.val + 1 - curOracleDomainIdx.val
        = (i.val - curOracleDomainIdx.val) + 1 := by
        have h_sub_succ' := Nat.succ_sub h_cur_le_i
        rw [Nat.succ_eq_add_one] at h_sub_succ'
        exact h_sub_succ'
      have h_kBefore_eq' : kBefore = i.val - curOracleDomainIdx.val := by
        have h_kBefore_eq'' := h_kBefore_eq
        simp only [stmtIdxBefore] at h_kBefore_eq''
        exact h_kBefore_eq''
      simp only [Fin.val_succ]
      rw [h_sub_succ, ← h_kBefore_eq']
      exact Nat.min_eq_right (Nat.succ_le_of_lt h_kBefore_lt)
    have h_snoc_eq :
        ∀ r_new : L,
          (fun cId : Fin (kBefore + 1) =>
            if h : curOracleDomainIdx.val + cId.val < stmtIdxBefore.val then
              challengesBefore ⟨curOracleDomainIdx.val + cId.val, h⟩
            else
              r_new) = Fin.snoc r_prefix r_new := by
      intro r_new
      funext cId
      by_cases h_lt : cId.val < kBefore
      · have h_guard : curOracleDomainIdx.val + cId.val < stmtIdxBefore.val := by
          omega
        simp [Fin.snoc, r_prefix, h_lt, h_guard]
      · have h_guard_false : ¬ curOracleDomainIdx.val + cId.val < stmtIdxBefore.val := by
          omega
        simp [Fin.snoc, h_lt, h_guard_false]
    conv_rhs => simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      ENNReal.coe_div, ENNReal.coe_natCast]
    exact h_res
  · dsimp only [sumcheckBadEvent]
    -- Strategy: ignore the `foldStepFreshDoomPreservationEvent`, plus `oracleWitnessConsistency`
      -- guarantees uniqueness of witMid, then we can transform this to prove the bound via
        -- `probability_bound_badSumcheckEventProp`
    let compatPred : MultilinearPoly L ℓ → Prop := fun t =>
      firstOracleWitnessConsistencyProp 𝔽q β t (getFirstOracle 𝔽q β stmtOStmtIn.2)
    by_cases hCompat : ∃ t : MultilinearPoly L ℓ, compatPred t
    · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
      let H_fixed : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t_fixed)
          (m := mp.multpoly stmtOStmtIn.1.ctx)
          (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
      let h_star_fixed : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ 𝓑 (i := i) (h := H_fixed)
      have h_prob_mono_sum := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
        (f := fun y => sumcheckBadEvent y)
        (g := fun y => badSumcheckEventProp y h_i h_star_fixed)
        (h_imp := by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, h_bad⟩
          have h_t_eq : witMid.t = t_fixed :=
            firstOracleWitnessConsistency_unique 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := i)
              (oStmt := stmtOStmtIn.2) (h₁ := h_cons.2) (h₂ := h_t_fixed_compat)
          have h_bad' := h_bad
          simp only [h_star_fixed, H_fixed, foldStepHStarFromWitMid,
            foldStepWitBeforeFromWitMid, foldRbrExtractor, Fin.isValue, h_t_eq] at h_bad' ⊢
          exact h_bad'
        )
      refine le_trans h_prob_mono_sum ?_
      have h_sz := probability_bound_badSumcheckEventProp (h_i := h_i) (h_star := h_star_fixed)
      conv_rhs =>
        rw [ENNReal.coe_div (hr := by
          simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])]
        simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
      exact h_sz
    · have h_prob_mono_false := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
        (f := fun y => sumcheckBadEvent y)
        (g := fun _ => False)
        (h_imp := by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, _h_bad⟩
          exact (hCompat ⟨witMid.t, h_cons.2⟩).elim
        )
      refine le_trans h_prob_mono_false ?_
      simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
        eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-! RBR knowledge soundness for a single round oracle verifier -/
open Classical in
omit [DecidableEq 𝔽q] in
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  classical
  -- One-liner via the reusable round-reducer: reduce r.b.r. knowledge soundness to the fold
  -- step's per-transcript doom bound (Schwartz–Zippel).
  let : ∀ j, Fintype ((pSpecFold (L := L)).Challenge j)
    | ⟨0, hj⟩ => by nomatch hj
    | ⟨1, _⟩ => inferInstanceAs (Fintype L)
  let : ∀ j, Inhabited ((pSpecFold (L := L)).Challenge j)
    | ⟨0, hj⟩ => by nomatch hj
    | ⟨1, _⟩ => ⟨(0 : L)⟩
  let : OracleSpec.Inhabited []ₒ := { inhabitedB := fun j => PEmpty.elim j }
  let : OracleSpec.Fintype [(pSpecFold (L := L)).Challenge]ₒ :=
    { fintypeB := fun j => inferInstanceAs (Fintype ((pSpecFold (L := L)).Challenge j.1)) }
  let : OracleSpec.Inhabited [(pSpecFold (L := L)).Challenge]ₒ :=
    { inhabitedB := fun j => inferInstanceAs (Inhabited ((pSpecFold (L := L)).Challenge j.1)) }
  let : IsUniformSpec ([]ₒ + [(pSpecFold (L := L)).Challenge]ₒ) :=
    IsUniformSpec.ofFintypeInhabited _
  exact OracleReduction.rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    (pSpec := pSpecFold (L := L)) (init := init) (impl := impl)
    (verifier := (foldOracleVerifier 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).toVerifier)
    (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.castSucc)
    (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (WitMid := foldWitMid 𝔽q β i)
    (rbrKnowledgeError := foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (kSF := foldKnowledgeStateFunction (mp := mp) (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (init := init) (impl := impl) 𝔽q β i)
    (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) (hDir0 := rfl) (hDir1 := rfl)
    (hbound := fun stmtOStmtIn msg₀ => foldStep_doom_escape_probability_bound 𝔽q β (i := i)
      (stmtOStmtIn := stmtOStmtIn) (h_i := msg₀) (init := init) (impl := impl) (mp := mp)
      (𝓑 := 𝓑) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

end FoldStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
