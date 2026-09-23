/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Protocol

/-!
# Binary Basefold block-composition security

Completeness and round-by-round knowledge soundness for the iterated fold/relay/commit blocks.
The protocol definitions and single-round composition lemmas are in `Protocol`.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial Equiv
open scoped NNReal


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

section ComponentReductions
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

section IteratedSumcheckFoldComposition

section SecurityProps

local instance foldChallengeFintype (j : (pSpecFold (L := L)).ChallengeIdx) :
    Fintype ((pSpecFold (L := L)).Challenge j) := by
  have hj : j.1 = 1 := by
    rcases j with ⟨j, hj⟩
    fin_cases j
    · simp at hj
    · rfl
  have h_type : (pSpecFold (L := L)).Challenge j = L := by
    simp [ProtocolSpec.Challenge, pSpecFold, hj]
  exact Fintype.ofEquiv L (Equiv.cast h_type.symm)

local instance foldChallengeFintypes :
    (j : (pSpecFold (L := L)).ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge j) :=
  fun j => foldChallengeFintype j

local instance foldChallengeInhabited :
    (j : (pSpecFold (L := L)).ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge j) :=
  fun _ => Classical.inhabited_of_nonempty inferInstance

local instance commitChallengeFintypes (i : Fin ℓ) :
    (j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Fintype ((pSpecCommit 𝔽q β i).Challenge j) := fun j => by
  have h := j.2
  simp [pSpecCommit] at h

local instance commitChallengeInhabited (i : Fin ℓ) :
    (j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Inhabited ((pSpecCommit 𝔽q β i).Challenge j) := fun j => by
  have h := j.2
  simp [pSpecCommit] at h

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Perfect completeness for a single non-last block -/
omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
lemma nonLastSingleBlockOracleReduction_perfectCompleteness
    (_hInit : NeverFail init) (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ) (h₁:=by
            change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          ) (by omega)
        ⟩)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (oracleReduction := nonLastSingleBlockOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) bIdx) := by
  unfold nonLastSingleBlockOracleReduction; simp only
  -- At this point the goal is perfectCompleteness for an `append`.
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
    (fun _ => Or.inr rfl)
    (rel₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      ⟨bIdx * ϑ + (ϑ - 1), by
        -- matches the index used by the append midpoint in the definition
        let fv: Fin ϑ := ⟨ϑ - 1, by
          have h := NeZero.one_le (n:=ϑ)
          exact Nat.sub_one_lt_of_lt h
        ⟩
        change ↑bIdx * ϑ + fv.val < ℓ + 1
        apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=1)
      ⟩)
    (impl := impl) (init := init)
  · -- Perfect completeness of the fold+relay sequence part (`seqCompose`), output-cast is rfl
    apply OracleReduction.castInOut_perfectCompleteness
      (h_stmtIn := by
        apply Statement.of_fin_eq;
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_stmtOut := by rfl)
      (h_witIn := by
        apply Witness.of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_witOut := by rfl)
      (h_idxIn := by
        apply OracleStatement.idx_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_idxOut := by rfl)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_ostmtOut := by rfl)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_relIn := by
        apply strictRoundRelation.of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_relOut := by rfl)
      (impl := impl) (init := init)
    let stmt : Fin (ϑ - 1 + 1) → Type :=
      fun i => Statement (L := L) (ℓ := ℓ) Context
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let oStmt := fun i: Fin (ϑ - 1 + 1) =>
      OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let wit := fun i: Fin (ϑ - 1 + 1) =>
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let foldRelayRoundsPerfectCompleteness :=
      OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
        (oSpec := []ₒ) (m := ϑ - 1)
        (pSpec := fun _ : Fin (ϑ - 1) => pSpecFoldRelay (L:=L))
        (Stmt := stmt)
        (OStmt := oStmt)
        (Wit := wit)
        (R := fun i => by
          have hNCR : ¬ isCommitmentRound ℓ ϑ
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
            isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
          exact foldRelayOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑:=𝓑) (i:=⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) hNCR
        )
        (rel := fun i ↦
          strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
            (⟨↑bIdx * ϑ + ↑i, by simp only [bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ]⟩ : Fin (ℓ + 1)))
        (init := init) (impl := impl)
    apply foldRelayRoundsPerfectCompleteness
      (hP := fun _ => inferInstance)
      (hV := fun _ => Verifier.GuardedForm.ofEmpty _ (fun input =>
        (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
    intro (i : Fin (ϑ - 1)) s
    have hNCR : ¬ isCommitmentRound ℓ ϑ
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
      isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
    let res := foldRelayOracleReduction_perfectCompleteness 𝔽q β (mp := mp) (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := pure s) (impl := impl)
      (hInit := by infer_instance)
      (i := ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) (hNCR := hNCR)
    exact res
  · -- Perfect completeness of the final fold+commit round, via castInOut
    intro s
    let init : ProbComp σ := pure s
    have hInit : NeverFail init := by infer_instance
    have h_ϑ_gt_zero : ϑ > 0 := Nat.pos_of_neZero ϑ
    apply OracleReduction.castInOut_perfectCompleteness
      (h_stmtIn := by
        apply Statement.of_fin_eq;
        simp only [Fin.castSucc_mk])
      (h_stmtOut := by
        apply Statement.of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_witIn := by
        apply Witness.of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_witOut := by
        apply Witness.of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_idxIn := by
        apply OracleStatement.idx_eq;
        simp only [Fin.castSucc_mk])
      (h_idxOut := by
        apply OracleStatement.idx_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq;
        simp only [Fin.castSucc_mk])
      (h_ostmtOut := by
        apply OracleStatement.heq_of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_relIn := by
        apply strictRoundRelation.of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_relOut := by
        apply strictRoundRelation.of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (impl := impl) (init := init)
    let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
      let fv: Fin ϑ := ⟨ϑ - 1, by
        have h := NeZero.one_le (n:=ϑ)
        exact Nat.sub_one_lt_of_lt h
      ⟩
      have h_eq: fv.val = ϑ - 1 := by rfl
      change ↑bIdx * ϑ + fv.val < ℓ + 0
      apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
    let h1_succ :  ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega
    exact foldCommitOracleReduction_perfectCompleteness 𝔽q β (mp := mp) (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := init) (impl := impl)
      (hCR := isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)
      (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩) (hInit := hInit)

/-! Perfect completeness for the last block -/
omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
lemma lastBlockOracleReduction_perfectCompleteness (_hInit : NeverFail init) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (oracleReduction := lastBlockOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)) := by
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  apply OracleReduction.castInOut_perfectCompleteness
    (h_stmtIn := by
      apply Statement.of_fin_eq;
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_stmtOut := by
      apply Statement.of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_witIn := by
      apply Witness.of_fin_eq -- ⊢ ⟨(ℓ / ϑ - 1) * ϑ + ↑0, ⋯⟩ = ⟨(ℓ / ϑ - 1) * ϑ, ⋯⟩
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_witOut := by
      apply Witness.of_fin_eq; -- ⊢ ⟨(ℓ / ϑ - 1) * ϑ + ↑(Fin.last ϑ), ⋯⟩ = Fin.last ℓ
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_idxIn := by
      apply OracleStatement.idx_eq;
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_idxOut := by
      apply OracleStatement.idx_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_ostmtIn := by
      apply OracleStatement.heq_of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_ostmtOut := by
      apply OracleStatement.heq_of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_Oₛᵢ := by
      apply instOracleStatementBinaryBasefold_heq_of_fin_eq
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_relIn := by
      apply strictRoundRelation.of_fin_eq
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_relOut := by
      apply strictRoundRelation.of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (impl := impl) (init := init)
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨bIdx * ϑ + i, by  apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let wit := fun i: Fin (ϑ + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let foldRelayRoundsPerfectCompleteness :=
    OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (oSpec := []ₒ) (m := ϑ)
    (Stmt := stmt)
    (OStmt := oStmt)
    (Wit := wit)
    (pSpec := fun i => pSpecFoldRelay (L:=L))
    (R := fun i => by
      have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
        lastBlockIdx_isNeCommitmentRound i
      exact foldRelayOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) (i:=⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) hNCR
    )
    (rel := fun i ↦
      strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        (⟨↑bIdx * ϑ + ↑i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩ : Fin (ℓ + 1)))
    (init := init) (impl := impl)
  apply foldRelayRoundsPerfectCompleteness
    (hP := fun _ => inferInstance)
    (hV := fun _ => Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
  intro (i : Fin ϑ) s
  have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
        lastBlockIdx_isNeCommitmentRound i
  let res := foldRelayOracleReduction_perfectCompleteness 𝔽q β (mp := mp) (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := pure s) (impl := impl)
    (hInit := by infer_instance)
    (i := ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) (hNCR := hNCR)
  exact res

/-! Perfect completeness for the core interaction oracle reduction -/
omit [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
theorem sumcheckFoldOracleReduction_perfectCompleteness (_hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (oracleReduction := sumcheckFoldOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
      (init := init)
      (impl := impl) := by
  unfold sumcheckFoldOracleReduction pSpecSumcheckFold
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let wit := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  apply OracleReduction.castInOut_perfectCompleteness
    (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (StmtIn₁ := stmt 0)
    (StmtIn₂ := Statement (L := L) (ℓ := ℓ) Context 0)
    (ιₛᵢ₁ := Fin (toOutCodewordsCount ℓ ϑ ⟨0 * ϑ, by omega⟩))
    (ιₛᵢ₂ := Fin (toOutCodewordsCount ℓ ϑ 0))
    (OStmtIn₁ := fun i => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨0 * ϑ, by omega⟩ i)
    (OStmtIn₂ := fun i => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 i)
    (WitIn₁ := wit 0)
    (WitIn₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (StmtOut₁ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (StmtOut₂ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (ιₛₒ₁ := Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (ιₛₒ₂ := Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (OStmtOut₁ := fun i => OracleStatement 𝔽q β ϑ (Fin.last ℓ) i)
    (OStmtOut₂ := fun i => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) i)
    (WitOut₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (WitOut₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (relIn₁ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) ⟨0 * ϑ, by omega⟩)
    (relIn₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) 0)
    (relOut₁ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) (Fin.last ℓ))
    (relOut₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) (Fin.last ℓ))
    (h_stmtIn := by
      apply Statement.of_fin_eq
      apply fin_zero_mul_eq)
    (h_stmtOut := by rfl)
    (h_witIn := by
      apply Witness.of_fin_eq
      apply fin_zero_mul_eq)
    (h_witOut := by rfl)
    (h_idxIn := by
      apply OracleStatement.idx_eq
      apply fin_zero_mul_eq)
    (h_idxOut := by rfl)
    (h_ostmtIn := by
      apply OracleStatement.heq_of_fin_eq
      apply fin_zero_mul_eq)
    (h_ostmtOut := by rfl)
    (h_Oₛᵢ := by
      apply instOracleStatementBinaryBasefold_heq_of_fin_eq
      ext; simp only [zero_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod])
    (h_relIn := by
      apply strictRoundRelation.of_fin_eq
      apply fin_zero_mul_eq)
    (h_relOut := by rfl)
    (impl := impl)
    (init := init)
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (V₁ := Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
    (V₂ := Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
    (hSeam := fun _ => Or.inl inferInstance)
    (rel₁ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) ⟨0 * ϑ, by omega⟩)
    (rel₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (rel₃ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) (Fin.last ℓ))
    (pSpec₁ := pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecLastBlock (L:=L) (ϑ:=ϑ))
    (R₁ := nonLastBlocksOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑))
    (R₂ := lastBlockOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑))
    (impl := impl)
    (init := init)
  · -- Perfect completeness of nonLastBlocksOracleReduction
    unfold nonLastBlocksOracleReduction
    apply OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
      (hP := fun _ => inferInstance)
      (hV := fun _ => Verifier.GuardedForm.ofEmpty _ (fun input =>
        (⟨0, fun _ => 0, input.1.ctx⟩, fun _ _ => 0)))
      (Stmt := fun i : Fin (ℓ / ϑ - 1 + 1) =>
        Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (OStmt := fun i : Fin (ℓ / ϑ - 1 + 1) =>
        OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (Wit := fun i : Fin (ℓ / ϑ - 1 + 1) =>
        Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
          ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (rel := fun i => strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (pSpec := fun (bIdx: Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β (ϑ:=ϑ) bIdx)
      (R := fun bIdx => nonLastSingleBlockOracleReduction (L:=L) 𝔽q β (mp := mp)
        (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (bIdx:=bIdx))
      (impl := impl)
      (init := init)
    intro bIdx s
    -- Prove perfectCompleteness for each individual block
    exact nonLastSingleBlockOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ) (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      (init := pure s) (impl := impl) (_hInit := by infer_instance) (bIdx:=bIdx)
  · -- Perfect completeness of lastBlockOracleReduction
    intro s
    exact lastBlockOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ) (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      (init := pure s) (impl := impl) (by infer_instance)

/-! RBR knowledge error for last block: seqCompose of foldRelay over ϑ rounds. -/
def lastBlockRbrKnowledgeError (k : (pSpecLastBlock (L := L) (ϑ := ϑ)).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨(ℓ / ϑ - 1) * ϑ + ij.1, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ ij.1⟩ ij.2

/-! RBR KS for last block verifier (seqCompose of foldRelay then castInOut). -/
omit [DecidableEq 𝔽q] in
theorem lastBlockOracleVerifier_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness init impl
      (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) ⟨(ℓ / ϑ - 1) * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (lastBlockOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (rbrKnowledgeError := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  apply OracleVerifier.castInOut_rbrKnowledgeSoundness
    (relIn₁ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) ⟨(ℓ / ϑ - 1) * ϑ + (0 : Fin (ϑ + 1)), by
        apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (relOut₁ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      ⟨(ℓ / ϑ - 1) * ϑ + (Fin.last ϑ : Fin (ϑ + 1)), by
        apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=ϑ) (hx:=by omega)⟩)
    (h_stmtIn := by
      apply Statement.of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_stmtOut := by
      apply Statement.of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Fin.val_last, Nat.sub_mul]
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]
      omega)
    (h_idxIn := by
      apply OracleStatement.idx_eq
      apply Fin.eq_of_val_eq
      simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_idxOut := by
      apply OracleStatement.idx_eq
      apply Fin.eq_of_val_eq
      simp only [Fin.val_last, Nat.sub_mul]
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]
      omega)
    (h_ostmtIn := by
      apply OracleStatement.heq_of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_ostmtOut := by
      apply OracleStatement.heq_of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Fin.val_last, Nat.sub_mul]
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]
      omega)
    (h_witIn := by rfl)
    (h_witOut := by
      apply Witness.of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Fin.val_last, Nat.sub_mul]
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]
      omega)
    (h_Oₛᵢ := by
      apply instOracleStatementBinaryBasefold_heq_of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_relIn := by
      apply roundRelation.of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_relOut := by
      apply roundRelation.of_fin_eq
      apply Fin.eq_of_val_eq
      simp only [Fin.val_last, Nat.sub_mul]
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]
      omega)
    (ε := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ:=ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨bIdx * ϑ + i, by  apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let foldRelayRoundsRbrKnowledgeSoundness := OracleVerifier.seqCompose_rbrKnowledgeSoundness
    (oSpec := []ₒ) (m := ϑ)
    (Stmt := stmt)
    (OStmt := oStmt)
    (pSpec := fun i => pSpecFoldRelay (L:=L))
    (V := fun i => by
      have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
        lastBlockIdx_isNeCommitmentRound i
      exact foldRelayOracleVerifier (L:=L) 𝔽q β (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ hNCR
    )
    (rel := fun i ↦
      roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        (⟨↑bIdx * ϑ + ↑i, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩ : Fin (ℓ + 1)))
    (rbrKnowledgeError := fun i =>
      foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩)
    (init := init) (impl := impl)
  have hCur :
      OracleVerifier.rbrKnowledgeSoundness init impl
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
          ⟨bIdx * ϑ + (0 : Fin (ϑ + 1)), by
            apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
          ⟨bIdx * ϑ + (Fin.last ϑ : Fin (ϑ + 1)), by
            apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=ϑ) (hx:=by omega)⟩)
        (OracleVerifier.seqCompose stmt oStmt (fun i => by
          have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
            lastBlockIdx_isNeCommitmentRound i
          exact foldRelayOracleVerifier (L:=L) 𝔽q β (mp := mp)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
            ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ hNCR))
        (fun combinedIdx =>
          let ij := seqComposeChallengeIdxToSigma combinedIdx
          foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ⟨bIdx * ϑ + ij.1, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ ij.1⟩ ij.2) := by
    apply foldRelayRoundsRbrKnowledgeSoundness
    intro (i : Fin ϑ)
    have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
      lastBlockIdx_isNeCommitmentRound i
    exact foldRelayOracleVerifier_rbrKnowledgeSoundness (L := L) 𝔽q β (ϑ := ϑ) (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (init := init) (impl := impl)
      (i := ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) hNCR
  exact OracleVerifier.rbrKnowledgeSoundness_of_eq_error (h := hCur) (h_ε := by
    intro k
    simp only [lastBlockRbrKnowledgeError, ChallengeIdx, Fin.vappend_zero, bIdx])

/-! The commitment-round index inside a non-last block. -/
def nonLastSingleBlockCommitIdx (bIdx : Fin (ℓ / ϑ - 1)) : Fin ℓ :=
  ⟨bIdx * ϑ + (ϑ - 1), by
    let fv : Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n := ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    change bIdx.val * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  ⟩

/-! RBR knowledge error for the fold-relay prefix inside one non-last block. -/
def nonLastSingleBlockFoldRelayRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1))
    (k : (pSpecFoldRelaySequence (L := L) (n := ϑ - 1)).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨bIdx * ϑ + ij.1, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx ij.1⟩ ij.2

/-! RBR knowledge error for one non-last block (fold-relay prefix + fold-commit suffix). -/
def nonLastSingleBlockRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1))
    (k : (pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (nonLastSingleBlockFoldRelayRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx))
    (ChallengeIdx.sumEquiv.symm k)

/-! RBR KS for one non-last block verifier. -/
omit [DecidableEq 𝔽q] in
theorem nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness
    (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) bIdx).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ) (h₁:=by
            change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          ) (by omega)
        ⟩)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (rbrKnowledgeError := nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) := by
  classical
  unfold nonLastSingleBlockOracleVerifier nonLastSingleBlockRbrKnowledgeError
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
    (rel₂ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      ⟨bIdx * ϑ + (ϑ - 1), by
        let fv: Fin ϑ := ⟨ϑ - 1, by
          have h := NeZero.one_le (n:=ϑ)
          exact Nat.sub_one_lt_of_lt h
        ⟩
        change ↑bIdx * ϑ + fv.val < ℓ + 1
        apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=1)
      ⟩)
    (rel₃ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
    (rbrKnowledgeError₁ := nonLastSingleBlockFoldRelayRbrKnowledgeError (L := L) 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (rbrKnowledgeError₂ := foldCommitKnowledgeError 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx))
  · let stmt : Fin (ϑ - 1 + 1) → Type :=
      fun i => Statement (L := L) (ℓ := ℓ) Context
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let oStmt := fun i: Fin (ϑ - 1 + 1) =>
      OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let hSeq := OracleVerifier.seqCompose_rbrKnowledgeSoundness
      (oSpec := []ₒ) (m := ϑ - 1)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun _ => pSpecFoldRelay (L:=L))
      (V := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
          isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
        exact foldRelayOracleVerifier (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑:=𝓑) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ hNCR
      )
      (rel := fun i ↦
        roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
          (⟨↑bIdx * ϑ + ↑i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩ : Fin (ℓ + 1)))
      (rbrKnowledgeError := fun i =>
        foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩)
      (init := init) (impl := impl)
    have hSeq' := hSeq (by
      intro i
      have hNCR : ¬ isCommitmentRound ℓ ϑ
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
        isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
      exact foldRelayOracleVerifier_rbrKnowledgeSoundness (L := L) 𝔽q β (ϑ := ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (init := init) (impl := impl)
        (i := ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) hNCR
    )
    exact OracleVerifier.rbrKnowledgeSoundness_of_eq_error (h := by
      dsimp [OracleVerifier.castOutSimple]
      exact hSeq') (h_ε := by
      intro k
      unfold nonLastSingleBlockFoldRelayRbrKnowledgeError
      rfl)
  · have h_ϑ_gt_zero : ϑ > 0 := Nat.pos_of_neZero ϑ
    have h_idxOut_eq :
        (nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx).succ =
          (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ + 1)) := by
      ext
      change (bIdx.val * ϑ + (ϑ - 1)) + 1 = (bIdx.val + 1) * ϑ
      rw [Nat.add_assoc, Nat.sub_add_cancel (NeZero.one_le (n := ϑ))]
      rw [Nat.add_mul, Nat.one_mul]
    apply OracleVerifier.castInOut_rbrKnowledgeSoundness
      (h_stmtIn := by
        apply Statement.of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_stmtOut := by
        apply Statement.of_fin_eq
        exact h_idxOut_eq)
      (h_idxIn := by
        apply OracleStatement.idx_eq
        simp only [Fin.castSucc_mk])
      (h_idxOut := by
        apply OracleStatement.idx_eq
        exact h_idxOut_eq)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_ostmtOut := by
        apply OracleStatement.heq_of_fin_eq
        exact h_idxOut_eq)
      (h_witIn := by
        rfl)
      (h_witOut := by
        apply Witness.of_fin_eq
        exact h_idxOut_eq)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_relIn := by
        apply roundRelation.of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_relOut := by
        apply roundRelation.of_fin_eq
        exact h_idxOut_eq)
      (ε := foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx))
    exact foldCommitOracleVerifier_rbrKnowledgeSoundness (L := L) 𝔽q β (ϑ := ϑ) (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (init := init) (impl := impl)
      (i := nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx)
      (hCR := isCommitmentRoundOfNonLastBlock (r:=r) (𝓡:=𝓡) bIdx)

/-! RBR knowledge error for non-last blocks: seqCompose over non-last blocks. -/
def nonLastBlocksRbrKnowledgeError
    (k : (pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) :
    ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ij.1 ij.2

/-! RBR KS for non-last blocks verifier (seqCompose of nonLastSingleBlock). -/
omit [DecidableEq 𝔽q] in
theorem nonLastBlocksOracleVerifier_rbrKnowledgeSoundness :
    (nonLastBlocksOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) ⟨0 * ϑ, by omega⟩)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (rbrKnowledgeError := nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  unfold nonLastBlocksOracleVerifier nonLastBlocksRbrKnowledgeError
  simp only
  refine OracleVerifier.seqCompose_rbrKnowledgeSoundness
    (oSpec := []ₒ)
    (Stmt := fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (OStmt := fun i =>
      OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (pSpec := fun (bIdx : Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (V := fun bIdx => nonLastSingleBlockOracleVerifier (L := L) 𝔽q β (mp := mp) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) bIdx)
    (rel := fun i => roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
    (rbrKnowledgeError := fun bIdx =>
      nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (init := init) (impl := impl) ?_
  intro bIdx
  exact nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness (L := L) 𝔽q β (ϑ := ϑ)
    (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (init := init) (impl := impl) bIdx

/-! RBR knowledge error for sumcheck-fold: append of non-last blocks and last block. -/
def sumcheckFoldKnowledgeError (j : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (g := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm j)

/-! Round-by-round knowledge soundness for the sumcheck fold oracle verifier.
    Proof: append (nonLastBlocks, lastBlock) has RBR KS by append_rbrKnowledgeSoundness;
    then castInOut preserves it; finally rbrKnowledgeSoundness_of_eq_error gives the flat
    sumcheckFoldKnowledgeError. The error equality (flat = Sum.elim form) remains. -/
omit [DecidableEq 𝔽q] in
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    (sumcheckFoldOracleVerifier 𝔽q β (mp := mp) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0 )
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ) )
      (rbrKnowledgeError := sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  unfold sumcheckFoldOracleVerifier pSpecSumcheckFold
  have hAppend := OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      ⟨0 * ϑ, by omega⟩)
    (rel₂ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (rel₃ := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
    (V₁ := nonLastBlocksOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (V₂ := lastBlockOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (rbrKnowledgeError₁ := nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rbrKnowledgeError₂ := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (h₁ := by
      exact nonLastBlocksOracleVerifier_rbrKnowledgeSoundness (L := L) 𝔽q β
        (ϑ := ϑ) (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (init := init) (impl := impl))
    (h₂ := by
      exact lastBlockOracleVerifier_rbrKnowledgeSoundness (L := L) 𝔽q β
        (ϑ := ϑ) (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (init := init) (impl := impl))
  apply OracleVerifier.castInOut_rbrKnowledgeSoundness
    (h_stmtIn := by
      apply Statement.of_fin_eq
      apply fin_zero_mul_eq)
    (h_stmtOut := by rfl)
    (h_idxIn := by
      apply OracleStatement.idx_eq
      apply fin_zero_mul_eq)
    (h_idxOut := by rfl)
    (h_ostmtIn := by
      apply OracleStatement.heq_of_fin_eq
      apply fin_zero_mul_eq)
    (h_ostmtOut := by rfl)
    (h_witIn := by
      apply Witness.of_fin_eq
      apply fin_zero_mul_eq)
    (h_witOut := by rfl)
    (h_Oₛᵢ := by
      apply instOracleStatementBinaryBasefold_heq_of_fin_eq
      ext
      simp only [zero_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod])
    (h_relIn := by
      apply roundRelation.of_fin_eq
      apply fin_zero_mul_eq)
    (h_relOut := by rfl)
    (ε := sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (hRbrKs := hAppend)

end SecurityProps

end IteratedSumcheckFoldComposition
end ComponentReductions


end

end Binius.BinaryBasefold.CoreInteraction
