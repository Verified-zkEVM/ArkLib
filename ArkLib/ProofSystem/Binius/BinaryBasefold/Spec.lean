/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

namespace Binius.BinaryBasefold

/-! ## Protocol Specs for Binary Basefold
This module contains the protocol specs, oracle index bounds,
instances of OracleInterface and SampleableType for the Binary Basefold protocol.
-/

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial AdditiveNTT
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
variable [hdiv : Fact (ϑ ∣ ℓ)]

section IndexBounds
-- TODO: need a main lemma for bounds involving last bIdx = (ℓ / ϑ - 1)
@[simp]
lemma lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x : ℕ) {hx : x ≤ ϑ} :
    (ℓ / ϑ - 1) * ϑ + x < ℓ + 1 := by
  have h_div : ℓ = (ℓ / ϑ) * ϑ := (Nat.div_mul_cancel hdiv.out).symm
  have h_ge_one : 1 ≤ ℓ / ϑ := by
    have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
    rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
  -- We have (ℓ / ϑ - 1) * ϑ + x ≤ (ℓ / ϑ - 1) * ϑ + ϑ = ℓ - ϑ + ϑ = ℓ
  have h_le_ℓ : (ℓ / ϑ - 1) * ϑ + x ≤ ℓ := by
    calc
      (ℓ / ϑ - 1) * ϑ + x ≤ (ℓ / ϑ - 1) * ϑ + ϑ := by gcongr
      _ = ℓ / ϑ * ϑ - ϑ + ϑ := by rw [Nat.sub_mul, Nat.one_mul]
      _ = ℓ / ϑ * ϑ := by
        rw [Nat.sub_add_cancel]
        have h_le: ϑ ≤ ℓ / ϑ * ϑ := by
          rw [Nat.div_mul_cancel hdiv.out]
          apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ)
          exact hdiv.out
        exact h_le
      _ = ℓ := Nat.div_mul_cancel hdiv.out
  omega

@[simp]
lemma lastBlockIdx_mul_ϑ_add_fin_lt_ℓ (i : Fin ϑ) :
    (ℓ / ϑ - 1) * ϑ + ↑i < ℓ := by
  have h_div : ℓ = (ℓ / ϑ) * ϑ := (Nat.div_mul_cancel hdiv.out).symm
  have h_ge_one : 1 ≤ ℓ / ϑ := by
    have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
    rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
  -- Since i < ϑ, we have (ℓ/ϑ - 1) * ϑ + i < (ℓ/ϑ - 1) * ϑ + ϑ = ℓ - ϑ + ϑ = ℓ
  calc
    (ℓ / ϑ - 1) * ϑ + ↑i < (ℓ / ϑ - 1) * ϑ + ϑ := by
      gcongr; exact i.isLt
    _ = ℓ / ϑ * ϑ - ϑ + ϑ := by rw [Nat.sub_mul, Nat.one_mul]
    _ = ℓ / ϑ * ϑ := by
      rw [Nat.sub_add_cancel]
      have h_le: ϑ ≤ ℓ / ϑ * ϑ := by
        rw [Nat.div_mul_cancel hdiv.out]
        apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ)
        exact hdiv.out
      exact h_le
    _ = ℓ := Nat.div_mul_cancel hdiv.out

omit [NeZero r] [NeZero 𝓡] in
lemma isNeCommitmentRound (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x < ϑ - 1} :
    ¬isCommitmentRound ℓ ϑ ⟨↑bIdx * ϑ + x, by
      conv_rhs => rw [←Nat.add_zero (n:=ℓ)]
      change bIdx.val * ϑ + (⟨x, by omega⟩: Fin ϑ).val < ℓ + 0
      apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0)
    ⟩ := by
  unfold isCommitmentRound
  let fin_val : Fin ℓ := ⟨↑bIdx * ϑ + x, by
    conv_rhs => rw [←Nat.add_zero (n:=ℓ)]
    change bIdx.val * ϑ + (⟨x, by omega⟩: Fin ϑ).val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0)
  ⟩
  generalize hA : (fin_val.val + 1) = val
  set k := fin_val.val + 1 with hk
  have hNeDiv: ¬(ϑ ∣ val) := by
    have hv: val = bIdx * ϑ + x + 1 := by rw [hA.symm, hk]
    rw [hv]
    have hleft: ↑bIdx * ϑ + x + 1 > ϑ * (bIdx) := by rw [Nat.mul_comm ϑ]; omega
    have hRight : ↑bIdx * ϑ + x + 1 < ϑ * (bIdx + 1) := by rw [Nat.mul_comm ϑ, Nat.add_mul]; omega
    refine (Nat.not_dvd_iff_lt_mul_succ (↑bIdx * ϑ + x + 1) ?_).mpr ?_
    · exact Nat.pos_of_neZero ϑ
    · use (bIdx.val)
  simp only [hNeDiv, ne_eq, false_and, not_false_eq_true]

lemma lastBlockIdx_isNeCommitmentRound (i : Fin ϑ) :
    ¬isCommitmentRound ℓ ϑ ⟨(ℓ / ϑ - 1) * ϑ + ↑i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ := by
  unfold isCommitmentRound
  let fin_val : Fin ℓ := ⟨(ℓ / ϑ - 1) * ϑ + ↑i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
  generalize hA : (fin_val.val + 1) = val
  set k := fin_val.val + 1 with hk
  -- ϑ ≤ ℓ / ϑ * ϑ
  have h_div_mul: ℓ / ϑ * ϑ = ℓ := by
    refine Nat.div_mul_cancel ?_
    exact hdiv.out
  have h_le: ϑ ≤ ℓ := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ)
    exact hdiv.out
  by_cases hi: i < ϑ - 1
  · have hNeDiv: ¬(ϑ ∣ val) := by
      have hv: val = (ℓ / ϑ - 1) * ϑ + ↑i + 1 := by rw [hA.symm, hk]
      rw [hv]
      have hleft: (ℓ / ϑ - 1) * ϑ < (ℓ / ϑ - 1) * ϑ + ↑i + 1 := by omega
      have hright: (ℓ / ϑ - 1) * ϑ + ↑i + 1 ≤ (ℓ / ϑ - 1 + 1) * ϑ := by
        conv_rhs => rw [Nat.add_mul, Nat.one_mul]
        conv_lhs => rw[Nat.add_assoc]
        gcongr; omega
      refine (Nat.not_dvd_iff_lt_mul_succ ((ℓ / ϑ - 1) * ϑ + ↑i + 1) ?_).mpr ?_
      · exact Nat.pos_of_neZero ϑ
      · use (ℓ / ϑ - 1)
        constructor
        · rw [Nat.mul_comm]; exact hleft
        · rw [Nat.mul_comm]; conv_rhs => rw [Nat.mul_add, Nat.mul_one]
          conv_lhs => rw [Nat.add_assoc]
          gcongr; omega
    simp only [hNeDiv, ne_eq, false_and, not_false_eq_true]
  · have h_val_eq_ℓ: val = ℓ := by
      rw [hA.symm, hk]
      simp only [fin_val]
      have hi_eq: i = ϑ - 1 := by omega
      rw [hi_eq, Nat.sub_mul, Nat.one_mul,
        Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by rw [h_div_mul]; exact h_le)]
      have h_sub: ϑ - (ϑ - 1) = 1 := by omega
      rw [h_sub, Nat.sub_add_cancel (by omega)]; exact h_div_mul
    simp only [h_val_eq_ℓ, ne_eq, not_true_eq_false, and_false, not_false_eq_true]

@[simp]
lemma blockIdx_mul_ϑ_lt_ℓ_succ (i : Fin (ℓ / ϑ - 1 + 1)) : ↑i * ϑ < ℓ + 1 := by
  have h_ge: ϑ ≤ ℓ := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ)
    exact hdiv.out
  have h_div_ge_1: ℓ/ϑ ≥ 1 := by
    change 1 ≤ ℓ/ϑ
    apply Nat.one_le_div_iff (hb:=by exact Nat.pos_of_neZero ϑ).mpr (by exact h_ge)
  have hi := i.isLt
  have h_eq: ℓ / ϑ - 1 + 1 = ℓ/ϑ := by omega
  have h_i_lt : ↑i < ℓ / ϑ := by omega
  -- Now ↑i * ϑ ≤ (ℓ / ϑ - 1) * ϑ < ℓ
  calc
    ↑i * ϑ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
    _ < ℓ := by
      -- (ℓ / ϑ - 1) * ϑ = ℓ / ϑ * ϑ - ϑ = ℓ - ϑ < ℓ
      have h_div : ℓ = (ℓ / ϑ) * ϑ := (Nat.div_mul_cancel hdiv.out).symm
      rw [Nat.sub_mul, Nat.one_mul]
      conv_lhs => rw [←h_div]
      have h_pos : 0 < ϑ := Nat.pos_of_neZero ϑ
      omega
    _ < ℓ + 1 := by omega

omit [NeZero r] [NeZero 𝓡] in
lemma isCommitmentRoundOfNonLastBlock (bIdx : Fin (ℓ / ϑ - 1)) :
    isCommitmentRound ℓ ϑ ⟨↑bIdx * ϑ + (ϑ - 1), by
      have hpos: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
      conv_rhs => rw [←Nat.add_zero (n:=ℓ)]
      change bIdx.val * ϑ + (⟨ϑ - 1, by omega⟩: Fin ϑ).val < ℓ + 0
      apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0)
    ⟩ := by
  unfold isCommitmentRound
  simp only [ne_eq] -- ⊢ ϑ ∣ ↑bIdx * ϑ + (ϑ - 1) + 1 ∧ ¬↑bIdx * ϑ + (ϑ - 1) + 1 = ℓ
  have h_eq: ↑bIdx * ϑ + (ϑ - 1) + 1 = (↑bIdx + 1) * ϑ := by
    rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le)];
    conv_lhs => enter [2]; rw [←Nat.one_mul (n:=ϑ)]
    rw [←Nat.add_mul];

  have hdivLe: ϑ ∣ ↑bIdx * ϑ + (ϑ - 1) + 1 := by
    rw [h_eq]
    exact Nat.dvd_mul_left ϑ (↑bIdx + 1)
  have h_lt: ↑bIdx * ϑ + (ϑ - 1) + 1 < ℓ := by
    rw [h_eq] -- ⊢ (↑bIdx + 1) * ϑ < ℓ
    calc
      (↑bIdx + 1) * ϑ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
      _ = ℓ - ϑ := by
        have h_bound : 1 ≤ ℓ / ϑ := by
          have h_le: ϑ ≤ ℓ := by
            apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
          rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
        rw [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
      _ < ℓ := by exact rounds_sub_steps_lt
  have h_ne_eq: ¬↑bIdx * ϑ + (ϑ - 1) + 1 = ℓ := by exact Nat.ne_of_lt h_lt
  exact Decidable.not_imp_iff_and_not.mp fun a ↦ h_ne_eq (a hdivLe)
end IndexBounds

section Pspec
-- Step-level reductions
@[reducible]
def pSpecFold (d : ℕ := 2) : ProtocolSpec 2 :=
  ⟨![Direction.P_to_V, Direction.V_to_P], ![L⦃≤ d⦄[X], L]⟩

-- Conditional 1-message protocol (only for commitment rounds)
@[reducible]
def pSpecCommit (i : Fin ℓ) : ProtocolSpec 1 :=
  ⟨![Direction.P_to_V],
   ![OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val + 1, by omega⟩]⟩

@[reducible]
def pSpecRelay : ProtocolSpec 0 := ⟨![], ![]⟩ -- relOut relay step

def pSpecFinalSumcheckStep : ProtocolSpec 1 := ⟨![Direction.P_to_V], ![L]⟩

-- Round-level reductions
@[reducible]
def pSpecFoldCommit (i : Fin ℓ) (d : ℕ := 2) : ProtocolSpec (3) :=
  pSpecFold (L:=L) (d := d) ++ₚ pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

@[reducible]
def pSpecFoldRelay (d : ℕ := 2) : ProtocolSpec (2) :=
  pSpecFold (L:=L) (d := d) ++ₚ pSpecRelay

-- Round-segment-level reductions
def pSpecFoldRelaySequence (n : ℕ) (d : ℕ := 2) :=
  ProtocolSpec.seqCompose fun (_: Fin n) ↦ pSpecFoldRelay (L:=L) (d := d)
-- Block-level reductions

/-- A non-last block consists of `(ϑ-1)` fold-relay round and `1` fold-commit round -/
def pSpecFullNonLastBlock (bIdx : Fin (ℓ / ϑ - 1)) (d : ℕ := 2) :=
  (pSpecFoldRelaySequence (L:=L) (n:=ϑ - 1) (d := d) ++ₚ
      pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨↑bIdx * ϑ + (ϑ - 1), by
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ bIdx (m:=0)
            (i:=⟨ϑ - 1, by exact ϑ_sub_one_le_self⟩)⟩ (d := d))

/-- The last block consists of `ϑ` fold-relay rounds -/
def pSpecLastBlock (d : ℕ := 2) := pSpecFoldRelaySequence (L:=L) (n:=ϑ) (d := d)

/-- A sequence of `(ℓ / ϑ - 1)` non-last blocks -/
def pSpecNonLastBlocks (d : ℕ := 2) := seqCompose fun bIdx ↦
  pSpecFullNonLastBlock 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx (d := d)

-- Protocol-level reductions
/-- The final `CoreInteraction` consists of `(ℓ / ϑ - 1)` non-last blocks and `1` last block -/
def pSpecSumcheckFold (d : ℕ := 2) :=
  (pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)) ++ₚ
  (pSpecLastBlock (L:=L) (ϑ:=ϑ) (d := d))

-- Complete protocol
def pSpecCoreInteraction (d : ℕ := 2) :=
  (pSpecSumcheckFold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)) ++ₚ
  (pSpecFinalSumcheckStep (L:=L))

/-- The protocol specification for the query phase.
V sends all γ challenges v₁, ..., v_γ ← B_{ℓ+R} to P. -/
def pSpecQuery : ProtocolSpec 1 :=
  ⟨![Direction.V_to_P],
    ![Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0]⟩
  -- Round 0: constant c, Round 1: all γ challenges

@[reducible]
def fullPSpec := (pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ++ₚ
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-! ## Oracle Interface instances for Messages-/

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecFold (L:=L) d).Message j)
    -- this covers .Message and .Challenge
  | ⟨0, h⟩ => by exact OracleInterface.instDefault -- h_i(X) polynomial
  | ⟨1, _⟩ => by exact OracleInterface.instDefault -- challenge r'_i

instance : ∀ j, OracleInterface ((pSpecRelay).Message j)
  | ⟨x, h⟩ => by exact x.elim0

instance {i : Fin ℓ} :
    ∀ j, OracleInterface ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message j)
  | ⟨0, _⟩ => by exact OracleInterface.instDefault -- oracle commitment (conditional)

instance : ∀ j, OracleInterface ((pSpecRelay).Message j)
  | ⟨x, hj⟩ => by exact x.elim0

instance {i : Fin ℓ} {d : ℕ} :
    ∀ j, OracleInterface ((pSpecFoldCommit 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (d := d)).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := pSpecFold (L := L) (d := d))
    (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecFoldRelay (L:=L) (d := d)).Message j) :=
  instOracleInterfaceMessageAppend

instance {i : Fin ℓ} {d : ℕ} :
    ∀ j, OracleInterface ((pSpecFoldCommit 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (d := d)).Message j) :=
  instOracleInterfaceMessageAppend

instance {n d : ℕ} :
    ∀ j, OracleInterface ((pSpecFoldRelaySequence (L:=L) n (d := d)).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance {bIdx : Fin (ℓ / ϑ - 1)} {d : ℕ} : ∀ j, OracleInterface ((pSpecFullNonLastBlock 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx (d := d)).Message j) :=
  instOracleInterfaceMessageAppend

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecLastBlock (L:=L) (ϑ:=ϑ)
    (d := d)).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)).Message j) := instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecFinalSumcheckStep (L:=L)).Message i)
  | ⟨0, _⟩ => by exact OracleInterface.instDefault

instance {d : ℕ} : ∀ i, OracleInterface ((pSpecCoreInteraction 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)).Message i) := instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i) := fun _ => OracleInterface.instDefault

instance : ∀ j, OracleInterface ((fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message j) := instOracleInterfaceMessageAppend

-- Oracle Interface instances for Ostmt
instance instOracleStatementBinaryBasefold {i : Fin (ℓ + 1)} :
    ∀ j, OracleInterface (OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j) :=
  fun j => {
    Query := (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨j.val * ϑ, by
      calc j.val * ϑ < ℓ := by exact toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j
      _ < r := by omega⟩
    toOC.spec := fun _ => L
    toOC.impl := fun queryPoint => do return (← read) queryPoint
  }

/-! ## SampleableType instances -/

instance {i : Fin ℓ} : ∀ j, SampleableType ((pSpecCommit 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)
  | ⟨0, hj⟩ => by nomatch hj

instance {d : ℕ} : ∀ j, SampleableType ((pSpecFold (L:=L) d).Challenge j)
  | ⟨j, hj⟩ => by
    dsimp [pSpecFold, Challenge]
    -- Only message 1 (index 1) has challenges, which are of type L
    -- From pSpec definition: dir = ![Direction.P_to_V, Direction.V_to_P, Direction.P_to_V]
    -- So only index 1 has Direction.V_to_P, which means i = 1
    have h_i_eq_1 : j = 1 := by
      -- Since i is in ChallengeIdx, we know pSpec.dir i = Direction.V_to_P
      -- From the pSpec definition, only index 1 has Direction.V_to_P
      have h_dir := hj
      dsimp [pSpecFold] at h_dir
      -- h_dir : ![Direction.P_to_V, Direction.V_to_P, Direction.P_to_V] i = Direction.V_to_P
      -- This forces i = 1 since only index 1 has V_to_P direction
      cases j using Fin.cases
      case zero => simp at h_dir
      case succ j1 =>
        cases j1 using Fin.cases
        case zero => rfl
        case succ k => exact k.elim0 (α := k.succ.succ = 1)
    rw [h_i_eq_1]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    infer_instance

instance : ∀ j, SampleableType ((pSpecRelay).Challenge j)
  | ⟨x, hj⟩ => by exact x.elim0

instance {d : ℕ} : ∀ j, SampleableType ((pSpecFoldRelay (L:=L) (d := d)).Challenge j) :=
  instSampleableTypeChallengeAppend

instance {i : Fin ℓ} {d : ℕ} : ∀ j, SampleableType ((pSpecFoldCommit 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (d := d)).Challenge j) :=
  instSampleableTypeChallengeAppend

instance {n d : ℕ} : ∀ j, SampleableType ((pSpecFoldRelaySequence (L:=L) n
    (d := d)).Challenge j) :=
  instSampleableTypeChallengeSeqCompose

instance {i : Fin (ℓ / ϑ - 1)} {d : ℕ} : ∀ j, SampleableType ((pSpecFullNonLastBlock
  𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (d := d)).Challenge j) :=
  instSampleableTypeChallengeAppend

instance {d : ℕ} : ∀ i, SampleableType ((pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)).Challenge i) :=
  instSampleableTypeChallengeSeqCompose

instance {d : ℕ} : ∀ i, SampleableType ((pSpecLastBlock (L:=L) (ϑ:=ϑ)
    (d := d)).Challenge i) :=
  instSampleableTypeChallengeSeqCompose

instance {d : ℕ} : ∀ i, SampleableType ((pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType ((pSpecFinalSumcheckStep (L:=L)).Challenge i)
  | ⟨0, _⟩ => by (expose_names; exact inst_5)

instance {d : ℕ} : ∀ i, SampleableType ((pSpecCoreInteraction 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (d := d)).Challenge i) :=
  instSampleableTypeChallengeAppend

/-- SampleableType instance for sDomain, constructed via its equivalence with a Fin type. -/
instance instSDomain {i : Fin r} (h_i : i < ℓ + 𝓡) :
    SampleableType (sDomain 𝔽q β h_ℓ_add_R_rate i) :=
  let T := sDomain 𝔽q β h_ℓ_add_R_rate i
  haveI : Fintype T := fintype_sDomain 𝔽q β h_ℓ_add_R_rate i
  haveI : Nonempty T := ⟨0⟩
  haveI : DecidableEq T := Classical.decEq T
  SampleableType.ofEquiv (e := (sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate i (by omega)).symm)

instance : ∀ i, SampleableType ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i)
  | ⟨i, hi⟩ => by
    unfold ProtocolSpec.Challenge
    simp only [pSpecQuery]
    have h_i: i = 0 := by omega
    rw [h_i]
    simp only [Fin.isValue, Matrix.cons_val_fin_one]
    letI : SampleableType (sDomain 𝔽q β h_ℓ_add_R_rate 0) := by
      apply instSDomain;
      have h_ℓ_gt_0 : ℓ > 0 := by exact Nat.pos_of_neZero ℓ
      exact Nat.lt_add_right 𝓡 h_ℓ_gt_0
    exact instSampleableTypeFinFunc

instance : ∀ j, SampleableType ((fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) := instSampleableTypeChallengeAppend

end Pspec

end
end Binius.BinaryBasefold
