/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
import ArkLib.ToVCVio.Oracle

namespace Binius.BinaryBasefold

/-! ## Protocol Specs for Binary Basefold

This module defines the protocol specs, index bounds, and the following instance types:

- **Protocol specs**: `pSpecFold`, `pSpecCommit`, `pSpecRelay`, `pSpecFoldCommit`, `pSpecFoldRelay`,
  `pSpecFoldRelaySequence`, `pSpecFullNonLastBlock`, `pSpecLastBlock`, `pSpecNonLastBlocks`,
  `pSpecSumcheckFold`, `pSpecFinalSumcheckStep`, `pSpecCoreInteraction`, `pSpecQuery`, `fullPSpec`.

- **OracleInterface**: For every `(pSpec ...).Message j` and `(pSpec ...).Challenge j` in the
  protocol, and for `OracleStatement`. Challenge oracles use
  `ProtocolSpec.challengeOracleInterface`.

- **SampleableType**: For all challenge types and for commitment-round message types; also for
  `sDomain` and query-phase messages.

- **OracleSpec.Inhabited**: For `[]ₒ`, `[OracleStatement ... i]ₒ`, and `[(pSpec ...).Message]ₒ` for
  every pSpec above (message oracle specs).

- **OracleSpec.Fintype**: For `[]ₒ`, and for various `[pSpec.Message]ₒ` and
  `[pSpec.Challenge]ₒ` specs.

- **Fintype / Inhabited**: For individual `(pSpec ...).Challenge i` and
  `(pSpec ...).Message i` types where needed.

**NOTE**: For `∀ i, OracleInterface ((pSpec ...).Challenge i)`, use
  `ProtocolSpec.challengeOracleInterface` to avoid conflict.
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
variable {𝓑 : Fin 2 ↪ L}
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
def pSpecFold : ProtocolSpec 2 := ⟨![Direction.P_to_V, Direction.V_to_P], ![L⦃≤ 2⦄[X], L]⟩

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
def pSpecFoldCommit (i : Fin ℓ) : ProtocolSpec (3) :=
  pSpecFold (L:=L) ++ₚ pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

@[reducible]
def pSpecFoldRelay : ProtocolSpec (2) :=
  pSpecFold (L:=L) ++ₚ pSpecRelay

@[reducible]
-- Round-segment-level reductions
def pSpecFoldRelaySequence (n : ℕ) :=
  ProtocolSpec.seqCompose fun (_: Fin n) ↦ pSpecFoldRelay (L:=L)
-- Block-level reductions

/-- A non-last block consists of `(ϑ-1)` fold-relay round and `1` fold-commit round -/
@[reducible]
def pSpecFullNonLastBlock (bIdx : Fin (ℓ / ϑ - 1)) :=
  (pSpecFoldRelaySequence (L:=L) (n:=ϑ - 1) ++ₚ
      pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨↑bIdx * ϑ + (ϑ - 1), by
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ bIdx (m:=0) (i:=⟨ϑ - 1, by exact ϑ_sub_one_le_self⟩)⟩)

/-- The last block consists of `ϑ` fold-relay rounds -/
@[reducible]
def pSpecLastBlock := pSpecFoldRelaySequence (L:=L) (n:=ϑ)

/-- A sequence of `(ℓ / ϑ - 1)` non-last blocks -/
@[reducible]
def pSpecNonLastBlocks := seqCompose fun bIdx ↦
  pSpecFullNonLastBlock 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx

-- Protocol-level reductions
/-- The final `CoreInteraction` consists of `(ℓ / ϑ - 1)` non-last blocks and `1` last block -/
@[reducible]
def pSpecSumcheckFold := (pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ++ₚ
  (pSpecLastBlock (L:=L) (ϑ:=ϑ))

-- Complete protocol
@[reducible]
def pSpecCoreInteraction := (pSpecSumcheckFold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ++ₚ
  (pSpecFinalSumcheckStep (L:=L))

/-- The protocol specification for the query phase.
V sends all γ challenges v₁, ..., v_γ ← B_{ℓ+R} to P. -/
@[reducible]
def pSpecQuery : ProtocolSpec 1 :=
  ⟨![Direction.V_to_P],
    ![Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0]⟩
  -- Round 0: constant c, Round 1: all γ challenges

@[reducible]
def fullPSpec := (pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ++ₚ
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-! ## Oracle Interface instances for Messages-/

instance instOracleInterfaceMessagePSpecFold :
  ∀ j, OracleInterface ((pSpecFold (L:=L)).Message j) :=
  fun _ => OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpecFold (L := L)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ j, OracleInterface ((pSpecRelay).Message j)
  | ⟨x, h⟩ => by exact x.elim0

instance {i : Fin ℓ} :
    ∀ j, OracleInterface ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message j)
  | ⟨0, _⟩ => by exact OracleInterface.instDefault -- oracle commitment (conditional)

instance {i : Fin ℓ} : ∀ j, OracleInterface
  ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ j, OracleInterface ((pSpecRelay).Message j)
  | ⟨x, hj⟩ => by exact x.elim0

instance {i : Fin ℓ} :
    ∀ j, OracleInterface ((pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := pSpecFold (L := L))
    (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)

instance : ∀ j, OracleInterface ((pSpecFoldRelay (L:=L)).Message j) :=
  instOracleInterfaceMessageAppend

instance {i : Fin ℓ} :
    ∀ j, OracleInterface ((pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message j) :=
  instOracleInterfaceMessageAppend

instance {n : ℕ} : ∀ j, OracleInterface ((pSpecFoldRelaySequence (L:=L) n).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance {bIdx : Fin (ℓ / ϑ - 1)} : ∀ j, OracleInterface ((pSpecFullNonLastBlock 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx).Message j) :=
  instOracleInterfaceMessageAppend

instance : ∀ j, OracleInterface ((pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message j) := instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface ((pSpecLastBlock (L:=L) (ϑ:=ϑ)).Message j) :=
  instOracleInterfaceMessageSeqCompose

instance : ∀ j, OracleInterface ((pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message j) := instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecFinalSumcheckStep (L:=L)).Message i)
  | ⟨0, _⟩ => by exact OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpecFinalSumcheckStep (L:=L)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ i, OracleInterface ((pSpecCoreInteraction 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i) := instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i) := fun _ => OracleInterface.instDefault

instance : ∀ i, OracleInterface ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ i, Fintype ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i)
  | ⟨0, _⟩ => by
      change Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0)
      infer_instance

instance : ∀ i, Inhabited ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i)
  | ⟨0, _⟩ => by
      change Inhabited (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0)
      exact ⟨fun _ => 0⟩

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

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] hdiv in
@[simp]
lemma instOracleStatementBinaryBasefold_heq_of_fin_eq {i₁ i₂ : Fin (ℓ + 1)} (h : i₁ = i₂) :
    HEq (instOracleStatementBinaryBasefold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i₁))
      (instOracleStatementBinaryBasefold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i₂)) := by subst h; rfl

/-! ## SampleableType instances -/

instance {i : Fin ℓ} : ∀ j, SampleableType ((pSpecCommit 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)
  | ⟨0, hj⟩ => by nomatch hj

instance : ∀ j, SampleableType ((pSpecFold (L:=L)).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    infer_instance

instance : ∀ j, SampleableType ((pSpecRelay).Challenge j)
  | ⟨x, hj⟩ => by exact x.elim0

instance : ∀ j, SampleableType ((pSpecFoldRelay (L:=L)).Challenge j) :=
  instSampleableTypeChallengeAppend

instance {i : Fin ℓ} : ∀ j, SampleableType ((pSpecFoldCommit 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) := instSampleableTypeChallengeAppend

instance {n : ℕ} : ∀ j, SampleableType ((pSpecFoldRelaySequence (L:=L) n).Challenge j) :=
  instSampleableTypeChallengeSeqCompose

instance {i : Fin (ℓ / ϑ - 1)} : ∀ j, SampleableType ((pSpecFullNonLastBlock 𝔽q β
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) := instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType ((pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i) := instSampleableTypeChallengeSeqCompose

instance : ∀ i, SampleableType ((pSpecLastBlock (L:=L) (ϑ:=ϑ)).Challenge i) :=
  instSampleableTypeChallengeSeqCompose

instance : ∀ i, SampleableType ((pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i) := instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType ((pSpecFinalSumcheckStep (L:=L)).Challenge i)
  | ⟨0, _⟩ => by (expose_names; exact inst_5)

instance : ∀ i, SampleableType ((pSpecCoreInteraction 𝔽q β (ϑ:=ϑ)
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i) := instSampleableTypeChallengeAppend

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
    simp only
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

instance : SampleableType (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) := by
  let res := instSDomain 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (h_i := by
    apply Nat.lt_add_of_pos_right_of_le; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le])
  exact instSampleableTypeFinFunc

/-! ## Additional OracleInterface and Fintype instances -/

/-- OracleInterface instance for the matrix-indexed message type family using instDefault. -/
instance : ∀ i, OracleInterface (![↥L⦃≤ 2⦄[X], L] i)
  | ⟨0, h⟩ => by exact OracleInterface.instDefault  -- Polynomial message
  | ⟨1, h⟩ => by exact OracleInterface.instDefault  -- Field element message
  | ⟨n+2, h⟩ => by omega  -- Only 2 elements in the matrix

omit [NeZero r] [CharP L 2] [SampleableType L] 𝔽q [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 γ_repetitions [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
private noncomputable def fintypeDegreeLETwo : Fintype (L⦃≤ 2⦄[X]) := by
  classical
  -- Bound elaboration for this explicit finite encoding proof.
  let coeffVec : L⦃≤ 2⦄[X] → Fin 3 → L := fun p i => p.1.coeff i
  have hcoeffVec : Function.Injective coeffVec := by
    intro p q h
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    cases n with
    | zero =>
        exact congr_fun h 0
    | succ n =>
        cases n with
        | zero =>
            exact congr_fun h 1
        | succ n =>
            cases n with
            | zero =>
                exact congr_fun h 2
            | succ n =>
                have hpnat : p.1.natDegree ≤ 2 := by
                  apply Polynomial.natDegree_le_of_degree_le
                  exact Polynomial.mem_degreeLE.mp p.2
                have hqnat : q.1.natDegree ≤ 2 := by
                  apply Polynomial.natDegree_le_of_degree_le
                  exact Polynomial.mem_degreeLE.mp q.2
                have hpzero : p.1.coeff n.succ.succ.succ = 0 := by
                  apply Polynomial.coeff_eq_zero_of_natDegree_lt
                  omega
                have hqzero : q.1.coeff n.succ.succ.succ = 0 := by
                  apply Polynomial.coeff_eq_zero_of_natDegree_lt
                  omega
                exact hpzero.trans hqzero.symm
  letI : Finite (L⦃≤ 2⦄[X]) := Finite.of_injective coeffVec hcoeffVec
  exact Fintype.ofFinite (L⦃≤ 2⦄[X])

/-! ## Fintype & Inhabited instances for oracle specifications -/

instance instInhabitedOracleSpecEmpty : (([]ₒ : OracleSpec PEmpty).Inhabited) where
  inhabited_B i := nomatch i

instance instFintypeOracleSpecEmpty : (([]ₒ : OracleSpec PEmpty).Fintype) where
  fintype_B i := nomatch i

/-! ## OracleSpec.Inhabited for OracleStatement and all pSpec.Message -/

instance instInhabitedOracleStatement {i : Fin (ℓ + 1)} :
    [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i]ₒ.Inhabited where
  inhabited_B x := by
    rcases x with ⟨j, q⟩
    change Inhabited L
    exact ⟨0⟩

instance instInhabitedPSpecRelayMessage : [(pSpecRelay).Message]ₒ.Inhabited where
  inhabited_B x := nomatch x.1

instance instInhabitedPSpecFinalSumcheckStepMessage :
    [(pSpecFinalSumcheckStep (L:=L)).Message]ₒ.Inhabited where
  inhabited_B x := by
    letI : Inhabited L := ⟨0⟩
    rcases x with ⟨⟨i, hi⟩, q⟩
    have h0 : i = 0 := Fin.eq_zero i
    subst h0
    cases q
    change Inhabited L
    infer_instance

instance {i : Fin ℓ} :
    ∀ j, ∀ q : OracleInterface.Query ((pSpecFoldCommit 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message j), Inhabited
        (OracleInterface.Response (Message := (pSpecFoldCommit 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message j) q)
  | ⟨0, h⟩, q => by
      change Inhabited ((ProtocolSpec.instOracleInterfaceMessageAppend
        (pSpec₁ := pSpecFold (L := L))
        (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        ⟨0, h⟩).toOC.spec q)
      cases q
      change Inhabited (L⦃≤ 2⦄[X])
      infer_instance
  | ⟨1, hj⟩, _ => by
      change Direction.V_to_P = Direction.P_to_V at hj
      cases hj
  | ⟨2, h⟩, q => by
      change Inhabited ((ProtocolSpec.instOracleInterfaceMessageAppend
        (pSpec₁ := pSpecFold (L := L))
        (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        ⟨2, h⟩).toOC.spec q)
      cases q
      change Inhabited
        (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val + 1, by omega⟩)
      exact ⟨fun _ => 0⟩

instance {i : Fin ℓ} :
    [(pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message]ₒ.Inhabited := by
  infer_instance

instance instInhabitedPSpecQueryMessage :
    [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ.Inhabited where
  inhabited_B x := by
    rcases x with ⟨⟨i, hi⟩, q⟩
    have h0 : i = 0 := Fin.eq_zero i
    subst h0
    have hfalse : False := by
      change Direction.V_to_P = Direction.P_to_V at hi
      cases hi
    exact False.elim hfalse

instance instFintypePSpecFold_AllChallenges : ∀ i, Fintype ((pSpecFold (L := L)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0
  | ⟨1, _⟩ => by
    change Fintype L
    infer_instance

instance instInhabitedPSpecFold_AllChallenges : ∀ i, Inhabited ((pSpecFold (L := L)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0
  | ⟨1, _⟩ => by
    change Inhabited L
    exact ⟨0⟩

/-- Fintype/Inhabited for the challenge oracle spec so unroll_*_reduction_perfectCompleteness
can use Pr[...]. -/
instance instFintypePSpecFoldChallenge :
    [(pSpecFold (L := L)).Challenge]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 1 := by
    match i with
    | ⟨0, _⟩ => simp at hi -- contradiction
    | ⟨1, _⟩ => simp only [Fin.mk_one, Fin.isValue]
  subst h0
  cases q
  change _root_.Fintype L
  infer_instance

instance instInhabitedPSpecFoldChallenge :
    [(pSpecFold (L := L)).Challenge]ₒ.Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  match i with
  | ⟨0, _⟩ =>
      change Direction.P_to_V = Direction.V_to_P at hi
      cases hi
  | ⟨1, _⟩ =>
      cases q
      change Inhabited L
      exact ⟨0⟩

instance : ∀ i, ∀ j, Inhabited
  ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)
  | _, ⟨0, h⟩ => nomatch h

/-- Fintype instance for pSpecFold message oracle specification. -/
instance : ∀ j, ∀ q : OracleInterface.Query ((pSpecFold (L:=L)).Message j), Fintype
    (OracleInterface.Response (Message := (pSpecFold (L:=L)).Message j) q)
  | ⟨0, h⟩, q => by
      change Fintype ((instOracleInterfaceMessagePSpecFold (L := L) ⟨0, h⟩).toOC.spec q)
      cases q
      change Fintype (L⦃≤ 2⦄[X])
      exact fintypeDegreeLETwo (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡)
  | ⟨1, hj⟩, _ => by
      change Direction.V_to_P = Direction.P_to_V at hj
      cases hj

instance : ([(pSpecFold (L:=L)).Message]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := by
    have hi_ne_one : i ≠ 1 := by
      intro h1
      rw [h1] at hi
      change Direction.V_to_P = Direction.P_to_V at hi
      cases hi
    have hval : i.val = 0 := by
      omega
    exact Fin.ext hval
  subst h0
  change Fintype ((instOracleInterfaceMessagePSpecFold (L := L) ⟨0, by rfl⟩).toOC.spec q)
  cases q
  change Fintype (L⦃≤ 2⦄[X])
  exact fintypeDegreeLETwo (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡)

instance instOracleStatementFintype {i : Fin (ℓ + 1)} :
  [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨j, q⟩
  change Fintype L
  infer_instance

instance instFintypePSpecFinalSumcheck_AllChallenges :
    ∀ i, Fintype ((pSpecFinalSumcheckStep (L:=L)).Challenge i)
  | ⟨0, h0⟩ => nomatch h0
  -- (i : pSpecFinalSumcheckStep.ChallengeIdx) → Fintype (pSpecFinalSumcheckStep.Challenge i)

instance instFintypePSpecFinalSumcheckStepChallenge :
  [pSpecFinalSumcheckStep (L := L).Challenge]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  have hfalse : False := by
    change Direction.P_to_V = Direction.V_to_P at hi
    cases hi
  exact False.elim hfalse
instance : Fintype (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) := by
  infer_instance

instance instInhabitedPSpecFinalSumcheckStepChallenge :
  [(pSpecFinalSumcheckStep (L:=L)).Challenge]ₒ.Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  have hfalse : False := by
    change Direction.P_to_V = Direction.V_to_P at hi
    cases hi
  exact False.elim hfalse

instance : ∀ i, Fintype ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i)
  | ⟨0, _⟩ => by
      change Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0)
      infer_instance

instance : ∀ i, Inhabited ((pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge i)
  | ⟨0, _⟩ => by
      change Inhabited (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0)
      exact ⟨fun _ => 0⟩

instance instFintypePSpecQueryChallenge : [(pSpecQuery 𝔽q β γ_repetitions
  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  cases q
  change Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0)
  infer_instance

instance instInhabitedPSpecQueryChallenge :
  [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ.Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  cases q
  change Inhabited (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0)
  exact ⟨fun _ => 0⟩

instance instFintypePspecCommit_AllChallenges {i : Fin ℓ} :
  ∀ j, Fintype ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)
  | ⟨0, h⟩ => nomatch h

instance instFintypePspecCommitChallenge {i : Fin ℓ} :
  [((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge)]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨j, hj⟩, q⟩
  have h0 : j = 0 := Fin.eq_zero j
  subst h0
  have hfalse : False := by
    change Direction.P_to_V = Direction.V_to_P at hj
    cases hj
  exact False.elim hfalse

instance instInhabitedPspecCommitChallenge {i : Fin ℓ} :
  [((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge)]ₒ.Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨j, hj⟩, q⟩
  have h0 : j = 0 := Fin.eq_zero j
  subst h0
  have hfalse : False := by
    change Direction.P_to_V = Direction.V_to_P at hj
    cases hj
  exact False.elim hfalse

instance instFintypePSpecRelay_AllChallenges : ∀ i, Fintype ((pSpecRelay).Challenge i)
  | ⟨x, h⟩ => x.elim0

instance instOracleInterfacePSpecRelay_AllChallenges
  : ∀ i, OracleInterface ((pSpecRelay).Challenge i) := ProtocolSpec.challengeOracleInterface

instance instFintypePSpecRelayChallenge :
  [(pSpecRelay).Challenge]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  nomatch x.1

instance instInhabitedPSpecRelayChallenge :
  [(pSpecRelay).Challenge]ₒ.Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  nomatch x.1

instance instFintypeOracleStatementFinLast :
  [fun j => OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Fin.last ℓ) j]ₒ.Fintype := by
  infer_instance

instance instFintypePSpecQueryMessage :
  [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  have hfalse : False := by
    change Direction.V_to_P = Direction.P_to_V at hi
    cases hi
  exact False.elim hfalse

instance instFintypePSpecQuery_AllChallenges :
  ∀ j, Fintype ((pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) := by
  infer_instance

instance instFintypePSpecFinalSumcheckStepMessage :
  [(pSpecFinalSumcheckStep (L := L)).Message]ₒ.Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h0 : i = 0 := Fin.eq_zero i
  subst h0
  cases q
  change Fintype L
  infer_instance

end Pspec

end
end Binius.BinaryBasefold
