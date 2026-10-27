/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
public import ArkLib.ProofSystem.Sumcheck.Structured

/-!
# Binary Basefold index arithmetic

Oracle-frontier indices and the index bounds of the block structure. The round-polynomial
projections are the structured sum-check's (`Sumcheck.Structured`), re-exported here.
-/

@[expose] public section

noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

section OracleStatementIndex
variable (ℓ : ℕ) (ϑ : ℕ) [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

omit [NeZero ϑ] in
/-- A positive multiple of the block size is at least one block. -/
lemma blockSize_le_rounds : ϑ ≤ ℓ :=
  Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out

/-- The number of committed codewords available at the beginning of state `i`. -/
def toOutCodewordsCount (i : Fin (ℓ + 1)) : ℕ :=
  i / ϑ + if i < ℓ then 1 else 0

/-- A nonfinal round that completes a block and commits its folded codeword. -/
def IsCommitmentRound (i : Fin ℓ) : Prop :=
  ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ

/-- Commitment rounds are decidable by natural-number divisibility and inequality. -/
instance instDecidableIsCommitmentRound (i : Fin ℓ) : Decidable (IsCommitmentRound ℓ ϑ i) :=
  inferInstanceAs (Decidable (ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ))

omit [NeZero ϑ] hdiv in
/-- The initial frontier contains one committed codeword. -/
lemma toOutCodewordsCount_zero : toOutCodewordsCount ℓ ϑ 0 = 1 := by
  unfold toOutCodewordsCount
  simp [Nat.pos_of_ne_zero (NeZero.ne ℓ)]

instance instNeZeroNatToOutCodewordsCount : ∀ i, NeZero (toOutCodewordsCount ℓ ϑ i) := by
  intro i
  have h_ne_0: toOutCodewordsCount ℓ ϑ i ≠ 0 := by
    simp only [toOutCodewordsCount]
    by_cases h_i_lt_ℓ: i.val < ℓ
    · simp only [h_i_lt_ℓ, ↓reduceIte]; apply Nat.succ_ne_zero
    · simp only [h_i_lt_ℓ, ↓reduceIte, add_zero, ne_eq, Nat.div_eq_zero_iff, not_or, not_lt]
      constructor
      · exact NeZero.ne ϑ
      · have h_i: i = ℓ := by omega
        rw [h_i]; apply Nat.le_of_dvd (by exact pos_of_neZero ℓ) (hdiv.out)
  exact NeZero.mk h_ne_0

omit [NeZero ϑ] [NeZero ℓ] hdiv in
/-- Every available codeword starts a block at or before the current frontier. -/
lemma oraclePosition_mul_blockSize_le_frontier (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ ≤
    (if i.val < ℓ then i.val else ℓ - ϑ) := by
  intro j
  split_ifs with h_il
  -- Case 1: i.val < ℓ
  case pos =>
    have hj : j.val ≤ i.val / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte] at hj_lt
      omega
    have h_mul := Nat.mul_le_mul_right ϑ hj
    exact h_mul.trans (Nat.div_mul_le_self i.val ϑ)
  -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
  case neg =>
    have h_ival_eq_l : i.val = ℓ := by omega
    have hj : j.val < ℓ / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte, add_zero] at hj_lt
      apply Nat.succ_lt_succ
      calc j.val < i.val / ϑ := by omega
        _ = _ := by congr
    have hj : j.val ≤ ℓ / ϑ - 1 := by apply Nat.le_sub_one_of_lt hj
    have h_mul := Nat.mul_le_mul_right ϑ hj
    rw [Nat.mul_sub_right_distrib, one_mul] at h_mul
    exact h_mul.trans (Nat.sub_le_sub_right (Nat.div_mul_le_self ℓ ϑ) ϑ)

omit hdiv [NeZero ℓ] [NeZero ϑ] in
/-- The frontier grows by one precisely at commitment rounds. -/
lemma toOutCodewordsCount_succ_eq_add_one_iff (i : Fin ℓ) :
    IsCommitmentRound ℓ ϑ i ↔
    (toOutCodewordsCount ℓ ϑ i.castSucc) + 1 = toOutCodewordsCount ℓ ϑ i.succ := by
  have hdiv := Nat.succ_div (a := i.val) (b := ϑ)
  simp only [IsCommitmentRound, toOutCodewordsCount, Fin.val_castSucc, Fin.val_succ,
    i.isLt, ↓reduceIte]
  split_ifs at hdiv ⊢ <;> omega

open Classical in
omit [NeZero ℓ] [NeZero ϑ] in
/-- A commitment round adds one codeword; every other round preserves the frontier size. -/
lemma toOutCodewordsCount_succ_eq (i : Fin ℓ) :
    (toOutCodewordsCount ℓ ϑ i.succ) =
    if IsCommitmentRound ℓ ϑ i then (toOutCodewordsCount ℓ ϑ i.castSucc) + 1
    else (toOutCodewordsCount ℓ ϑ i.castSucc) := by
  have hd := Nat.succ_div (a := i.val) (b := ϑ)
  have hboundary : i.val + 1 < ℓ ∨ ϑ ∣ i.val + 1 := by
    by_cases h : i.val + 1 < ℓ
    · exact Or.inl h
    · have heq : i.val + 1 = ℓ := by omega
      exact Or.inr (heq.symm ▸ hdiv.out)
  simp only [toOutCodewordsCount, Fin.val_succ, Fin.val_castSucc, i.isLt, ↓reduceIte,
    IsCommitmentRound]
  split_ifs at hd ⊢ <;> omega

omit [NeZero ℓ] [NeZero ϑ] in
/-- The committed-oracle frontier size is nondecreasing through a fold round. -/
lemma toOutCodewordsCount_castSucc_le_succ (i : Fin ℓ) :
    toOutCodewordsCount ℓ ϑ i.castSucc ≤ toOutCodewordsCount ℓ ϑ i.succ := by
  rw [toOutCodewordsCount_succ_eq ℓ ϑ]
  split_ifs
  · omega
  · omega

/-- The final frontier contains exactly `ℓ / ϑ` codewords. -/
@[simp]
lemma toOutCodewordsCount_last ℓ ϑ : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ := by
  unfold toOutCodewordsCount
  simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero]

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- The next committed codeword's block endpoint is the current round. -/
lemma toOutCodewordsCount_castSucc_mul_eq_succ_of_dvd (i : Fin ℓ) (hCR : ϑ ∣ i.val + 1) :
    toOutCodewordsCount ℓ ϑ i.castSucc * ϑ = i.val + 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.val_castSucc, i.isLt, ↓reduceIte]
  rw [← Nat.succ_div_of_dvd hCR, Nat.div_mul_cancel hCR]

/-- Every committed codeword domain level is strictly below `ℓ`. -/
lemma oraclePosition_mul_blockSize_lt_rounds (ℓ ϑ : ℕ) [NeZero ϑ] [NeZero ℓ] (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ < ℓ := by
  intro j
  unfold toOutCodewordsCount
  have h_j_lt : j.val < i.val / ϑ + if i.val < ℓ then 1 else 0 := j.2
  have h_j_mul_ϑ_lt := oraclePosition_mul_blockSize_le_frontier ℓ ϑ i j
  calc
    ↑j * ϑ ≤ if ↑i < ℓ then ↑i else ℓ - ϑ := by omega
    _ < _ := by
      by_cases h_i_lt_ℓ : i.val < ℓ
      · -- Case 1: i.val < ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte]
      · -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte, tsub_lt_self_iff]
        constructor
        · exact pos_of_neZero ℓ
        · exact pos_of_neZero ϑ

omit hdiv in
/-- The base index k = j * ϑ is less than ℓ for valid oracle indices -/
@[simp]
lemma oracle_block_k_bound (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ < ℓ :=
  oraclePosition_mul_blockSize_lt_rounds ℓ ϑ i j

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- The base index k = j * ϑ is less than or equal to i -/
@[simp]
lemma oracle_block_k_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ ≤ i := by
  have h := oraclePosition_mul_blockSize_le_frontier ℓ ϑ i j
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

/-- The next oracle index k + ϑ = (j+1) * ϑ is at most i -/
@[simp]
lemma oracle_block_k_next_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i) : j.val * ϑ + ϑ ≤ i := by
  have h := oraclePosition_mul_blockSize_le_frontier ℓ ϑ i (j + 1)
  rw [Fin.val_add_one' (h_a_add_1:=hj), Nat.add_mul, Nat.one_mul] at h
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

omit [NeZero ℓ] [NeZero ϑ] in
/-- For any oracle position j, the domain index j*ϑ plus ϑ steps is at most ℓ.
This is a key bound for proving fiber-wise closeness requirements. -/
@[simp]
lemma oracle_index_add_steps_le_ℓ (i : Fin (ℓ + 1))
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ + ϑ ≤ ℓ := by
  unfold toOutCodewordsCount
  by_cases h : i < ℓ
  · -- Case: i < ℓ, so toOutCodewordsCount = i/ϑ + 1
    have hj_bound : j.val < i / ϑ + 1 := by
      have : toOutCodewordsCount ℓ ϑ i = i / ϑ + 1 := by simp [toOutCodewordsCount, h]
      rw [← this]; exact j.isLt
    rw [← Nat.add_one_mul]
    apply Nat.le_trans (Nat.mul_le_mul_right ϑ (Nat.succ_le_of_lt hj_bound))
    apply Nat.mul_le_of_le_div
    apply Nat.succ_le_of_lt
    apply Nat.div_lt_of_lt_mul; rw [mul_comm]
    rw [Nat.div_mul_cancel hdiv.out]
    exact h
  · -- Case: i ≥ ℓ, so toOutCodewordsCount = i/ϑ
    have hj_bound : j.val < i / ϑ := by
      have : toOutCodewordsCount ℓ ϑ i = i / ϑ := by simp [toOutCodewordsCount, h]
      rw [← this]; exact j.isLt
    calc j.val * ϑ + ϑ
        = (j.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (i / ϑ) * ϑ := by gcongr; omega
      _ ≤ i := Nat.div_mul_le_self i ϑ
      _ ≤ ℓ := Fin.is_le i

omit [NeZero ℓ] [NeZero ϑ] in
/-- For any oracle position j, the domain index j*ϑ is at most ℓ.
This is a key bound for proving fiber-wise closeness requirements. -/
@[simp]
lemma oracle_index_le_ℓ (i : Fin (ℓ + 1))
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ ≤ ℓ := by
  have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ i j
  omega

/-- Convert oracle position index to oracle domain index by multiplying by ϑ.
The position index j corresponds to the j-th oracle in the list of committed oracles,
and the domain index is j*ϑ, which is the actual index in the Fin ℓ domain. -/
@[reducible]
def oraclePositionToDomainIndex {i : Fin (ℓ + 1)}
    (positionIdx : Fin (toOutCodewordsCount ℓ ϑ i)) : Fin ℓ :=
  ⟨positionIdx.val * ϑ, oracle_block_k_bound ℓ ϑ i positionIdx⟩

/-- The final position of the nonempty committed-oracle frontier. -/
def getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ i) := by
  let ne0 := (instNeZeroNatToOutCodewordsCount ℓ ϑ i).out
  exact ⟨(toOutCodewordsCount ℓ ϑ i) - 1, by omega⟩

/-- The domain level of the last committed codeword. -/
@[reducible]
def getLastOracleDomainIndex (oracleFrontierIdx : Fin (ℓ + 1)) :
    Fin (ℓ) :=
  oraclePositionToDomainIndex (positionIdx := (getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx))

/-- At the last state, the final committed position is `ℓ / ϑ - 1`. -/
lemma getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    = ⟨ℓ / ϑ - 1, by
      dsimp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false];
      simp only [lt_self_iff_false,
        ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff, zero_lt_one, and_true]
      constructor
      · exact pos_of_neZero ϑ
      · exact blockSize_le_rounds ℓ ϑ
      ⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOraclePositionIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet]
  rw [toOutCodewordsCount_last]

/-- At the last state, the final committed word is at level `ℓ - ϑ`. -/
lemma getLastOracleDomainIndex_last : getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
    = ⟨ℓ - ϑ, by
      have h_ne_0 : 0 < ϑ := by exact pos_of_neZero ϑ
      have h_lt: ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
      omega⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOracleDomainIndex]
  rw [getLastOraclePositionIndex_last]; simp only;
  rw [Nat.sub_mul, Nat.one_mul]
  rw [Nat.div_mul_cancel (hdiv.out)]

/-- The final committed codeword starts a block ending no later than `ℓ`. -/
lemma getLastOracleDomainIndex_add_ϑ_le (i : Fin (ℓ + 1)) :
    (getLastOracleDomainIndex ℓ ϑ i).val + ϑ ≤ ℓ := by
  rw [getLastOracleDomainIndex, oraclePositionToDomainIndex]
  simp only [oracle_index_add_steps_le_ℓ]
/-- Before the last state, the last oracle position is the current block number. -/
lemma getLastOraclePositionIndex_castSucc_val (i : Fin ℓ) :
    (getLastOraclePositionIndex ℓ ϑ i.castSucc).val = i.val / ϑ := by
  simp [getLastOraclePositionIndex, toOutCodewordsCount, i.isLt]

/-- Before the last state, the last oracle domain is the beginning of the current block. -/
lemma getLastOracleDomainIndex_castSucc_val (i : Fin ℓ) :
    (getLastOracleDomainIndex ℓ ϑ i.castSucc).val = i.val / ϑ * ϑ := by
  change (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ = i.val / ϑ * ϑ
  rw [getLastOraclePositionIndex_castSucc_val]

/-- The number of rounds since the last committed oracle is the remainder modulo the block size. -/
lemma sub_getLastOracleDomainIndex_castSucc_val (i : Fin ℓ) :
    i.val - (getLastOracleDomainIndex ℓ ϑ i.castSucc).val = i.val % ϑ := by
  rw [getLastOracleDomainIndex_castSucc_val, Nat.mod_eq_sub_mul_div, Nat.mul_comm]

end OracleStatementIndex

section IndexBounds
variable {ℓ ϑ : ℕ} [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

/-- ϑ is positive -/
lemma blockSize_pos : (ϑ : ℕ) > 0 := pos_of_neZero ϑ

omit hdiv in
/-- ℓ - ϑ < ℓ when both are positive -/
lemma rounds_sub_blockSize_lt : ℓ - ϑ < ℓ :=
  Nat.sub_lt (pos_of_neZero ℓ) (blockSize_pos)

/-- Subtracting one from a positive block size gives a smaller number. -/
lemma blockSize_sub_one_lt : ϑ - 1 < ϑ := by
  have lt_0: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  exact Nat.sub_one_lt_of_lt lt_0

omit [NeZero ℓ] in
/-- The start of each valid committed block lies before the final round. -/
@[simp]
lemma k_mul_ϑ_lt_ℓ {k : Fin (ℓ / ϑ)} :
    ↑k * ϑ < ℓ := by
  have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  calc
    ↑k * ϑ < (ℓ / ϑ) * ϑ := Nat.mul_lt_mul_of_pos_right k.isLt (NeZero.pos ϑ)
    _ = ℓ := h_mul_eq

omit [NeZero ℓ] [NeZero ϑ] in
/-- The end of each valid committed block is at most the final round. -/
@[simp]
lemma k_succ_mul_ϑ_le_ℓ {k : Fin (ℓ / ϑ)} : (k.val + 1) * ϑ ≤ ℓ := by
  have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  calc
    (k.val + 1) * ϑ ≤ (ℓ / ϑ) * ϑ := Nat.mul_le_mul_right (k := ϑ) (h := by omega)
    _ = ℓ := h_mul_eq

omit [NeZero ℓ] [NeZero ϑ] in
/-- A valid block start plus one block size is at most the final round. -/
@[simp]
lemma k_succ_mul_ϑ_le_ℓ_₂ {k : Fin (ℓ / ϑ)} : k.val * ϑ + ϑ ≤ ℓ := by
  conv_lhs => enter [2]; rw [← Nat.one_mul ϑ]
  rw [← Nat.add_mul]
  exact k_succ_mul_ϑ_le_ℓ

variable {r 𝓡 : ℕ} [NeZero r] [NeZero 𝓡]

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
/-- An index at most the number of rounds lies below the ambient basis rank. -/
lemma lt_r_of_le_ℓ (h_ℓ_add_R_rate : ℓ + 𝓡 < r) {x : ℕ} (h : x ≤ ℓ) : x < r := by
  omega

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
/-- An index before the final round lies below the ambient basis rank. -/
lemma lt_r_of_lt_ℓ (h_ℓ_add_R_rate : ℓ + 𝓡 < r) {x : ℕ} (h : x < ℓ) : x < r := by
  omega

/-- An offset of at most one block in a nonfinal block is at most the final block start. -/
@[simp]
lemma blockStart_add_offset_le_rounds_sub_blockSize (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) (hx : x ≤ ϑ) :
    ↑bIdx * ϑ + x ≤ ℓ - ϑ := by
  have h_x_lt : x < ϑ + 1 := Nat.lt_succ_of_le hx
  have h_fin : x < ϑ ∨ x = ϑ := Nat.lt_or_eq_of_le hx
  calc
    ↑bIdx * ϑ + x ≤ ↑bIdx * ϑ + ϑ := by omega
    _ = (↑bIdx + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
    _ = ℓ - ϑ := by
      have h_bound : 1 ≤ ℓ / ϑ := by
        have h_le: ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
        rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
      rw [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    _ ≤ ℓ - ϑ := by omega

/-- Every position in a nonfinal block lies below the number of rounds plus any offset. -/
@[simp]
lemma blockStart_add_offset_lt_rounds_add {m : ℕ} (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin ϑ) :
    ↑bIdx * ϑ + ↑i < ℓ + m :=
  calc
    _ ≤ ℓ - ϑ := by apply blockStart_add_offset_le_rounds_sub_blockSize bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_blockSize_lt
    _ ≤ ℓ + m := by omega

/-- A position through the end of a nonfinal block lies before the state-count bound. -/
lemma bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1 + 1)) :
    ↑bIdx * ϑ + i < ℓ + 1 := by
  calc
    ↑bIdx * ϑ + i ≤ ℓ - ϑ := by
      apply blockStart_add_offset_le_rounds_sub_blockSize bIdx (x:=i.val) (hx:=by omega)
    _ < ℓ + 1 := by omega

/-- An offset before the last position in a nonfinal block lies before the final round. -/
@[simp]
lemma bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1)) :
    ↑bIdx * ϑ + ↑i < ℓ := by
  calc
    _ ≤ ℓ - ϑ := by apply blockStart_add_offset_le_rounds_sub_blockSize bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_blockSize_lt

end IndexBounds

/-- Oracle frontier index: captures valid oracle indices for a given statement index.
    In Binary Basefold, the oracle can be at most 1 index behind the statement index.
    - At statement index `i+1`, the oracle can be at `i` (after fold) or `i+1` (after commit)
-/
def OracleFrontierIndex {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :=
  { val : Fin (ℓ + 1) // val.val ≤ stmtIdx.val ∧ stmtIdx.val ≤ val.val + 1 }

namespace OracleFrontierIndex

/-- Create oracle frontier index equal to statement index (synchronized case) -/
def mkFromStmtIdx {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :
    OracleFrontierIndex stmtIdx :=
  ⟨stmtIdx, by constructor <;> omega⟩

/-- Create oracle frontier index for statement i.succ with oracle at i (lagging case).
    Used after fold step where stmtIdx advances but oracle hasn't committed yet. -/
def mkFromStmtIdxCastSuccOfSucc {ℓ : ℕ} (i : Fin ℓ) :
    OracleFrontierIndex i.succ :=
  ⟨i.castSucc, by
    constructor
    · exact Nat.le_of_lt (by exact Nat.lt_add_one (i.castSucc).val)
    · simp only [Fin.val_succ, Fin.val_castSucc, le_refl]
  ⟩

/-- The synchronized frontier has the statement index. -/
@[simp]
lemma val_mkFromStmtIdx {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :
    (mkFromStmtIdx stmtIdx).val = stmtIdx := rfl

/-- The lagging frontier has the preceding statement index. -/
@[simp]
lemma val_mkFromStmtIdxCastSuccOfSucc {ℓ : ℕ} (i : Fin ℓ) :
    (mkFromStmtIdxCastSuccOfSucc i).val = i.castSucc := rfl

/-- The oracle frontier never lies ahead of the statement index. -/
@[simp]
lemma val_le_i {ℓ : ℕ} (i : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex i) :
    oracleIdx.val ≤ i := by
  unfold OracleFrontierIndex at oracleIdx
  let h := oracleIdx.property
  cases h
  · exact h.left

end OracleFrontierIndex

-- The round-polynomial projections are the structured sum-check's
-- (`ArkLib.ProofSystem.Sumcheck.Structured`). Binary Basefold is the `P · t` sum-check: its
-- relations take the multiplier `P` as a function `Context → MultilinearPoly L ℓ` (the type of
-- `SumcheckMultiplierParam.multpoly`) and use the identity-combinator projections.
export Sumcheck.Structured (computeInitialSumcheckPoly projectToNextSumcheckPoly)


end Binius.BinaryBasefold
