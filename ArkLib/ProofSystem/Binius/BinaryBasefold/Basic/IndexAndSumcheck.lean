/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
public import ArkLib.ProofSystem.Sumcheck.Structured

/-!
# Binary Basefold index arithmetic and sumcheck operations

Oracle-frontier indices, index bounds, and sumcheck polynomial projections.
-/

@[expose] public section

noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
variable (𝓑 : Fin 2 ↪ L)

section OracleStatementIndex
variable (ℓ : ℕ) (ϑ : ℕ) [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

lemma div_add_one_eq_if_dvd (i ϑ : ℕ) [NeZero ϑ] :
    (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ := by
  split_ifs with h_dvd
  case pos => exact Nat.succ_div_of_dvd h_dvd
  case neg => exact Nat.succ_div_of_not_dvd h_dvd

def toOutCodewordsCount (i : Fin (ℓ + 1)) : ℕ := by
  -- the number of codewords available as oracle at state `i` (at the beginning of round `i`)
  exact i/ϑ + (if (i < ℓ) then 1 else 0)

def isCommitmentRound (i : Fin ℓ) : Prop :=
  ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ

omit [NeZero ϑ] hdiv in
lemma toOutCodewordsCountOf0 : toOutCodewordsCount ℓ ϑ 0 = 1 := by
  unfold toOutCodewordsCount
  simp [Nat.pos_of_ne_zero (NeZero.ne ℓ)]

@[simp]
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
lemma toCodewordsCount_mul_ϑ_le_i (i : Fin (ℓ + 1)) :
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

omit hdiv in
lemma toOutCodewordsCount_succ_eq_add_one_iff (i : Fin ℓ) :
    isCommitmentRound ℓ ϑ i ↔
    (toOutCodewordsCount ℓ ϑ i.castSucc) + 1 = toOutCodewordsCount ℓ ϑ i.succ := by
  have h_i_succ: i.val + 1 = i.succ.val := rfl
  rw [isCommitmentRound, h_i_succ]
  constructor
  · intro h_i_transition
    unfold toOutCodewordsCount
    -- We know i.val < ℓ because i : Fin ℓ. We also know i.succ.val < ℓ from the hypothesis.
    have h_i_lt_l : i.val < ℓ := i.isLt
    have h_succ_lt_l : i.succ.val < ℓ := by
      apply Nat.lt_of_le_of_ne
      · omega
      · intro h_eq
        apply h_i_transition.2
        exact h_eq
    -- Simplify the expression using the known inequalities
    simp only [Fin.val_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ]
    ring_nf
    simp only [Fin.val_succ] at h_succ_lt_l
    rw [add_comm] at h_succ_lt_l
    simp only [h_succ_lt_l, ↓reduceIte]
    rw [add_comm 1 i.val]
    let k := (i + 1) / ϑ
    have h_k: (i + 1) / ϑ = k := rfl
    have h_k_mul_v: k * ϑ = i + 1 := by
      rw [mul_comm]
      rw [Nat.mul_div_eq_iff_dvd]
      exact h_i_transition.1
    have h_v_ne_0: ϑ ≠ 0 := by exact Ne.symm (NeZero.ne' ϑ)
    have h_k_gt_0: k > 0 := by
      by_contra h
      simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
      have h_i_add_1_eq_0: i.val + 1 = 0 := by
        simp only [h, Nat.div_eq_zero_iff, h_v_ne_0, false_or] at h_k -- h_k : ↑i + 1 < ϑ
        have h_v_ne_i_add_1: ϑ ≤ i.val + 1 := by
          apply Nat.le_of_dvd (by
            simp only [Fin.val_succ, lt_add_iff_pos_left, add_pos_iff, Fin.val_pos_iff, zero_lt_one,
              or_true]
          ) h_i_transition.1
        linarith -- h_v_ne_i_add_1 and h_k
      linarith
    have h_i_div_ϑ : i / ϑ = k - 1 := by
      apply Nat.div_eq_of_lt_le ?_ ?_
      · -- ⊢ (k - 1) * ϑ ≤ ↑i
        apply Nat.le_of_add_le_add_right (b:=ϑ)
        calc
          _ = (k - 1) * ϑ + 1 * ϑ := by omega
          _ = (k - 1 + 1) * ϑ := by exact Eq.symm (Nat.add_mul (k - 1) 1 ϑ)
          _ = i.val + 1 := by rw [←h_k_mul_v]; congr; omega -- uses h_k_gt_0
          _ ≤ i.val + ϑ := by apply Nat.add_le_add_left; omega
      · -- ⊢ ↑i < (k - 1 + 1) * ϑ
        rw [Nat.sub_one_add_one (by omega), h_k_mul_v]; omega
    rw [h_i_div_ϑ, h_k, add_comm]
    omega
  · -- ⊢ toOutCodewordsCount ℓ ϑ i.castSucc + 1 = toOutCodewordsCount ℓ ϑ i.succ →
    --   ϑ ∣ ↑i.succ ∧ i.succ ≠ ⟨ℓ, ⋯⟩
    intro h_eq
    constructor
    · -- Prove ϑ ∣ ↑i.succ
      unfold toOutCodewordsCount at h_eq
      have h_i_lt_l : i.val < ℓ := i.isLt
      simp only [Fin.val_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ] at h_eq
      -- We have: i / ϑ + 1 + 1 = (i + 1) / ϑ + (if i + 1 < ℓ then 1 else 0)
      by_cases h_succ_lt_l : i.val + 1 < ℓ
      · -- Case: i.succ < ℓ
        simp only [h_succ_lt_l, ↓reduceIte] at h_eq
        -- Now we have: i / ϑ + 2 = (i + 1) / ϑ + 1
        -- So: i / ϑ + 1 = (i + 1) / ϑ
        have h_div_eq : i.val / ϑ + 1 = (i.val + 1) / ϑ := by omega
        -- Use div_add_one_eq_if_dvd: (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ
        have h_from_lemma := div_add_one_eq_if_dvd i.val ϑ
        rw [h_from_lemma] at h_div_eq
        -- If ϑ ∣ (i + 1), then i / ϑ + 1 = i / ϑ + 1 ✓
        -- If ¬(ϑ ∣ (i + 1)), then i / ϑ + 1 = i / ϑ, which gives 1 = 0 ✗
        by_cases h_dvd_case : ϑ ∣ (i.val + 1)
        · exact h_dvd_case
        · simp [h_dvd_case] at h_div_eq
      · -- Case: ¬(i.succ < ℓ), so i.succ.val = ℓ
        simp only [h_succ_lt_l, ↓reduceIte] at h_eq
        -- Now we have: i / ϑ + 2 = (i + 1) / ϑ
        have h_i_succ_eq_l : i.val + 1 = ℓ := by omega
        -- Use div_add_one_eq_if_dvd: (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ
        have h_from_lemma := div_add_one_eq_if_dvd i.val ϑ
        -- Substitute the lemma directly into h_eq
        rw [h_from_lemma] at h_eq
        -- If ϑ ∣ (i + 1), then i / ϑ + 2 = i / ϑ + 1, which gives 2 = 1 ✗
        -- If ¬(ϑ ∣ (i + 1)), then i / ϑ + 2 = i / ϑ, which gives 2 = 0 ✗
        by_cases h_dvd_case : ϑ ∣ (i.val + 1)
        · -- If ϑ ∣ (i + 1), then we have our goal since i.succ.val = i.val + 1
          rw [Fin.val_succ]
          exact h_dvd_case
        · -- If ¬(ϑ ∣ (i + 1)), then h_eq becomes: i / ϑ + 2 = i / ϑ, so 2 = 0
          simp [h_dvd_case] at h_eq
          -- This gives us 2 = 0, which is impossible
          omega
    · -- Prove i.succ ≠ ⟨ℓ, ⋯⟩
      intro h_eq_l
      -- But i : Fin ℓ means i.val < ℓ, so i.succ.val = i.val + 1 ≤ ℓ
      -- If i.succ.val = ℓ, then i.val = ℓ - 1
      have h_i_eq : i.val = ℓ - 1 := by
        have h_succ : i.succ.val = i.val + 1 := by simp [Fin.val_succ]
        rw [h_eq_l] at h_succ
        omega
      -- Now check if the equation can hold
      unfold toOutCodewordsCount at h_eq
      have h_i_lt_l : i.val < ℓ := i.isLt
      simp only [Fin.val_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ] at h_eq
      -- We know that i.succ.val = ℓ, so i.val + 1 = ℓ, which means i.val + 1 ≮ ℓ
      have h_not_lt : ¬(i.val + 1 < ℓ) := by
        have h_succ_val : i.succ.val = i.val + 1 := by
          simp only [Fin.val_succ]
        rw [h_eq_l] at h_succ_val
        omega
      simp only [h_not_lt, ↓reduceIte] at h_eq
      -- We get: i / ϑ + 2 = ℓ / ϑ
      rw [h_i_eq] at h_eq
      -- So: (ℓ - 1) / ϑ + 2 = ℓ / ϑ
      -- Simplify the arithmetic first
      ring_nf at h_eq
      -- Now h_eq is: 2 + (ℓ - 1) / ϑ = (1 + (ℓ - 1)) / ϑ
      -- Note that 1 + (ℓ - 1) = ℓ
      have h_simp : 1 + (ℓ - 1) = ℓ := by omega
      rw [h_simp] at h_eq
      -- Use div_add_one_eq_if_dvd: ℓ / ϑ = if ϑ ∣ ℓ then (ℓ - 1) / ϑ + 1 else (ℓ - 1) / ϑ
      have h_ℓ_pos : 0 < ℓ := by omega -- since i.val < ℓ and i.val = ℓ - 1 ≥ 0
      have h_from_lemma := div_add_one_eq_if_dvd (ℓ - 1) ϑ
      -- Rewrite ℓ as (ℓ - 1) + 1 in the division
      have h_ℓ_div : ℓ = (ℓ - 1) + 1 := by omega
      rw [h_ℓ_div, h_from_lemma] at h_eq
      -- If ϑ ∣ ℓ, then (ℓ - 1) / ϑ + 2 = (ℓ - 1) / ϑ + 1, so 2 = 1 ✗
      -- If ¬(ϑ ∣ ℓ), then (ℓ - 1) / ϑ + 2 = (ℓ - 1) / ϑ, so 2 = 0 ✗
      by_cases h_dvd_ℓ : ϑ ∣ ℓ
      · -- If ϑ ∣ ℓ, then the if-then-else becomes (ℓ - 1) / ϑ + 1
        -- First simplify the arithmetic in h_eq
        have h_arith : ℓ - 1 + 1 - 1 = ℓ - 1 := by omega
        rw [h_arith] at h_eq
        -- Now simplify the if-then-else using h_dvd_ℓ
        have h_ℓ_eq : ℓ - 1 + 1 = ℓ := by omega
        rw [h_ℓ_eq] at h_eq
        simp [h_dvd_ℓ] at h_eq
        -- h_eq is now: 2 + (ℓ - 1) / ϑ = (ℓ - 1) / ϑ + 1
        -- This simplifies to: 2 = 1, which is impossible
        omega
      · -- If ¬(ϑ ∣ ℓ), then the if-then-else becomes (ℓ - 1) / ϑ
        -- First simplify the arithmetic in h_eq
        have h_arith : ℓ - 1 + 1 - 1 = ℓ - 1 := by omega
        rw [h_arith] at h_eq
        -- Now simplify the if-then-else using h_dvd_ℓ
        have h_ℓ_eq : ℓ - 1 + 1 = ℓ := by omega
        rw [h_ℓ_eq] at h_eq
        simp [h_dvd_ℓ] at h_eq
        -- h_eq is now: 2 + (ℓ - 1) / ϑ = (ℓ - 1) / ϑ
        -- This simplifies to: 2 = 0, which is impossible

open Classical in
lemma toOutCodewordsCount_succ_eq (i : Fin ℓ) :
    (toOutCodewordsCount ℓ ϑ i.succ) =
    if isCommitmentRound ℓ ϑ i then (toOutCodewordsCount ℓ ϑ i.castSucc) + 1
    else (toOutCodewordsCount ℓ ϑ i.castSucc) := by
  have h_succ_val: i.succ.val = i.val + 1 := rfl
  by_cases hv: ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ
  · have h_succ := (toOutCodewordsCount_succ_eq_add_one_iff ℓ ϑ i).mp hv
    rw [←h_succ];
    simp only [left_eq_ite_iff, Nat.add_eq_left, one_ne_zero, imp_false, Decidable.not_not]
    exact hv
  · rw [isCommitmentRound]
    simp only [ne_eq, hv, ↓reduceIte]
    unfold toOutCodewordsCount
    have h_i_lt_ℓ: i.castSucc.val < ℓ := by
      change i.val < ℓ
      omega
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.is_lt, ↓reduceIte]
    rw [div_add_one_eq_if_dvd]
    by_cases hv_div_succ: ϑ ∣ i.val + 1
    · simp only [hv_div_succ, ↓reduceIte, Nat.add_eq_left, ite_eq_right_iff, one_ne_zero,
      imp_false, not_lt, ge_iff_le]
      simp only [hv_div_succ, ne_eq, true_and, Decidable.not_not] at hv
      have h_eq: i.succ.val = ℓ := by
        change i.succ.val = (⟨ℓ, by omega⟩: Fin (ℓ + 1)).val
        exact hv
      omega
    · simp only [hv_div_succ, ↓reduceIte, Nat.add_left_cancel_iff, ite_eq_left_iff, not_lt,
      zero_ne_one, imp_false, not_le, gt_iff_lt]
      if hi_succ_lt: i.succ.val < ℓ then
        omega
      else
        simp only [Fin.val_succ, not_lt] at hi_succ_lt
        have hi_succ_le_ℓ: i.succ.val ≤ ℓ := by omega
        have hi_succ_eq_ℓ: i.val + 1 = ℓ := by omega
        rw [hi_succ_eq_ℓ] at hv_div_succ
        exact False.elim (hv_div_succ (hdiv.out))

lemma toOutCodewordsCount_i_le_of_succ (i : Fin ℓ) :
    toOutCodewordsCount ℓ ϑ i.castSucc ≤ toOutCodewordsCount ℓ ϑ i.succ := by
  rw [toOutCodewordsCount_succ_eq ℓ ϑ]
  split_ifs
  · omega
  · omega

@[simp]
lemma toOutCodewordsCount_last ℓ ϑ : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ := by
  unfold toOutCodewordsCount
  simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero]

omit [NeZero ℓ] hdiv in
/--
If a new oracle is committed at round `i + 1` (i.e., `ϑ ∣ i + 1`), then the index of this
new oracle (which is the count of oracles from the previous round, `i`) multiplied by `ϑ`
equals the current round number `i + 1`.
TODO: double check why this is still correct when replacing `hCR` with `ϑ | i + 1`
-/
lemma toOutCodewordsCount_mul_ϑ_eq_i_succ (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (toOutCodewordsCount ℓ ϑ i.castSucc) * ϑ = i.val + 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.val_castSucc, i.isLt, ↓reduceIte]
  have h_mod : i.val % ϑ = ϑ - 1 := by
    refine (mod_eq_sub_iff ?_ ?_).mpr hCR.1
    · omega
    · exact NeZero.one_le
  -- After unfolding, we have: (i.val / ϑ + 1) * ϑ = i.val + 1
  rw [Nat.add_mul, one_mul]
  -- Now we have: (i.val / ϑ) * ϑ + ϑ = i.val + 1
  -- Since ϑ ∣ (i.val + 1), we can use Nat.div_mul_cancel
  -- ⊢ ↑i / ϑ * ϑ + ϑ = ↑i + 1
  rw [Nat.div_mul_self_eq_mod_sub_self, h_mod]
  rw [←Nat.sub_add_comm (k:=ϑ - 1) (m:=ϑ) (by
    calc _ = i.val % ϑ := by omega
      _ ≤ i := by exact Nat.mod_le (↑i) ϑ
  )]
  -- ⊢ ↑i + ϑ - (ϑ - 1) = ↑i + 1
  rw [Nat.sub_sub_right (a:=i.val + ϑ) (b:=ϑ) (c:=1) (by exact NeZero.one_le)]
  omega

lemma toCodewordsCount_mul_ϑ_lt_ℓ (ℓ ϑ : ℕ) [NeZero ϑ] [NeZero ℓ] (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ < ℓ := by
  intro j
  unfold toOutCodewordsCount
  have h_j_lt : j.val < i.val / ϑ + if i.val < ℓ then 1 else 0 := j.2
  have h_j_mul_ϑ_lt := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
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
  toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- The base index k = j * ϑ is less than or equal to i -/
@[simp]
lemma oracle_block_k_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ ≤ i := by
  have h := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

/-- The next oracle index k + ϑ = (j+1) * ϑ is at most i -/
@[simp]
lemma oracle_block_k_next_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i) : j.val * ϑ + ϑ ≤ i := by
  have h := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i (j + 1)
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

def mkLastOracleIndex (i : Fin (ℓ + 1)) : Fin (toOutCodewordsCount ℓ ϑ i) := by
  have hv: ϑ ∣ ℓ := by exact hdiv.out
  rw [toOutCodewordsCount]
  if hi: i.val < ℓ then
    exact ⟨i.val / ϑ, by simp only [hi, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one];⟩
  else
    have hi_eq_ℓ: i.val = ℓ := by omega
    exact ⟨ℓ/ϑ - 1 , by
      simp_rw [hi_eq_ℓ]
      simp only [lt_self_iff_false, ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff,
        zero_lt_one, and_true]
      constructor
      · exact pos_of_neZero ϑ
      · apply Nat.le_of_dvd (h:=by exact pos_of_neZero ℓ); omega
    ⟩

lemma mkLastOracleIndex_last : mkLastOracleIndex ℓ ϑ (Fin.last ℓ) = ℓ / ϑ - 1 := by
  dsimp only [mkLastOracleIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet]
  simp only [lt_self_iff_false, ↓reduceDIte]; rfl

def getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ i) := by
  let ne0 := (instNeZeroNatToOutCodewordsCount ℓ ϑ i).out
  exact ⟨(toOutCodewordsCount ℓ ϑ i) - 1, by omega⟩

@[reducible]
def getLastOracleDomainIndex (oracleFrontierIdx : Fin (ℓ + 1)) :
    Fin (ℓ) :=
  oraclePositionToDomainIndex (positionIdx := (getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx))

lemma mkLastOracleIndex_eq_getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    mkLastOracleIndex ℓ ϑ i = getLastOraclePositionIndex ℓ ϑ i := by
  unfold mkLastOracleIndex getLastOraclePositionIndex
  apply Fin.eq_of_val_eq
  by_cases hi : i.val < ℓ
  · simp only [hi, ↓reduceDIte]
    unfold toOutCodewordsCount
    simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceDIte]
    unfold toOutCodewordsCount
    simp only [hi, ↓reduceIte, add_zero];
    have h_eq: i.val = ℓ := by omega
    set_option backward.isDefEq.respectTransparency false in
      simp [h_eq]

lemma getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    = ⟨ℓ / ϑ - 1, by
      dsimp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false];
      simp only [lt_self_iff_false,
        ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff, zero_lt_one, and_true]
      constructor
      · exact pos_of_neZero ϑ
      · apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
      ⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOraclePositionIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet]
  rw [toOutCodewordsCount_last]

lemma getLastOracleDomainIndex_last : getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
    = ⟨ℓ - ϑ, by
      have h_ne_0 : 0 < ϑ := by exact pos_of_neZero ϑ
      have h_lt: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
      omega⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOracleDomainIndex]
  rw [getLastOraclePositionIndex_last]; simp only;
  rw [Nat.sub_mul, Nat.one_mul]
  rw [Nat.div_mul_cancel (hdiv.out)]

lemma getLastOracleDomainIndex_add_ϑ_le (i : Fin (ℓ + 1)) :
    (getLastOracleDomainIndex ℓ ϑ i).val + ϑ ≤ ℓ := by
  rw [getLastOracleDomainIndex, oraclePositionToDomainIndex]
  simp only [oracle_index_add_steps_le_ℓ]
end OracleStatementIndex

section IndexBounds
variable {ℓ ϑ : ℕ} [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

/-- ϑ is positive -/
lemma folding_steps_pos : (ϑ : ℕ) > 0 := pos_of_neZero ϑ

omit hdiv in
/-- ℓ - ϑ < ℓ when both are positive -/
lemma rounds_sub_steps_lt : ℓ - ϑ < ℓ :=
  Nat.sub_lt (pos_of_neZero ℓ) (folding_steps_pos)

lemma ϑ_sub_one_le_self : ϑ - 1 < ϑ := by
  have lt_0: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  exact Nat.sub_one_lt_of_lt lt_0

omit [NeZero ℓ] in
@[simp]
lemma k_mul_ϑ_lt_ℓ {k : Fin (ℓ / ϑ)} :
    ↑k * ϑ < ℓ := by
  have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  calc
    ↑k * ϑ < (ℓ / ϑ) * ϑ := Nat.mul_lt_mul_of_pos_right k.isLt (NeZero.pos ϑ)
    _ = ℓ := h_mul_eq

omit [NeZero ℓ] [NeZero ϑ] in
@[simp]
lemma k_succ_mul_ϑ_le_ℓ {k : Fin (ℓ / ϑ)} : (k.val + 1) * ϑ ≤ ℓ := by
  have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  calc
    (k.val + 1) * ϑ ≤ (ℓ / ϑ) * ϑ := Nat.mul_le_mul_right (k := ϑ) (h := by omega)
    _ = ℓ := h_mul_eq

omit [NeZero ℓ] [NeZero ϑ] in
@[simp]
lemma k_succ_mul_ϑ_le_ℓ_₂ {k : Fin (ℓ / ϑ)} : k.val * ϑ + ϑ ≤ ℓ := by
  conv_lhs => enter [2]; rw [← Nat.one_mul ϑ]
  rw [← Nat.add_mul]
  exact k_succ_mul_ϑ_le_ℓ

variable {r 𝓡 : ℕ} [NeZero r] [NeZero 𝓡]

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
@[simp]
lemma lt_r_of_le_ℓ {h_ℓ_add_R_rate : ℓ + 𝓡 < r} {x : ℕ} (h : x ≤ ℓ) : x < r := by
  omega

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
@[simp]
lemma lt_r_of_lt_ℓ {h_ℓ_add_R_rate : ℓ + 𝓡 < r} {x : ℕ} (h : x < ℓ) : x < r := by
  omega

@[simp] -- main lemma for bIdx: Fin (ℓ / ϑ - 1) bounds
lemma bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x ≤ ℓ - ϑ := by
  have h_x_lt : x < ϑ + 1 := Nat.lt_succ_of_le hx
  have h_fin : x < ϑ ∨ x = ϑ := Nat.lt_or_eq_of_le hx
  calc
    ↑bIdx * ϑ + x ≤ ↑bIdx * ϑ + ϑ := by omega
    _ = (↑bIdx + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
    _ = ℓ - ϑ := by
      have h_bound : 1 ≤ ℓ / ϑ := by
        have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
        rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
      rw [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    _ ≤ ℓ - ϑ := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_lt_ℓ_succ {m : ℕ} (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin ϑ) :
    ↑bIdx * ϑ + ↑i < ℓ + m :=
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt
    _ ≤ ℓ + m := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1 + 1)) :
    ↑bIdx * ϑ + i < ℓ + 1 := by
  calc
    ↑bIdx * ϑ + i ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx (x:=i.val) (hx:=by omega)
    _ < ℓ + 1 := by omega

@[simp]
lemma bIdx_mul_ϑ_add_x_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x < ℓ + 1 := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx x (hx:=hx)
    _ < ℓ + 1 := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1)) :
    ↑bIdx * ϑ + ↑i < ℓ := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt

/-- When the block size allows it, we can get a strict inequality -/
lemma bIdx_succ_mul_ϑ_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) :
    (↑bIdx + 1) * ϑ < ℓ + 1 := by
  calc
    (↑bIdx + 1) * ϑ = ↑bIdx * ϑ + ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx ϑ (hx:=by omega)
    _ < ℓ + 1 := by omega

lemma bIdx_succ_mul_ϑ_le_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) : (↑bIdx + 1) * ϑ ≤ ℓ + 1 := by
  exact Nat.le_of_lt (bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx)

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

@[simp]
lemma val_mkFromStmtIdx {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :
    (mkFromStmtIdx stmtIdx).val = stmtIdx := rfl

@[simp]
lemma val_mkFromStmtIdxCastSuccOfSucc {ℓ : ℕ} (i : Fin ℓ) :
    (mkFromStmtIdxCastSuccOfSucc i).val = i.castSucc := rfl

@[simp]
lemma val_le_i {ℓ : ℕ} (i : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex i) :
    oracleIdx.val ≤ i := by
  unfold OracleFrontierIndex at oracleIdx
  let h := oracleIdx.property
  cases h
  · exact h.left

@[simp]
lemma val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx {ℓ : ℕ} (i : Fin ℓ) :
    (mkFromStmtIdxCastSuccOfSucc i).val = (mkFromStmtIdx i.castSucc).val := by rfl

end OracleFrontierIndex

section SumcheckOperations

/-- We treat the multiplier poly as a blackbox for protocol abstraction.
For example, in Binary Basefold it's `eqTilde(r₀, .., r_{ℓ-1}, X₀, .., X_{ℓ-1})` -/
structure SumcheckMultiplierParam (L : Type) [CommRing L] (ℓ : ℕ) (Context : Type := Unit) where
  multpoly : (ctx: Context) → MultilinearPoly L ℓ

/-- `H₀(X₀, ..., X_{ℓ-1}) = h(X₀, ..., X_{ℓ-1}) =`
  `m(X_0, ..., X_{ℓ-1}) · t(X_0, ..., X_{ℓ-1})` -/
def computeInitialSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) : MultiquadraticPoly L ℓ :=
  ⟨m * t, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    have h_t_deg: degreeOf i t.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (t.property) a i
    have h_m_deg: degreeOf i m.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (m.property) a i
    calc
      _ ≤ (degreeOf i m.val) + (degreeOf i t.val) :=
        degreeOf_mul_le i m.val t.val
      _ ≤ 2 := by omega
  ⟩

/-- `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = ∑ ω ∈ 𝓑ᵢ, H₀(ω₀, …, ω_{i-1}, Xᵢ, …, X_{ℓ-1}) (where H₀=h)` -/
-- TODO: how to generalize this?
def projectToMidSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L) :
    MultiquadraticPoly L (ℓ-i) :=
  let H₀: MultiquadraticPoly L ℓ := computeInitialSumcheckPoly (ℓ:=ℓ) t m
  let Hᵢ := fixFirstVariablesOfMQP (ℓ := ℓ) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)
  ⟨Hᵢ, by
    have hp := H₀.property
    exact
      fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ) (v := ⟨i, by omega⟩)
        (poly := H₀.val) (challenges := challenges) (deg := 2) hp
  ⟩

/-- Derive `H_{i+1}` from `H_i` by projecting the first variable -/
def projectToNextSumcheckPoly (i : Fin (ℓ)) (Hᵢ : MultiquadraticPoly L (ℓ - i))
    (rᵢ : L) : -- the current challenge
    MultiquadraticPoly L (ℓ - i.succ) := by
  let projectedH := fixFirstVariablesOfMQP (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
    (H := Hᵢ.val) (challenges := fun _ => rᵢ)
  exact ⟨projectedH, by
    have hp := Hᵢ.property
    exact
      fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
        (poly := Hᵢ.val) (challenges := fun _ => rᵢ) (deg := 2) hp
  ⟩

omit [NeZero ℓ] in
lemma projectToNextSumcheckPoly_eval_eq (i : Fin ℓ) (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L)
    (x : Fin (ℓ - i.succ) → L) :
    (projectToNextSumcheckPoly ℓ i Hᵢ rᵢ).val.eval x =
    Hᵢ.val.eval (Fin.cons rᵢ x ∘ Fin.cast (by simp only [Fin.val_succ]; omega)) := by
  have : NeZero (ℓ - i) := ⟨Nat.sub_ne_zero_of_lt i.isLt⟩
  have h_eq_nat : ℓ - i = (ℓ - i.succ) + 1 := by
    exact (Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.sub_pos_of_lt i.isLt))).symm
  unfold projectToNextSumcheckPoly
  dsimp
  have h_eval := fixFirstVariablesOfMQP_eval_eq (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
    (poly := Hᵢ.val) (challenges := fun _ => rᵢ) (x := x)
  have h_fun :
      (fun j : Fin (ℓ - i) =>
        if hj : j.val < 1 then
          (fun _ : Fin 1 => rᵢ) ⟨j.val, hj⟩
        else
          x ⟨j.val - 1, by omega⟩) =
      Fin.cons rᵢ x ∘ Fin.cast h_eq_nat := by
    ext j
    rcases Fin.eq_zero_or_eq_succ (Fin.cast h_eq_nat j) with hzero | ⟨k, hk⟩
    · have hj0 : j = 0 := by
        apply Fin.cast_injective h_eq_nat
        exact hzero
      subst hj0
      simp [hzero]
    · have hj_val : j.val = k.val + 1 := by
        have h_val : (Fin.cast h_eq_nat j).val = k.succ.val := congrArg Fin.val hk
        simp only [Fin.val_succ] at h_val
        exact h_val
      have hj_not_lt : ¬ j.val < 1 := by
        omega
      have hk_eq : ⟨j.val - 1, by omega⟩ = k := by
        apply Fin.ext
        simp [hj_val]
      simp only [hj_not_lt, ↓reduceDIte, Function.comp_apply]
      rw [hk]
      change x ⟨j.val - 1, by omega⟩ = x k
      rw [hk_eq]
  change (MvPolynomial.eval x)
    (fixFirstVariablesOfMQP (ℓ - i) ⟨1, by omega⟩ Hᵢ.val (fun _ => rᵢ)) =
      (MvPolynomial.eval (fun j =>
        if hj : j.val < 1 then (fun _ : Fin 1 => rᵢ) ⟨j.val, hj⟩
        else x ⟨j.val - 1, by omega⟩)) Hᵢ.val at h_eval
  rw [h_fun] at h_eval
  exact h_eval

omit [NeZero ℓ] in
/-- **Key Sumcheck Property**: Evaluating the sumcheck round polynomial at a challenge equals
    the sum of the projected polynomial evaluations over the boolean hypercube.
    This is the fundamental relationship for the sumcheck protocol: when we create the round
    polynomial `g_i = getSumcheckRoundPoly(H_i)` and evaluate it at a challenge `rᵢ`, this equals
    the sum of evaluations of `H_{i+1} = projectToNextSumcheckPoly(H_i, rᵢ)` over all boolean
    points.
    Mathematically: `g_i(rᵢ) = ∑_{x ∈ {0,1}^{ℓ-i-1}} H_{i+1}(x)` where
    - `g_i` is the univariate sumcheck round polynomial derived from `H_i`
    - `H_{i+1}` is obtained by fixing the first variable of `H_i` to `rᵢ`
-/
lemma projectToNextSumcheckPoly_sum_eq (i : Fin ℓ) (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L) :
    (getSumcheckRoundPoly ℓ 𝓑 i Hᵢ).val.eval rᵢ =
    (∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
      (projectToNextSumcheckPoly ℓ i Hᵢ rᵢ).val.eval x) := by
  rw [getSumcheckRoundPoly_eval_eq]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [projectToNextSumcheckPoly_eval_eq]

set_option maxHeartbeats 200000 in
-- Bound elaboration for the explicit `bind₁` normalization proof.
omit [NeZero ℓ] in
lemma fixFirstVariablesOfMQP_eq_bind₁ (v : Fin (ℓ + 1)) (poly : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) :
    fixFirstVariablesOfMQP (L := L) ℓ v poly challenges =
      bind₁ (fun j =>
        if hj : j.val < v.val then
          C (challenges ⟨j.val, hj⟩)
        else
          X (⟨j.val - v, by omega⟩ : Fin (ℓ - v))) poly := by
  let subst : Fin ℓ → MvPolynomial (Fin (ℓ - v)) L := fun j =>
    if hj : j.val < v.val then
      C (challenges ⟨j.val, hj⟩)
    else
      X (⟨j.val - v, by omega⟩ : Fin (ℓ - v))
  have hX : ∀ j : Fin ℓ,
      fixFirstVariablesOfMQP (L := L) ℓ v (X j) challenges = bind₁ subst (X j) := by
    intro j
    rw [bind₁_X_right]
    unfold subst
    unfold fixFirstVariablesOfMQP
    dsimp
    rw [MvPolynomial.rename_X]
    change
      (MvPolynomial.map (MvPolynomial.eval challenges))
        ((MvPolynomial.sumAlgEquiv L (Fin (ℓ - v)) (Fin v))
          (MvPolynomial.X (if hj : j.val < v.val then
            Sum.inr ⟨j.val, hj⟩
          else
            Sum.inl ⟨j.val - v, by omega⟩))) =
      (if hj : j.val < v.val then
        MvPolynomial.C (challenges ⟨j.val, hj⟩)
      else
        MvPolynomial.X (⟨j.val - v, by omega⟩ : Fin (ℓ - v)))
    by_cases hj : j.val < v.val
    · simp [hj, MvPolynomial.sumAlgEquiv_X_inr]
    · simp [hj, MvPolynomial.sumAlgEquiv_X_inl]
  induction poly using MvPolynomial.induction_on with
  | C a =>
      unfold fixFirstVariablesOfMQP
      simp only [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_C_inl,
        MvPolynomial.map_C, MvPolynomial.eval_C, bind₁_C_right]
  | add p q hp hq =>
      calc
        fixFirstVariablesOfMQP (L := L) ℓ v (p + q) challenges =
            fixFirstVariablesOfMQP (L := L) ℓ v p challenges +
              fixFirstVariablesOfMQP (L := L) ℓ v q challenges := by
          unfold fixFirstVariablesOfMQP
          simp
        _ = bind₁ subst p + bind₁ subst q := by
          rw [hp, hq]
        _ = bind₁ subst (p + q) := by
          symm
          exact (bind₁ subst).map_add p q
  | mul_X p j hp =>
      calc
        fixFirstVariablesOfMQP (L := L) ℓ v (p * X j) challenges =
            fixFirstVariablesOfMQP (L := L) ℓ v p challenges *
              fixFirstVariablesOfMQP (L := L) ℓ v (X j) challenges := by
          unfold fixFirstVariablesOfMQP
          simp
        _ = bind₁ subst p * bind₁ subst (X j) := by
          rw [hp, hX]
        _ = bind₁ subst (p * X j) := by
          symm
          exact (bind₁ subst).map_mul p (X j)

set_option maxHeartbeats 200000 in
-- Bound elaboration for the substitution-composition proof.
omit [NeZero ℓ] in
lemma projectToMidSumcheckPoly_succ (t : MultilinearPoly L ℓ) (m : MultilinearPoly L ℓ) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i') =
    projectToNextSumcheckPoly ℓ i (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i' := by
  apply Subtype.ext
  unfold projectToMidSumcheckPoly projectToNextSumcheckPoly
  dsimp
  have : NeZero (ℓ - i) := ⟨Nat.sub_ne_zero_of_lt i.isLt⟩
  let H0 : MvPolynomial (Fin ℓ) L := (computeInitialSumcheckPoly (L := L) (ℓ := ℓ) t m).val
  change
    fixFirstVariablesOfMQP (L := L) ℓ (v := i.succ) H0 (Fin.snoc challenges r_i') =
      fixFirstVariablesOfMQP (L := L) (ℓ - i) (v := (⟨1, by omega⟩ : Fin ((ℓ - i) + 1)))
        (fixFirstVariablesOfMQP (L := L) ℓ (v := i.castSucc) H0 challenges)
        (fun _ => r_i')
  rw [fixFirstVariablesOfMQP_eq_bind₁ (L := L) (ℓ := ℓ) (v := i.succ) (poly := H0)
    (challenges := Fin.snoc challenges r_i')]
  rw [fixFirstVariablesOfMQP_eq_bind₁ (L := L) (ℓ := ℓ) (v := i.castSucc) (poly := H0)
    (challenges := challenges)]
  let oldPoly : MvPolynomial (Fin (ℓ - i)) L :=
    bind₁
      (fun j =>
        if hj : j.val < i.castSucc.val then
          C (challenges ⟨j.val, hj⟩)
        else
          X (⟨j.val - i.castSucc, by
            have hj_ge : i.castSucc.val ≤ j.val := Nat.le_of_not_gt hj
            have hsub : j.val - i.val < ℓ - i.val := Nat.sub_lt_sub_right hj_ge j.isLt
            rw [Fin.val_castSucc]
            exact hsub⟩ : Fin (ℓ - i))) H0
  change
    bind₁
        (fun j =>
          if hj : j.val < i.succ.val then
            C ((Fin.snoc challenges r_i' : Fin i.succ → L) ⟨j.val, hj⟩)
          else
            X (⟨j.val - i.succ, by
              have hj_ge : i.succ.val ≤ j.val := Nat.le_of_not_gt hj
              exact Nat.sub_lt_sub_right hj_ge j.isLt⟩ : Fin (ℓ - i.succ))) H0 =
      fixFirstVariablesOfMQP (L := L) (ℓ - i) (v := (⟨1, by omega⟩ : Fin ((ℓ - i) + 1)))
        oldPoly (fun _ => r_i')
  rw [fixFirstVariablesOfMQP_eq_bind₁ (L := L) (ℓ := ℓ - i)
    (v := (⟨1, by omega⟩ : Fin ((ℓ - i) + 1)))
    (poly := oldPoly)
    (challenges := fun _ => r_i')]
  dsimp only [oldPoly]
  conv_rhs => rw [bind₁_bind₁]
  let lhsSubst : Fin ℓ → MvPolynomial (Fin (ℓ - i.succ)) L := fun j =>
    if hj : j.val < i.succ.val then
      C ((Fin.snoc challenges r_i' : Fin (i.val + 1) → L)
        ⟨j.val, by simpa only [Fin.val_succ] using hj⟩)
    else
      X (⟨j.val - i.succ, by
        have hj_ge : i.succ.val ≤ j.val := Nat.le_of_not_gt hj
        exact Nat.sub_lt_sub_right hj_ge j.isLt⟩ : Fin (ℓ - i.succ))
  let oldSubst : Fin ℓ → MvPolynomial (Fin (ℓ - i)) L := fun j =>
    if hj : j.val < i.castSucc.val then
      C (challenges ⟨j.val, hj⟩)
    else
      X (⟨j.val - i.castSucc, by
        have hj_ge : i.castSucc.val ≤ j.val := Nat.le_of_not_gt hj
        have hsub : j.val - i.val < ℓ - i.val := Nat.sub_lt_sub_right hj_ge j.isLt
        rw [Fin.val_castSucc]
        exact hsub⟩ : Fin (ℓ - i))
  let oneSubst : Fin (ℓ - i) → MvPolynomial (Fin (ℓ - i.succ)) L := fun j =>
    if hj : j.val < 1 then
      C r_i'
    else
      X (⟨j.val - 1, by
        have hj_ge : 1 ≤ j.val := Nat.le_of_not_gt hj
        exact Nat.sub_lt_sub_right hj_ge j.isLt⟩ : Fin (ℓ - i.succ))
  change bind₁ lhsSubst H0 = bind₁ (fun j => bind₁ oneSubst (oldSubst j)) H0
  have hsubst : lhsSubst = fun j => bind₁ oneSubst (oldSubst j) := by
    funext j
    by_cases hj : j.val < i.val
    · have hsucc : j.val < i.succ.val := by
        rw [Fin.val_succ]
        omega
      have hleft :
          lhsSubst j = MvPolynomial.C
            ((Fin.snoc challenges r_i' : Fin (i.val + 1) → L) ⟨j.val, by omega⟩) := by
        dsimp [lhsSubst]
        split_ifs with h
        · rfl
        · exfalso
          omega
      have hold :
          oldSubst j = MvPolynomial.C (challenges ⟨j.val, by
            rw [Fin.val_castSucc]
            exact hj⟩) := by
        dsimp [oldSubst]
        simp [hj]
      rw [hleft, hold, bind₁_C_right]
      let k : Fin i.castSucc := ⟨j.val, by
        rw [Fin.val_castSucc]
        exact hj⟩
      have hsnoc_idx : (⟨j.val, by omega⟩ : Fin (i.val + 1)) = k.castSucc := by
        apply Fin.ext
        rfl
      rw [hsnoc_idx]
      simp [Fin.snoc]
      congr 1
    · by_cases hji : j = i
      · subst j
        have hsucc : i.val < i.succ.val := by
          rw [Fin.val_succ]
          omega
        have hnotcast : ¬ i.val < i.castSucc.val := by
          rw [Fin.val_castSucc]
          omega
        have hzero :
            (⟨i.val - i.castSucc, by
              dsimp
              omega⟩ : Fin (ℓ - i)) = 0 := by
          apply Fin.ext
          dsimp
          omega
        have hleft :
            lhsSubst i = MvPolynomial.C
              ((Fin.snoc challenges r_i' : Fin (i.val + 1) → L) ⟨i.val, by omega⟩) := by
          dsimp [lhsSubst]
          split_ifs with h
          · rfl
          · exfalso
            omega
        have hold : oldSubst i = MvPolynomial.X (0 : Fin (ℓ - i)) := by
          dsimp [oldSubst]
          simp
        have hright : bind₁ oneSubst (oldSubst i) = MvPolynomial.C r_i' := by
          rw [hold, bind₁_X_right]
          dsimp [oneSubst]
        rw [hleft, hright]
        have hlast : (⟨i.val, by omega⟩ : Fin (i.val + 1)) = Fin.last i.val := by
          apply Fin.ext
          simp [Fin.val_last]
        rw [hlast, Fin.snoc_last]
      · have hnotsucc : ¬ j.val < i.succ.val := by
          rw [Fin.val_succ]
          omega
        have hnotcast : ¬ j.val < i.castSucc.val := by
          rw [Fin.val_castSucc]
          exact hj
        let k : Fin (ℓ - i) := ⟨j.val - i.castSucc, by
          have hj_ge : i.castSucc.val ≤ j.val := Nat.le_of_not_gt hnotcast
          have hsub : j.val - i.val < ℓ - i.val := Nat.sub_lt_sub_right hj_ge j.isLt
          rw [Fin.val_castSucc]
          exact hsub⟩
        let lhsIdx : Fin (ℓ - i.succ) := ⟨j.val - i.succ, by
          have hj_ge : i.succ.val ≤ j.val := Nat.le_of_not_gt hnotsucc
          exact Nat.sub_lt_sub_right hj_ge j.isLt⟩
        have hnotone : ¬ k.val < 1 := by
          dsimp [k]
          omega
        have hidx :
            lhsIdx =
              ⟨k.val - 1, by
                have hk_ge : 1 ≤ k.val := Nat.le_of_not_gt hnotone
                exact Nat.sub_lt_sub_right hk_ge k.isLt⟩ := by
          apply Fin.ext
          dsimp [lhsIdx, k]
          omega
        have hleft : lhsSubst j = MvPolynomial.X lhsIdx := by
          dsimp [lhsSubst, lhsIdx]
          split_ifs with h
          · exfalso
            change j.val < i.succ.val at h
            exact hnotsucc h
          · rfl
        have hold : oldSubst j = MvPolynomial.X k := by
          change
            (if h : j.val < i.val then
              MvPolynomial.C (challenges ⟨j.val, by
                rw [Fin.val_castSucc]
                exact h⟩)
            else
              MvPolynomial.X k) = MvPolynomial.X k
          split_ifs
          rfl
        have hright : bind₁ oneSubst (oldSubst j) = MvPolynomial.X lhsIdx := by
          rw [hold, bind₁_X_right]
          dsimp [oneSubst]
          simp [hnotone, hidx]
        rw [hleft, hright]
  rw [hsubst]

omit [NeZero ℓ] in
lemma projectToMidSumcheckPoly_eq_prod (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L) :
    projectToMidSumcheckPoly (ℓ := ℓ) (t := t) (m := m) (i := i) (challenges := challenges) =
      (fixFirstVariablesOfMQP ℓ (v := i) (H := m) (challenges := challenges)) *
       (fixFirstVariablesOfMQP ℓ (v := i) (H := t) (challenges := challenges)) := by
  unfold projectToMidSumcheckPoly computeInitialSumcheckPoly fixFirstVariablesOfMQP
  simp

omit [NeZero ℓ] in
lemma fixFirstVariablesOfMQP_full_eval_eq_eval {deg : ℕ} {challenges : Fin (Fin.last ℓ) → L}
    {poly : L[X Fin ℓ]} (_hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) (x : Fin (ℓ - ℓ) → L) :
      (fixFirstVariablesOfMQP ℓ (v := Fin.last ℓ) poly challenges).eval x
      = poly.eval challenges := by
  have h_eval := fixFirstVariablesOfMQP_eval_eq (L := L) (ℓ := ℓ) (v := Fin.last ℓ)
    (poly := poly) (challenges := challenges) (x := x)
  have h_fun :
      (fun j =>
        if hj : j.val < (Fin.last ℓ).val then
          challenges ⟨j.val, hj⟩
        else
          x ⟨j.val - Fin.last ℓ, by omega⟩) = challenges := by
    funext j
    have hj : j.val < (Fin.last ℓ).val := by
      change j.val < ℓ
      exact j.isLt
    have h_cast : (⟨j.val, hj⟩ : Fin (Fin.last ℓ)) = j := by
      apply Fin.ext
      rfl
    rw [dif_pos hj, h_cast]
  exact h_eval.trans (congrArg (fun f => MvPolynomial.eval f poly) h_fun)

omit [NeZero ℓ] in
/-- At `Fin.last ℓ`, the projected sumcheck polynomial evaluates to `multiplier * t(challenges)`.
When evaluated at the "zero" point (empty domain), the product structure emerges. -/
lemma projectToMidSumcheckPoly_at_last_eval
    (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ)
    (challenges : Fin ℓ → L) :
    ∀ x, (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
      (i := Fin.last ℓ) (challenges := challenges)).val.eval x =
    m.val.eval challenges * t.val.eval challenges := by
  intro x
  -- At Fin.last ℓ, the projection has ℓ - ℓ = 0 remaining variables
  -- So we're evaluating a constant polynomial
  -- Use projectToMidSumcheckPoly_eq_prod to decompose into product
  have h_eq_prod := projectToMidSumcheckPoly_eq_prod (L := L) (ℓ := ℓ) t m (Fin.last ℓ) challenges
  -- Extract the .val equality
  have h_val_eq : (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
      (i := Fin.last ℓ) (challenges := challenges)).val =
    ((fixFirstVariablesOfMQP ℓ (v := Fin.last ℓ) (H := m) (challenges := challenges)) *
     (fixFirstVariablesOfMQP ℓ (v := Fin.last ℓ) (H := t) (challenges := challenges))) := by
    rw [h_eq_prod]
  rw [h_val_eq, map_mul]
  -- Both factors become full evaluations at challenges
  have h_m := fixFirstVariablesOfMQP_full_eval_eq_eval (ℓ := ℓ)
    (poly := m.val) (challenges := challenges) (_hp := m.property)
    (x := x)
  have h_t := fixFirstVariablesOfMQP_full_eval_eq_eval (ℓ := ℓ)
    (poly := t.val) (challenges := challenges) (_hp := t.property)
    (x := x)
  congr 1 -- this auto rw using h_m and h_t

omit [NeZero ℓ] in
/-- At `Fin.last ℓ`, the projected sumcheck polynomial is exactly the constant polynomial
equal to the product of the evaluations. This does NOT require an infinite field. -/
lemma projectToMidSumcheckPoly_at_last_eq
    (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ)
    (challenges : Fin ℓ → L) :
    (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
      (i := Fin.last ℓ) (challenges := challenges)).val =
    MvPolynomial.C (m.val.eval challenges * t.val.eval challenges) := by
  -- The domain Fin (ℓ - ℓ) is empty, so both sides are constant polynomials
  -- We prove equality by showing they have the same constant coefficient
  have h_dim : ℓ - ↑(Fin.last ℓ) = 0 := Nat.sub_self ℓ
  -- Since Fin (ℓ - ℓ) is empty (isomorphic to Fin 0), use isEmpty instance
  have : IsEmpty (Fin (ℓ - ↑(Fin.last ℓ))) := by
    rw [h_dim]
    infer_instance
  rw [MvPolynomial.eq_C_of_isEmpty
      (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
        (i := Fin.last ℓ) (challenges := challenges)).val]
  rw [← congrFun MvPolynomial.constantCoeff_eq]
  rw [← MvPolynomial.eval_zero]
  exact congrArg MvPolynomial.C
    (projectToMidSumcheckPoly_at_last_eval (L := L) (ℓ := ℓ) (t := t) (m := m)
      (challenges := challenges) (x := (0 : Fin (ℓ - (Fin.last ℓ).val) → L)))

end SumcheckOperations


end Binius.BinaryBasefold
