/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude
import ArkLib.Data.MvPolynomial.ComputableDegreeLE
import ArkLib.Data.MvPolynomial.MultilinearComputational

/- ## Fundamental OracleReduction-related defintions for protocol specifications -/

section
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
  simp only [Fin.coe_ofNat_eq_mod, zero_mod, Nat.zero_div, zero_add, ite_eq_left_iff, not_lt,
    nonpos_iff_eq_zero, zero_ne_one, imp_false]
  exact NeZero.ne ℓ

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
lemma oracle_block_k_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    : j.val * ϑ ≤ i := by
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
    simp only [hi, eq_mpr_eq_cast, cast_eq, ↓reduceIte, add_zero];
    have h_eq: i.val = ℓ := by omega
    rw [h_eq]

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
lemma bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1 + 1))
    : ↑bIdx * ϑ + i < ℓ + 1 := by
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
lemma bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1))
    : ↑bIdx * ϑ + ↑i < ℓ := by
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

variable [DecidableEq L]

/-- Computable multilinear polynomial from hypercube evaluations (`CMvPolynomial` / `CMLE'`).
See `MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE'`. -/
def MultilinearPoly.ofCMLEEvals {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) : MultilinearPoly L ℓ :=
  CPoly.CMvPolynomial.ofDegreeLE (n := ℓ) (R := L) 1 (MvPolynomial.Computational.CMLE' evals)

theorem MultilinearPoly.ofCMLEEvals_val {L : Type} [CommRing L] [DecidableEq L] [BEq L]
    [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) :
    (ofCMLEEvals evals).val = MLE' evals := by
  sorry

/-- Same carrier as `⟨MLE evals, MLE_mem_restrictDegree evals⟩`, built via `CMLE'`. -/
def MultilinearPoly.ofHypercubeEvals {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : (Fin ℓ → Fin 2) → L) : MultilinearPoly L ℓ :=
  ofCMLEEvals (fun i => evals (finFunctionFinEquiv.symm i))

theorem MultilinearPoly.ofHypercubeEvals_val {L : Type} [CommRing L] [DecidableEq L] [BEq L]
    [LawfulBEq L] {ℓ : ℕ}
    (evals : (Fin ℓ → Fin 2) → L) :
    (ofHypercubeEvals evals).val = MLE evals := by
  sorry

/-- Multilinear witness from a `CMvPolynomial` carrier (multilinearity deferred). -/
def MultilinearPoly.ofCMvPoly {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (p : CPoly.CMvPolynomial ℓ L) : MultilinearPoly L ℓ :=
  CPoly.CMvPolynomial.ofDegreeLE (n := ℓ) (R := L) 1 p

/-- Multiquadratic witness from a `CMvPolynomial` carrier (degree bound deferred). -/
def MultiquadraticPoly.ofCMvPoly {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (p : CPoly.CMvPolynomial ℓ L) : MultiquadraticPoly L ℓ :=
  CPoly.CMvPolynomial.ofDegreeLE (n := ℓ) (R := L) 2 p

/-- Executable `CMLE'` for the hypercube evaluations of a multilinear witness. -/
def MultilinearPoly.toCMvPoly {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (p : MultilinearPoly L ℓ) : CPoly.CMvPolynomial ℓ L :=
  p

theorem MultilinearPoly.ofCMLEEvals_eval_zeroOne {L : Type} [CommRing L] [DecidableEq L]
    [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) (x : Fin ℓ → Fin 2) :
    MvPolynomial.eval (x : Fin ℓ → L) (ofCMLEEvals evals).val = evals (finFunctionFinEquiv x) := by
  sorry

theorem MultilinearPoly.ofCMLEEvals_cmEval_eq_val_eval {L : Type} [CommRing L] [DecidableEq L]
    [BEq L] [LawfulBEq L] {ℓ : ℕ} (evals : Fin (2 ^ ℓ) → L) (x : Fin ℓ → Fin 2) :
    CPoly.CMvPolynomial.eval (x : Fin ℓ → L) (MvPolynomial.Computational.CMLE' evals) =
      MvPolynomial.eval (x : Fin ℓ → L) (ofCMLEEvals evals).val := by
  sorry

/-- We treat the multiplier poly as a blackbox for protocol abstraction.
For example, in Binary Basefold it's `eqTilde(r₀, .., r_{ℓ-1}, X₀, .., X_{ℓ-1})` -/
structure SumcheckMultiplierParam (L : Type) [CommRing L] (ℓ : ℕ) (Context : Type := Unit) where
  multpoly : (ctx: Context) → MultilinearPoly L ℓ

/-- `H₀(X₀, ..., X_{ℓ-1}) = h(X₀, ..., X_{ℓ-1}) =`
  `m(X_0, ..., X_{ℓ-1}) · t(X_0, ..., X_{ℓ-1})` -/
def computeInitialSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) : MultiquadraticPoly L ℓ :=
  by
    let h0 : CPoly.CMvPolynomial ℓ L := by
      simpa using (MultilinearPoly.toCMvPoly m * MultilinearPoly.toCMvPoly t)
    refine ⟨h0, ?_⟩
    intro i
    sorry

/-- `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = ∑ ω ∈ 𝓑ᵢ, H₀(ω₀, …, ω_{i-1}, Xᵢ, …, X_{ℓ-1}) (where H₀=h)` -/
-- TODO: how to generalize this?
def projectToMidSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : MultiquadraticPoly L (ℓ-i) :=
  let H₀ : MultiquadraticPoly L ℓ := computeInitialSumcheckPoly (ℓ := ℓ) t m
  fixFirstVariablesOfDegreeLE (L := L) (ℓ := ℓ) (d := 2) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)

/-- Derive `H_{i+1}` from `H_i` by projecting the first variable -/
def projectToNextSumcheckPoly (i : Fin (ℓ)) (Hᵢ : MultiquadraticPoly L (ℓ - i))
    (rᵢ : L) : -- the current challenge
    MultiquadraticPoly L (ℓ - i.succ) :=
  fixFirstVariablesOfDegreeLE (L := L) (ℓ := ℓ - i) (d := 2) (v := ⟨1, by omega⟩)
    (H := Hᵢ) (challenges := fun _ => rᵢ)

lemma projectToNextSumcheckPoly_eval_eq (i : Fin ℓ) (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L)
    (x : Fin (ℓ - i.succ) → L) :
    (projectToNextSumcheckPoly ℓ i Hᵢ rᵢ).val.eval x =
    Hᵢ.val.eval (Fin.cons rᵢ x ∘ Fin.cast (by simp only [Fin.val_succ]; omega)) := by
  haveI : NeZero (ℓ - i) := ⟨Nat.sub_ne_zero_of_lt i.isLt⟩
  have h_eq_nat : ℓ - i = (ℓ - i.succ) + 1 := by
    exact (Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.sub_pos_of_lt i.isLt))).symm
  have h_eval := fixFirstVariablesOfCMvPoly_eval_eq (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
    (H := Hᵢ) (challenges := fun _ => rᵢ) (x := x)
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
      simp [hj_not_lt, hk, hk_eq]
  rw [h_fun] at h_eval
  simpa [projectToNextSumcheckPoly, MultiquadraticPoly.val, fixFirstVariablesOfDegreeLE] using h_eval

/-- **Key Sumcheck Property**: Evaluating the sumcheck round polynomial at a challenge equals
    the sum of the projected polynomial evaluations over the boolean hypercube.
    This is the fundamental relationship for the sumcheck protocol: when we create the round
    message polynomial `g_i = getSumcheckRoundMessage(H_i)` and evaluate it at a challenge
    `rᵢ`, this equals the sum of evaluations of `H_{i+1} = projectToNextSumcheckPoly(H_i, rᵢ)`
    over all boolean points.
    Mathematically: `g_i(rᵢ) = ∑_{x ∈ {0,1}^{ℓ-i-1}} H_{i+1}(x)` where
    - `g_i` is the univariate computable fold message derived from `H_i`
    - `H_{i+1}` is obtained by fixing the first variable of `H_i` to `rᵢ`
-/
lemma projectToNextSumcheckPoly_sum_eq (i : Fin ℓ) (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L) :
    FoldMessage.eval (getSumcheckRoundMessage (L := L) (ℓ := ℓ) (𝓑 := 𝓑) i Hᵢ) rᵢ =
    (∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
      (projectToNextSumcheckPoly ℓ i Hᵢ rᵢ).val.eval x) :=
  by
  sorry

set_option maxHeartbeats 200000 in
-- Bound elaboration for the explicit `bind₁` normalization proof.
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
        ((sumToIter L (Fin (ℓ - v)) (Fin v))
          (MvPolynomial.X (if hj : j.val < v.val then
            Sum.inr ⟨j.val, hj⟩
          else
            Sum.inl ⟨j.val - v, by omega⟩))) =
      (if hj : j.val < v.val then
        MvPolynomial.C (challenges ⟨j.val, hj⟩)
      else
        MvPolynomial.X (⟨j.val - v, by omega⟩ : Fin (ℓ - v)))
    by_cases hj : j.val < v.val
    · simp [hj, MvPolynomial.sumToIter_Xr]
    · simp [hj, MvPolynomial.sumToIter_Xl]
  induction poly using MvPolynomial.induction_on with
  | C a =>
      unfold fixFirstVariablesOfMQP
      simp only [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_apply, MvPolynomial.sumToIter_C,
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
lemma projectToMidSumcheckPoly_succ (t : MultilinearPoly L ℓ) (m : MultilinearPoly L ℓ) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i') =
    projectToNextSumcheckPoly ℓ i (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i' := by
  sorry

lemma projectToMidSumcheckPoly_eq_prod (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : (projectToMidSumcheckPoly (ℓ := ℓ) (t := t) (m := m)
        (i := i) (challenges := challenges)).val =
      (fixFirstVariablesOfMQP ℓ (v := i) (H := MultilinearPoly.val m)
        (challenges := challenges)) *
      (fixFirstVariablesOfMQP ℓ (v := i) (H := MultilinearPoly.val t)
        (challenges := challenges)) := by
  sorry

lemma fixFirstVariablesOfMQP_full_eval_eq_eval {deg : ℕ} {challenges : Fin (Fin.last ℓ) → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) (x : Fin (ℓ - ℓ) → L) :
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

/-- At `Fin.last ℓ`, the projected sumcheck polynomial evaluates to `multiplier * t(challenges)`.
When evaluated at the "zero" point (empty domain), the product structure emerges. -/
lemma projectToMidSumcheckPoly_at_last_eval
    (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ)
    (challenges : Fin ℓ → L) :
    ∀ x, (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
      (i := Fin.last ℓ) (challenges := challenges)).val.eval x =
    m.val.eval challenges * t.val.eval challenges := by
  sorry

/-- At `Fin.last ℓ`, the projected sumcheck polynomial is exactly the constant polynomial
equal to the product of the evaluations. This does NOT require an infinite field. -/
lemma projectToMidSumcheckPoly_at_last_eq
    (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ)
    (challenges : Fin ℓ → L) :
    (projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t) (m := m)
      (i := Fin.last ℓ) (challenges := challenges)).val =
    MvPolynomial.C (m.val.eval challenges * t.val.eval challenges) := by
  sorry

end SumcheckOperations

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section OracleReductionComponents
-- In this section, we use notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-!
## Core Protocol Structures

Basic structures and definitions used throughout the Binary Basefold protocol.
-/

/-- Input context for the sumcheck protocol, used mainly in BinaryBasefold.
For other protocols, there might be other context data.
NOTE: might add a flag `rejected` to indicate if prover has been rejected before. But that seems
like a fundamental feature of OracleReduction instead, so no action taken for now. -/
structure SumcheckBaseContext (L : Type) (ℓ : ℕ) where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

/-- Statement per iterated sumcheck round -/
structure Statement (Context : Type) (i : Fin (ℓ + 1)) where
  -- Current round state
  sumcheck_target : L              -- s_i (current sumcheck target for round i)
  challenges : Fin i → L           -- R'_i = (r'_0, ..., r'_{i-1}) from previous rounds
  ctx : Context -- external context for composition from the outer protocol

/-- Statement for the final sumcheck step - includes the final constant c -/
structure FinalSumcheckStatementOut extends
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ) where
  final_constant : L               -- c = f^(ℓ)(0, ..., 0)

def toStatement (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ)  :=
  {
    sumcheck_target := stmt.sumcheck_target,
    challenges := stmt.challenges,
    ctx := stmt.ctx
  }

/-- For the `i`-th round of the protocol, there will be oracle statements corresponding
to all committed codewords. The verifier has oracle access to functions corresponding
to the handles in committed_handles. -/
@[reducible]
def OracleStatement (ϑ : ℕ) [NeZero ϑ] (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ (i:=i)) → Type := fun j =>
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩

/- First oracle witness consistency: the witness polynomial t, when projected to level 0 and
   evaluated on the initial domain S^(0), must be close within unique decoding radius to f^(0). -/

def firstOracleWitnessConsistencyProp (t : MultilinearPoly L ℓ)
    (f₀ : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0) : Prop := by
  sorry

/-- **Oracle Access Congruence**:
Proves equality of oracle evaluations `oStmtIn j x = oStmtIn j' x'` -/
lemma OracleStatement.oracle_eval_congr
    -- Context: The oracle collection for a fixed round (usually Fin.last ℓ)
    {i : Fin (ℓ + 1)}
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    -- 1. Outer Index Equality (j = j')
    {j j' : Fin (toOutCodewordsCount ℓ ϑ i)} (h_j : j = j')
    -- 2. Inner Point Equality (x = x')
    -- Note: x and x' have different types because they depend on j and j'
    {x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := i) j, by omega⟩)}
    {x' : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := i) j', by omega⟩)}
    (h_x : x = cast (by rw [h_j]) x') : oStmtIn j x = oStmtIn j' x' := by
  sorry
  /-
  have h_x' :
      AdditiveNTT.Comp.toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩) x =
      cast (by rw [h_j]) (
        AdditiveNTT.Comp.toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
          (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨oraclePositionToDomainIndex ℓ ϑ j', by omega⟩) x') := by
    simpa using congrArg
      (AdditiveNTT.Comp.toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)) h_x
  simpa using congrArg (fun z => oStmtIn j z) h_x'
  -/

def mapOStmtOutRelayStep (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j := fun j => by
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  -- oracle index mapping
  exact oStmt ⟨j, by rw [h_oracle_size_eq]; omega⟩

/-- The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and
`Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁', Xᵢ, Xᵢ₊₁, ..., Xₗ₋₁) ∈ L[≤ 2][X Fin (ℓ-i)]`.
This ensures efficient computability and constraint on the structure of `H_i`
according to `t`.
-/
structure Witness (i : Fin (ℓ + 1)) where
  t : MultilinearPoly L ℓ  -- The original polynomial t
  H : MultiquadraticPoly L (ℓ - i) -- Hᵢ
  f : OracleFunction (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) ⟨i, by omega⟩ -- fᵢ

/-- The extractor that recovers the multilinear polynomial t from f^(i).
In the current protocol flow, call sites decode only the first oracle (`i = 0`). -/
noncomputable def extractMLP (i : Fin ℓ)
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) ⟨i, by omega⟩) :
    Option (MultilinearPoly L (ℓ - i)) := by
  sorry

private lemma monomialToINovelCoeffs_zero_eq_monomialToNovelCoeffs
    [NeZero 𝓡] (monomial_coeffs : Fin (2 ^ ℓ) → L) :
    AdditiveNTT.monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate
      (i := (0 : Fin r)) (h_i := by simp) monomial_coeffs =
      AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs := by
  have hA :
      AdditiveNTT.intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r)) (h_i := by simp) =
        AdditiveNTT.changeOfBasisMatrix 𝔽q β ℓ (by omega) := by
    ext j k
    change
      (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r)) (h_i := by simp) j).coeff k.val =
      (Xⱼ 𝔽q β ℓ (by omega) j).coeff k.val
    rw [AdditiveNTT.base_intermediateNovelBasisX
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (j := j)]
  simp [AdditiveNTT.monomialToINovelCoeffs, AdditiveNTT.monomialToNovelCoeffs, hA]

private lemma polynomialFromNovelCoeffs_eq_self_of_monomialToNovelCoeffs
    [NeZero 𝓡] (P : L[X]) (hP : P.degree < 2 ^ ℓ) :
    polynomialFromNovelCoeffs 𝔽q β ℓ (by omega)
      (AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val)) = P := by
  have hget :
      getINovelCoeffs 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r)) (h_i := by simp) P =
        AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val) := by
    simp [getINovelCoeffs, monomialToINovelCoeffs_zero_eq_monomialToNovelCoeffs
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]
  let hbase := intermediate_poly_P_base (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (L := L) (ℓ := ℓ) (h_ℓ := by omega)
    (coeffs := getINovelCoeffs 𝔽q β h_ℓ_add_R_rate
      (i := (0 : Fin r)) (h_i := by simp) P)
  let hself := intermediateEvaluationPoly_from_inovel_coeffs_eq_self
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (L := L) (i := (0 : Fin r)) (h_i := by simp) (P := P) hP
  rw [hget] at hbase hself
  exact hbase.symm.trans hself

private lemma binaryFinMapToNat_invFun_eq (ω : Fin (2 ^ ℓ)) :
    Nat.binaryFinMapToNat
      (n := ℓ)
      (m := fun i => ((finFunctionFinEquiv.invFun ω) i).val)
      (h_binary := by
        intro j
        change ((finFunctionFinEquiv.invFun ω j : Fin 2) : ℕ) ≤ 1
        exact Nat.le_of_lt_succ (finFunctionFinEquiv.invFun ω j).isLt) = ω := by
  apply Fin.eq_of_val_eq
  rw [Nat.eq_iff_eq_all_getBits]
  intro k
  rw [Nat.getBit_of_binaryFinMapToNat]
  split_ifs with hk
  · rw [Equiv.invFun_as_coe, finFunctionFinEquiv_symm_apply_val, Nat.getBit,
      Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  · have hk' : ℓ ≤ k := Nat.le_of_not_gt hk
    have hω_lt : (ω : ℕ) < 2 ^ k := by
      calc
        (ω : ℕ) < 2 ^ ℓ := ω.isLt
        _ ≤ 2 ^ k := by
          exact Nat.pow_le_pow_right (by omega) hk'
    rw [Nat.getBit_eq_testBit, Nat.testBit_eq_false_of_lt hω_lt]
    simp

private lemma extracted_mle_eval_bits [NeZero 𝓡] (P : L[X]) (ω : Fin (2 ^ ℓ)) :
    let monomial_coeffs : Fin (2 ^ ℓ) → L := fun k => P.coeff k.val
    let t_coeffs := AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs
    let hypercube_evals : (Fin ℓ → Fin 2) → L := fun w =>
      let w_index : Fin (2 ^ ℓ) := Nat.binaryFinMapToNat
        (n := ℓ) (m := fun i => (w i).val)
        (h_binary := by
          intro j
          change ((w j : Fin 2) : ℕ) ≤ 1
          exact Nat.le_of_lt_succ (w j).isLt)
      t_coeffs w_index
    MvPolynomial.eval (bitsOfIndex (L := L) ω) (MultilinearPoly.ofHypercubeEvals hypercube_evals).val =
        t_coeffs ω := by
  let t_coeffs : Fin (2 ^ ℓ) → L :=
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val)
  dsimp only
  simp_rw [MultilinearPoly.ofHypercubeEvals_val]
  rw [← coe_fin_pow_two_eq_bitsOfIndex (L := L) (k := ω)]
  rw [MvPolynomial.MLE_eval_zeroOne]
  have h_index := congrArg (fun x => t_coeffs x) (binaryFinMapToNat_invFun_eq (ℓ := ℓ) ω)
  exact h_index

private lemma extracted_mle_polynomial_eq
    [NeZero 𝓡] (P : L[X]) (hP : P.degree < 2 ^ ℓ) :
    polynomialFromNovelCoeffs 𝔽q β ℓ (by omega)
      (fun ω =>
        let monomial_coeffs : Fin (2 ^ ℓ) → L := fun k => P.coeff k.val
        let t_coeffs := AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs
        let hypercube_evals : (Fin ℓ → Fin 2) → L := fun w =>
          let w_index : Fin (2 ^ ℓ) := Nat.binaryFinMapToNat
            (n := ℓ) (m := fun i => (w i).val)
            (h_binary := by
              intro j
              change ((w j : Fin 2) : ℕ) ≤ 1
              exact Nat.le_of_lt_succ (w j).isLt)
          t_coeffs w_index
        MvPolynomial.eval (bitsOfIndex (L := L) ω)
            (MultilinearPoly.ofHypercubeEvals hypercube_evals).val) = P := by
  let t_coeffs : Fin (2 ^ ℓ) → L :=
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val)
  have h_eval :
      (fun ω =>
        let monomial_coeffs : Fin (2 ^ ℓ) → L := fun k => P.coeff k.val
        let t_coeffs := AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs
        let hypercube_evals : (Fin ℓ → Fin 2) → L := fun w =>
          let w_index : Fin (2 ^ ℓ) := Nat.binaryFinMapToNat
            (n := ℓ) (m := fun i => (w i).val)
            (h_binary := by
              intro j
              change ((w j : Fin 2) : ℕ) ≤ 1
              exact Nat.le_of_lt_succ (w j).isLt)
          t_coeffs w_index
        MvPolynomial.eval (bitsOfIndex (L := L) ω)
            (MultilinearPoly.ofHypercubeEvals hypercube_evals).val) = t_coeffs := by
    funext ω
    exact extracted_mle_eval_bits (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (P := P) ω
  rw [h_eval]
  exact polynomialFromNovelCoeffs_eq_self_of_monomialToNovelCoeffs
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (P := P) hP

private lemma coeff_polynomialFromNovelCoeffsF₂_eq_novelToMonomialCoeffs
    [NeZero 𝓡] (coeffs : Fin (2 ^ ℓ) → L) :
    (fun k =>
      (↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) coeffs) : L[X]).coeff k.val) =
      AdditiveNTT.novelToMonomialCoeffs 𝔽q β ℓ (by omega) coeffs := by
  funext k
  change
    (AdditiveNTT.polynomialFromNovelCoeffs 𝔽q β ℓ (by omega) coeffs).coeff k.val =
      AdditiveNTT.novelToMonomialCoeffs 𝔽q β ℓ (by omega) coeffs k
  unfold AdditiveNTT.polynomialFromNovelCoeffs AdditiveNTT.novelToMonomialCoeffs
  simp only [finset_sum_coeff, Polynomial.coeff_C_mul]
  have h_matrix_def :
      ∀ j : Fin (2 ^ ℓ),
        (Xⱼ 𝔽q β ℓ (by omega) j).coeff k.val =
          (AdditiveNTT.changeOfBasisMatrix 𝔽q β ℓ (by omega)) j k := by
    intro j
    dsimp only [AdditiveNTT.changeOfBasisMatrix, AdditiveNTT.toCoeffsVec,
      AdditiveNTT.basisVectors, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [h_matrix_def]
  dsimp only [Matrix.vecMul, dotProduct]

private lemma monomialToNovelCoeffs_polynomialFromNovelCoeffsF₂
    [NeZero 𝓡] (coeffs : Fin (2 ^ ℓ) → L) :
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega)
      (fun k =>
        (↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) coeffs) : L[X]).coeff k.val) = coeffs := by
  rw [coeff_polynomialFromNovelCoeffsF₂_eq_novelToMonomialCoeffs
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (coeffs := coeffs)]
  exact AdditiveNTT.novelToMonomial_monomialToNovel_inverse 𝔽q β ℓ (by omega) coeffs

private lemma closest_eq_of_le_udr
    {ι : Type*} [Fintype ι] (C : Set (ι → L)) [Nonempty C] (u : ι → L) {v : ι → L}
    (hv : v ∈ C)
    (hvu : Δ₀(u, v) ≤ Code.uniqueDecodingRadius C) :
    (Code.pickClosestCodeword_of_Nonempty_Code C u : C) = ⟨v, hv⟩ := by
  let w : C := Code.pickClosestCodeword_of_Nonempty_Code C u
  have hwdist : Δ₀(u, (w : ι → L)) ≤ Code.uniqueDecodingRadius C := by
    have hdist : Δ₀(u, C) ≤ Δ₀(u, v) := Code.distFromCode_le_dist_to_mem u v hv
    have hdist' : Δ₀(u, C) = Δ₀(u, (w : ι → L)) :=
      Code.distFromPickClosestCodeword_of_Nonempty_Code C u
    have haux : Δ₀(u, C) ≤ (Code.uniqueDecodingRadius C : ℕ∞) := by
      exact le_trans hdist (by exact_mod_cast hvu)
    rw [hdist'] at haux
    exact_mod_cast haux
  have hw_mem : (w : ι → L) ∈ C := w.property
  have h_eq : (w : ι → L) = v := by
    apply Code.eq_of_le_uniqueDecodingRadius (C := C) (u := u)
      (v := (w : ι → L)) (w := v)
      (hv := hw_mem) (hw := hv)
      (huv := hwdist) (huw := hvu)
  apply Subtype.ext
  exact h_eq

/-- For index 0, `extractMLP 0 f = some tpoly` iff `f` is pair-UDR-close to the oracle function
of the multilinear polynomial `tpoly` (i.e. the polynomial-as-oracle from novel coeffs of tpoly).
Forward: decoder succeeds only when within UDR. Backward: within UDR the decoded codeword
is the computable oracle induced by `computablePolynomialFromNovelCoeffsF₂`. -/
lemma extractMLP_eq_some_iff_pair_UDRClose
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) ⟨0, by omega⟩)
    (tpoly : MultilinearPoly L ℓ) :
    let P : CompPoly.CPolynomial L :=
      ⟨CompPoly.CPolynomial.Raw.trim (Array.ofFn (fun i : Fin (2 ^ ℓ) =>
          AdditiveNTT.novelToMonomialCoeffs 𝔽q β ℓ (by omega)
            (fun ω => tpoly.val.eval (bitsOfIndex ω)) i)), by
        exact CompPoly.CPolynomial.Raw.Trim.trim_twice _⟩
    (extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some tpoly) ↔
      2 * Δ₀(f, (fun y => P.eval y.val)) <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) := by
  intro P
  sorry

/-- If a block starting at index `0` is compliant in the sense of `isCompliant`, then the
Berlekamp–Welch decoder `extractMLP` at index `0` succeeds on the source oracle.

Mathematically: `isCompliant` gives fiberwise-closeness of the source oracle to the
appropriate code, which implies UDR-closeness, and hence decoder success. -/
lemma extractMLP_some_of_isCompliant_at_zero
    {destIdx : Fin r} {steps : ℕ} [NeZero steps]
    (zero_Idx : Fin r) (h_zero_Idx : zero_Idx.val = 0)
    (h_destIdx : destIdx = zero_Idx + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) zero_Idx)
    (challenges : Fin steps → L) :
    ∃ tpoly : MultilinearPoly L ℓ,
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (fun x => f_i (cast (by
            have h_eq := AdditiveNTT.Comp.sDomain_eq_of_eq (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := (0 : Fin r)) (j := zero_Idx) (h := by
                apply Fin.eq_of_val_eq
                simpa only [Fin.coe_ofNat_eq_mod, zero_mod] using h_zero_Idx.symm)
            simpa using congrArg (fun S : Submodule 𝔽q L => ↥S) h_eq) x)) = some tpoly := by
  sorry

noncomputable def dummyLastWitness :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) := {
  t := 0,
  H := 0,
  f := fun _ => 0
}

/-- The initial statement for the commitment phase contains the evaluation claim s = t(r) -/
structure MLPEvalStatement (L : Type) (ℓ : ℕ) where
  -- Original evaluation claim: s = t(r)
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

section SnocOracleHelpers
/-- Helper lemma: If it is not a commitment round, the oracle count does not increase,
    so an index `j` cannot exist in the range `[old_count, new_count)`. -/
lemma snoc_oracle_impossible {i : Fin ℓ} {j : Fin (toOutCodewordsCount ℓ ϑ i.succ)}
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc)
    (h_not_commit : ¬ isCommitmentRound ℓ ϑ i) : False := by
  -- The count relation implies new_count = old_count
  have h_counts_eq : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc := by
    rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [h_not_commit, ↓reduceIte]
  -- But j is bounded by new_count
  have h_j_lt_new := j.isLt
  conv_rhs at h_j_lt_new => rw [h_counts_eq]
  -- Contradiction with hj
  exact hj h_j_lt_new

omit [NeZero r] [NeZero 𝓡] in
/-- Helper lemma: If it is a commitment round, the index `j` (which is ≥ old_count)
    must be exactly equal to `old_count`, and consequently its domain index corresponds
    to `destIdx` (which is `i + 1`). -/
lemma snoc_oracle_dest_eq_j {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc)
    (h_commit : isCommitmentRound ℓ ϑ i) :
    destIdx = ⟨(oraclePositionToDomainIndex ℓ ϑ j).val,
               by have := oraclePositionToDomainIndex ℓ ϑ j; omega⟩ := by
  -- 1. Prove counts relation: new = old + 1
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ =
      toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [h_commit, ↓reduceIte]
  -- 2. Prove j must be exactly old_count
  have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h_lt := j.isLt
    conv_rhs at h_lt => rw [h_count_succ]
    -- j < old + 1 AND NOT j < old  =>  j = old
    omega
  -- 3. Calculate the domain index value for j
  -- We need to prove: destIdx.val = j * ϑ
  apply Fin.eq_of_val_eq
  simp only [h_destIdx]
  -- We know j * ϑ = i + 1 from the structure of commitment rounds
  rw [h_j_eq]
  rw [toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i h_commit]

/-- snoc_oracle adds the latest oracle function to the end of an oStmtIn -/
def snoc_oracle {i : Fin ℓ} {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.succ),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i.succ j := fun j =>
  sorry
  /-

 -/

def take_snoc_oracle (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) → -- We specify range type so Lean won't be stuck
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j
    := fun j => snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx
      oStmtIn newOracleFn ⟨j, by
        have h : (toOutCodewordsCount ℓ ϑ i.castSucc) ≤ toOutCodewordsCount ℓ ϑ i.succ := by
          exact toOutCodewordsCount_i_le_of_succ ℓ ϑ i
        omega
      ⟩

lemma take_snoc_oracle_eq_oStmtIn (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    (take_snoc_oracle 𝔽q β i h_destIdx oStmtIn newOracleFn) = oStmtIn := by
  sorry

end SnocOracleHelpers

/-- Extract the first oracle f^(0) from oracle statements -/
def getFirstOracle {oracleFrontierIdx : Fin (ℓ + 1)}
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ oracleFrontierIdx j)) :
    OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0 :=
  sorry
  /-

 -/

def getLastOracle {oracleFrontierIdx : Fin (ℓ + 1)} {destIdx : Fin r}
    (h_destIdx : destIdx.val = getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx)
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (i := oracleFrontierIdx) j)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  sorry
end OracleReductionComponents

end Binius.BinaryBasefold
