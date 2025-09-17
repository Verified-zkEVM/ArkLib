/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.Fin.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Bit operations on natural numbers

-/

namespace Nat

-- Note: this is already done with `Nat.sub_add_eq_max`
theorem max_eq_add_sub {m n : Nat} : Nat.max m n = m + (n - m) := by
  by_cases h : n ≤ m
  · simp [Nat.sub_eq_zero_of_le, h]
  · simp only [Nat.max_eq_right (Nat.le_of_not_le h), Nat.add_sub_of_le (Nat.le_of_not_le h)]

/--
Returns the `k`-th least significant bit of a natural number `n` as a natural number (in `{0, 1}`).

We decompose each number `j < 2^ℓ` into its binary representation : `j = Σ k ∈ Fin ℓ, jₖ * 2ᵏ`
-/
def getBit (k n : Nat) : Nat := (n >>> k) &&& 1

lemma testBit_true_eq_getBit_eq_1 (k n : Nat) : n.testBit k = ((Nat.getBit k n) = 1) := by
  unfold getBit
  rw [Nat.testBit]
  simp only [one_and_eq_mod_two, mod_two_bne_zero, beq_iff_eq, and_one_is_mod]

lemma testBit_false_eq_getBit_eq_0 (k n : Nat) :
  (n.testBit k = false) = ((Nat.getBit k n) = 0) := by
  unfold getBit
  rw [Nat.testBit]
  simp only [one_and_eq_mod_two, mod_two_bne_zero, beq_eq_false_iff_ne, ne_eq, mod_two_not_eq_one,
    and_one_is_mod]

def popCount (n : Nat) := (Nat.digits 2 n).sum

-- #eval Nat.popCount 13

lemma getBit_lt_2 {k n : Nat} : getBit k n < 2 := by
  unfold getBit
  rw [Nat.and_one_is_mod]
  simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt]

lemma getBit_eq_testBit (k n : Nat) : getBit k n = if n.testBit k then 1 else 0 := by
  unfold getBit
  rw [Nat.testBit]
  simp only [and_one_is_mod, one_and_eq_mod_two, mod_two_bne_zero, beq_iff_eq]
  if h: (n >>> k) % 2 = 1 then
    simp only [h, ↓reduceIte]
  else
    simp only [h, ↓reduceIte]
    have h_getBit_lt_2: getBit k n < 2 := by exact Nat.getBit_lt_2 (k:=k) (n:=n)
    simp only [getBit, and_one_is_mod] at h_getBit_lt_2
    omega

lemma getBit_zero_eq_zero {k : Nat} : getBit k 0 = 0 := by
  unfold getBit
  rw [Nat.zero_shiftRight]
  rw [Nat.and_one_is_mod]

lemma getBit_eq_zero_or_one {k n : Nat} :
  getBit k n = 0 ∨ getBit k n = 1 := by
  unfold getBit
  rw [Nat.and_one_is_mod]
  simp only [Nat.mod_two_eq_zero_or_one]

lemma getBit_zero_eq_self {n : ℕ} (h_n : n < 2) : getBit 0 n = n := by
  unfold getBit
  rw [Nat.shiftRight_zero]
  rw [Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt h_n

lemma getBit_zero_of_two_mul {n : ℕ} : getBit 0 (2*n) = 0 := by
  unfold getBit
  rw [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_mod_right]

/-- Get the `numLowBits` least significant bits of `n`. -/
def getLowBits (numLowBits : ℕ) (n : ℕ) := n &&& ((1 <<< numLowBits) - 1)

lemma getLowBits_zero_eq_zero {n : ℕ} : getLowBits 0 n = 0 := by
  unfold getLowBits
  simp only [Nat.shiftLeft_zero, Nat.sub_self, Nat.and_zero]

lemma getLowBits_eq_mod_two_pow {numLowBits : ℕ} (n : ℕ) :
  getLowBits numLowBits n = n % (2 ^ numLowBits) := by
  unfold getLowBits
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod n numLowBits

lemma getLowBits_lt_two_pow {n : ℕ} (numLowBits : ℕ) :
    getLowBits numLowBits n < 2 ^ numLowBits := by
  rw [getLowBits_eq_mod_two_pow]
  omega

lemma getLowBits_le_self {n : ℕ} (numLowBits : ℕ) : getLowBits numLowBits n ≤ n := by
  rw [getLowBits_eq_mod_two_pow]
  apply Nat.mod_le

lemma and_eq_zero_iff {n m : ℕ} : n &&& m = 0 ↔ ∀ k, (n >>> k) &&& (m >>> k) = 0 := by
  constructor
  · intro h_and_zero -- h_and_zero : n &&& m = 0
    intro k
    rw [← Nat.shiftRight_and_distrib]
    rw [h_and_zero]
    rw [Nat.zero_shiftRight]
  · intro h_forall_k
    have h_k_is_zero := h_forall_k 0
    simp only [Nat.shiftRight_zero] at h_k_is_zero -- utilize n = (n >>> 0), m = (m >>> 0)
    exact h_k_is_zero

lemma eq_iff_eq_all_getBits {n m : ℕ} : n = m ↔ ∀ k, getBit k n = getBit k m := by
  unfold getBit
  constructor
  · intro h_eq -- h_eq : n = m
    intro k
    rw [h_eq]
  · intro h_all_getBits -- h_all_getBits : ∀ k, (n >>> k) &&& 1 = (m >>> k) &&& 1
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_eq_beq]
    simp only [Nat.and_one_is_mod] at h_all_getBits k
    rw [h_all_getBits k]

lemma shiftRight_and_one_distrib {n m k : ℕ} :
    (n &&& m) >>> k &&& 1 = ((n >>> k) &&& 1) &&& ((m >>> k) &&& 1) := by
  rw [Nat.shiftRight_and_distrib]
  conv =>
    lhs
    rw [←Nat.and_self (x := 1)]
    rw [←Nat.and_assoc]
    rw [Nat.and_assoc (y := m >>> k) (z := 1), Nat.and_comm (x := m>>>k) (y := 1), ←Nat.and_assoc]
    rw [Nat.and_assoc]

lemma and_eq_zero_iff_and_each_getBit_eq_zero {n m : ℕ} :
    n &&& m = 0 ↔ ∀ k, ((n >>> k) &&& 1) &&& ((m >>> k) &&& 1) = 0 := by
  constructor
  · intro h_and_zero
    intro k
    have h_k := shiftRight_and_one_distrib (n := n) (m := m) (k := k)
    rw [←h_k]
    rw [h_and_zero, Nat.zero_shiftRight, Nat.zero_and]
  · intro h_forall_k -- h_forall_k : ∀ (k : ℕ), n >>> k &&& 1 &&& (m >>> k &&& 1) = 0
    apply eq_iff_eq_all_getBits.mpr
    unfold getBit
    intro k
    -- ⊢ (n &&& m) >>> k &&& 1 = 0 >>> k &&& 1
    have h_forall_k_eq : ∀ k, ((n &&& m) >>> k) &&& 1 = 0 := by
      intro k
      rw [shiftRight_and_one_distrib]
      exact h_forall_k k
    rw [h_forall_k_eq k]
    rw [Nat.zero_shiftRight, Nat.zero_and]

lemma getBit_two_pow {i k: ℕ} : (getBit k (2^i) = if i == k then 1 else 0) := by
  have h_two_pow_i: 2^i = 1 <<< i := by
    simp only [Nat.shiftLeft_eq, one_mul]
  rw [getBit, h_two_pow_i]
  if h_i_eq_k: i = k then
    rw [h_i_eq_k.symm]
    simp only [Nat.and_one_is_mod, BEq.rfl, ↓reduceIte]
    rw [Nat.shiftLeft_shiftRight]
  else
    push_neg at h_i_eq_k
    simp only [beq_iff_eq, h_i_eq_k, ↓reduceIte]
    if h_k_lt_i: i < k then
      have h_res : (1 <<< i >>> k &&& 1) = 0 := by
        set k_sub_i := k - i with h_k_sub_i
        have h_k_sub_i_le_1: k_sub_i ≥ 1 := by omega
        have h_1_le: (1: ℕ) < (2^k_sub_i) := by
          calc
            _ = 2^0 := by omega;
            _ < 2^k_sub_i := by
              apply Nat.pow_lt_pow_right (m:=0) (n:=k_sub_i)
              omega; omega;
        have h_sum: k_sub_i + i = k := by
          simp [k_sub_i]
          rw [Nat.sub_add_cancel (by omega)]
        have h_sum2: i + k_sub_i = k := by omega
        rw [←h_sum2, Nat.shiftRight_add, Nat.shiftLeft_shiftRight]
        rw [Nat.shiftRight_eq_div_pow]
        have h_one_div_2_pow_k_sub_i := (Nat.div_eq_zero_iff_lt (x:=1) (k:=2^k_sub_i)
          (by exact Nat.two_pow_pos (w:=k_sub_i))).mpr h_1_le
        rw [h_one_div_2_pow_k_sub_i, Nat.zero_and]
      rw [h_res]
    else
      push_neg at h_k_lt_i
      have h_res : (1 <<< i >>> k &&& 1) = 0 := by
        set i_sub_k := i - k with h_i_sub_k
        have h_i_sub_k_le_1: i_sub_k ≥ 1 := by omega
        have h_1_le: (1: ℕ) < (2^i_sub_k) := by
          calc
            _ = 2^0 := by omega;
            _ < 2^i_sub_k := by
              apply Nat.pow_lt_pow_right (m:=0) (n:=i_sub_k)
              omega; omega;
        have h_sum: i_sub_k + k = i := by
          simp [i_sub_k]
          rw [Nat.sub_add_cancel (by omega)]
        rw [←h_sum, Nat.shiftLeft_add, Nat.shiftLeft_shiftRight]
        rw [Nat.shiftLeft_eq, one_mul]
        simp only [Nat.and_one_is_mod, Nat.two_pow_mod_two_eq_zero, gt_iff_lt]
        omega
      rw [h_res]

lemma and_two_pow_eq_zero_of_getBit_0 {n i : ℕ} (h_getBit: getBit i n = 0) : n &&& (2 ^ i) = 0 := by
  apply and_eq_zero_iff_and_each_getBit_eq_zero.mpr
  intro k
  have h_getBit_two_pow := getBit_two_pow (i := i) (k := k)
  if h_k: k = i then
    simp only [h_k, BEq.rfl, ↓reduceIte] at h_getBit_two_pow
    rw [getBit, h_k.symm] at h_getBit
    rw [h_getBit, Nat.zero_and]
  else
    push_neg at h_k
    simp only [beq_iff_eq, h_k.symm, ↓reduceIte] at h_getBit_two_pow
    rw [getBit] at h_getBit_two_pow
    rw [h_getBit_two_pow]
    rw [Nat.and_zero]

lemma and_two_pow_eq_two_pow_of_getBit_1 {n i : ℕ} (h_getBit: getBit i n = 1) :
    n &&& (2 ^ i) = 2 ^ i := by
  have h_testBit_i_eq_1 : n.testBit i = true := by
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_iff_eq]
    simp only [getBit, Nat.and_one_is_mod] at h_getBit
    exact h_getBit
  conv_lhs => rw [Nat.and_two_pow (n:=n) (i:=i)]
  simp only [h_testBit_i_eq_1, Bool.toNat_true, one_mul]

lemma and_two_pow_eq_two_pow_of_getBit_eq_one {n i : ℕ} (h_getBit: getBit i n = 1)
    : n &&& (2 ^ i) = 2 ^ i := by
  apply eq_iff_eq_all_getBits.mpr; unfold getBit
  intro k
  have h_getBit_two_pow := getBit_two_pow (i := i) (k := k)
  if h_k: k = i then
    simp only [h_k, BEq.rfl, ↓reduceIte] at h_getBit_two_pow
    rw [getBit, h_k.symm] at h_getBit
    -- ⊢ getBit k (n &&& 2 ^ i) = 2 ^ i >>> k &&& 1
    rw [getBit, h_k.symm] at h_getBit_two_pow
    rw [h_k.symm, h_getBit_two_pow]
    rw [Nat.shiftRight_and_distrib, Nat.and_assoc, Nat.and_comm (2^k >>> k) 1, ←Nat.and_assoc]
    rw [h_getBit, ←one_mul (2^k), ←Nat.shiftLeft_eq, Nat.shiftLeft_shiftRight, Nat.and_self]
  else
    push_neg at h_k
    simp only [beq_iff_eq, h_k.symm, ↓reduceIte] at h_getBit_two_pow
    rw [getBit] at h_getBit_two_pow
    rw [h_getBit_two_pow, Nat.shiftRight_and_distrib, Nat.and_assoc, h_getBit_two_pow]
    rw [Nat.and_zero]

lemma and_one_eq_of_eq {a b : ℕ} : a = b → a &&& 1 = b &&& 1 := by
  intro h_eq
  rw [h_eq]

lemma eq_zero_or_eq_one_of_lt_two {n : ℕ} (h_lt : n < 2) : n = 0 ∨ n = 1 := by
  interval_cases n
  · left; rfl
  · right; rfl

lemma div_2_form {nD2 b : ℕ} (h_b : b < 2):
  (nD2 * 2 + b) / 2 = nD2 := by
  rw [←add_comm, ←mul_comm]
  rw [Nat.add_mul_div_left (x := b) (y := 2) (z := nD2) (H := by norm_num)]
  norm_num; exact h_b;

lemma and_by_split_lowBits {n m n1 m1 bn bm : ℕ} (h_bn : bn < 2) (h_bm : bm < 2)
  (h_n : n = n1 * 2 + bn) (h_m : m = m1 * 2 + bm):
  n &&& m = (n1 &&& m1) * 2 + (bn &&& bm) := by -- main tool : Nat.div_add_mod /2
  rw [h_n, h_m]
  -- ⊢ (n1 * 2 + bn) &&& (m1 * 2 + bm) = (n1 &&& m1) * 2 + (bn &&& bm)
  have h_n1_mul_2_add_bn_div_2 : (n1 * 2 + bn) / 2 = n1 := div_2_form h_bn;
  have h_m1_mul_2_add_bm_div_2 : (m1 * 2 + bm) / 2 = m1 := div_2_form h_bm;
  have h_and_bn_bm : (bn &&& bm) < 2 := by
    interval_cases bn
    · rw [Nat.zero_and]; norm_num;
    · interval_cases bm
      · rw [Nat.and_zero]; norm_num;
      · rw [Nat.and_self]; norm_num;
  -- Part 1 : Prove the `mod 2` parts are equal.
  have h_mod_eq : ((n1 * 2 + bn) &&& (m1 * 2 + bm)) % 2 = ((n1 &&& m1) * 2 + (bn &&& bm)) % 2 := by
    simp only [Nat.and_mod_two_pow (n := 1), pow_one, Nat.mul_add_mod_self_right]
  -- Part 2 : Prove the `div 2` parts are equal.
  have h_div_eq : ((n1 * 2 + bn) &&& (m1 * 2 + bm)) / 2 = ((n1 &&& m1) * 2 + (bn &&& bm)) / 2 := by
    simp only [Nat.and_div_two_pow (n := 1), pow_one]
    -- ⊢ (n1 * 2 + bn) / 2 &&& (m1 * 2 + bm) / 2 = ((n1 &&& m1) * 2 + (bn &&& bm)) / 2
    rw [h_n1_mul_2_add_bn_div_2, h_m1_mul_2_add_bm_div_2]
    -- ⊢ n1 &&& m1 = ((n1 &&& m1) * 2 + (bn &&& bm)) / 2
    have h_result : ((n1 &&& m1) * 2 + (bn &&& bm)) / 2 = n1 &&& m1 := by
      rw [←add_comm, ←mul_comm] -- (x + y * z) / y = x / y + z
      rw [Nat.add_mul_div_left (x := bn &&& bm) (y := 2) (z := n1 &&& m1) (H := by norm_num)]
      rw [(Nat.div_eq_zero_iff_lt (h := by norm_num)).mpr h_and_bn_bm, zero_add]
    rw [h_result]
  rw [←Nat.div_add_mod ((n1 * 2 + bn) &&& (m1 * 2 + bm)) 2, h_div_eq, h_mod_eq, Nat.div_add_mod]

lemma xor_by_split_lowBits {n m n1 m1 bn bm : ℕ} (h_bn : bn < 2) (h_bm : bm < 2)
  (h_n : n = n1 * 2 + bn) (h_m : m = m1 * 2 + bm):
  n ^^^ m = (n1 ^^^ m1) * 2 + (bn ^^^ bm) := by
  rw [h_n, h_m]
  -- ⊢ (n1 * 2 + bn) ^^^ (m1 * 2 + bm) = (n1 ^^^ m1) * 2 + (bn ^^^ bm)
  have h_n1_mul_2_add_bn_div_2 : (n1 * 2 + bn) / 2 = n1 := div_2_form h_bn;
  have h_m1_mul_2_add_bm_div_2 : (m1 * 2 + bm) / 2 = m1 := div_2_form h_bm;
  have h_xor_bn_bm : (bn ^^^ bm) < 2 := by
    interval_cases bn
    · interval_cases bm
      · rw [Nat.zero_xor]; norm_num;
      · rw [Nat.zero_xor]; norm_num;
    · interval_cases bm
      · rw [Nat.xor_zero]; norm_num;
      · rw [Nat.xor_self]; norm_num;
  -- Part 1 : Prove the `mod 2` parts are equal.
  have h_mod_eq : ((n1 * 2 + bn) ^^^ (m1 * 2 + bm)) % 2 = ((n1 ^^^ m1) * 2 + (bn ^^^ bm)) % 2 := by
    simp only [Nat.xor_mod_two_pow (n := 1), pow_one, Nat.mul_add_mod_self_right]
  -- Part 2 : Prove the `div 2` parts are equal.
  have h_div_eq : ((n1 * 2 + bn) ^^^ (m1 * 2 + bm)) / 2 = ((n1 ^^^ m1) * 2 + (bn ^^^ bm)) / 2 := by
    simp only [Nat.xor_div_two_pow (n := 1), pow_one]
    -- ⊢ (n1 * 2 + bn) / 2 &&& (m1 * 2 + bm) / 2 = ((n1 &&& m1) * 2 + (bn &&& bm)) / 2
    rw [h_n1_mul_2_add_bn_div_2, h_m1_mul_2_add_bm_div_2]
    -- ⊢ n1 &&& m1 = ((n1 &&& m1) * 2 + (bn &&& bm)) / 2
    have h_result : ((n1 ^^^ m1) * 2 + (bn ^^^ bm)) / 2 = n1 ^^^ m1 := by
      rw [←add_comm, ←mul_comm] -- (x + y * z) / y = x / y + z
      rw [Nat.add_mul_div_left (x := bn ^^^ bm) (y := 2) (z := n1 ^^^ m1) (H := by norm_num)]
      rw [(Nat.div_eq_zero_iff_lt (h := by norm_num)).mpr h_xor_bn_bm, zero_add]
    rw [h_result]
  rw [←Nat.div_add_mod ((n1 * 2 + bn) ^^^ (m1 * 2 + bm)) 2, h_div_eq, h_mod_eq, Nat.div_add_mod]

lemma or_by_split_lowBits {n m n1 m1 bn bm : ℕ} (h_bn : bn < 2) (h_bm : bm < 2)
  (h_n : n = n1 * 2 + bn) (h_m : m = m1 * 2 + bm):
  n ||| m = (n1 ||| m1) * 2 + (bn ||| bm) := by
  rw [h_n, h_m]
  -- ⊢ (n1 * 2 + bn) ||| (m1 * 2 + bm) = (n1 ||| m1) * 2 + (bn ||| bm)
  have h_n1_mul_2_add_bn_div_2 : (n1 * 2 + bn) / 2 = n1 := div_2_form h_bn;
  have h_m1_mul_2_add_bm_div_2 : (m1 * 2 + bm) / 2 = m1 := div_2_form h_bm;
  have h_or_bn_bm : (bn ||| bm) < 2 := by
    interval_cases bn
    · interval_cases bm
      · rw [Nat.zero_or]; norm_num;
      · rw [Nat.zero_or]; norm_num;
    · interval_cases bm
      · rw [Nat.or_zero]; norm_num;
      · rw [Nat.or_self]; norm_num;
  -- Part 1 : Prove the `mod 2` parts are equal.
  have h_mod_eq : ((n1 * 2 + bn) ||| (m1 * 2 + bm)) % 2 = ((n1 ||| m1) * 2 + (bn ||| bm)) % 2 := by
    simp only [Nat.or_mod_two_pow (n := 1), pow_one, Nat.mul_add_mod_self_right]
  -- Part 2 : Prove the `div 2` parts are equal.
  have h_div_eq : ((n1 * 2 + bn) ||| (m1 * 2 + bm)) / 2 = ((n1 ||| m1) * 2 + (bn ||| bm)) / 2 := by
    simp only [Nat.or_div_two_pow (n := 1), pow_one]
    -- ⊢ (n1 * 2 + bn) / 2 ||| (m1 * 2 + bm) / 2 = ((n1 ||| m1) * 2 + (bn ||| bm)) / 2
    rw [h_n1_mul_2_add_bn_div_2, h_m1_mul_2_add_bm_div_2]
    -- ⊢ n1 ||| m1 = ((n1 ||| m1) * 2 + (bn ||| bm)) / 2
    have h_result : ((n1 ||| m1) * 2 + (bn ||| bm)) / 2 = n1 ||| m1 := by
      rw [←add_comm, ←mul_comm] -- (x + y * z) / y = x / y + z
      rw [Nat.add_mul_div_left (x := bn ||| bm) (y := 2) (z := n1 ||| m1) (H := by norm_num)]
      rw [(Nat.div_eq_zero_iff_lt (h := by norm_num)).mpr h_or_bn_bm, zero_add]
    rw [h_result]
  rw [←Nat.div_add_mod ((n1 * 2 + bn) ||| (m1 * 2 + bm)) 2, h_div_eq, h_mod_eq, Nat.div_add_mod]

lemma sum_eq_xor_plus_twice_and (n : Nat) : ∀ m : ℕ, n + m = (n ^^^ m) + 2 * (n &&& m) := by
  induction n using Nat.binaryRec with
  | z =>
    intro m
    rw [zero_add, Nat.zero_and, mul_zero, add_zero, Nat.zero_xor]
  | f bn n2 ih =>
    intro m
    let resDiv2M := Nat.boddDiv2 m
    let bm := resDiv2M.fst
    let m2 := resDiv2M.snd
    have h_m2 : m2 = Nat.div2 m := by
      rfl
    have h_bm : bm = Nat.bodd m := by
      rfl
    let mVal := Nat.bit bm m2
    set nVal := Nat.bit bn n2
    set getBitN := bn.toNat
    set getBitM := bm.toNat
    have h_getBitN : getBitN < 2 := by
      exact Bool.toNat_lt bn
    have h_getBitM : getBitM < 2 := by
      exact Bool.toNat_lt bm
    have h_and_getBitN_getBitM : (getBitN &&& getBitM) < 2 := by
      interval_cases getBitN
      · interval_cases getBitM
        · rw [Nat.zero_and]; norm_num;
        · rw [Nat.zero_and]; norm_num;
      · interval_cases getBitM
        · rw [Nat.and_zero]; norm_num;
        · rw [Nat.and_self]; norm_num;
    have h_n : nVal = n2 * 2 + getBitN := by
      unfold nVal
      rw [Nat.bit_val, mul_comm]
    have h_m : mVal = m2 * 2 + getBitM := by
      unfold mVal
      rw [Nat.bit_val, mul_comm]
    have h_mVal_eq_m : mVal = m := by
      unfold mVal
      rw [Nat.bit_val, mul_comm]
      rw [←h_m]
      unfold mVal
      simp only [h_bm, h_m2]
      exact Nat.bit_decomp m
    rw [←h_mVal_eq_m]
    -- h_prev : n2 + m2 = n2 ^^^ m2 + 2 * (n2 &&& m2)
    -- ⊢ nVal + mVal = nVal ^^^ mVal + 2 * (nVal &&& mVal)
    have h_and : nVal &&& mVal = (n2 &&& m2) * 2 + (getBitN &&& getBitM) :=
      and_by_split_lowBits (h_bn := h_getBitN) (h_bm := h_getBitM) (h_n := h_n) (h_m := h_m)
    have h_xor : nVal ^^^ mVal = (n2 ^^^ m2) * 2 + (getBitN ^^^ getBitM) :=
      xor_by_split_lowBits (h_bn := h_getBitN) (h_bm := h_getBitM) (h_n := h_n) (h_m := h_m)
    have h_or : nVal ||| mVal = (n2 ||| m2) * 2 + (getBitN ||| getBitM) :=
      or_by_split_lowBits (h_bn := h_getBitN) (h_bm := h_getBitM) (h_n := h_n) (h_m := h_m)
    have h_prev := ih m2
    -- ⊢ nVal + mVal = (nVal ^^^ mVal) + (2 * (nVal &&& mVal))
    have sum_eq : nVal + mVal = (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getBitN + getBitM) := by
      calc
        _ = (n2 * 2 + getBitN) + (m2 * 2 + getBitM) := by rw [h_n, h_m]
        _ = (n2 + m2) * 2 + (getBitN + getBitM) := by
          rw [Nat.right_distrib, ←add_assoc, ←add_assoc]; omega;
        _ = ((n2 ^^^ m2) + 2 * (n2 &&& m2)) * 2 + (getBitN + getBitM) := by rw [h_prev]
        _ = (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getBitN + getBitM) := by
          rw [Nat.right_distrib]; omega
    rw [sum_eq]
    -- From this point, we basically do case analysis on `bn &&& bm`
    -- rw [h_n, h_m]
    by_cases h_and_getBitN_getBitM_eq_1 : getBitN &&& getBitM = 1
    · have h_getBitN_and_getBitM_eq_1 : getBitN = 1 ∧ getBitM = 1 := by
        interval_cases getBitN
        · interval_cases getBitM
          · contradiction
          · contradiction
        · interval_cases getBitM
          · contradiction
          · and_intros; rfl; rfl;
      have h_sum_getBits : (getBitN + getBitM) = 2 := by omega
      have h_xor_getBits : getBitN ^^^ getBitM = 0 := by
        simp only [h_getBitN_and_getBitM_eq_1, Nat.xor_self];
      have h_and_getBits : getBitN &&& getBitM = 1 := by
        simp only [h_getBitN_and_getBitM_eq_1, Nat.and_self];
      -- ⊢ (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getBitN + getBitM)
      -- = (nVal ^^^ mVal) + 2 * (nVal &&& mVal)
      have h_left : (n2 ^^^ m2) * 2 = (nVal ^^^ mVal) := by
        calc
          _ = (n2 ^^^ m2) * 2 + 0 := by omega;
          _ = (n2 ^^^ m2) * 2 + (getBitN ^^^ getBitM) := by rw [h_xor_getBits];
          _ = _ := by exact h_xor.symm
      rw [h_left]
      rw [add_assoc]
      have h_right : 4 * (n2 &&& m2) + (getBitN + getBitM) = 2 * (nVal &&& mVal) := by
        calc
          _ = 4 * (n2 &&& m2) + 2 := by rw [h_sum_getBits];
          _ = 2 * (2 * (n2 &&& m2) + 1) := by omega;
          _ = 2 * ((n2 &&& m2) * 2 + (getBitN &&& getBitM)) := by
            rw [h_and_getBits, mul_comm (a := (n2 &&& m2)) (b := 2)];
          _ = 2 * (nVal &&& mVal) := by rw [h_and];
      rw [h_right]
    · push_neg at h_and_getBitN_getBitM_eq_1;
      have h_and_getBitN_getBitM_eq_0 : (getBitN &&& getBitM) = 0 := by
        interval_cases (getBitN &&& getBitM)
        · rfl
        · contradiction
      have h_getBits_eq : getBitN = 0 ∨ getBitM = 0 := by
        interval_cases getBitN
        · left; rfl
        · right;
          interval_cases getBitM
          · rfl
          · contradiction
      have h_sum_getBits : (getBitN + getBitM) = (getBitN ^^^ getBitM) := by
        interval_cases getBitN
        · interval_cases getBitM
          · rfl
          · rfl
        · interval_cases getBitM
          · rfl
          · contradiction -- with h_and_getBitN_getBitM_eq_0
      -- ⊢ (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getBitN + getBitM)
      -- = (nVal ^^^ mVal) + 2 * (nVal &&& mVal)
      rw [←add_assoc, add_assoc (b := getBitN) (c := getBitM), add_assoc]
      rw [add_comm (b := (getBitN + getBitM)), ←add_assoc]
      have h_left : (n2 ^^^ m2) * 2 + (getBitN + getBitM) = (nVal ^^^ mVal) := by
        calc
          _ = (n2 ^^^ m2) * 2 + (getBitN ^^^ getBitM) := by rw [h_sum_getBits];
          _ = _ := by exact h_xor.symm
      rw [h_left]

      -- 4 * (n2 &&& m2) = 2 * (2 * (n2 &&& m2) + (bn &&& bm)) = 2 * (n &&& m)
      have h_right : 4 * (n2 &&& m2) = 2 * (nVal &&& mVal) := by
        calc
          _ = 4 * (n2 &&& m2) + 0 := by omega;
          _ = 4 * (n2 &&& m2) + (getBitN &&& getBitM) := by rw [h_and_getBitN_getBitM_eq_0];
          _ = 2 * (2 * (n2 &&& m2) + (getBitN &&& getBitM)) := by omega;
          _ = 2 * ((n2 &&& m2) * 2 + (getBitN &&& getBitM)) := by
            rw [mul_comm (a := (n2 &&& m2)) (b := 2)];
          _ = 2 * (nVal &&& mVal) := by rw [h_and];
      rw [h_right]

lemma add_shiftRight_distrib {n m k : ℕ} (h_and_zero : n &&& m = 0):
  (n + m) >>> k = (n >>> k) + (m >>> k) := by
  rw [sum_eq_xor_plus_twice_and, h_and_zero, mul_zero, add_zero]
  conv =>
    rhs
    rw [sum_eq_xor_plus_twice_and]
    rw [←Nat.shiftRight_and_distrib, h_and_zero]
    rw [Nat.zero_shiftRight, mul_zero, add_zero]
    rw [←Nat.shiftRight_xor_distrib]

lemma sum_of_and_eq_zero_is_xor {n m : ℕ} (h_n_AND_m : n &&& m = 0) : n + m = n ^^^ m := by
  rw [sum_eq_xor_plus_twice_and, h_n_AND_m]
  omega

lemma xor_of_and_eq_zero_is_or {n m : ℕ} (h_n_AND_m : n &&& m = 0) : n ^^^ m = n ||| m := by
  apply eq_iff_eq_all_getBits.mpr; unfold getBit
  intro k
  rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_or_distrib]
  rw [Nat.and_xor_distrib_right] -- lhs
  rw [Nat.and_distrib_right] -- rhs
  -- ⊢ (n >>> k &&& 1) ^^^ (m >>> k &&& 1) = (n >>> k &&& 1) ||| (m >>> k &&& 1)
  set getBitN := n >>> k &&& 1
  set getBitM := m >>> k &&& 1
  have h_getBitN : getBitN < 2 := by
    simp only [getBitN, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := n >>> k) (y := 2)]
  have h_getBitM : getBitM < 2 := by
    simp only [getBitM, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := m >>> k) (y := 2)]
  -- ⊢ getBitN ^^^ getBitM = getBitN ||| getBitM
  have h_and_getBitN_getBitM : (getBitN &&& getBitM) = 0 := by
    exact and_eq_zero_iff_and_each_getBit_eq_zero.mp h_n_AND_m k
  interval_cases getBitN -- case analysis on `getBitN, getBitM`
  · interval_cases getBitM
    · rfl
    · rfl
  · interval_cases getBitM
    · rfl
    · contradiction

lemma sum_of_and_eq_zero_is_or {n m : ℕ} (h_n_AND_m : n &&& m = 0) : n + m = n ||| m := by
  rw [sum_eq_xor_plus_twice_and, h_n_AND_m, mul_zero, add_zero]
  exact xor_of_and_eq_zero_is_or h_n_AND_m

lemma xor_eq_sub_iff_submask {n m : ℕ} (h: m ≤ n) : n ^^^ m = n - m ↔ n &&& m = m := by
  constructor
  · intro h
    have h_sum: (n ^^^ m) + m = n := by
      rw [h, Nat.sub_add_cancel (m:=m) (by omega)]
    rw [sum_eq_xor_plus_twice_and (n:=n^^^m) (m:=m)] at h_sum
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.and_xor_distrib_right] at h_sum
    rw [Nat.and_self] at h_sum
    conv_rhs at h_sum => rw [←Nat.add_zero (n:=n)]
    rw [Nat.add_left_cancel_iff] at h_sum
    have h_and_zero : (n ^^^ m) &&& m = 0 := by
      cases (Nat.mul_eq_zero.mp h_sum) with
      | inl h_two => contradiction -- The case 2 = 0 is impossible.
      | inr h_and => -- h_and : n &&& m ^^^ m = 0
        simp only [Nat.xor_eq_zero] at h_and
        conv_lhs => enter [1]; rw [←h_and] -- h_and : n &&& m = m
        rw [Nat.and_xor_distrib_right] -- ⊢ n &&& m ^^^ n &&& m &&& m = 0
        rw [Nat.and_assoc, Nat.and_self, Nat.xor_self]
    -- ⊢ (n ^^^ m) &&& m = 0
    rw [Nat.and_xor_distrib_right, Nat.and_self] at h_and_zero --h_and_zero : n &&& m ^^^ m = 0
    rw [Nat.xor_eq_zero] at h_and_zero
    exact h_and_zero
  · intro h
    rw [Nat.sub_eq_of_eq_add (a:=n) (c:=n^^^m) (b:=m)]
    -- ⊢ n = (n ^^^ m) + m
    rw [sum_eq_xor_plus_twice_and (n:=n^^^m) (m:=m)]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.and_xor_distrib_right, h]
    rw [Nat.and_self, Nat.xor_self, mul_zero, add_zero]

lemma getBit_of_add_distrib {n m k : ℕ}
  (h_n_AND_m : n &&& m = 0) : getBit k (n + m) = getBit k n + getBit k m := by
  unfold getBit
  rw [sum_of_and_eq_zero_is_xor h_n_AND_m]
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
  set getBitN := n >>> k &&& 1
  set getBitM := m >>> k &&& 1
  have h_getBitN : getBitN < 2 := by
    simp only [getBitN, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := n >>> k) (y := 2)]
  have h_getBitM : getBitM < 2 := by
    simp only [getBitM, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := m >>> k) (y := 2)]
  have h_getBitN_and_getBitM : (getBitN &&& getBitM) = 0 := by
    exact and_eq_zero_iff_and_each_getBit_eq_zero.mp h_n_AND_m k
  exact (sum_of_and_eq_zero_is_xor (n := getBitN) (m := getBitM) h_getBitN_and_getBitM).symm

lemma add_two_pow_of_getBit_eq_zero_lt_two_pow {n m i : ℕ} (h_n: n < 2^m) (h_i: i < m)
  (h_getBit_at_i_eq_zero: getBit i n = 0) :
  n + 2^i < 2^m := by
  have h_j_and: n &&& (2^i) = 0 := by
    rw [and_two_pow_eq_zero_of_getBit_0 (n:=n) (i:=i)]
    rw [←h_getBit_at_i_eq_zero]
  rw [sum_eq_xor_plus_twice_and, h_j_and, mul_zero, add_zero]
  have h_and_lt := Nat.xor_lt_two_pow (x:=n) (y:=2^i) (n:=m) (by omega) (by
    apply Nat.pow_lt_pow_right (a:=2) (m:=i) (n:=m) (ha:=by omega) (h:=by omega)
  )
  exact h_and_lt

lemma getBit_of_multiple_of_power_of_two {n p : ℕ}: ∀ k,
  getBit (k) (2^p * n) = if k < p then 0 else getBit (k-p) n := by
  intro k
  have h_test := Nat.testBit_two_pow_mul (i := p) (a := n) (j:=k)
  simp only [Nat.testBit, Nat.and_comm 1] at h_test
  if h_k: p > k then
    have h_ne_p_le_k: ¬(p ≤ k) := by omega
    simp only [Nat.and_one_is_mod, Nat.mod_two_bne_zero, ge_iff_le, h_ne_p_le_k, decide_false,
      Bool.false_and, beq_eq_false_iff_ne, ne_eq, Nat.mod_two_not_eq_one, h_k,
      ↓reduceIte] at h_test ⊢
    simp only [getBit, Nat.and_one_is_mod]
    omega
  else
    have h_p_le_k: p ≤ k := by omega
    have h_ne_k_lt_p: ¬(k < p) := by omega
    simp only [Nat.and_one_is_mod, Nat.mod_two_bne_zero, ge_iff_le, h_p_le_k, decide_true,
      Bool.true_and, beq_eq_beq, h_ne_k_lt_p, ↓reduceIte] at h_test ⊢
    simp only [getBit]
    -- ⊢ (2 ^ p * n) >>> k % 2 = n >>> (k - p) % 2
    change getBit k (2^p * n) = getBit (k - p) n
    have h_getBit_left_lt: getBit (k - p) n < 2 := getBit_lt_2
    have h_getBit_right_lt: getBit k n < 2 := getBit_lt_2
    interval_cases h_getBit_left_lt_eq: getBit (k - p) n
    · simp only [getBit, Nat.and_one_is_mod] at h_getBit_left_lt_eq
      simp [h_getBit_left_lt_eq] at h_test
      simp only [getBit, Nat.and_one_is_mod, h_test]
    · simp only [getBit, Nat.and_one_is_mod] at h_getBit_left_lt_eq
      simp only [h_getBit_left_lt_eq, iff_true] at h_test
      simp only [getBit, Nat.and_one_is_mod, h_test]

lemma getBit_of_shiftLeft {n p : ℕ}:
  ∀ k, getBit (k) (n <<< p) = if k < p then 0 else getBit (k - p) n := by
  intro k
  rw [getBit_of_multiple_of_power_of_two (n:=n) (p:=p) (k:=k).symm]
  congr
  rw [Nat.shiftLeft_eq, mul_comm]

lemma getBit_of_shiftRight {n p : ℕ}:
  ∀ k, getBit k (n >>> p) = getBit (k+p) n := by
  intro k
  unfold getBit
  rw [←Nat.shiftRight_add]
  rw [←add_comm]

lemma getBit_of_or {n m k: ℕ} : getBit k (n ||| m) = getBit k n ||| getBit k m := by
  unfold getBit
  rw [Nat.shiftRight_or_distrib]
  conv_lhs =>
    rw [Nat.and_distrib_right]

lemma getBit_of_xor {n m k: ℕ} : getBit k (n ^^^ m) = getBit k n ^^^ getBit k m := by
  unfold getBit
  rw [Nat.shiftRight_xor_distrib]
  conv_lhs =>
    rw [Nat.and_xor_distrib_right]

lemma getBit_of_and {n m k: ℕ} : getBit k (n &&& m) = getBit k n &&& getBit k m := by
  unfold getBit
  rw [Nat.shiftRight_and_distrib]
  rw [Nat.and_comm (m >>>k) 1, ←Nat.and_assoc, Nat.and_assoc (n>>>k) 1 1]
  rw [Nat.and_self, Nat.and_assoc (n>>>k) 1 (m >>> k), Nat.and_comm 1 (m >>> k)]
  rw [←Nat.and_assoc]

lemma getBit_of_two_pow_sub_one {i k: ℕ} : getBit k (2^i - 1) =
    if k < i then 1 else 0 := by
  have h_test := Nat.testBit_two_pow_sub_one (n := i) (i := k)
  simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero] at h_test
  if h_k: k < i then
    simp only [h_k, decide_true, beq_iff_eq] at h_test ⊢
    simp only [getBit, Nat.and_one_is_mod]
    simp only [h_test, ↓reduceIte]
  else
    simp only [h_k, decide_false, beq_eq_false_iff_ne, ne_eq, Nat.mod_two_not_eq_one,
      ↓reduceIte] at h_test ⊢
    simp only [getBit, Nat.and_one_is_mod]
    simp only [h_test]

lemma getBit_of_sub_two_pow_of_bit_1 {n i j: ℕ} (h_getBit_eq_1: getBit i n = 1) :
  getBit j (n - 2^i) = (if j = i then 0 else getBit j n) := by
  have h_2_pow_i_lt_n: 2^i ≤ n := by
    apply Nat.ge_two_pow_of_testBit
    rw [Nat.testBit_true_eq_getBit_eq_1]
    exact h_getBit_eq_1
  have h_xor_eq_sub := (Nat.xor_eq_sub_iff_submask (n:=n) (m:=2^i) (h_2_pow_i_lt_n)).mpr (by
    exact and_two_pow_eq_two_pow_of_getBit_1 h_getBit_eq_1)
  rw [h_xor_eq_sub.symm]
  rw [Nat.getBit_of_xor]
  if h_j_eq_i: j = i then
    rw [h_j_eq_i]
    rw [h_getBit_eq_1]
    rw [Nat.getBit_two_pow]
    simp only [BEq.rfl, ↓reduceIte, Nat.xor_self]
  else
    rw [Nat.getBit_two_pow]
    simp only [beq_iff_eq]
    simp only [h_j_eq_i, ↓reduceIte]
    push_neg at h_j_eq_i
    simp only [if_neg h_j_eq_i.symm, xor_zero]

lemma getBit_of_lowBits {n: ℕ} (numLowBits : ℕ) : ∀ k, getBit k (getLowBits numLowBits n) =
    if k < numLowBits then getBit k n else 0 := by
  intro k
  simp only [getLowBits, getBit_of_and]
  if h_k: k < numLowBits then
    simp only [h_k, ↓reduceIte]
    have getBit_k_mask : getBit k (1 <<< numLowBits - 1) = 1:= by
      rw [Nat.shiftLeft_eq, one_mul]
      rw [getBit_of_two_pow_sub_one (i := numLowBits) (k := k)]
      simp only [ite_eq_left_iff, not_lt, zero_ne_one, imp_false, not_le]
      omega
    rw [getBit_k_mask]
    have h_getBit_k_n: getBit k n < 2 := by exact getBit_lt_2
    interval_cases h_getBit_k_n_eq: getBit k n
    · simp only [Nat.and_one_is_mod]
    · simp only [Nat.and_one_is_mod]
  else
    push_neg at h_k
    have getBit_k_mask : getBit k (1 <<< numLowBits - 1) = 0:= by
      rw [Nat.shiftLeft_eq, one_mul]
      rw [getBit_of_two_pow_sub_one (i := numLowBits) (k := k)]
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt]
      omega
    rw [getBit_k_mask, Nat.and_zero]
    simp only [right_eq_ite_iff]
    omega

lemma getBit_eq_succ_getBit_of_mul_two {n k : ℕ} : getBit (k+1) (2*n) = getBit k n := by
  have h_n_eq: n = (2*n) >>> 1 := by omega
  have res := (getBit_of_shiftRight (n := 2*n) (p := 1) k).symm
  conv_rhs at res => rw [←h_n_eq]
  exact res

lemma getBit_eq_succ_getBit_of_mul_two_add_one {n k : ℕ} : getBit (k+1) (2*n + 1) = getBit k n := by
  have h_n_eq: n = (2*n + 1) >>> 1 := by omega
  have res := (getBit_of_shiftRight (n := 2*n + 1) (p := 1) k).symm
  conv_rhs at res => rw [←h_n_eq]
  exact res

lemma getBit_eq_pred_getBit_of_div_two {n k : ℕ} (h_k: k > 0) :
    getBit k (n) = getBit (k-1) (n/2) := by
  rw [←Nat.pow_one 2]
  rw [←Nat.shiftRight_eq_div_pow]
  conv_lhs => rw [←Nat.sub_add_cancel (n:=k) (m:=1) (h:=by omega)]
  exact Eq.symm (getBit_of_shiftRight (k - 1))

-- TODO: uniqueness of this representation?
theorem getBit_repr {ℓ : Nat} : ∀ j, j < 2^ℓ →
  j = ∑ k ∈ Finset.Icc 0 (ℓ-1), (getBit k j) * 2^k := by
  induction ℓ with
  | zero =>
    -- Base case : ℓ = 0
    intro j h_j
    have h_j_zero : j = 0 := by exact Nat.lt_one_iff.mp h_j
    subst h_j_zero
    simp only [zero_tsub, Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]
    unfold getBit
    rw [Nat.shiftRight_zero, Nat.and_one_is_mod]
  | succ ℓ₁ ih =>
    by_cases h_ℓ₁ : ℓ₁ = 0
    · simp only [h_ℓ₁, zero_add, pow_one, tsub_self, Finset.Icc_self, Finset.sum_singleton,
      pow_zero, mul_one];
      intro j hj
      interval_cases j
      · simp only [getBit, Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.zero_mod]
      · simp only [getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
    · push_neg at h_ℓ₁
      set ℓ := ℓ₁ + 1
      have h_ℓ_eq : ℓ = ℓ₁ + 1 := by rfl
      intro j h_j
      -- Inductive step : assume theorem holds for ℓ₁ = ℓ - 1
      -- => show j = ∑ k ∈ Finset.range (ℓ + 1), (getBit k j) * 2^k
      -- Split j into lowBits (b) and higher getLowBits (m) &
      -- reason inductively from the predicate of (m, ℓ₁)
      set b := getBit 0 j -- Least significant getBit : j % 2
      set m := j >>> 1 -- Higher getLowBits : j / 2
      have h_b_eq : b = getBit 0 j := by rfl
      have h_m_eq : m = j >>> 1 := by rfl
      have h_getBit_shift : ∀ k, getBit (k+1) j = getBit k m := by
        intro k
        rw [h_m_eq]
        exact (getBit_of_shiftRight (n := j) (p := 1) k).symm
      have h_j_eq : j = b + 2 * m := by
        calc
          _ = 2 * m + b := by
            have h_m_eq : m = j/2 := by rfl
            have h_b_eq : b = j%2 := by
              rw [h_b_eq]; unfold getBit; rw [Nat.shiftRight_zero]; rw [Nat.and_one_is_mod];
            rw [h_m_eq, h_b_eq];
            rw [Nat.div_add_mod (m := j) (n := 2)]; -- n * (m / n) + m % n = m := by
          _ = b + 2 * m := by omega;
      have h_m : m < 2^ℓ₁ := by
        by_contra h_m_ge_2_pow_ℓ
        push_neg at h_m_ge_2_pow_ℓ
        have h_j_ge : j ≥ 2^ℓ := by
          calc _ = 2 * m + b := by rw [h_j_eq]; omega
            _ ≥ 2 * (2^ℓ₁) + b := by omega
            _ = 2^ℓ + b := by rw [h_ℓ_eq]; omega;
            _ ≥ 2^ℓ := by omega;
        exact Nat.not_lt_of_ge h_j_ge h_j -- contradiction
      have h_m_repr := ih (j := m) h_m
      have getBit_shift : ∀ k, getBit (k + 1) j = getBit k m := by
        intro k
        rw [h_m_eq]
        exact (getBit_of_shiftRight (n := j) (p := 1) k).symm
      -- ⊢ j = ∑ k ∈ Finset.range ℓ, getBit k j * 2 ^ k
      have h_sum : ∑ k ∈ Finset.Icc 0 (ℓ-1), getBit k j * 2 ^ k
        = (∑ k ∈ Finset.Icc 0 0, getBit k j * 2 ^ k)
        + (∑ k ∈ Finset.Icc 1 (ℓ-1), getBit k j * 2 ^ k) := by
        apply sum_Icc_split
        omega
        omega
      rw [h_sum]
      rw [h_j_eq]
      rw [Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]

      have h_sum_2 : ∑ k ∈ Finset.Icc 1 (ℓ-1), getBit k (b + 2 * m) * 2 ^ k
        = ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getBit k (m) * 2 ^ (k+1) := by
        apply Finset.sum_bij' (fun i _ => i - 1) (fun i _ => i + 1)
        · -- left inverse
          intro i hi
          simp only [Finset.mem_Icc] at hi ⊢
          exact Nat.sub_add_cancel hi.1
        · -- right inverse
          intro i hi
          norm_num
        · -- function value match
          intro i hi
          rw [←h_j_eq]
          rw [getBit_of_shiftRight]
          have ⟨left_bound, right_bound⟩ := Finset.mem_Icc.mp hi
          rw [Nat.sub_add_cancel left_bound]
        · -- left membership preservation
          intro i hi -- hi : i ∈ Finset.Icc 1 (ℓ - 1)
          rw [Finset.mem_Icc]
          have ⟨left_bound, right_bound⟩ := Finset.mem_Icc.mp hi
          -- ⊢ 0 ≤ i - 1 ∧ i - 1 ≤ ℓ₁ - 1
          apply And.intro
          · exact Nat.pred_le_pred left_bound
          · exact Nat.pred_le_pred right_bound
        · -- right membership preservation
          intro j hj
          rw [Finset.mem_Icc]
          have ⟨left_bound, right_bound⟩ := Finset.mem_Icc.mp hj -- (0 ≤ j ∧ j ≤ ℓ₁ - 1)
          -- ⊢ 1 ≤ j + 1 ∧ j + 1 ≤ ℓ - 1
          apply And.intro
          · exact Nat.le_add_of_sub_le left_bound
          · rw [h_ℓ_eq]; rw [Nat.add_sub_cancel]; -- ⊢ j + 1 ≤ ℓ₁
            have h_j_add_1_le_ℓ₁ : j + 1 ≤ ℓ₁ := by
              calc j + 1 ≤ (ℓ₁ - 1) + 1 := by apply Nat.add_le_add_right; exact right_bound;
              _ = ℓ₁ := by rw [Nat.sub_add_cancel]; omega;
            exact h_j_add_1_le_ℓ₁
      rw [h_sum_2]

      have h_sum_3 : ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getBit k (m) * 2 ^ (k+1)
        = 2 * ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getBit k (m) * 2 ^ k := by
        calc
          _ = ∑ k ∈ Finset.Icc 0 (ℓ₁-1), ((getBit k (m) * 2^k) * 2) := by
            apply Finset.sum_congr rfl (fun k hk => by
              rw [Finset.mem_Icc] at hk -- hk : 0 ≤ k ∧ k ≤ ℓ₁ - 1
              have h_res : getBit k (m) * 2 ^ (k+1) = getBit k (m) * 2 ^ k * 2 := by
                rw [Nat.pow_succ, ←mul_assoc]
              exact h_res
            )
        _ = (∑ k ∈ Finset.Icc 0 (ℓ₁-1), getBit k (m) * 2 ^ k) * 2 := by rw [Finset.sum_mul]
        _ = 2 * ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getBit k (m) * 2 ^ k := by rw [mul_comm]
      rw [h_sum_3]
      rw [←h_m_repr]
      conv =>
        rhs
        rw [←h_j_eq]

theorem getBit_repr_univ {ℓ : Nat} : ∀ j, j < 2^ℓ →
  j = ∑ k ∈ Finset.univ (α:=Fin ℓ), (getBit k j) * 2^k.val := by
  intro j h_j
  have h_repr_Icc := getBit_repr (ℓ:=ℓ) (j:=j) (by omega)
  rw [h_repr_Icc]
  if h_ℓ_eq_0: ℓ = 0 then
    subst h_ℓ_eq_0
    have h_j_eq_0: j = 0 := by omega
    subst h_j_eq_0
    rfl
  else
    apply Finset.sum_bij' (s:=Finset.Icc 0 (ℓ-1)) (t:=Finset.univ (α:=Fin ℓ))
      (i:=fun a ha => by exact ⟨a, by
        simp only [Finset.mem_Icc, _root_.zero_le, true_and] at ha; omega
      ⟩) (j := fun a ha => by exact a.val)
    · intro a ha; rfl
    · intro a ha; rfl
    · intro a ha
      rw [←h_repr_Icc]
    · intro a ha
      simp only [Finset.mem_univ]
    · intro a ha
      simp only [Finset.mem_Icc, _root_.zero_le, true_and]
      have h_a_lt_ℓ: a < ℓ := by exact a.isLt
      omega

lemma getLowBits_succ {n: ℕ} (numLowBits: ℕ) :
    getLowBits (numLowBits + 1) n = getLowBits numLowBits n
    + (getBit numLowBits n) <<< numLowBits := by
  apply eq_iff_eq_all_getBits.mpr;
  intro k
  have h_getBit_lt_numLowBits: getBit numLowBits n < 2 := by exact getBit_lt_2
  interval_cases h_getBit: getBit numLowBits n
  · rw [Nat.zero_shiftLeft]
    simp only [add_zero]
    -- ⊢ getLowBits n (numLowBits + 1) >>> k &&& 1 = getLowBits n numLowBits >>> k &&& 1
    change getBit k (getLowBits (numLowBits + 1) n) = getBit k (getLowBits numLowBits n)
    have getBit_right := getBit_of_lowBits (n := n) (numLowBits := numLowBits) k
    have getBit_left := getBit_of_lowBits (n := n) (numLowBits := numLowBits + 1) k
    rw [getBit_right, getBit_left]
    if h_k: k < numLowBits then
      simp only [h_k, ↓reduceIte]
      have h_k_lt: k < numLowBits + 1 := by omega
      simp only [h_k_lt, ↓reduceIte]
    else if h_k_eq: k = numLowBits then
      simp only [h_k_eq]
      simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false]
      omega
    else
      have k_ne_lt: ¬(k < numLowBits) := by omega
      have k_ne_lt_add_1: ¬(k < numLowBits + 1) := by omega
      simp only [k_ne_lt_add_1, ↓reduceIte, k_ne_lt]
  · change getBit k (getLowBits (numLowBits + 1) n)
      = getBit k (getLowBits numLowBits n + 1 <<< numLowBits)
    have getBit_left := getBit_of_lowBits (n := n) (numLowBits := numLowBits + 1) k
    have getBit_right := getBit_of_lowBits (n := n) (numLowBits := numLowBits) k
    rw [getBit_left]

    have h_and_eq_0 := and_two_pow_eq_zero_of_getBit_0 (n:=getLowBits numLowBits n)
      (i:=numLowBits) (by
      simp only [getBit_of_lowBits (n := n) (numLowBits := numLowBits) numLowBits,
        lt_self_iff_false, ↓reduceIte]
    )
    rw [←one_mul (a:=2 ^ numLowBits)] at h_and_eq_0
    rw [←Nat.shiftLeft_eq (a:=1) (b:=numLowBits)] at h_and_eq_0
    have h_sum_eq_xor := sum_of_and_eq_zero_is_xor (n:=getLowBits numLowBits n)
      (m:=1 <<< numLowBits) (h_n_AND_m:=h_and_eq_0)
    have h_sum_eq_or := xor_of_and_eq_zero_is_or (n:=getLowBits numLowBits n)
      (m:=1 <<< numLowBits) (h_n_AND_m:=h_and_eq_0)
    rw [h_sum_eq_or] at h_sum_eq_xor
    rw [h_sum_eq_xor]
    rw [getBit_of_or]
    rw [getBit_of_lowBits]
    conv_rhs =>
      enter [2, 2]; rw [Nat.shiftLeft_eq, one_mul]
    rw [getBit_two_pow]

    if h_k: k < numLowBits then
      have h_k_lt: k < numLowBits + 1 := by omega
      simp only [h_k_lt, ↓reduceIte, h_k, beq_iff_eq]
      have h_k_ne_eq: numLowBits ≠ k := by omega
      simp only [h_k_ne_eq, ↓reduceIte, Nat.or_zero]
    else if h_k_eq: k = numLowBits then
      simp only [h_k_eq, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false, BEq.rfl,
        Nat.zero_or]
      omega
    else
      have k_ne_lt: ¬(k < numLowBits) := by omega
      have k_ne_lt_add_1: ¬(k < numLowBits + 1) := by omega
      simp only [k_ne_lt_add_1, ↓reduceIte, k_ne_lt, beq_iff_eq, Nat.zero_or, right_eq_ite_iff,
        zero_ne_one, imp_false, ne_eq]
      omega

/-- This takes a argument for the number of lowBitss to remove from the number -/
def getHighBits_no_shl (numLowBits : ℕ) (n : ℕ) : ℕ := n >>> numLowBits

def getHighBits (numLowBits : ℕ) (n : ℕ) : ℕ :=
  (getHighBits_no_shl numLowBits n) <<< numLowBits

theorem and_highBits_lowBits_eq_zero {n : ℕ} (numLowBits : ℕ) :
    getHighBits numLowBits n &&& getLowBits numLowBits n = 0 := by
  change (n >>> numLowBits <<< numLowBits) &&& (getLowBits numLowBits n) = 0
  set highBits_no_shl := n >>> numLowBits
  have h_getBit_highBits_shl := getBit_of_shiftLeft (n := highBits_no_shl) (p := numLowBits)
  have h_getBit_lowBits := getBit_of_lowBits (n := n) (numLowBits := numLowBits)
  apply and_eq_zero_iff_and_each_getBit_eq_zero.mpr
  intro j
  change getBit j ((n >>> numLowBits) <<< numLowBits)
    &&& getBit j (getLowBits numLowBits n) = 0
  if h_j: j < numLowBits then
    have h_getBit_lhs := h_getBit_highBits_shl (k:=j - numLowBits)
    have h_ne: ¬(numLowBits ≤ j) := by omega
    have h_getBit_left_eq_0 :  getBit j ((n >>> numLowBits) <<< numLowBits) = 0:= by
      rw [h_getBit_highBits_shl]
      simp only [ite_eq_left_iff, not_lt, h_ne, IsEmpty.forall_iff, highBits_no_shl]
    rw [h_getBit_left_eq_0, Nat.zero_and]
  else
    have h_getBit_rhs := h_getBit_lowBits (k:=j)
    have h_getBit_right_eq_0: getBit j (getLowBits numLowBits n) = 0 := by
      simp only [h_getBit_rhs, ite_eq_right_iff]
      omega
    rw [h_getBit_right_eq_0, Nat.and_zero]

lemma num_eq_highBits_add_lowBits {n: ℕ} (numLowBits: ℕ) :
  n = getHighBits numLowBits n + getLowBits numLowBits n := by
  apply eq_iff_eq_all_getBits.mpr; unfold getBit
  intro k
  --- use 2 getBit extractions to get the condition for getLowBits of ((n >>> numLowBits) <<<
  --  numLowBits)
  set highBits_no_shl := n >>> numLowBits
  have h_getBit_highBits_shl := getBit_of_shiftLeft (n := highBits_no_shl) (p := numLowBits)
  have h_getBit_lowBits := getBit_of_lowBits (n := n) (numLowBits := numLowBits)
  -- AND of highBitss & lowBitss is 0 => we use this to convert the sum into OR
  have h_and := and_highBits_lowBits_eq_zero (n := n) (numLowBits := numLowBits)
  rw [sum_of_and_eq_zero_is_or h_and]
  --- now reason on bitwise operations only
  rw [Nat.shiftRight_or_distrib, Nat.and_distrib_right]
  change getBit k n = getBit k ((n >>> numLowBits) <<< numLowBits)
    ||| getBit k (getLowBits numLowBits n)
  rw [h_getBit_highBits_shl, h_getBit_lowBits]
  if h_k: k < numLowBits then
    simp only [h_k, ↓reduceIte, Nat.zero_or] at *
  else
    have h_ne: ¬(k < numLowBits) := by omega
    have h_num_le_k: numLowBits ≤ k := by omega
    simp only [h_ne, not_false_eq_true, ↓reduceIte, Nat.or_zero] at *
    rw [getBit_of_shiftRight]
    congr
    rw [Nat.sub_add_cancel (n:=k) (m:=numLowBits) (by omega)]

lemma num_eq_highBits_xor_lowBits {n: ℕ} (numLowBits: ℕ) :
  n = getHighBits numLowBits n ^^^ getLowBits numLowBits n := by
  rw [←sum_of_and_eq_zero_is_xor]
  · exact num_eq_highBits_add_lowBits (n := n) (numLowBits := numLowBits)
  · exact and_highBits_lowBits_eq_zero (n := n) (numLowBits := numLowBits)

lemma getBit_of_highBits {n: ℕ} (numLowBits : ℕ) : ∀ k, getBit k (getHighBits numLowBits n) =
    if k < numLowBits then 0 else getBit (k) (n) := by
  intro k
  simp only [getHighBits, getHighBits_no_shl]
  rw [getBit_of_shiftLeft]
  if h_k: k < numLowBits then
    simp only [h_k, ↓reduceIte]
  else
    simp only [h_k, ↓reduceIte]
    rw [getBit_of_shiftRight]
    rw [Nat.sub_add_cancel (by omega)]

lemma getBit_of_highBits_no_shl {n: ℕ} (numLowBits : ℕ) :
    ∀ k, getBit k (getHighBits_no_shl numLowBits n)
  = getBit (k + numLowBits) (n) := by
  intro k
  simp only [getHighBits_no_shl]
  exact getBit_of_shiftRight k

lemma getBit_of_lt_two_pow {n: ℕ} (a: Fin (2^n)) (k: ℕ) :
  getBit k a = if k < n then getBit k a else 0 := by
  if h_k: k < n then
    simp only [h_k, ↓reduceIte]
  else
    simp only [h_k, ↓reduceIte]
    rw [getBit_eq_testBit]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Bool.not_eq_true]
    rw [Nat.testBit_eq_false_of_lt]
    simp only [not_lt] at h_k
    calc a.val < 2^n := a.isLt
      _ ≤ 2^k := Nat.pow_le_pow_right (by omega) h_k

-- Note: maybe we can generalize this into a non-empty set of diff bits
lemma exist_bit_diff_if_diff {n: ℕ} (a: Fin (2^n)) (b: Fin (2^n)) (h_a_ne_b: a ≠ b):
  ∃ k: Fin n, getBit k a ≠ getBit k b := by
  by_contra h_no_diff
  push_neg at h_no_diff
  have h_a_eq_b: a = b := by
    apply Fin.eq_of_val_eq
    apply eq_iff_eq_all_getBits.mpr
    intro k
    change getBit k a = getBit k b
    rw [getBit_of_lt_two_pow, getBit_of_lt_two_pow]
    if h_k: k < n then
      simp only [h_k, ↓reduceIte]
      exact h_no_diff ⟨k, by omega⟩
    else
      simp only [h_k, ↓reduceIte]
      rw [getBit_eq_testBit]
      simp only [right_eq_ite_iff, zero_ne_one, imp_false, Bool.not_eq_true]
      rw [Nat.testBit_eq_false_of_lt]
      simp only [not_lt] at h_k
      calc b.val < 2^n := b.isLt
        _ ≤ 2^k := Nat.pow_le_pow_right (by omega) h_k
  contradiction

def binaryFinMapToNat {n : ℕ} (m : Fin n → ℕ) (h_binary : ∀ j: Fin n, m j ≤ 1) : Fin (2^n) := by
  let i_of_m := ∑ j ∈ Finset.univ, (2^j.val) * (m j)
  have h_lt: 2^n - 1 < 2^n := by
    refine sub_one_lt ?_
    exact Ne.symm (NeZero.ne' (2 ^ n))
  have h_i_lt : i_of_m < 2^n := by
    -- Use a calc block for a clear chain of inequalities
    calc
      i_of_m = ∑ j, 2^j.val * m j         := rfl
      _      ≤ ∑ j: Fin n, (2^j.val) * 1 := by
        -- ⊢ ∑ j, 2 ^ ↑j * m j ≤ ∑ j, 2 ^ ↑j * 1
        have h_le: ∀ j: Fin n, (2^j.val) * (m j) ≤ (2^j.val) * 1 := by
          intro j
          simp only [mul_one, ofNat_pos, pow_pos, mul_le_iff_le_one_right]
          exact h_binary j
        apply Finset.sum_le_sum
        intro i hi
        exact h_le i
      _      = ∑ j : Fin n, 2^j.val        := by simp
      _      = 2^n - 1                     := by
        rw [getBit_repr_univ (ℓ:=n) (j:=2^n-1) (by omega)]
        conv_rhs =>
          enter [2, k]; rw [getBit_of_two_pow_sub_one (i:=n)]; simp only [Fin.is_lt, ↓reduceIte,
            one_mul]
      _      < 2^n                         := by exact h_lt
  exact ⟨i_of_m, h_i_lt⟩

lemma getBit_of_binaryFinMapToNat {n : ℕ} (m : Fin n → ℕ) (h_binary: ∀ j: Fin n, m j ≤ 1) :
    ∀ k: ℕ, Nat.getBit k (binaryFinMapToNat m h_binary).val
      = if h_k: k < n then m ⟨k, by omega⟩ else 0 := by
  -- We prove this by induction on `n`.
  induction n with
  | zero =>
    intro k;
    simp only [Nat.pow_zero, Fin.val_eq_zero, not_lt_zero', ↓reduceDIte]
    exact getBit_zero_eq_zero
  | succ n ih =>
    -- Inductive step: Assume the property holds for `n`, prove it for `n+1`.
    have h_lt: 2^n - 1 < 2^n := by
      refine sub_one_lt ?_
      exact Ne.symm (NeZero.ne' (2 ^ n))
    intro k
    dsimp [binaryFinMapToNat]
    -- ⊢ (↑k).getBit (∑ j, 2 ^ ↑j * m j) = m k
    rw [Fin.sum_univ_castSucc] -- split the msb
    set prevSum := ∑ i: Fin n, (2 ^ i.castSucc.val) * (m i.castSucc)
    let mPrev := fun i: Fin n => m i.castSucc
    have h_getBit_prevSum := ih (m:=mPrev) (h_binary:=by exact fun j ↦ h_binary j.castSucc)
    have h_prevSum_eq: prevSum = binaryFinMapToNat mPrev
      (by exact fun j ↦ h_binary j.castSucc) := by rfl
    set msbTerm := 2 ^ ((Fin.last n).val) * m (Fin.last n)
    -- ⊢ (↑k).getBit (prevSum + msbTerm) = m k
    have h_m_at_last: m ⟨n, by omega⟩ ≤ 1 := by exact h_binary (Fin.last n)
    have h_sum_eq_xor: prevSum + msbTerm = prevSum ^^^ msbTerm := by
      rw [sum_of_and_eq_zero_is_xor]
      unfold msbTerm
      interval_cases h_m_last_val: m ⟨n, by omega⟩
      · simp only [Fin.last, h_m_last_val, mul_zero, Nat.and_zero]
      · simp only [Fin.last, h_m_last_val, mul_one]
        apply and_two_pow_eq_zero_of_getBit_0
        have h_getBit_prevSum_at_n := getBit_of_lt_two_pow (k:=n) (n:=n) (a:=⟨prevSum, by omega⟩)
        simp only [lt_self_iff_false, ↓reduceIte] at h_getBit_prevSum_at_n
        rw [h_getBit_prevSum_at_n]
    rw [h_sum_eq_xor, getBit_of_xor]
    if h_k_eq: k = n then
      rw [h_k_eq]
      simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte]
      rw [h_prevSum_eq]
      rw [getBit_of_lt_two_pow]
      simp only [lt_self_iff_false, ↓reduceIte, zero_xor]
      unfold msbTerm
      -- ⊢ n.getBit (2 ^ ↑(Fin.last n) * m (Fin.last n)) = m ⟨n, ⋯⟩
      interval_cases h_m_last_val: m ⟨n, by omega⟩
      · -- ⊢ n.getBit (2 ^ ↑(Fin.last n) * m (Fin.last n)) = 0
        rw [Fin.val_last, Fin.last]
        rw [h_m_last_val, mul_zero]
        exact getBit_zero_eq_zero
      · -- ⊢ n.getBit (2 ^ ↑(Fin.last n) * m (Fin.last n)) = 1
        simp only [Fin.last]
        rw [h_m_last_val, mul_one]
        rw [Nat.getBit_two_pow]
        simp only [BEq.rfl, ↓reduceIte]
    else
      have hBitLhs := h_getBit_prevSum (k:=k)
      simp only at hBitLhs
      rw [h_prevSum_eq.symm] at hBitLhs
      rw [hBitLhs]
      if h_k_lt_n: k < n then
        have h_k_lt_n_add_1: k < n + 1 := by omega
        simp only [h_k_lt_n_add_1, ↓reduceDIte]
        push_neg at h_k_eq
        simp only [h_k_lt_n, ↓reduceDIte]
        unfold msbTerm
        interval_cases h_m_last_val: m ⟨n, by omega⟩
        · simp only [Fin.last, h_m_last_val, mul_zero]
          rw [Nat.getBit_zero_eq_zero, Nat.xor_zero]
          rfl
        · simp only [Fin.last, h_m_last_val, mul_one]
          rw [Nat.getBit_two_pow]
          simp only [beq_iff_eq]
          simp only [h_k_eq.symm, ↓reduceIte, xor_zero]
          rfl
      else
        have h_k_not_lt_n_add_1: ¬(k < n + 1) := by omega
        have h_k_not_lt_n: ¬(k < n) := by omega
        simp only [h_k_not_lt_n_add_1, h_k_not_lt_n, ↓reduceDIte, Nat.zero_xor]
        unfold msbTerm
        interval_cases h_m_last_val: m ⟨n, by omega⟩
        · simp only [Fin.last, h_m_last_val, mul_zero]
          exact getBit_zero_eq_zero
        · simp only [Fin.last, h_m_last_val, mul_one]
          rw [Nat.getBit_two_pow]
          simp only [beq_iff_eq]
          simp only [ite_eq_right_iff, one_ne_zero, imp_false, ne_eq]
          omega

end Nat
