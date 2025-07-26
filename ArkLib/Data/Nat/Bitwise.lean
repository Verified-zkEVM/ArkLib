/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.Fin.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Bitwise

/-!
# Bit operations on natural numbers

-/

namespace Nat

/--
Returns the `k`-th least significant bit of a natural number `n` as a natural number (in `{0, 1}`).

We decompose each number `j < 2^ℓ` into its binary representation : `j = Σ k ∈ Fin ℓ, jₖ * 2ᵏ`
-/
def getLsb (k n : Nat) : Nat := (n >>> k) &&& 1

lemma getLsb_lt_2 {k n : Nat} : getLsb k n < 2 := by
  unfold getLsb
  rw [Nat.and_one_is_mod]
  simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt]

lemma getLsb_zero_eq_zero {k : Nat} : getLsb k 0 = 0 := by
  unfold getLsb
  rw [Nat.zero_shiftRight]
  rw [Nat.and_one_is_mod]

lemma getLsb_eq_zero_or_one {k n : Nat} :
  getLsb k n = 0 ∨ getLsb k n = 1 := by
  unfold getLsb
  rw [Nat.and_one_is_mod]
  simp only [Nat.mod_two_eq_zero_or_one]

lemma lsb_of_single_getLsb {n : ℕ} (h_n : n < 2) : getLsb 0 n = n := by
  unfold getLsb
  rw [Nat.shiftRight_zero]
  rw [Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt h_n

lemma lsb_of_multiple_of_two {n : ℕ} : getLsb 0 (2*n) = 0 := by
  unfold getLsb
  rw [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_mod_right]

def get_lsb (n : ℕ) (num_lsb_getLsbs : ℕ) := n &&& ((1 <<< num_lsb_getLsbs) - 1)

lemma get_zero_lsb_eq_zero {n : ℕ} : get_lsb n 0 = 0 := by
  unfold get_lsb
  simp only [Nat.shiftLeft_zero, Nat.sub_self, Nat.and_zero]

lemma get_lsb_eq_mod_two_pow {n : ℕ} (num_lsb_getLsbs : ℕ) :
  get_lsb n num_lsb_getLsbs = n % (2 ^ num_lsb_getLsbs) := by
  unfold get_lsb
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod n num_lsb_getLsbs

lemma get_lsb_lt_two_pow {n : ℕ} (num_lsb_getLsbs : ℕ) :
    get_lsb n num_lsb_getLsbs < 2 ^ num_lsb_getLsbs := by
  rw [get_lsb_eq_mod_two_pow]
  omega

lemma get_lsb_le_self {n : ℕ} (num_lsb_getLsbs : ℕ) : get_lsb n num_lsb_getLsbs ≤ n := by
  rw [get_lsb_eq_mod_two_pow]
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

lemma eq_iff_eq_all_getLsbs {n m : ℕ} : n = m ↔ ∀ k, (n >>> k) &&& 1 = (m >>> k) &&& 1 := by
  constructor
  · intro h_eq -- h_eq : n = m
    intro k
    rw [h_eq]
  · intro h_all_getLsbs -- h_all_getLsbs : ∀ k, (n >>> k) &&& 1 = (m >>> k) &&& 1
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_eq_beq]
    simp only [Nat.and_one_is_mod] at h_all_getLsbs k
    rw [h_all_getLsbs k]

lemma shiftRight_and_one_distrib {n m k : ℕ} :
    (n &&& m) >>> k &&& 1 = ((n >>> k) &&& 1) &&& ((m >>> k) &&& 1) := by
  rw [Nat.shiftRight_and_distrib]
  conv =>
    lhs
    rw [←Nat.and_self (x := 1)]
    rw [←Nat.and_assoc]
    rw [Nat.and_assoc (y := m >>> k) (z := 1), Nat.and_comm (x := m>>>k) (y := 1), ←Nat.and_assoc]
    rw [Nat.and_assoc]

lemma and_eq_zero_iff_and_each_getLsb_eq_zero {n m : ℕ} :
    n &&& m = 0 ↔ ∀ k, ((n >>> k) &&& 1) &&& ((m >>> k) &&& 1) = 0 := by
  constructor
  · intro h_and_zero
    intro k
    have h_k := shiftRight_and_one_distrib (n := n) (m := m) (k := k)
    rw [←h_k]
    rw [h_and_zero, Nat.zero_shiftRight, Nat.zero_and]
  · intro h_forall_k -- h_forall_k : ∀ (k : ℕ), n >>> k &&& 1 &&& (m >>> k &&& 1) = 0
    apply eq_iff_eq_all_getLsbs.mpr
    intro k
    -- ⊢ (n &&& m) >>> k &&& 1 = 0 >>> k &&& 1
    have h_forall_k_eq : ∀ k, ((n &&& m) >>> k) &&& 1 = 0 := by
      intro k
      rw [shiftRight_and_one_distrib]
      exact h_forall_k k
    rw [h_forall_k_eq k]
    rw [Nat.zero_shiftRight, Nat.zero_and]

lemma getLsb_two_pow {i k: ℕ} : (getLsb k (2^i) = if i == k then 1 else 0) := by
  have h_two_pow_i: 2^i = 1 <<< i := by
    simp only [Nat.shiftLeft_eq, one_mul]
  rw [getLsb, h_two_pow_i]
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

lemma and_two_pow_eq_zero_of_getLsb_0 {n i : ℕ} (h_getLsb: getLsb i n = 0) : n &&& (2 ^ i) = 0 := by
  apply and_eq_zero_iff_and_each_getLsb_eq_zero.mpr
  intro k
  have h_getLsb_two_pow := getLsb_two_pow (i := i) (k := k)
  if h_k: k = i then
    simp only [h_k, BEq.rfl, ↓reduceIte] at h_getLsb_two_pow
    rw [getLsb, h_k.symm] at h_getLsb
    rw [h_getLsb, Nat.zero_and]
  else
    push_neg at h_k
    simp only [beq_iff_eq, h_k.symm, ↓reduceIte] at h_getLsb_two_pow
    rw [getLsb] at h_getLsb_two_pow
    rw [h_getLsb_two_pow]
    rw [Nat.and_zero]

lemma and_two_pow_eq_two_pow_of_getLsb_1 {n i : ℕ} (h_getLsb: getLsb i n = 1) :
    n &&& (2 ^ i) = 2 ^ i := by
  have h_testBit_i_eq_1 : n.testBit i = true := by
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_iff_eq]
    simp only [getLsb, Nat.and_one_is_mod] at h_getLsb
    exact h_getLsb
  conv_lhs => rw [Nat.and_two_pow (n:=n) (i:=i)]
  simp only [h_testBit_i_eq_1, Bool.toNat_true, one_mul]

lemma and_two_pow_eq_two_pow_of_getLsb_eq_one {n i : ℕ} (h_getLsb: getLsb i n = 1)
    : n &&& (2 ^ i) = 2 ^ i := by
  apply eq_iff_eq_all_getLsbs.mpr
  intro k
  have h_getLsb_two_pow := getLsb_two_pow (i := i) (k := k)
  if h_k: k = i then
    simp only [h_k, BEq.rfl, ↓reduceIte] at h_getLsb_two_pow
    rw [getLsb, h_k.symm] at h_getLsb
    -- ⊢ getLsb k (n &&& 2 ^ i) = 2 ^ i >>> k &&& 1
    rw [getLsb, h_k.symm] at h_getLsb_two_pow
    rw [h_k.symm, h_getLsb_two_pow]
    rw [Nat.shiftRight_and_distrib, Nat.and_assoc, Nat.and_comm (2^k >>> k) 1, ←Nat.and_assoc]
    rw [h_getLsb, ←one_mul (2^k), ←Nat.shiftLeft_eq, Nat.shiftLeft_shiftRight, Nat.and_self]
  else
    push_neg at h_k
    simp only [beq_iff_eq, h_k.symm, ↓reduceIte] at h_getLsb_two_pow
    rw [getLsb] at h_getLsb_two_pow
    rw [h_getLsb_two_pow, Nat.shiftRight_and_distrib, Nat.and_assoc, h_getLsb_two_pow]
    rw [Nat.and_zero]

lemma and_one_eq_of_eq {a b : ℕ} : a = b → a &&& 1 = b &&& 1 := by
  intro h_eq
  rw [h_eq]

lemma eq_zero_or_eq_one_of_lt_two {n : ℕ} (h_lt : n < 2) : n = 0 ∨ n = 1 := by
  interval_cases n
  · left; rfl
  · right; rfl

lemma div_2_form {nD2 bn : ℕ} (h_bn : bn < 2):
  (nD2 * 2 + bn) / 2 = nD2 := by
  rw [←add_comm, ←mul_comm]
  rw [Nat.add_mul_div_left (x := bn) (y := 2) (z := nD2) (H := by norm_num)]
  norm_num; exact h_bn;

lemma and_of_chopped_lsb {n m n1 m1 bn bm : ℕ} (h_bn : bn < 2) (h_bm : bm < 2)
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

lemma xor_of_chopped_lsb {n m n1 m1 bn bm : ℕ} (h_bn : bn < 2) (h_bm : bm < 2)
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

lemma or_of_chopped_lsb {n m n1 m1 bn bm : ℕ} (h_bn : bn < 2) (h_bm : bm < 2)
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
    set getLsbN := bn.toNat
    set getLsbM := bm.toNat
    have h_getLsbN : getLsbN < 2 := by
      exact Bool.toNat_lt bn
    have h_getLsbM : getLsbM < 2 := by
      exact Bool.toNat_lt bm
    have h_and_getLsbN_getLsbM : (getLsbN &&& getLsbM) < 2 := by
      interval_cases getLsbN
      · interval_cases getLsbM
        · rw [Nat.zero_and]; norm_num;
        · rw [Nat.zero_and]; norm_num;
      · interval_cases getLsbM
        · rw [Nat.and_zero]; norm_num;
        · rw [Nat.and_self]; norm_num;
    have h_n : nVal = n2 * 2 + getLsbN := by
      unfold nVal
      rw [Nat.bit_val, mul_comm]
    have h_m : mVal = m2 * 2 + getLsbM := by
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
    have h_and : nVal &&& mVal = (n2 &&& m2) * 2 + (getLsbN &&& getLsbM) :=
      and_of_chopped_lsb (h_bn := h_getLsbN) (h_bm := h_getLsbM) (h_n := h_n) (h_m := h_m)
    have h_xor : nVal ^^^ mVal = (n2 ^^^ m2) * 2 + (getLsbN ^^^ getLsbM) :=
      xor_of_chopped_lsb (h_bn := h_getLsbN) (h_bm := h_getLsbM) (h_n := h_n) (h_m := h_m)
    have h_or : nVal ||| mVal = (n2 ||| m2) * 2 + (getLsbN ||| getLsbM) :=
      or_of_chopped_lsb (h_bn := h_getLsbN) (h_bm := h_getLsbM) (h_n := h_n) (h_m := h_m)
    have h_prev := ih m2
    -- ⊢ nVal + mVal = (nVal ^^^ mVal) + (2 * (nVal &&& mVal))
    have sum_eq : nVal + mVal = (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getLsbN + getLsbM) := by
      calc
        _ = (n2 * 2 + getLsbN) + (m2 * 2 + getLsbM) := by rw [h_n, h_m]
        _ = (n2 + m2) * 2 + (getLsbN + getLsbM) := by
          rw [Nat.right_distrib, ←add_assoc, ←add_assoc]; omega;
        _ = ((n2 ^^^ m2) + 2 * (n2 &&& m2)) * 2 + (getLsbN + getLsbM) := by rw [h_prev]
        _ = (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getLsbN + getLsbM) := by
          rw [Nat.right_distrib]; omega
    rw [sum_eq]
    -- From this point, we basically do case analysis on `bn &&& bm`
    -- rw [h_n, h_m]
    by_cases h_and_getLsbN_getLsbM_eq_1 : getLsbN &&& getLsbM = 1
    · have h_getLsbN_and_getLsbM_eq_1 : getLsbN = 1 ∧ getLsbM = 1 := by
        interval_cases getLsbN
        · interval_cases getLsbM
          · contradiction
          · contradiction
        · interval_cases getLsbM
          · contradiction
          · and_intros; rfl; rfl;
      have h_sum_getLsbs : (getLsbN + getLsbM) = 2 := by omega
      have h_xor_getLsbs : getLsbN ^^^ getLsbM = 0 := by
        simp only [h_getLsbN_and_getLsbM_eq_1, Nat.xor_self];
      have h_and_getLsbs : getLsbN &&& getLsbM = 1 := by
        simp only [h_getLsbN_and_getLsbM_eq_1, Nat.and_self];
      -- ⊢ (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getLsbN + getLsbM)
      -- = (nVal ^^^ mVal) + 2 * (nVal &&& mVal)
      have h_left : (n2 ^^^ m2) * 2 = (nVal ^^^ mVal) := by
        calc
          _ = (n2 ^^^ m2) * 2 + 0 := by omega;
          _ = (n2 ^^^ m2) * 2 + (getLsbN ^^^ getLsbM) := by rw [h_xor_getLsbs];
          _ = _ := by exact h_xor.symm
      rw [h_left]
      rw [add_assoc]
      have h_right : 4 * (n2 &&& m2) + (getLsbN + getLsbM) = 2 * (nVal &&& mVal) := by
        calc
          _ = 4 * (n2 &&& m2) + 2 := by rw [h_sum_getLsbs];
          _ = 2 * (2 * (n2 &&& m2) + 1) := by omega;
          _ = 2 * ((n2 &&& m2) * 2 + (getLsbN &&& getLsbM)) := by
            rw [h_and_getLsbs, mul_comm (a := (n2 &&& m2)) (b := 2)];
          _ = 2 * (nVal &&& mVal) := by rw [h_and];
      rw [h_right]
    · push_neg at h_and_getLsbN_getLsbM_eq_1;
      have h_and_getLsbN_getLsbM_eq_0 : (getLsbN &&& getLsbM) = 0 := by
        interval_cases (getLsbN &&& getLsbM)
        · rfl
        · contradiction
      have h_getLsbs_eq : getLsbN = 0 ∨ getLsbM = 0 := by
        interval_cases getLsbN
        · left; rfl
        · right;
          interval_cases getLsbM
          · rfl
          · contradiction
      have h_sum_getLsbs : (getLsbN + getLsbM) = (getLsbN ^^^ getLsbM) := by
        interval_cases getLsbN
        · interval_cases getLsbM
          · rfl
          · rfl
        · interval_cases getLsbM
          · rfl
          · contradiction -- with h_and_getLsbN_getLsbM_eq_0
      -- ⊢ (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (getLsbN + getLsbM)
      -- = (nVal ^^^ mVal) + 2 * (nVal &&& mVal)
      rw [←add_assoc, add_assoc (b := getLsbN) (c := getLsbM), add_assoc]
      rw [add_comm (b := (getLsbN + getLsbM)), ←add_assoc]
      have h_left : (n2 ^^^ m2) * 2 + (getLsbN + getLsbM) = (nVal ^^^ mVal) := by
        calc
          _ = (n2 ^^^ m2) * 2 + (getLsbN ^^^ getLsbM) := by rw [h_sum_getLsbs];
          _ = _ := by exact h_xor.symm
      rw [h_left]

      -- 4 * (n2 &&& m2) = 2 * (2 * (n2 &&& m2) + (bn &&& bm)) = 2 * (n &&& m)
      have h_right : 4 * (n2 &&& m2) = 2 * (nVal &&& mVal) := by
        calc
          _ = 4 * (n2 &&& m2) + 0 := by omega;
          _ = 4 * (n2 &&& m2) + (getLsbN &&& getLsbM) := by rw [h_and_getLsbN_getLsbM_eq_0];
          _ = 2 * (2 * (n2 &&& m2) + (getLsbN &&& getLsbM)) := by omega;
          _ = 2 * ((n2 &&& m2) * 2 + (getLsbN &&& getLsbM)) := by
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
  apply eq_iff_eq_all_getLsbs.mpr
  intro k
  rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_or_distrib]
  rw [Nat.and_xor_distrib_right] -- lhs
  rw [Nat.and_distrib_right] -- rhs
  -- ⊢ (n >>> k &&& 1) ^^^ (m >>> k &&& 1) = (n >>> k &&& 1) ||| (m >>> k &&& 1)
  set getLsbN := n >>> k &&& 1
  set getLsbM := m >>> k &&& 1
  have h_getLsbN : getLsbN < 2 := by
    simp only [getLsbN, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := n >>> k) (y := 2)]
  have h_getLsbM : getLsbM < 2 := by
    simp only [getLsbM, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := m >>> k) (y := 2)]
  -- ⊢ getLsbN ^^^ getLsbM = getLsbN ||| getLsbM
  have h_and_getLsbN_getLsbM : (getLsbN &&& getLsbM) = 0 := by
    exact and_eq_zero_iff_and_each_getLsb_eq_zero.mp h_n_AND_m k
  interval_cases getLsbN -- case analysis on `getLsbN, getLsbM`
  · interval_cases getLsbM
    · rfl
    · rfl
  · interval_cases getLsbM
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

lemma getLsb_of_add_distrib {n m k : ℕ}
  (h_n_AND_m : n &&& m = 0) : getLsb k (n + m) = getLsb k n + getLsb k m := by
  unfold getLsb
  rw [sum_of_and_eq_zero_is_xor h_n_AND_m]
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
  set getLsbN := n >>> k &&& 1
  set getLsbM := m >>> k &&& 1
  have h_getLsbN : getLsbN < 2 := by
    simp only [getLsbN, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := n >>> k) (y := 2)]
  have h_getLsbM : getLsbM < 2 := by
    simp only [getLsbM, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := m >>> k) (y := 2)]
  have h_getLsbN_and_getLsbM : (getLsbN &&& getLsbM) = 0 := by
    exact and_eq_zero_iff_and_each_getLsb_eq_zero.mp h_n_AND_m k
  exact (sum_of_and_eq_zero_is_xor (n := getLsbN) (m := getLsbM) h_getLsbN_and_getLsbM).symm

lemma add_two_pow_of_getLsb_eq_zero_lt_two_pow {n m i : ℕ} (h_n: n < 2^m) (h_i: i < m)
  (h_getLsb_at_i_eq_zero: getLsb i n = 0) :
  n + 2^i < 2^m := by
  have h_j_and: n &&& (2^i) = 0 := by
    rw [and_two_pow_eq_zero_of_getLsb_0 (n:=n) (i:=i)]
    rw [←h_getLsb_at_i_eq_zero]
  rw [sum_eq_xor_plus_twice_and, h_j_and, mul_zero, add_zero]
  have h_and_lt := Nat.xor_lt_two_pow (x:=n) (y:=2^i) (n:=m) (by omega) (by
    apply Nat.pow_lt_pow_right (a:=2) (m:=i) (n:=m) (ha:=by omega) (h:=by omega)
  )
  exact h_and_lt

lemma getLsb_of_multiple_of_power_of_two {n p : ℕ}: ∀ k,
  getLsb (k) (2^p * n) = if k < p then 0 else getLsb (k-p) n := by
  intro k
  have h_test := Nat.testBit_two_pow_mul (i := p) (a := n) (j:=k)
  simp only [Nat.testBit, Nat.and_comm 1] at h_test
  if h_k: p > k then
    have h_ne_p_le_k: ¬(p ≤ k) := by omega
    simp only [Nat.and_one_is_mod, Nat.mod_two_bne_zero, ge_iff_le, h_ne_p_le_k, decide_false,
      Bool.false_and, beq_eq_false_iff_ne, ne_eq, Nat.mod_two_not_eq_one, h_k,
      ↓reduceIte] at h_test ⊢
    simp only [getLsb, Nat.and_one_is_mod]
    omega
  else
    have h_p_le_k: p ≤ k := by omega
    have h_ne_k_lt_p: ¬(k < p) := by omega
    simp only [Nat.and_one_is_mod, Nat.mod_two_bne_zero, ge_iff_le, h_p_le_k, decide_true,
      Bool.true_and, beq_eq_beq, h_ne_k_lt_p, ↓reduceIte] at h_test ⊢
    simp only [getLsb]
    -- ⊢ (2 ^ p * n) >>> k % 2 = n >>> (k - p) % 2
    change getLsb k (2^p * n) = getLsb (k - p) n
    have h_getLsb_left_lt: getLsb (k - p) n < 2 := getLsb_lt_2
    have h_getLsb_right_lt: getLsb k n < 2 := getLsb_lt_2
    interval_cases h_getLsb_left_lt_eq: getLsb (k - p) n
    · simp only [getLsb, Nat.and_one_is_mod] at h_getLsb_left_lt_eq
      simp [h_getLsb_left_lt_eq] at h_test
      simp only [getLsb, Nat.and_one_is_mod, h_test]
    · simp only [getLsb, Nat.and_one_is_mod] at h_getLsb_left_lt_eq
      simp only [h_getLsb_left_lt_eq, iff_true] at h_test
      simp only [getLsb, Nat.and_one_is_mod, h_test]

lemma getLsb_of_shiftLeft {n p : ℕ}:
  ∀ k, getLsb (k) (n <<< p) = if k < p then 0 else getLsb (k - p) n := by
  intro k
  rw [getLsb_of_multiple_of_power_of_two (n:=n) (p:=p) (k:=k).symm]
  congr
  rw [Nat.shiftLeft_eq, mul_comm]

lemma getLsb_of_shiftRight {n p : ℕ}:
  ∀ k, getLsb k (n >>> p) = getLsb (k+p) n := by
  intro k
  unfold getLsb
  rw [←Nat.shiftRight_add]
  rw [←add_comm]

lemma getLsb_of_or {n m k: ℕ} : getLsb k (n ||| m) = getLsb k n ||| getLsb k m := by
  unfold getLsb
  rw [Nat.shiftRight_or_distrib]
  conv_lhs =>
    rw [Nat.and_distrib_right]

lemma getLsb_of_xor {n m k: ℕ} : getLsb k (n ^^^ m) = getLsb k n ^^^ getLsb k m := by
  unfold getLsb
  rw [Nat.shiftRight_xor_distrib]
  conv_lhs =>
    rw [Nat.and_xor_distrib_right]

lemma getLsb_of_and {n m k: ℕ} : getLsb k (n &&& m) = getLsb k n &&& getLsb k m := by
  unfold getLsb
  rw [Nat.shiftRight_and_distrib]
  rw [Nat.and_comm (m >>>k) 1, ←Nat.and_assoc, Nat.and_assoc (n>>>k) 1 1]
  rw [Nat.and_self, Nat.and_assoc (n>>>k) 1 (m >>> k), Nat.and_comm 1 (m >>> k)]
  rw [←Nat.and_assoc]

lemma getLsb_of_two_pow_sub_one {i k: ℕ} : getLsb k (2^i - 1) =
    if k < i then 1 else 0 := by
  have h_test := Nat.testBit_two_pow_sub_one (n := i) (i := k)
  simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero] at h_test
  if h_k: k < i then
    simp only [h_k, decide_true, beq_iff_eq] at h_test ⊢
    simp only [getLsb, Nat.and_one_is_mod]
    simp only [h_test, ↓reduceIte]
  else
    simp only [h_k, decide_false, beq_eq_false_iff_ne, ne_eq, Nat.mod_two_not_eq_one,
      ↓reduceIte] at h_test ⊢
    simp only [getLsb, Nat.and_one_is_mod]
    simp only [h_test]

lemma getLsb_of_lsb {n: ℕ} (num_lsb_getLsbs : ℕ) : ∀ k, getLsb k (get_lsb n num_lsb_getLsbs) =
    if k < num_lsb_getLsbs then getLsb k n else 0 := by
  intro k
  simp only [get_lsb, getLsb_of_and]
  if h_k: k < num_lsb_getLsbs then
    simp only [h_k, ↓reduceIte]
    have getLsb_k_mask : getLsb k (1 <<< num_lsb_getLsbs - 1) = 1:= by
      rw [Nat.shiftLeft_eq, one_mul]
      rw [getLsb_of_two_pow_sub_one (i := num_lsb_getLsbs) (k := k)]
      simp only [ite_eq_left_iff, not_lt, zero_ne_one, imp_false, not_le]
      omega
    rw [getLsb_k_mask]
    have h_getLsb_k_n: getLsb k n < 2 := by exact getLsb_lt_2
    interval_cases h_getLsb_k_n_eq: getLsb k n
    · simp only [Nat.and_one_is_mod]
    · simp only [Nat.and_one_is_mod]
  else
    push_neg at h_k
    have getLsb_k_mask : getLsb k (1 <<< num_lsb_getLsbs - 1) = 0:= by
      rw [Nat.shiftLeft_eq, one_mul]
      rw [getLsb_of_two_pow_sub_one (i := num_lsb_getLsbs) (k := k)]
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt]
      omega
    rw [getLsb_k_mask, Nat.and_zero]
    simp only [right_eq_ite_iff]
    omega

lemma getLsb_eq_succ_getLsb_of_mul_two {n k : ℕ} : getLsb (k+1) (2*n) = getLsb k n := by
  have h_n_eq: n = (2*n) >>> 1 := by omega
  have res := (getLsb_of_shiftRight (n := 2*n) (p := 1) k).symm
  conv_rhs at res => rw [←h_n_eq]
  exact res

lemma getLsb_eq_succ_getLsb_of_mul_two_add_one {n k : ℕ} : getLsb (k+1) (2*n + 1) = getLsb k n := by
  have h_n_eq: n = (2*n + 1) >>> 1 := by omega
  have res := (getLsb_of_shiftRight (n := 2*n + 1) (p := 1) k).symm
  conv_rhs at res => rw [←h_n_eq]
  exact res

lemma getLsb_eq_pred_getLsb_of_div_two {n k : ℕ} (h_k: k > 0) :
    getLsb k (n) = getLsb (k-1) (n/2) := by
  rw [←Nat.pow_one 2]
  rw [←Nat.shiftRight_eq_div_pow]
  conv_lhs => rw [←Nat.sub_add_cancel (n:=k) (m:=1) (h:=by omega)]
  exact Eq.symm (getLsb_of_shiftRight (k - 1))

theorem getLsb_repr {ℓ : Nat} (h_ℓ : ℓ > 0) : ∀ j, j < 2^ℓ →
  j = ∑ k ∈ Finset.Icc 0 (ℓ-1), (getLsb k j) * 2^k := by
  induction ℓ with
  | zero =>
    -- Base case : ℓ = 0
    intro j h_j
    have h_j_zero : j = 0 := by exact Nat.lt_one_iff.mp h_j
    subst h_j_zero
    simp only [zero_tsub, Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]
    unfold getLsb
    rw [Nat.shiftRight_zero, Nat.and_one_is_mod]
  | succ ℓ₁ ih =>
    by_cases h_ℓ₁ : ℓ₁ = 0
    · simp only [h_ℓ₁, zero_add, pow_one, tsub_self, Finset.Icc_self, Finset.sum_singleton,
      pow_zero, mul_one];
      intro j hj
      interval_cases j
      · simp only [getLsb, Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.zero_mod]
      · simp only [getLsb, Nat.shiftRight_zero, Nat.and_one_is_mod]
    · push_neg at h_ℓ₁
      set ℓ := ℓ₁ + 1
      have h_ℓ_eq : ℓ = ℓ₁ + 1 := by rfl
      intro j h_j
      -- Inductive step : assume theorem holds for ℓ₁ = ℓ - 1
      -- => show j = ∑ k ∈ Finset.range (ℓ + 1), (getLsb k j) * 2^k
      -- Split j into lsb (b) and higher getLsbs (m) &
      -- reason inductively from the predicate of (m, ℓ₁)
      set b := getLsb 0 j -- Least significant getLsb : j % 2
      set m := j >>> 1 -- Higher getLsbs : j / 2
      have h_b_eq : b = getLsb 0 j := by rfl
      have h_m_eq : m = j >>> 1 := by rfl
      have h_getLsb_shift : ∀ k, getLsb (k+1) j = getLsb k m := by
        intro k
        rw [h_m_eq]
        exact (getLsb_of_shiftRight (n := j) (p := 1) k).symm
      have h_j_eq : j = b + 2 * m := by
        calc
          _ = 2 * m + b := by
            have h_m_eq : m = j/2 := by rfl
            have h_b_eq : b = j%2 := by
              rw [h_b_eq]; unfold getLsb; rw [Nat.shiftRight_zero]; rw [Nat.and_one_is_mod];
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
      have h_m_repr := ih (j := m) (by omega) h_m
      have getLsb_shift : ∀ k, getLsb (k + 1) j = getLsb k m := by
        intro k
        rw [h_m_eq]
        exact (getLsb_of_shiftRight (n := j) (p := 1) k).symm
      -- ⊢ j = ∑ k ∈ Finset.range ℓ, getLsb k j * 2 ^ k
      have h_sum : ∑ k ∈ Finset.Icc 0 (ℓ-1), getLsb k j * 2 ^ k
        = (∑ k ∈ Finset.Icc 0 0, getLsb k j * 2 ^ k)
        + (∑ k ∈ Finset.Icc 1 (ℓ-1), getLsb k j * 2 ^ k) := by
        apply sum_Icc_split
        omega
        omega
      rw [h_sum]
      rw [h_j_eq]
      rw [Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]

      have h_sum_2 : ∑ k ∈ Finset.Icc 1 (ℓ-1), getLsb k (b + 2 * m) * 2 ^ k
        = ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getLsb k (m) * 2 ^ (k+1) := by
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
          rw [getLsb_of_shiftRight]
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

      have h_sum_3 : ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getLsb k (m) * 2 ^ (k+1)
        = 2 * ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getLsb k (m) * 2 ^ k := by
        calc
          _ = ∑ k ∈ Finset.Icc 0 (ℓ₁-1), ((getLsb k (m) * 2^k) * 2) := by
            apply Finset.sum_congr rfl (fun k hk => by
              rw [Finset.mem_Icc] at hk -- hk : 0 ≤ k ∧ k ≤ ℓ₁ - 1
              have h_res : getLsb k (m) * 2 ^ (k+1) = getLsb k (m) * 2 ^ k * 2 := by
                rw [Nat.pow_succ, ←mul_assoc]
              exact h_res
            )
        _ = (∑ k ∈ Finset.Icc 0 (ℓ₁-1), getLsb k (m) * 2 ^ k) * 2 := by rw [Finset.sum_mul]
        _ = 2 * ∑ k ∈ Finset.Icc 0 (ℓ₁-1), getLsb k (m) * 2 ^ k := by rw [mul_comm]
      rw [h_sum_3]
      rw [←h_m_repr]
      conv =>
        rhs
        rw [←h_j_eq]

lemma get_lsb_succ {n: ℕ} (num_lsb_getLsbs: ℕ) : get_lsb n (num_lsb_getLsbs + 1) = get_lsb n num_lsb_getLsbs
    + (getLsb num_lsb_getLsbs n) <<< num_lsb_getLsbs := by
  apply eq_iff_eq_all_getLsbs.mpr
  intro k
  have h_getLsb_lt_num_lsb_getLsbs: getLsb num_lsb_getLsbs n < 2 := by exact getLsb_lt_2
  interval_cases h_getLsb: getLsb num_lsb_getLsbs n
  · rw [Nat.zero_shiftLeft]
    simp only [add_zero]
    -- ⊢ get_lsb n (num_lsb_getLsbs + 1) >>> k &&& 1 = get_lsb n num_lsb_getLsbs >>> k &&& 1
    change getLsb k (get_lsb n (num_lsb_getLsbs + 1)) = getLsb k (get_lsb n num_lsb_getLsbs)
    have getLsb_right := getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs) k
    have getLsb_left := getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs + 1) k
    rw [getLsb_right, getLsb_left]
    if h_k: k < num_lsb_getLsbs then
      simp only [h_k, ↓reduceIte]
      have h_k_lt: k < num_lsb_getLsbs + 1 := by omega
      simp only [h_k_lt, ↓reduceIte]
    else if h_k_eq: k = num_lsb_getLsbs then
      simp only [h_k_eq]
      simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false]
      omega
    else
      have k_ne_lt: ¬(k < num_lsb_getLsbs) := by omega
      have k_ne_lt_add_1: ¬(k < num_lsb_getLsbs + 1) := by omega
      simp only [k_ne_lt_add_1, ↓reduceIte, k_ne_lt]
  · change getLsb k (get_lsb n (num_lsb_getLsbs + 1))
      = getLsb k (get_lsb n num_lsb_getLsbs + 1 <<< num_lsb_getLsbs)
    have getLsb_left := getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs + 1) k
    have getLsb_right := getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs) k
    rw [getLsb_left]

    have h_and_eq_0 := and_two_pow_eq_zero_of_getLsb_0 (n:=get_lsb n num_lsb_getLsbs)
      (i:=num_lsb_getLsbs) (by
      simp only [getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs) num_lsb_getLsbs,
        lt_self_iff_false, ↓reduceIte]
    )
    rw [←one_mul (a:=2 ^ num_lsb_getLsbs)] at h_and_eq_0
    rw [←Nat.shiftLeft_eq (a:=1) (b:=num_lsb_getLsbs)] at h_and_eq_0
    have h_sum_eq_xor := sum_of_and_eq_zero_is_xor (n:=get_lsb n num_lsb_getLsbs)
      (m:=1 <<< num_lsb_getLsbs) (h_n_AND_m:=h_and_eq_0)
    have h_sum_eq_or := xor_of_and_eq_zero_is_or (n:=get_lsb n num_lsb_getLsbs)
      (m:=1 <<< num_lsb_getLsbs) (h_n_AND_m:=h_and_eq_0)
    rw [h_sum_eq_or] at h_sum_eq_xor
    rw [h_sum_eq_xor]
    rw [getLsb_of_or]
    rw [getLsb_of_lsb]
    conv_rhs =>
      enter [2, 2]; rw [Nat.shiftLeft_eq, one_mul]
    rw [getLsb_two_pow]

    if h_k: k < num_lsb_getLsbs then
      have h_k_lt: k < num_lsb_getLsbs + 1 := by omega
      simp only [h_k_lt, ↓reduceIte, h_k, beq_iff_eq]
      have h_k_ne_eq: num_lsb_getLsbs ≠ k := by omega
      simp only [h_k_ne_eq, ↓reduceIte, Nat.or_zero]
    else if h_k_eq: k = num_lsb_getLsbs then
      simp only [h_k_eq, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false, BEq.rfl,
        Nat.zero_or]
      omega
    else
      have k_ne_lt: ¬(k < num_lsb_getLsbs) := by omega
      have k_ne_lt_add_1: ¬(k < num_lsb_getLsbs + 1) := by omega
      simp only [k_ne_lt_add_1, ↓reduceIte, k_ne_lt, beq_iff_eq, Nat.zero_or, right_eq_ite_iff,
        zero_ne_one, imp_false, ne_eq]
      omega

/-- This takes a argument for the number of lsbs to remove from the number -/
def get_msb_no_shl (n : ℕ) (num_lsb_getLsbs : ℕ) : ℕ := n >>> num_lsb_getLsbs
def get_msb (n : ℕ) (num_lsb_getLsbs : ℕ) : ℕ := (get_msb_no_shl n num_lsb_getLsbs) <<< num_lsb_getLsbs

theorem msb_and_lsb_eq_zero {n : ℕ} (num_lsb_getLsbs : ℕ) :
    get_msb n num_lsb_getLsbs &&& get_lsb n num_lsb_getLsbs = 0 := by
  change (n >>> num_lsb_getLsbs <<< num_lsb_getLsbs) &&& (get_lsb n num_lsb_getLsbs) = 0
  set msb_no_shl := n >>> num_lsb_getLsbs
  have h_getLsb_msb_shl := getLsb_of_shiftLeft (n := msb_no_shl) (p := num_lsb_getLsbs)
  have h_getLsb_lsb := getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs)
  apply and_eq_zero_iff_and_each_getLsb_eq_zero.mpr
  intro j
  change getLsb j ((n >>> num_lsb_getLsbs) <<< num_lsb_getLsbs) &&& getLsb j (get_lsb n num_lsb_getLsbs) = 0
  if h_j: j < num_lsb_getLsbs then
    have h_getLsb_lhs := h_getLsb_msb_shl (k:=j - num_lsb_getLsbs)
    have h_ne: ¬(num_lsb_getLsbs ≤ j) := by omega
    have h_getLsb_left_eq_0 :  getLsb j ((n >>> num_lsb_getLsbs) <<< num_lsb_getLsbs) = 0:= by
      rw [h_getLsb_msb_shl]
      simp only [ite_eq_left_iff, not_lt, h_ne, IsEmpty.forall_iff, msb_no_shl]
    rw [h_getLsb_left_eq_0, Nat.zero_and]
  else
    have h_getLsb_rhs := h_getLsb_lsb (k:=j)
    have h_getLsb_right_eq_0: getLsb j (get_lsb n num_lsb_getLsbs) = 0 := by
      simp only [h_getLsb_rhs, ite_eq_right_iff]
      omega
    rw [h_getLsb_right_eq_0, Nat.and_zero]

lemma num_eq_msb_add_lsb {n: ℕ} (num_lsb_getLsbs: ℕ) :
  n = get_msb n num_lsb_getLsbs + get_lsb n num_lsb_getLsbs := by
  apply eq_iff_eq_all_getLsbs.mpr
  intro k
  --- use 2 getLsb extractions to get the condition for getLsbs of ((n >>> num_lsb_getLsbs) <<< num_lsb_getLsbs)
  set msb_no_shl := n >>> num_lsb_getLsbs
  have h_getLsb_msb_shl := getLsb_of_shiftLeft (n := msb_no_shl) (p := num_lsb_getLsbs)
  have h_getLsb_lsb := getLsb_of_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs)
  -- AND of msbs & lsbs is 0 => we use this to convert the sum into OR
  have h_and := msb_and_lsb_eq_zero (n := n) (num_lsb_getLsbs := num_lsb_getLsbs)
  rw [sum_of_and_eq_zero_is_or h_and]
  --- now reason on getLsbwise operation only
  rw [Nat.shiftRight_or_distrib, Nat.and_distrib_right]
  change getLsb k n = getLsb k ((n >>> num_lsb_getLsbs) <<< num_lsb_getLsbs) ||| getLsb k (get_lsb n num_lsb_getLsbs)
  rw [h_getLsb_msb_shl, h_getLsb_lsb]
  if h_k: k < num_lsb_getLsbs then
    simp only [h_k, ↓reduceIte, Nat.zero_or] at *
  else
    have h_ne: ¬(k < num_lsb_getLsbs) := by omega
    have h_num_le_k: num_lsb_getLsbs ≤ k := by omega
    simp only [h_ne, not_false_eq_true, ↓reduceIte, Nat.or_zero] at *
    rw [getLsb_of_shiftRight]
    congr
    rw [Nat.sub_add_cancel (n:=k) (m:=num_lsb_getLsbs) (by omega)]

lemma num_eq_msb_xor_lsb {n: ℕ} (num_lsb_getLsbs: ℕ) :
  n = get_msb n num_lsb_getLsbs ^^^ get_lsb n num_lsb_getLsbs := by
  rw [←sum_of_and_eq_zero_is_xor]
  · exact num_eq_msb_add_lsb (n := n) (num_lsb_getLsbs := num_lsb_getLsbs)
  · exact msb_and_lsb_eq_zero (n := n) (num_lsb_getLsbs := num_lsb_getLsbs)

lemma getLsb_of_msb {n: ℕ} (num_lsb_getLsbs : ℕ) : ∀ k, getLsb k (get_msb n num_lsb_getLsbs) =
    if k < num_lsb_getLsbs then 0 else getLsb (k) (n) := by
  intro k
  simp only [get_msb, get_msb_no_shl]
  rw [getLsb_of_shiftLeft]
  if h_k: k < num_lsb_getLsbs then
    simp only [h_k, ↓reduceIte]
  else
    simp only [h_k, ↓reduceIte]
    rw [getLsb_of_shiftRight]
    rw [Nat.sub_add_cancel (by omega)]

lemma getLsb_of_msb_no_shl {n: ℕ} (num_lsb_getLsbs : ℕ) : ∀ k, getLsb k (get_msb_no_shl n num_lsb_getLsbs)
  = getLsb (k + num_lsb_getLsbs) (n) := by
  intro k
  simp only [get_msb_no_shl]
  exact getLsb_of_shiftRight k

end Nat
