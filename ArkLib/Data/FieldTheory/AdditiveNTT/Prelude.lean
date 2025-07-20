/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Notation
import ArkLib.Data.FieldTheory.BinaryField.Tower.Prelude
import Mathlib.Data.Nat.Bitwise

/-!
# Prelude for Additive NTT
- Bitwise identities
- Monomial basis for submodule of polynomials of degree less than `n`
- Frobenius polynomial identity on prime-characteristic fields and its algebras
- Field-vanishing polynomial equality in polynomial ring of algebras
-/

#check Nat.testBit
namespace AdditiveNTT
open Polynomial FiniteDimensional
section BitwiseIdentities
-- We decompose each number `j < 2^ℓ` into its binary representation : `j = Σ k ∈ Fin ℓ, jₖ * 2ᵏ`
def bit (k n : Nat) : Nat := (n >>> k) &&& 1 -- k'th LSB bit of `n`

lemma bit_lt_2 {k n : Nat} : bit k n < 2 := by
  unfold bit
  rw [Nat.and_one_is_mod]
  simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt]

lemma bit_eq_zero_or_one {k n : Nat} :
  bit k n = 0 ∨ bit k n = 1 := by
  unfold bit
  rw [Nat.and_one_is_mod]
  simp only [Nat.mod_two_eq_zero_or_one]

lemma lsb_of_single_bit {n : ℕ} (h_n : n < 2) : bit 0 n = n := by
  unfold bit
  rw [Nat.shiftRight_zero]
  rw [Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt h_n

lemma lsb_of_multiple_of_two {n : ℕ} : bit 0 (2*n) = 0 := by
  unfold bit
  rw [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_mod_right]

def get_lsb (n : ℕ) (num_lsb_bits : ℕ) := n &&& ((1 <<< num_lsb_bits) - 1)

lemma get_zero_lsb_eq_zero {n : ℕ} : get_lsb n 0 = 0 := by
  unfold get_lsb
  simp only [Nat.shiftLeft_zero, Nat.sub_self, Nat.and_zero]

lemma get_lsb_eq_mod_two_pow {n : ℕ} (num_lsb_bits : ℕ) :
  get_lsb n num_lsb_bits = n % (2 ^ num_lsb_bits) := by
  unfold get_lsb
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod n num_lsb_bits

lemma get_lsb_lt_two_pow {n : ℕ} (num_lsb_bits : ℕ) :
    get_lsb n num_lsb_bits < 2 ^ num_lsb_bits := by
  rw [get_lsb_eq_mod_two_pow]
  omega

lemma get_lsb_le_self {n : ℕ} (num_lsb_bits : ℕ) : get_lsb n num_lsb_bits ≤ n := by
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

lemma eq_iff_eq_all_bits {n m : ℕ} : n = m ↔ ∀ k, (n >>> k) &&& 1 = (m >>> k) &&& 1 := by
  constructor
  · intro h_eq -- h_eq : n = m
    intro k
    rw [h_eq]
  · intro h_all_bits -- h_all_bits : ∀ k, (n >>> k) &&& 1 = (m >>> k) &&& 1
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_eq_beq]
    simp only [Nat.and_one_is_mod] at h_all_bits k
    rw [h_all_bits k]

lemma shiftRight_and_one_distrib {n m k : ℕ} :
    (n &&& m) >>> k &&& 1 = ((n >>> k) &&& 1) &&& ((m >>> k) &&& 1) := by
  rw [Nat.shiftRight_and_distrib]
  conv =>
    lhs
    rw [←Nat.and_self (x := 1)]
    rw [←Nat.and_assoc]
    rw [Nat.and_assoc (y := m >>> k) (z := 1), Nat.and_comm (x := m>>>k) (y := 1), ←Nat.and_assoc]
    rw [Nat.and_assoc]

lemma and_eq_zero_iff_and_each_bit_eq_zero {n m : ℕ} :
    n &&& m = 0 ↔ ∀ k, ((n >>> k) &&& 1) &&& ((m >>> k) &&& 1) = 0 := by
  constructor
  · intro h_and_zero
    intro k
    have h_k := shiftRight_and_one_distrib (n := n) (m := m) (k := k)
    rw [←h_k]
    rw [h_and_zero, Nat.zero_shiftRight, Nat.zero_and]
  · intro h_forall_k -- h_forall_k : ∀ (k : ℕ), n >>> k &&& 1 &&& (m >>> k &&& 1) = 0
    apply eq_iff_eq_all_bits.mpr
    intro k
    -- ⊢ (n &&& m) >>> k &&& 1 = 0 >>> k &&& 1
    have h_forall_k_eq : ∀ k, ((n &&& m) >>> k) &&& 1 = 0 := by
      intro k
      rw [shiftRight_and_one_distrib]
      exact h_forall_k k
    rw [h_forall_k_eq k]
    rw [Nat.zero_shiftRight, Nat.zero_and]

lemma bit_two_pow {i k: ℕ} : (bit k (2^i) = if i == k then 1 else 0) := by
  have h_two_pow_i: 2^i = 1 <<< i := by
    simp only [Nat.shiftLeft_eq, one_mul]
  rw [bit, h_two_pow_i]
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

lemma and_two_pow_eq_zero_of_bit_0 {n i : ℕ} (h_bit: bit i n = 0) : n &&& (2 ^ i) = 0 := by
  apply and_eq_zero_iff_and_each_bit_eq_zero.mpr
  intro k
  have h_bit_two_pow := bit_two_pow (i := i) (k := k)
  if h_k: k = i then
    simp only [h_k, BEq.rfl, ↓reduceIte] at h_bit_two_pow
    rw [bit, h_k.symm] at h_bit
    rw [h_bit, Nat.zero_and]
  else
    push_neg at h_k
    simp only [beq_iff_eq, h_k.symm, ↓reduceIte] at h_bit_two_pow
    rw [bit] at h_bit_two_pow
    rw [h_bit_two_pow]
    rw [Nat.and_zero]

lemma and_two_pow_eq_two_pow_of_bit_1 {n i : ℕ} (h_bit: bit i n = 1) : n &&& (2 ^ i) = 2 ^ i := by
  have h_testBit_i_eq_1 : n.testBit i = true := by
    simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_iff_eq]
    simp only [bit, Nat.and_one_is_mod] at h_bit
    exact h_bit
  conv_lhs => rw [Nat.and_two_pow (n:=n) (i:=i)]
  simp only [h_testBit_i_eq_1, Bool.toNat_true, one_mul]

lemma and_two_pow_eq_two_pow_of_bit_eq_one {n i : ℕ} (h_bit: bit i n = 1)
    : n &&& (2 ^ i) = 2 ^ i := by
  apply eq_iff_eq_all_bits.mpr
  intro k
  have h_bit_two_pow := bit_two_pow (i := i) (k := k)
  if h_k: k = i then
    simp only [h_k, BEq.rfl, ↓reduceIte] at h_bit_two_pow
    rw [bit, h_k.symm] at h_bit
    -- ⊢ bit k (n &&& 2 ^ i) = 2 ^ i >>> k &&& 1
    rw [bit, h_k.symm] at h_bit_two_pow
    rw [h_k.symm, h_bit_two_pow]
    rw [Nat.shiftRight_and_distrib, Nat.and_assoc, Nat.and_comm (2^k >>> k) 1, ←Nat.and_assoc]
    rw [h_bit, ←one_mul (2^k), ←Nat.shiftLeft_eq, Nat.shiftLeft_shiftRight, Nat.and_self]
  else
    push_neg at h_k
    simp only [beq_iff_eq, h_k.symm, ↓reduceIte] at h_bit_two_pow
    rw [bit] at h_bit_two_pow
    rw [h_bit_two_pow, Nat.shiftRight_and_distrib, Nat.and_assoc, h_bit_two_pow]
    rw [Nat.and_zero]

lemma and_one_eq_of_eq {a b : ℕ} : a = b → a &&& 1 = b &&& 1 := by
  intro h_eq
  rw [h_eq]

lemma Nat.eq_zero_or_eq_one_of_lt_two {n : ℕ} (h_lt : n < 2) : n = 0 ∨ n = 1 := by
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
    set bitN := bn.toNat
    set bitM := bm.toNat
    have h_bitN : bitN < 2 := by
      exact Bool.toNat_lt bn
    have h_bitM : bitM < 2 := by
      exact Bool.toNat_lt bm
    have h_and_bitN_bitM : (bitN &&& bitM) < 2 := by
      interval_cases bitN
      · interval_cases bitM
        · rw [Nat.zero_and]; norm_num;
        · rw [Nat.zero_and]; norm_num;
      · interval_cases bitM
        · rw [Nat.and_zero]; norm_num;
        · rw [Nat.and_self]; norm_num;
    have h_n : nVal = n2 * 2 + bitN := by
      unfold nVal
      rw [Nat.bit_val, mul_comm]
    have h_m : mVal = m2 * 2 + bitM := by
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
    have h_and : nVal &&& mVal = (n2 &&& m2) * 2 + (bitN &&& bitM) :=
      and_of_chopped_lsb (h_bn := h_bitN) (h_bm := h_bitM) (h_n := h_n) (h_m := h_m)
    have h_xor : nVal ^^^ mVal = (n2 ^^^ m2) * 2 + (bitN ^^^ bitM) :=
      xor_of_chopped_lsb (h_bn := h_bitN) (h_bm := h_bitM) (h_n := h_n) (h_m := h_m)
    have h_or : nVal ||| mVal = (n2 ||| m2) * 2 + (bitN ||| bitM) :=
      or_of_chopped_lsb (h_bn := h_bitN) (h_bm := h_bitM) (h_n := h_n) (h_m := h_m)
    have h_prev := ih m2
    -- ⊢ nVal + mVal = (nVal ^^^ mVal) + (2 * (nVal &&& mVal))
    have sum_eq : nVal + mVal = (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (bitN + bitM) := by
      calc
        _ = (n2 * 2 + bitN) + (m2 * 2 + bitM) := by rw [h_n, h_m]
        _ = (n2 + m2) * 2 + (bitN + bitM) := by
          rw [Nat.right_distrib, ←add_assoc, ←add_assoc]; omega;
        _ = ((n2 ^^^ m2) + 2 * (n2 &&& m2)) * 2 + (bitN + bitM) := by rw [h_prev]
        _ = (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (bitN + bitM) := by rw [Nat.right_distrib]; omega;
    rw [sum_eq]
    -- From this point, we basically do case analysis on `bn &&& bm`
    -- rw [h_n, h_m]
    by_cases h_and_bitN_bitM_eq_1 : bitN &&& bitM = 1
    · have h_bitN_and_bitM_eq_1 : bitN = 1 ∧ bitM = 1 := by
        interval_cases bitN
        · interval_cases bitM
          · contradiction
          · contradiction
        · interval_cases bitM
          · contradiction
          · and_intros; rfl; rfl;
      have h_sum_bits : (bitN + bitM) = 2 := by omega
      have h_xor_bits : bitN ^^^ bitM = 0 := by simp only [h_bitN_and_bitM_eq_1, Nat.xor_self];
      have h_and_bits : bitN &&& bitM = 1 := by simp only [h_bitN_and_bitM_eq_1, Nat.and_self];
      -- ⊢ (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (bitN + bitM) = (nVal ^^^ mVal) + 2 * (nVal &&& mVal)
      have h_left : (n2 ^^^ m2) * 2 = (nVal ^^^ mVal) := by
        calc
          _ = (n2 ^^^ m2) * 2 + 0 := by omega;
          _ = (n2 ^^^ m2) * 2 + (bitN ^^^ bitM) := by rw [h_xor_bits];
          _ = _ := by exact h_xor.symm
      rw [h_left]
      rw [add_assoc]
      have h_right : 4 * (n2 &&& m2) + (bitN + bitM) = 2 * (nVal &&& mVal) := by
        calc
          _ = 4 * (n2 &&& m2) + 2 := by rw [h_sum_bits];
          _ = 2 * (2 * (n2 &&& m2) + 1) := by omega;
          _ = 2 * ((n2 &&& m2) * 2 + (bitN &&& bitM)) := by
            rw [h_and_bits, mul_comm (a := (n2 &&& m2)) (b := 2)];
          _ = 2 * (nVal &&& mVal) := by rw [h_and];
      rw [h_right]
    · push_neg at h_and_bitN_bitM_eq_1;
      have h_and_bitN_bitM_eq_0 : (bitN &&& bitM) = 0 := by
        interval_cases (bitN &&& bitM)
        · rfl
        · contradiction
      have h_bits_eq : bitN = 0 ∨ bitM = 0 := by
        interval_cases bitN
        · left; rfl
        · right;
          interval_cases bitM
          · rfl
          · contradiction
      have h_sum_bits : (bitN + bitM) = (bitN ^^^ bitM) := by
        interval_cases bitN
        · interval_cases bitM
          · rfl
          · rfl
        · interval_cases bitM
          · rfl
          · contradiction -- with h_and_bitN_bitM_eq_0
      -- ⊢ (n2 ^^^ m2) * 2 + 4 * (n2 &&& m2) + (bitN + bitM) = (nVal ^^^ mVal) + 2 * (nVal &&& mVal)
      rw [←add_assoc, add_assoc (b := bitN) (c := bitM), add_assoc]
      rw [add_comm (b := (bitN + bitM)), ←add_assoc]
      have h_left : (n2 ^^^ m2) * 2 + (bitN + bitM) = (nVal ^^^ mVal) := by
        calc
          _ = (n2 ^^^ m2) * 2 + (bitN ^^^ bitM) := by rw [h_sum_bits];
          _ = _ := by exact h_xor.symm
      rw [h_left]

      -- 4 * (n2 &&& m2) = 2 * (2 * (n2 &&& m2) + (bn &&& bm)) = 2 * (n &&& m)
      have h_right : 4 * (n2 &&& m2) = 2 * (nVal &&& mVal) := by
        calc
          _ = 4 * (n2 &&& m2) + 0 := by omega;
          _ = 4 * (n2 &&& m2) + (bitN &&& bitM) := by rw [h_and_bitN_bitM_eq_0];
          _ = 2 * (2 * (n2 &&& m2) + (bitN &&& bitM)) := by omega;
          _ = 2 * ((n2 &&& m2) * 2 + (bitN &&& bitM)) := by
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
  apply eq_iff_eq_all_bits.mpr
  intro k
  rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_or_distrib]
  rw [Nat.and_xor_distrib_right] -- lhs
  rw [Nat.and_distrib_right] -- rhs
  -- ⊢ (n >>> k &&& 1) ^^^ (m >>> k &&& 1) = (n >>> k &&& 1) ||| (m >>> k &&& 1)
  set bitN := n >>> k &&& 1
  set bitM := m >>> k &&& 1
  have h_bitN : bitN < 2 := by
    simp only [bitN, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := n >>> k) (y := 2)]
  have h_bitM : bitM < 2 := by
    simp only [bitM, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := m >>> k) (y := 2)]
  -- ⊢ bitN ^^^ bitM = bitN ||| bitM
  have h_and_bitN_bitM : (bitN &&& bitM) = 0 := by
    exact and_eq_zero_iff_and_each_bit_eq_zero.mp h_n_AND_m k
  interval_cases bitN -- case analysis on `bitN, bitM`
  · interval_cases bitM
    · rfl
    · rfl
  · interval_cases bitM
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

lemma bit_of_add_distrib {n m k : ℕ}
  (h_n_AND_m : n &&& m = 0) : bit k (n + m) = bit k n + bit k m := by
  unfold bit
  rw [sum_of_and_eq_zero_is_xor h_n_AND_m]
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
  set bitN := n >>> k &&& 1
  set bitM := m >>> k &&& 1
  have h_bitN : bitN < 2 := by
    simp only [bitN, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := n >>> k) (y := 2)]
  have h_bitM : bitM < 2 := by
    simp only [bitM, Nat.and_one_is_mod]
    simp only [gt_iff_lt, Nat.ofNat_pos, Nat.mod_lt (x := m >>> k) (y := 2)]
  have h_bitN_and_bitM : (bitN &&& bitM) = 0 := by
    exact and_eq_zero_iff_and_each_bit_eq_zero.mp h_n_AND_m k
  exact (sum_of_and_eq_zero_is_xor (n := bitN) (m := bitM) h_bitN_and_bitM).symm

lemma add_two_pow_of_bit_eq_zero_lt_two_pow {n m i : ℕ} (h_n: n < 2^m) (h_i: i < m)
  (h_bit_at_i_eq_zero: bit i n = 0) :
  n + 2^i < 2^m := by
  have h_j_and: n &&& (2^i) = 0 := by
    rw [and_two_pow_eq_zero_of_bit_0 (n:=n) (i:=i)]
    rw [←h_bit_at_i_eq_zero]
  rw [sum_eq_xor_plus_twice_and, h_j_and, mul_zero, add_zero]
  have h_and_lt := Nat.xor_lt_two_pow (x:=n) (y:=2^i) (n:=m) (by omega) (by
    apply Nat.pow_lt_pow_right (a:=2) (m:=i) (n:=m) (ha:=by omega) (h:=by omega)
  )
  exact h_and_lt

lemma bit_of_multiple_of_power_of_two {n p : ℕ}: ∀ k,
  bit (k) (2^p * n) = if k < p then 0 else bit (k-p) n := by
  intro k
  have h_test := Nat.testBit_two_pow_mul (i := p) (a := n) (j:=k)
  simp only [Nat.testBit, Nat.and_comm 1] at h_test
  if h_k: p > k then
    have h_ne_p_le_k: ¬(p ≤ k) := by omega
    simp only [Nat.and_one_is_mod, Nat.mod_two_bne_zero, ge_iff_le, h_ne_p_le_k, decide_false,
      Bool.false_and, beq_eq_false_iff_ne, ne_eq, Nat.mod_two_not_eq_one, h_k,
      ↓reduceIte] at h_test ⊢
    simp only [bit, Nat.and_one_is_mod]
    omega
  else
    have h_p_le_k: p ≤ k := by omega
    have h_ne_k_lt_p: ¬(k < p) := by omega
    simp only [Nat.and_one_is_mod, Nat.mod_two_bne_zero, ge_iff_le, h_p_le_k, decide_true,
      Bool.true_and, beq_eq_beq, h_ne_k_lt_p, ↓reduceIte] at h_test ⊢
    simp only [bit]
    -- ⊢ (2 ^ p * n) >>> k % 2 = n >>> (k - p) % 2
    change bit k (2^p * n) = bit (k - p) n
    have h_bit_left_lt: bit (k - p) n < 2 := bit_lt_2
    have h_bit_right_lt: bit k n < 2 := bit_lt_2
    interval_cases h_bit_left_lt_eq: bit (k - p) n
    · simp only [bit, Nat.and_one_is_mod] at h_bit_left_lt_eq
      simp [h_bit_left_lt_eq] at h_test
      simp only [bit, Nat.and_one_is_mod, h_test]
    · simp only [bit, Nat.and_one_is_mod] at h_bit_left_lt_eq
      simp only [h_bit_left_lt_eq, iff_true] at h_test
      simp only [bit, Nat.and_one_is_mod, h_test]

lemma bit_of_shiftLeft {n p : ℕ}:
  ∀ k, bit (k) (n <<< p) = if k < p then 0 else bit (k - p) n := by
  intro k
  rw [bit_of_multiple_of_power_of_two (n:=n) (p:=p) (k:=k).symm]
  congr
  rw [Nat.shiftLeft_eq, mul_comm]

lemma bit_of_shiftRight {n p : ℕ}:
  ∀ k, bit k (n >>> p) = bit (k+p) n := by
  intro k
  unfold bit
  rw [←Nat.shiftRight_add]
  rw [←add_comm]

lemma bit_of_or {n m k: ℕ} : bit k (n ||| m) = bit k n ||| bit k m := by
  unfold bit
  rw [Nat.shiftRight_or_distrib]
  conv_lhs =>
    rw [Nat.and_distrib_right]

lemma bit_of_xor {n m k: ℕ} : bit k (n ^^^ m) = bit k n ^^^ bit k m := by
  unfold bit
  rw [Nat.shiftRight_xor_distrib]
  conv_lhs =>
    rw [Nat.and_xor_distrib_right]

lemma bit_of_and {n m k: ℕ} : bit k (n &&& m) = bit k n &&& bit k m := by
  unfold bit
  rw [Nat.shiftRight_and_distrib]
  rw [Nat.and_comm (m >>>k) 1, ←Nat.and_assoc, Nat.and_assoc (n>>>k) 1 1]
  rw [Nat.and_self, Nat.and_assoc (n>>>k) 1 (m >>> k), Nat.and_comm 1 (m >>> k)]
  rw [←Nat.and_assoc]

lemma bit_of_two_pow_sub_one {i k: ℕ} : bit k (2^i - 1) =
    if k < i then 1 else 0 := by
  have h_test := Nat.testBit_two_pow_sub_one (n := i) (i := k)
  simp only [Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero] at h_test
  if h_k: k < i then
    simp only [h_k, decide_true, beq_iff_eq] at h_test ⊢
    simp only [bit, Nat.and_one_is_mod]
    simp only [h_test, ↓reduceIte]
  else
    simp only [h_k, decide_false, beq_eq_false_iff_ne, ne_eq, Nat.mod_two_not_eq_one,
      ↓reduceIte] at h_test ⊢
    simp only [bit, Nat.and_one_is_mod]
    simp only [h_test]

lemma bit_of_lsb {n: ℕ} (num_lsb_bits : ℕ) : ∀ k, bit k (get_lsb n num_lsb_bits) =
    if k < num_lsb_bits then bit k n else 0 := by
  intro k
  simp only [get_lsb, bit_of_and]
  if h_k: k < num_lsb_bits then
    simp only [h_k, ↓reduceIte]
    have bit_k_mask : bit k (1 <<< num_lsb_bits - 1) = 1:= by
      rw [Nat.shiftLeft_eq, one_mul]
      rw [bit_of_two_pow_sub_one (i := num_lsb_bits) (k := k)]
      simp only [ite_eq_left_iff, not_lt, zero_ne_one, imp_false, not_le]
      omega
    rw [bit_k_mask]
    have h_bit_k_n: bit k n < 2 := by exact bit_lt_2
    interval_cases h_bit_k_n_eq: bit k n
    · simp only [Nat.and_one_is_mod]
    · simp only [Nat.and_one_is_mod]
  else
    push_neg at h_k
    have bit_k_mask : bit k (1 <<< num_lsb_bits - 1) = 0:= by
      rw [Nat.shiftLeft_eq, one_mul]
      rw [bit_of_two_pow_sub_one (i := num_lsb_bits) (k := k)]
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt]
      omega
    rw [bit_k_mask, Nat.and_zero]
    simp only [right_eq_ite_iff]
    omega

lemma bit_eq_succ_bit_of_mul_two {n k : ℕ} : bit (k+1) (2*n) = bit k n := by
  have h_n_eq: n = (2*n) >>> 1 := by omega
  have res := (bit_of_shiftRight (n := 2*n) (p := 1) k).symm
  conv_rhs at res => rw [←h_n_eq]
  exact res

lemma bit_eq_succ_bit_of_mul_two_add_one {n k : ℕ} : bit (k+1) (2*n + 1) = bit k n := by
  have h_n_eq: n = (2*n + 1) >>> 1 := by omega
  have res := (bit_of_shiftRight (n := 2*n + 1) (p := 1) k).symm
  conv_rhs at res => rw [←h_n_eq]
  exact res

theorem bit_repr {ℓ : Nat} (h_ℓ : ℓ > 0) : ∀ j, j < 2^ℓ →
  j = ∑ k ∈ Finset.Icc 0 (ℓ-1), (bit k j) * 2^k := by
  induction ℓ with
  | zero =>
    -- Base case : ℓ = 0
    intro j h_j
    have h_j_zero : j = 0 := by exact Nat.lt_one_iff.mp h_j
    subst h_j_zero
    simp only [zero_tsub, Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]
    unfold bit
    rw [Nat.shiftRight_zero, Nat.and_one_is_mod]
  | succ ℓ₁ ih =>
    by_cases h_ℓ₁ : ℓ₁ = 0
    · simp only [h_ℓ₁, zero_add, pow_one, tsub_self, Finset.Icc_self, Finset.sum_singleton,
      pow_zero, mul_one];
      intro j hj
      interval_cases j
      · simp only [bit, Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.zero_mod]
      · simp only [bit, Nat.shiftRight_zero, Nat.and_one_is_mod]
    · push_neg at h_ℓ₁
      set ℓ := ℓ₁ + 1
      have h_ℓ_eq : ℓ = ℓ₁ + 1 := by rfl
      intro j h_j
      -- Inductive step : assume theorem holds for ℓ₁ = ℓ - 1
      -- => show j = ∑ k ∈ Finset.range (ℓ + 1), (bit k j) * 2^k
      -- Split j into lsb (b) and higher bits (m) & reason inductively from the predicate of (m, ℓ₁)
      set b := bit 0 j -- Least significant bit : j % 2
      set m := j >>> 1 -- Higher bits : j / 2
      have h_b_eq : b = bit 0 j := by rfl
      have h_m_eq : m = j >>> 1 := by rfl
      have h_bit_shift : ∀ k, bit (k+1) j = bit k m := by
        intro k
        rw [h_m_eq]
        exact (bit_of_shiftRight (n := j) (p := 1) k).symm
      have h_j_eq : j = b + 2 * m := by
        calc
          _ = 2 * m + b := by
            have h_m_eq : m = j/2 := by rfl
            have h_b_eq : b = j%2 := by
              rw [h_b_eq]; unfold bit; rw [Nat.shiftRight_zero]; rw [Nat.and_one_is_mod];
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
      have bit_shift : ∀ k, bit (k + 1) j = bit k m := by
        intro k
        rw [h_m_eq]
        exact (bit_of_shiftRight (n := j) (p := 1) k).symm
      -- ⊢ j = ∑ k ∈ Finset.range ℓ, bit k j * 2 ^ k
      have h_sum : ∑ k ∈ Finset.Icc 0 (ℓ-1), bit k j * 2 ^ k
        = (∑ k ∈ Finset.Icc 0 0, bit k j * 2 ^ k)
        + (∑ k ∈ Finset.Icc 1 (ℓ-1), bit k j * 2 ^ k) := by
        apply sum_Icc_split
        omega
        omega
      rw [h_sum]
      rw [h_j_eq]
      rw [Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]

      have h_sum_2 : ∑ k ∈ Finset.Icc 1 (ℓ-1), bit k (b + 2 * m) * 2 ^ k
        = ∑ k ∈ Finset.Icc 0 (ℓ₁-1), bit k (m) * 2 ^ (k+1) := by
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
          rw [bit_of_shiftRight]
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

      have h_sum_3 : ∑ k ∈ Finset.Icc 0 (ℓ₁-1), bit k (m) * 2 ^ (k+1)
        = 2 * ∑ k ∈ Finset.Icc 0 (ℓ₁-1), bit k (m) * 2 ^ k := by
        calc
          _ = ∑ k ∈ Finset.Icc 0 (ℓ₁-1), ((bit k (m) * 2^k) * 2) := by
            apply Finset.sum_congr rfl (fun k hk => by
              rw [Finset.mem_Icc] at hk -- hk : 0 ≤ k ∧ k ≤ ℓ₁ - 1
              have h_res : bit k (m) * 2 ^ (k+1) = bit k (m) * 2 ^ k * 2 := by
                rw [Nat.pow_succ, ←mul_assoc]
              exact h_res
            )
        _ = (∑ k ∈ Finset.Icc 0 (ℓ₁-1), bit k (m) * 2 ^ k) * 2 := by rw [Finset.sum_mul]
        _ = 2 * ∑ k ∈ Finset.Icc 0 (ℓ₁-1), bit k (m) * 2 ^ k := by rw [mul_comm]
      rw [h_sum_3]
      rw [←h_m_repr]
      conv =>
        rhs
        rw [←h_j_eq]

lemma get_lsb_succ {n: ℕ} (num_lsb_bits: ℕ) : get_lsb n (num_lsb_bits + 1) = get_lsb n num_lsb_bits
    + (bit num_lsb_bits n) <<< num_lsb_bits := by
  apply eq_iff_eq_all_bits.mpr
  intro k
  have h_bit_lt_num_lsb_bits: bit num_lsb_bits n < 2 := by exact bit_lt_2
  interval_cases h_bit: bit num_lsb_bits n
  · rw [Nat.zero_shiftLeft]
    simp only [add_zero]
    -- ⊢ get_lsb n (num_lsb_bits + 1) >>> k &&& 1 = get_lsb n num_lsb_bits >>> k &&& 1
    change bit k (get_lsb n (num_lsb_bits + 1)) = bit k (get_lsb n num_lsb_bits)
    have bit_right := bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits) k
    have bit_left := bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits + 1) k
    rw [bit_right, bit_left]
    if h_k: k < num_lsb_bits then
      simp only [h_k, ↓reduceIte]
      have h_k_lt: k < num_lsb_bits + 1 := by omega
      simp only [h_k_lt, ↓reduceIte]
    else if h_k_eq: k = num_lsb_bits then
      simp only [h_k_eq]
      simp only [lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false]
      omega
    else
      have k_ne_lt: ¬(k < num_lsb_bits) := by omega
      have k_ne_lt_add_1: ¬(k < num_lsb_bits + 1) := by omega
      simp only [k_ne_lt_add_1, ↓reduceIte, k_ne_lt]
  · change bit k (get_lsb n (num_lsb_bits + 1))
      = bit k (get_lsb n num_lsb_bits + 1 <<< num_lsb_bits)
    have bit_left := bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits + 1) k
    have bit_right := bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits) k
    rw [bit_left]

    have h_and_eq_0 := and_two_pow_eq_zero_of_bit_0 (n:=get_lsb n num_lsb_bits)
      (i:=num_lsb_bits) (by
      simp only [bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits) num_lsb_bits,
        lt_self_iff_false, ↓reduceIte]
    )
    rw [←one_mul (a:=2 ^ num_lsb_bits)] at h_and_eq_0
    rw [←Nat.shiftLeft_eq (a:=1) (b:=num_lsb_bits)] at h_and_eq_0
    have h_sum_eq_xor := sum_of_and_eq_zero_is_xor (n:=get_lsb n num_lsb_bits)
      (m:=1 <<< num_lsb_bits) (h_n_AND_m:=h_and_eq_0)
    have h_sum_eq_or := xor_of_and_eq_zero_is_or (n:=get_lsb n num_lsb_bits)
      (m:=1 <<< num_lsb_bits) (h_n_AND_m:=h_and_eq_0)
    rw [h_sum_eq_or] at h_sum_eq_xor
    rw [h_sum_eq_xor]
    rw [bit_of_or]
    rw [bit_of_lsb]
    conv_rhs =>
      enter [2, 2]; rw [Nat.shiftLeft_eq, one_mul]
    rw [bit_two_pow]

    if h_k: k < num_lsb_bits then
      have h_k_lt: k < num_lsb_bits + 1 := by omega
      simp only [h_k_lt, ↓reduceIte, h_k, beq_iff_eq]
      have h_k_ne_eq: num_lsb_bits ≠ k := by omega
      simp only [h_k_ne_eq, ↓reduceIte, Nat.or_zero]
    else if h_k_eq: k = num_lsb_bits then
      simp only [h_k_eq, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false, BEq.rfl,
        Nat.zero_or]
      omega
    else
      have k_ne_lt: ¬(k < num_lsb_bits) := by omega
      have k_ne_lt_add_1: ¬(k < num_lsb_bits + 1) := by omega
      simp only [k_ne_lt_add_1, ↓reduceIte, k_ne_lt, beq_iff_eq, Nat.zero_or, right_eq_ite_iff,
        zero_ne_one, imp_false, ne_eq]
      omega

/-- This takes a argument for the number of lsbs to remove from the number -/
def get_msb (n : ℕ) (num_lsb_bits : ℕ) : ℕ := (n >>> num_lsb_bits) <<< num_lsb_bits

theorem msb_and_lsb_eq_zero {n : ℕ} (num_lsb_bits : ℕ) :
    get_msb n num_lsb_bits &&& get_lsb n num_lsb_bits = 0 := by
  change (n >>> num_lsb_bits <<< num_lsb_bits) &&& (get_lsb n num_lsb_bits) = 0
  set msb_no_shl := n >>> num_lsb_bits
  have h_bit_msb_shl := bit_of_shiftLeft (n := msb_no_shl) (p := num_lsb_bits)
  have h_bit_lsb := bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits)
  apply and_eq_zero_iff_and_each_bit_eq_zero.mpr
  intro j
  change bit j ((n >>> num_lsb_bits) <<< num_lsb_bits) &&& bit j (get_lsb n num_lsb_bits) = 0
  if h_j: j < num_lsb_bits then
    have h_bit_lhs := h_bit_msb_shl (k:=j - num_lsb_bits)
    have h_ne: ¬(num_lsb_bits ≤ j) := by omega
    have h_bit_left_eq_0 :  bit j ((n >>> num_lsb_bits) <<< num_lsb_bits) = 0:= by
      rw [h_bit_msb_shl]
      simp only [ite_eq_left_iff, not_lt, h_ne, IsEmpty.forall_iff, msb_no_shl]
    rw [h_bit_left_eq_0, Nat.zero_and]
  else
    have h_bit_rhs := h_bit_lsb (k:=j)
    have h_bit_right_eq_0: bit j (get_lsb n num_lsb_bits) = 0 := by
      simp only [h_bit_rhs, ite_eq_right_iff]
      omega
    rw [h_bit_right_eq_0, Nat.and_zero]

lemma num_eq_msb_add_lsb {n: ℕ} (num_lsb_bits: ℕ) :
  n = get_msb n num_lsb_bits + get_lsb n num_lsb_bits := by
  apply eq_iff_eq_all_bits.mpr
  intro k
  --- use 2 bit extractions to get the condition for bits of ((n >>> num_lsb_bits) <<< num_lsb_bits)
  set msb_no_shl := n >>> num_lsb_bits
  have h_bit_msb_shl := bit_of_shiftLeft (n := msb_no_shl) (p := num_lsb_bits)
  have h_bit_lsb := bit_of_lsb (n := n) (num_lsb_bits := num_lsb_bits)
  -- AND of msbs & lsbs is 0 => we use this to convert the sum into OR
  have h_and := msb_and_lsb_eq_zero (n := n) (num_lsb_bits := num_lsb_bits)
  rw [sum_of_and_eq_zero_is_or h_and]
  --- now reason on bitwise operation only
  rw [Nat.shiftRight_or_distrib, Nat.and_distrib_right]
  change bit k n = bit k ((n >>> num_lsb_bits) <<< num_lsb_bits) ||| bit k (get_lsb n num_lsb_bits)
  rw [h_bit_msb_shl, h_bit_lsb]
  if h_k: k < num_lsb_bits then
    simp only [h_k, ↓reduceIte, Nat.zero_or] at *
  else
    have h_ne: ¬(k < num_lsb_bits) := by omega
    have h_num_le_k: num_lsb_bits ≤ k := by omega
    simp only [h_ne, not_false_eq_true, ↓reduceIte, Nat.or_zero] at *
    rw [bit_of_shiftRight]
    congr
    rw [Nat.sub_add_cancel (n:=k) (m:=num_lsb_bits) (by omega)]

lemma num_eq_msb_xor_lsb {n: ℕ} (num_lsb_bits: ℕ) :
  n = get_msb n num_lsb_bits ^^^ get_lsb n num_lsb_bits := by
  rw [←sum_of_and_eq_zero_is_xor]
  · exact num_eq_msb_add_lsb (n := n) (num_lsb_bits := num_lsb_bits)
  · exact msb_and_lsb_eq_zero (n := n) (num_lsb_bits := num_lsb_bits)

end BitwiseIdentities
section FinNatHelper

theorem mul_two_add_bit_lt_two_pow (a b c : ℕ) (i : Fin 2)
    (h_a : a < 2 ^ b) (h_b : b < c) :
    a * 2 + i.val < 2^c := by
  if h_b_eq_0: b = 0 then
    rw [h_b_eq_0, pow_zero] at h_a
    interval_cases a
    · simp only [zero_mul, zero_add];
      have h_c_gt_0: c > 0 := by omega
      have h_i_lt_2_pow_c: i.val < 2^c := by
        calc
          _ ≤ 2^1 := by omega
          _ ≤ 2^c := by apply pow_le_pow_right' (by omega) (by omega)
      exact h_i_lt_2_pow_c
  else
    have h_le: 2^(b+1) ≤ 2^c := by
      rw [pow_le_pow_iff_right₀ (a:=2) (n:=b+1) (m:=c) (by omega)]
      omega
    have h_a_mul_2_add_i_lt_2_pow_c: a * 2 + i ≤ 2^c - 1 := by
      calc
        _ ≤ 2^(b+1) - 1 := by omega
        _ ≤ 2^c - 1 := by omega
    exact Nat.lt_of_le_sub_one (n:=a * 2 + i) (m:=2^c) (by omega) (h_a_mul_2_add_i_lt_2_pow_c)

theorem div_two_pow_lt_two_pow (x i j : ℕ) (h_x_lt_2_pow_i : x < 2 ^ (i + j)): x / 2^j < 2^(i) := by
  by_cases h_i_eq_0: i = 0
  · simp only [h_i_eq_0, zero_add, pow_zero, Nat.lt_one_iff, Nat.div_eq_zero_iff, Nat.pow_eq_zero,
    OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *;
    omega
  · push_neg at h_i_eq_0
    apply Nat.div_lt_of_lt_mul (m:=x) (n:=2^j) (k:=2^i) (by
      have h_rhs_eq : 2^(i+j) = 2^j * 2^i := by
        rw [pow_add (a:=2) (m:=i) (n:=j), mul_comm]
      rw [h_rhs_eq.symm]
      omega
    )

lemma lt_two_pow_of_lt_two_pow_exp_le (x i j: ℕ)
    (h_x_lt_2_pow_i: x < 2^i) (h_i_le_j: i ≤ j): x < 2^j := by
  calc
    _ < 2^i := by omega
    _ ≤ 2^j := by apply pow_le_pow_right' (by omega) (by omega)

variable {r : ℕ} [NeZero r]

lemma Fin.val_add_one (a : Fin r) (h_a_add_1 : a + 1 < r) : (a + 1).val = a.val + 1 := by
  rw [←Nat.mod_eq_of_lt (a := 1) (b := r) (by omega)] -- ⊢ ↑(b + 1) = ↑b + 1 % r
  apply Fin.val_add_eq_of_add_lt -- ⊢ ↑b + ↑1 < r
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  exact h_a_add_1

lemma Fin.val_sub_one (a : Fin r) (h_a_sub_1 : a > 0) : (a - 1).val = a.val - 1 := by
  rw [Fin.val_sub_one_of_ne_zero (by omega)] -- can use Fin.sub_val_of_le

lemma Fin.lt_iff_le_pred (a b : Fin r) (h_b : b > 0) : a < b ↔ a ≤ b - 1 := by
  have h_b_sub_1 : (b - 1).val = b.val - 1 := Fin.val_sub_one (a := b) (h_a_sub_1 := h_b)
  constructor
  · intro h
    apply Fin.mk_le_of_le_val
    omega
  · intro h
    apply Fin.mk_lt_of_lt_val
    omega

lemma Fin.le_iff_lt_succ (a b : Fin r) (h_b : b + 1 < r) : a ≤ b ↔ a < b + 1 := by
  have h_b_add_1 := Fin.val_add_one (a := b) (h_a_add_1 := h_b)
  constructor
  · intro h
    apply Fin.mk_lt_of_lt_val
    omega
  · intro h
    apply Fin.mk_le_of_le_val
    omega

lemma Fin.lt_succ (a : Fin r) (h_a_add_1 : a + 1 < r) : a < a + 1 := by
  apply Fin.mk_lt_of_lt_val
  rw [Fin.val_add_one (a := a) (h_a_add_1 := h_a_add_1)]
  exact Nat.lt_succ_self a.val

lemma Fin.le_succ (a : Fin r) (h_a_add_1 : a + 1 < r) : a ≤ a + 1 := by
  apply Fin.le_of_lt
  exact Fin.lt_succ (a := a) (h_a_add_1 := h_a_add_1)

@[elab_as_elim] def Fin.succRecOnSameFinType {motive : Fin r → Sort _}
    (zero : motive (0 : Fin r))
    (succ : ∀ i : Fin r, i + 1 < r → motive i → motive (i + 1)) : ∀ (i : Fin r), motive i
  | ⟨0, _⟩ => by exact zero
  | ⟨Nat.succ i_val, h⟩ => by -- ⊢ motive ⟨i_val.succ, h⟩
    simp only [Nat.succ_eq_add_one] at h
    set i : Fin r := ⟨i_val, by omega⟩
    set i_succ : Fin r := ⟨i_val.succ, by omega⟩
    have i_succ_val_eq : i_succ.val = i_val.succ := by rfl
    if h_i_add_1 : i + 1 < r then -- ⊢ motive ⟨i.succ, h⟩
      have motive_prev : motive i := Fin.succRecOnSameFinType zero succ i
      have res := succ (i := i) h_i_add_1 motive_prev
      have h_i_succ_eq : i_succ = i + 1 := by
        rw [Fin.eq_mk_iff_val_eq]
        rw [i_succ_val_eq]
        rw [Fin.val_add_one]
        omega
      rw [h_i_succ_eq]
      exact res
    else
      by_contra h_i_add_1
      simp only at h_i_add_1
      contradiction

-- The theorem statement and its proof.
-- TODO: state a more generalized and reusable version of this, where f is from Fin r → M
theorem Fin.sum_univ_odd_even {n : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : Fin (2 ^ n), f (2 * i)) + (∑ i : Fin (2 ^ n), f (2 * i + 1))
    = ∑ i: Fin (2 ^ (n+1)), f i := by
  set f_even := fun i => f (2 * i)
  set f_odd := fun i => f (2 * i + 1)
  conv_lhs =>
    enter [1, 2, i]
    change f_even i
  conv_lhs =>
    enter [2, 2, i]
    change f_odd i
  simp only [Fin.sum_univ_eq_sum_range]

  -- Let's define the sets of even and odd numbers.
  let evens: Finset ℕ := Finset.image (fun i ↦ 2 * i) (Finset.range (2^n))
  let odds: Finset ℕ := Finset.image (fun i ↦ 2 * i + 1) (Finset.range (2^n))

  conv_lhs =>
    enter [1];
    rw [←Finset.sum_image (g:=fun i => 2 * i) (by simp)]

  conv_lhs =>
    enter [2];
    rw [← Finset.sum_image (g:=fun i => 2 * i + 1) (by simp)]

  -- First, we prove that the set on the RHS is the disjoint union of evens and odds.
  have h_disjoint : Disjoint evens odds := by
    apply Finset.disjoint_iff_ne.mpr
  -- Assume for contradiction that an element `x` is in both sets.
    rintro x hx y hy hxy
    -- Unpack the definitions of `evens` and `odds`.
    rcases Finset.mem_image.mp hx with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨k₂, _, rfl⟩
    omega

  have h_union : evens ∪ odds = Finset.range (2 ^ (n + 1)) := by
    apply Finset.ext; intro x
    simp only [Finset.mem_union, Finset.mem_range]
    -- ⊢ x ∈ evens ∨ x ∈ odds ↔ x < 2 ^ (n + 1)
    constructor
    · -- First direction: `x ∈ evens ∪ odds → x < 2^(n+1)`
      -- This follows from the bounds of the original range `Finset.range (2^n)`.
      intro h
      rcases h with (h_even | h_odd)
      · rcases Finset.mem_image.mp h_even with ⟨k₁, hk₁, rfl⟩
        simp at hk₁
        omega
      · rcases Finset.mem_image.mp h_odd with ⟨k₂, hk₂, rfl⟩
        simp at hk₂
        omega
    · -- Second direction: `x < 2^(n+1) → x ∈ evens ∪ odds`
      intro hx
      obtain (⟨k, rfl⟩ | ⟨k, rfl⟩) := Nat.even_or_odd x
      · left;
        unfold evens
        simp only [Finset.mem_image, Finset.mem_range]
        use k;
        omega
      · right;
        unfold odds
        simp only [Finset.mem_image, Finset.mem_range]
        use k;
        omega
  -- Now, rewrite the RHS using this partition.
  rw [←h_union, Finset.sum_union h_disjoint]

end FinNatHelper

section FinFieldPolyHelper
variable {Fq : Type*} [Field Fq] [Fintype Fq]

section FieldVanishingPolynomialEquality
-- NOTE : We lift `∏_{c ∈ Fq} (X - c) = X^q - X` from `Fq[X]` to `L[X]`,
-- then achieve a generic version `∏_{c ∈ Fq} (p - c) = p^q - p` for any `p` in `L[X]`

/--
The polynomial `X^q - X` factors into the product of `(X - c)` ∀ `c` ∈ `Fq`,
i.e. `∏_{c ∈ Fq} (X - c) = X^q - X`.
-/
theorem prod_X_sub_C_eq_X_pow_card_sub_X (h_Fq_card_gt_1 : Fintype.card Fq > 1):
  (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)) =
    Polynomial.X^(Fintype.card Fq) - Polynomial.X := by

  -- Step 1 : Setup - Define P and Q for clarity.
  set P : Fq[X] := ∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)
  set Q : Fq[X] := Polynomial.X^(Fintype.card Fq) - Polynomial.X

  -- We will prove P = Q by showing they are both monic and have the same roots.

  -- Step 2 : Prove P and Q are monic.
  have hP_monic : P.Monic := by
    apply Polynomial.monic_prod_of_monic
    intro c _
    exact Polynomial.monic_X_sub_C c

  have hQ_monic : Q.Monic := by
    apply Polynomial.monic_X_pow_sub
    -- The condition is that degree(X) < Fintype.card Fq
    rw [Polynomial.degree_X]
    exact_mod_cast h_Fq_card_gt_1

  have h_roots_P : P.roots = (Finset.univ : Finset Fq).val := by
    apply Polynomial.roots_prod_X_sub_C
  -- The roots of Q are, by Fermat's Little Theorem, also all elements of Fq.
  have h_roots_Q : Q.roots = (Finset.univ : Finset Fq).val := by
    exact FiniteField.roots_X_pow_card_sub_X Fq

  -- Step 3 : Prove P and Q have the same set of roots.
  -- We show that both root sets are equal to `Finset.univ`.
  have h_roots_eq : P.roots = Q.roots := by
    rw [h_roots_P, h_roots_Q]

  have hP_splits : P.Splits (RingHom.id Fq) := by
    -- ⊢ Splits (RingHom.id Fq) (∏ c ∈ Finset.univ, X - C c)
    apply Polynomial.splits_prod
    intro c _
    apply Polynomial.splits_X_sub_C

  have hQ_card_roots : Q.roots.card = Fintype.card Fq := by
    rw [h_roots_Q]
    exact rfl

  have natDegree_Q : Q.natDegree = Fintype.card Fq := by
    unfold Q
    have degLt : (X : Fq[X]).natDegree < ((X : Fq[X]) ^ Fintype.card Fq).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      rw [Polynomial.natDegree_X]
      exact h_Fq_card_gt_1
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt degLt]
    rw [Polynomial.natDegree_X_pow]

  have hQ_splits : Q.Splits (RingHom.id Fq) := by
    unfold Q
    apply Polynomial.splits_iff_card_roots.mpr
    -- ⊢ (X ^ Fintype.card Fq - X).roots.card = (X ^ Fintype.card Fq - X).natDegree
    rw [hQ_card_roots]
    rw [natDegree_Q]

  -- 4. CONCLUSION : Since P and Q are monic, split, and have the same roots, they are equal.
  have hP_eq_prod : P = (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) P.roots).prod := by
    apply Polynomial.eq_prod_roots_of_monic_of_splits_id hP_monic hP_splits
  have hQ_eq_prod : Q = (Multiset.map (fun a ↦ Polynomial.X - Polynomial.C a) Q.roots).prod := by
    apply Polynomial.eq_prod_roots_of_monic_of_splits_id hQ_monic hQ_splits
  rw [hP_eq_prod, hQ_eq_prod, h_roots_eq]

variable {L : Type*} [CommRing L] [Algebra Fq L]
/--
The identity `∏_{c ∈ Fq} (X - c) = X^q - X` also holds in the polynomial ring `L[X]`,
where `L` is any field extension of `Fq`.
-/
theorem prod_X_sub_C_eq_X_pow_card_sub_X_in_L
  (h_Fq_card_gt_1 : Fintype.card Fq > 1):
  (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C (algebraMap Fq L c))) =
    Polynomial.X^(Fintype.card Fq) - Polynomial.X := by

  -- Let `f` be the ring homomorphism from `Fq` to `L`.
  let f := algebraMap Fq L

  -- The goal is an equality in L[X]. We will show that this equality is just
  -- the "mapped" version of the equality in Fq[X], which we already proved.

  -- First, show the LHS of our goal is the mapped version of the LHS of the base theorem.
  have h_lhs_map : (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C (f c))) =
      Polynomial.map f (∏ c ∈ (Finset.univ : Finset Fq), (Polynomial.X - Polynomial.C c)) := by
    -- `map` is a ring homomorphism, so it distributes over products, subtraction, X, and C.
    rw [Polynomial.map_prod]
    congr! with c
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

  -- Next, show the RHS of our goal is the mapped version of the RHS of the base theorem.
  have h_rhs_map : (Polynomial.X^(Fintype.card Fq) - Polynomial.X) =
      Polynomial.map f (Polynomial.X^(Fintype.card Fq) - Polynomial.X) := by
    -- `map` also distributes over powers.
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]

  -- Now, we can rewrite our goal using these facts.
  rw [h_lhs_map, h_rhs_map]
  -- ⊢ map f (∏ c, (X - C c)) = map f (X ^ Fintype.card Fq - X)

  -- The goal is now `map f (LHS_base) = map f (RHS_base)`.
  -- This is true if `LHS_base = RHS_base`, which is exactly our previous theorem.
  rw [prod_X_sub_C_eq_X_pow_card_sub_X h_Fq_card_gt_1]

/--
The identity `∏_{c ∈ Fq} (X - c) = X^q - X` also holds in the polynomial ring `L[X]`,
where `L` is any field extension of `Fq`.
-/
theorem prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L
  (h_Fq_card_gt_1 : Fintype.card Fq > 1) (p : L[X]):
  (∏ c ∈ (Finset.univ : Finset Fq), (p - Polynomial.C (algebraMap Fq L c))) =
    p^(Fintype.card Fq) - p := by

  -- The strategy is to take the known identity for the polynomial X and substitute
  -- X with the arbitrary polynomial p. This substitution is formally known as
  -- polynomial composition (`Polynomial.comp`).

  -- Let `q` be the cardinality of the field Fq for brevity.
  let q := Fintype.card Fq

  -- From the previous theorem, we have the base identity in L[X]:
  -- `(∏ c, (X - C c)) = X^q - X`
  let base_identity := prod_X_sub_C_eq_X_pow_card_sub_X_in_L (L := L) h_Fq_card_gt_1

  -- `APPROACH : f = g => f.comp(p) = g.comp(p)`
  have h_composed_eq : (∏ c ∈ (Finset.univ : Finset Fq), (X - C (algebraMap Fq L c))).comp p
    = ((X:L[X])^q - X).comp p := by
    rw [base_identity]

  -- Now, we simplify the left-hand side (LHS) and right-hand side (RHS) of `h_composed_eq`
  -- to show they match the goal.

  -- First, simplify the LHS : `(∏ c, (X - C c)).comp(p)`
  have h_lhs_simp : (∏ c ∈ (Finset.univ : Finset Fq), (X - C (algebraMap Fq L c))).comp p =
                     ∏ c ∈ (Finset.univ : Finset Fq), (p - C (algebraMap Fq L c)) := by
    -- Use the theorem that composition distributes over products
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro c _
    --⊢ (X - C ((algebraMap Fq L) c)).comp p = p - C ((algebraMap Fq L) c)
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]

  -- Next, simplify the RHS : `(X^q - X).comp(p)`
  have h_rhs_simp : ((X:L[X])^q - X).comp p = p^q - p := by
    -- Composition distributes over subtraction and powers.
    rw [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp]

  -- By substituting our simplified LHS and RHS back into `h_composed_eq`,
  -- we arrive at the desired goal.
  rw [h_lhs_simp, h_rhs_simp] at h_composed_eq
  exact h_composed_eq
end FieldVanishingPolynomialEquality

section FrobeniusPolynomialIdentity
-- NOTE : We lift the Frobenius identity from `Fq[X]` to `L[X]`
/--
The Frobenius identity for polynomials in `Fq[X]`.
The `q`-th power of a sum of polynomials is the sum of their `q`-th powers.
-/
theorem frobenius_identity_in_ground_field
  {h_Fq_char_prime : Fact (Nat.Prime (ringChar Fq))} (f g : Fq[X]) :
    (f + g)^(Fintype.card Fq) = f^(Fintype.card Fq) + g^(Fintype.card Fq) := by
  -- The Freshman's Dream `(a+b)^e = a^e + b^e` holds if `e` is a power of the characteristic.
  -- First, we establish that `q = p^n` where `p` is the characteristic of `Fq`.
  let p := ringChar Fq
  have h_p_prime : Fact p.Prime := h_Fq_char_prime
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq p
  rw [hn]
  -- The polynomial ring `Fq[X]` also has characteristic `p`.
  haveI : CharP Fq[X] p := Polynomial.charP
  -- Apply the general "Freshman's Dream" theorem for prime powers.
  exact add_pow_expChar_pow f g p ↑n

variable {L : Type*} [CommRing L] [Algebra Fq L] [Nontrivial L]

/--
The lifted Frobenius identity for polynomials in `L[X]`, where `L` is an `Fq`-algebra.
The exponent `q` is the cardinality of the base field `Fq`.
-/
theorem frobenius_identity_in_algebra {h_Fq_char_prime : Fact (Nat.Prime (ringChar Fq))}
  (f g : L[X]) : (f + g)^(Fintype.card Fq) = f^(Fintype.card Fq) + g^(Fintype.card Fq) := by
  -- The logic is identical. The key is that `L` inherits the characteristic of `Fq`.
  let p := ringChar Fq
  haveI : Fact p.Prime := h_Fq_char_prime
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq p

  -- Rewrite the goal using `q = p^n`.
  rw [hn]

  -- Since `L` is an `Fq`-algebra, it must have the same characteristic `p`.
  have h_charP_Fq : CharP Fq p := by
    simp only [p]
    exact ringChar.charP Fq

  have h_charP_L : CharP L p := by
    have h_inj : Function.Injective (algebraMap Fq L) := by
      exact RingHom.injective (algebraMap Fq L) -- L must be nontrivial
    have h_charP_L := (RingHom.charP_iff (A := L) (f := algebraMap Fq L)
      (H := h_inj) p).mp h_charP_Fq
    exact h_charP_L
  -- The polynomial ring `L[X]` also has characteristic `p`.
  have h_charP_L_X : CharP L[X] p := by
    exact Polynomial.charP
  exact add_pow_expChar_pow f g p ↑n

omit [Fintype Fq] [Nontrivial L] in
/-- Restricting a linear map on polynomial composition to a linear map on polynomial evaluation.
-/
theorem linear_map_of_comp_to_linear_map_of_eval (f : L[X])
  (h_f_linear : IsLinearMap (R := Fq) (M := L[X]) (M₂ := L[X])
    (f := fun inner_p ↦ f.comp inner_p)) :
    IsLinearMap (R := Fq) (M := L) (M₂ := L) (f := fun x ↦ f.eval x) := by
  constructor
  · intro x y
    -- ⊢ eval (x + y) f = eval x f + eval y f
    have h_comp_add := h_f_linear.map_add
    have h_spec := h_comp_add (C x) (C y)
    have h_lhs_simp : f.comp (C x + C y) = C (f.eval (x + y)) := by
      rw [←Polynomial.C_add, Polynomial.comp_C]
    have h_rhs_simp : f.comp (C x) + f.comp (C y) = C (f.eval x + f.eval y) := by
      rw [Polynomial.comp_C, Polynomial.comp_C, Polynomial.C_add]
    rw [h_lhs_simp, h_rhs_simp] at h_spec
    exact (Polynomial.C_injective) h_spec
  · intro k x
    have h_comp_smul := h_f_linear.map_smul
    have h_spec := h_comp_smul k (C x)
    have h_lhs_simp : f.comp (k • C x) = C (f.eval (k • x)) := by
      rw [Polynomial.smul_C, Polynomial.comp_C]
    have h_rhs_simp : k • f.comp (C x) = C (k • f.eval x) := by
      rw [Polynomial.comp_C, Polynomial.smul_C]
    rw [h_lhs_simp, h_rhs_simp] at h_spec
    exact (Polynomial.C_injective) h_spec
end FrobeniusPolynomialIdentity

end FinFieldPolyHelper

section MonomialBasis

universe u

-- Fix a binary field `L` of degree `r` over its prime subfield `F₂`
variable {L : Type u} [Field L] [Fintype L]
variable {F₂ : Type u} [Field F₂] [Fintype F₂] (hF₂ : Fintype.card F₂ = 2)
variable [Algebra F₂ L]
-- We assume an `F₂`-basis for `L`, denoted by `(β₀, β₁, ..., β_{r-1})`, indexed by natural numbers.
variable (β : Nat → L) (hβ_lin_indep : LinearIndependent (R := F₂) (M := L) (v := β))

omit [Fintype L] in
@[simp]
theorem sum_degreeLT_monomial_eq_subtype {n : ℕ} (p : L⦃< n⦄[X]) :
  (⟨p.val.sum (fun n a => Polynomial.monomial n a), by
    -- degree of sum is degree of p.val, which is < n
    rw [Polynomial.sum_monomial_eq p.val]
    exact p.property
  ⟩ : L⦃< n⦄[X]) = p :=
      -- `span_le` changes the goal to showing every vector in the generating set
  Subtype.eq (Polynomial.sum_monomial_eq p.val)

noncomputable def monomialBasisOfDegreeLT {n : ℕ} : Basis (Fin n) L (L⦃< n⦄[X]) := by
  set monomials_in_submodule:Fin n → L⦃< n⦄[X] := fun ⟨i, hi⟩ =>
  ⟨monomial (R := L) (n := i) (a := 1), by
    simp only [Polynomial.mem_degreeLT]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, degree_monomial, Nat.cast_lt]
    exact hi
  ⟩

  have h_li_submodule : LinearIndependent L monomials_in_submodule := by
    rw [linearIndependent_iff] -- alternative : linearIndependent_powers_iff_aeval
    intro l hl -- l : Fin n →₀ L, hl : (Finsupp.linearCombination L monomials_in_submodule) l = 0
    apply Finsupp.ext -- ⊢ ∀ (a : Fin n), l a = 0 a
    intro i
    have h_poly_eq_zero : (Finsupp.linearCombination L monomials_in_submodule l).val = 0 := by
      -- converts the equality of subtypes `hl` to an equality of values
      exact Subtype.ext_iff.mp hl

    have h_coeff_eq_li :
      coeff (Finsupp.linearCombination L monomials_in_submodule l).val i = l i := by
      -- `span_le` changes the goal to showing every vector in the generating set
      set v := monomials_in_submodule
      simp only [v, monomials_in_submodule, monomial_one_right_eq_X_pow]
      rw [Finsupp.linearCombination_apply]
      simp only [SetLike.mk_smul_mk]
      conv =>
        lhs
        simp only [Finsupp.sum, AddSubmonoidClass.coe_finset_sum, finset_sum_coeff, coeff_smul,
          coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, monomials_in_submodule, v]
      -- ⊢ (∑ x ∈ l.support, if ↑i = ↑x then l x else 0) = l i
      simp_rw [Fin.val_eq_val, eq_comm]
      -- ⊢ l i = ∑ x ∈ l.support, if i = x then l x else 0
      by_cases h_i_in_l_support : i ∈ l.support
      -- `span_le` changes the goal to showing every vector in the generating set
      · rw [Finset.sum_ite_eq_of_mem] -- ⊢ represent l i as a sum over l.support
        exact h_i_in_l_support
      · have l_i_is_zero : l i = 0 := by
          exact Finsupp.notMem_support_iff.mp h_i_in_l_support
        simp only [l_i_is_zero, Finset.sum_ite_eq, Finsupp.mem_support_iff, ne_eq,
          not_true_eq_false, ↓reduceIte]
    rw [h_poly_eq_zero] at h_coeff_eq_li
    simp only [coeff_zero] at h_coeff_eq_li
    exact h_coeff_eq_li.symm

  have h_span_submodule : Submodule.span (R := L) (Set.range monomials_in_submodule) = ⊤ :=by
    apply le_antisymm
    · -- First goal : Prove that your span is a subspace of the whole space.
      -- `span_le` changes the goal to showing every vector in the generating set
      rw [Submodule.span_le]
      -- ⊢ ↑(Finset.image (fun n ↦ X ^ n) (Finset.range n)) ⊆ ↑L⦃< n⦄[X]
      rw [Set.range_subset_iff] -- simp [Set.image_subset_image_iff]
      intro j -- `j` is an index for your family, e.g., `j : Fin n`
      -- ⊢ monomials_in_submodule j ∈ ↑⊤
      simp only [Submodule.top_coe, Set.mem_univ, monomials_in_submodule]
    · -- Second goal : Prove the whole space is a subspace of your span.
      rw [Submodule.top_le_span_range_iff_forall_exists_fun]
      intro p
      have hp := p.property
      have h_deg_p : p.val.degree < n := by
        rw [Polynomial.mem_degreeLT] at hp
        exact hp
      -- ⊢ ∃ c, ∑ i, c i • monomials_in_submodule i = p
      set c : Fin n → L := fun i => p.val.coeff i
      have h_c : c = fun (i : Fin n) => p.val.coeff i := by rfl
      use c
      -- ⊢ ∑ i, c i • monomials_in_submodule i = p
      apply Subtype.ext -- bring equality from ↑L⦃< n⦄[X] to L[X]
      rw [←sum_degreeLT_monomial_eq_subtype (p := p)] -- convert ↑p in rhs into (↑p).sum form
      conv =>
        rhs -- ↑⟨(↑p).sum fun n a ↦ (monomial n) a, ⋯⟩
        -- we have to convert (↑p).sum into Fin n → L form using Polynomial.sum_fin
        simp only [monomial_zero_right, implies_true, ←Polynomial.sum_fin (hn := h_deg_p)]
      -- ⊢ ↑(∑ i, c i • monomials_in_submodule i) = ∑ i, (monomial ↑i) ((↑p).coeff ↑i)
      rw [AddSubmonoidClass.coe_finset_sum] -- bring both sides back to L[X]
      apply Finset.sum_congr rfl
      intro ⟨i, hi_finN⟩ hi
      simp only [SetLike.mk_smul_mk, c, monomials_in_submodule]
      -- ⊢ (↑p).coeff i • (monomial i) 1 = (monomial i) ((↑p).coeff i)
      simp only [monomial_one_right_eq_X_pow]
      rw [←Polynomial.smul_X_eq_monomial]

  apply Basis.mk (R := L) (M := degreeLT (R := L) (n := n))
  · exact h_li_submodule
  · exact le_of_eq (hab := h_span_submodule.symm)

omit [Fintype L] in
theorem finrank_degreeLT_n (n : ℕ) : Module.finrank L (L⦃< n⦄[X]) = n := by
  have monomial_basis : Basis (Fin n) (R := L) (M := L⦃< n⦄[X]) := monomialBasisOfDegreeLT (n := n)
  rw [Module.finrank_eq_card_basis monomial_basis]
  rw [Fintype.card_fin]

instance finiteDimensional_degreeLT {n : ℕ} (h_n_pos : 0 < n) :
  FiniteDimensional (K := L) (V := L⦃< n⦄[X]) := by
  have h : 0 < Module.finrank L (L⦃< n⦄[X]) := by
    rw [finrank_degreeLT_n n]
    omega
  exact FiniteDimensional.of_finrank_pos h

end MonomialBasis
end AdditiveNTT
