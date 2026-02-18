/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Chung Thai Nguyen, Quang Dao
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.FieldDivision
import ArkLib.Data.Polynomial.Frobenius
import Mathlib.Algebra.EuclideanDomain.Basic
import ArkLib.Data.RingTheory.CanonicalEuclideanDomain
import Mathlib.Tactic.DepRewrite

/-! # Common Utilities for Binary Fields

This file provides shared utilities for binary field implementations (fields of characteristic 2).
It includes:

1. **ZMod2Poly lemmas** — Properties of polynomials over GF(2)
2. **BitVec operations** — Carry-less multiplication, squaring
3. **BitVec ↔ Polynomial isomorphism** — `toPoly` and related lemmas

These utilities are used by both the tower construction (`Tower/`) and the
direct GF(2^128) implementation (`BF128Ghash/`).

## Main Definitions

- `ZMod2Poly.add_self_cancel`: In char 2, `a + a = 0`
- `toPoly`: Convert a BitVec to a polynomial over GF(2)
- `clMul`: Carry-less multiplication of bit vectors
- `toPoly_xor`: `toPoly (a ^^^ b) = toPoly a + toPoly b`
- `toPoly_clMul_no_overflow`: `toPoly (clMul a b) = toPoly a * toPoly b`
-/

/-! ## Section 1: ZMod 2 Polynomial Lemmas -/

section ZMod2Poly
open Polynomial

lemma ZMod2Poly.add_self_cancel (a : Polynomial (ZMod 2)) : a + a = 0 := by
  exact ZModModule.add_self a

lemma ZMod2Poly.sub_eq_add (a b : Polynomial (ZMod 2)) : a - b = a + b := by
  exact ZModModule.sub_eq_add a b

lemma ZMod2Poly.neg_eq_self (a : Polynomial (ZMod 2)) : -a = a := by
  exact ZModModule.neg_eq_self a

lemma ZMod2Poly.add_eq_sub (a b : Polynomial (ZMod 2)) : a + b = a - b := by
  exact Eq.symm (sub_eq_add a b)

lemma ZMod2Poly.two_mul (a : Polynomial (ZMod 2)) : 2 * a = 0 := by
  rw [_root_.two_mul]; rw [ZModModule.add_self]

lemma ZMod2Poly.mul_two (a : Polynomial (ZMod 2)) : a * 2 = 0 := by
  rw [mul_comm]; exact two_mul a

lemma ZMod2Poly.two_eq_zero : (2 : Polynomial (ZMod 2)) = 0 := by
  exact CharP.ofNat_eq_zero (ZMod 2)[X] 2

lemma ZMod2Poly.three_eq_one : (3 : Polynomial (ZMod 2)) = 1 := by rfl

lemma ZMod2Poly.mul_three (a : Polynomial (ZMod 2)) : a * 3 = a := by
  simp only [three_eq_one, mul_one];

@[simp]
lemma ZMod2Poly.natCast_ZMod2 (n : ℕ) : (n : Polynomial (ZMod 2)) = ((n % 2) : ℕ) := by
  have : CharP (Polynomial (ZMod 2)) 2 := inferInstance
  exact CharP.cast_eq_mod (Polynomial (ZMod 2)) 2 n

lemma ZMod2_value_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl;
  · right; rfl

/--
Helper: In Polynomial (ZMod 2), the only unit is 1.
Therefore, if two polynomials are Associated (differ by a unit), they must be Equal.
-/
lemma eq_of_associated_ZMod2 {a b : Polynomial (ZMod 2)} (h : Associated a b) : a = b := by
  rcases h with ⟨u, h_eq⟩
  -- 1. Get the unit as a polynomial
  let u_poly : Polynomial (ZMod 2) := u
  -- 2. Prove the unit must be constant 1
  have h_unit_is_one : u_poly = 1 := by
    -- The degree of a unit in K[X] is 0
    have h_deg : u_poly.degree = 0 := Polynomial.degree_eq_zero_of_isUnit u.isUnit
    -- The constant coefficient must be a unit in ZMod 2
    have h_coeff : IsUnit (u_poly.coeff 0) := by
      rw [← Polynomial.isUnit_C, ← Polynomial.eq_C_of_degree_eq_zero h_deg]
      exact u.isUnit
    -- The only unit in ZMod 2 is 1
    have h_val : u_poly.coeff 0 = 1 := by
      -- In ZMod 2, elements are either 0 or 1. 0 is not a unit.
      have u_poly_coeff_0_cases := ZMod2_value_eq_zero_or_one (u_poly.coeff 0)

      rcases u_poly_coeff_0_cases with u_poly_coeff_0_zero | u_poly_coeff_0_one
      · exfalso;
        have h_isUnit_zero: IsUnit (0 : ZMod 2) := by
          rw [u_poly_coeff_0_zero.symm]
          exact h_coeff
        exact not_isUnit_zero h_isUnit_zero
      · exact u_poly_coeff_0_one
    -- Therefore u_poly is 1
    rw [Polynomial.eq_C_of_degree_eq_zero h_deg, h_val, map_one]
  unfold u_poly at h_unit_is_one
  -- 3. Substitute back
  rw [h_unit_is_one] at h_eq
  simp only [mul_one] at h_eq
  exact h_eq

lemma ZMod2Poly.fintypeCard_eq_two : Fintype.card (ZMod 2) = 2 := by rfl

lemma ZMod2Poly.frobenius (a b : Polynomial (ZMod 2)) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h_2_eq_fintypecard : 2 = Fintype.card (ZMod 2) := by rfl
  change (a + b) ^ (Fintype.card (ZMod 2))
    = a ^ (Fintype.card (ZMod 2)) + b ^ (Fintype.card (ZMod 2))
  have hRingCharZMod2 : ringChar (ZMod 2) = 2 := by exact ZMod.ringChar_zmod_n 2
  letI : Fact (Nat.Prime (ringChar (ZMod 2))) := by
    rw [hRingCharZMod2]
    exact Nat.fact_prime_two
  rw [frobenius_identity_in_algebra (Fq := ZMod 2) (f := a) (g := b)]

/--
**EuclideanDomain.gcd_comm for Polynomials**
Commutativity: EuclideanDomain.gcd(a, b) = EuclideanDomain.gcd(b, a)
Uses the fact that EuclideanDomain provides a GCDMonoid instance, which has gcd_comm'.
-/
lemma ZMod2Poly.euclidean_gcd_comm (a b : Polynomial (ZMod 2)) :
    EuclideanDomain.gcd a b = EuclideanDomain.gcd b a := by
  letI : GCDMonoid (Polynomial (ZMod 2)) := by apply EuclideanDomain.gcdMonoid
  have h_assoc := gcd_comm' a b
  apply eq_of_associated_ZMod2
  exact h_assoc

end ZMod2Poly

/-! ## Section 2: Polynomial Helper Lemmas -/

section PolynomialHelperLemmas
open Polynomial

/--
Helper Lemma:
If P is a degree 128 polynomial and is REDUCIBLE,
then it must have an irreducible factor q with degree ≤ 64.
-/
lemma Polynomial.exists_factor_le_64_of_reducible.{u} {R : Type u} [Field R] (P : Polynomial R)
    (h_deg : P.natDegree = 128) (h_red : ¬ Irreducible P) :
    ∃ q, Irreducible q ∧ q ∣ P ∧ q.natDegree ≤ 64 := by
  -- 1. P is not zero and not a unit (since deg=128)
  have h_ne_zero : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at h_deg; contradiction
  have h_not_unit : ¬ IsUnit P := by
    by_contra h_unit
    rw [Polynomial.isUnit_iff_degree_eq_zero] at h_unit
    have h_natDeg_P_eq_0 : P.natDegree = 0 := by
      exact (Polynomial.degree_eq_iff_natDegree_eq h_ne_zero).mp h_unit
    have h_natDeg_ne_0 : P.natDegree ≠ 0 := by
      exact Nat.ne_of_gt (by exact Nat.lt_of_sub_eq_succ h_deg)
    exact h_natDeg_ne_0 h_natDeg_P_eq_0

  -- 2. Definition of Reducible: P = a * b where a, b are non-units
  -- We rely on the definition of Irreducible to find these factors.
  have h_exists_split : ∃ a b, P = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    -- Irreducible p ↔ ¬IsUnit p ∧ (∀ a b, p = a * b → IsUnit a ∨ IsUnit b)
    -- Therefore ¬Irreducible p ∧ ¬IsUnit p ↔ ∃ a b, p = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b
    rw [irreducible_iff, not_and_or, not_forall] at h_red
    -- We know P is not a unit, so the first part of the OR is false
    simp only [h_not_unit, not_false_eq_true] at h_red
    push_neg at h_red
    simp only [IsEmpty.exists_iff, false_or] at h_red
    rcases h_red with ⟨a, b, h_eq, h_non_units⟩
    use a, b

  rcases h_exists_split with ⟨a, b, h_eq, ha_nu, hb_nu⟩

  -- 3. Degrees add up: deg(P) = deg(a) + deg(b)
  have h_nonzero : P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at h_deg; contradiction

  have h_a_ne_zero : a ≠ 0 := by
    intro h_a_eq_0; rw [h_eq, h_a_eq_0] at h_deg; simp only [zero_mul, natDegree_zero,
      OfNat.zero_ne_ofNat] at h_deg;
  have h_b_ne_zero : b ≠ 0 := by
    intro h_b_eq_0; rw [h_eq, h_b_eq_0] at h_deg; simp only [mul_zero, natDegree_zero,
      OfNat.zero_ne_ofNat] at h_deg;
  have h_deg_sum : a.natDegree + b.natDegree = 128 := by
    rw [← h_deg, h_eq, Polynomial.natDegree_mul (hp := h_a_ne_zero) (hq := h_b_ne_zero)]

  -- 4. Pick the smaller factor.
  -- WLOG, assume deg(a) ≤ deg(b). Then deg(a) ≤ 64.
  -- If deg(b) < deg(a), we just swap names.
  by_cases h_le : a.natDegree ≤ b.natDegree
  · -- Case: a is the small one
    have h_deg_a : a.natDegree ≤ 64 := by omega
    -- 'a' is a non-unit, so it must have an irreducible factor 'q'
    -- This comes from UniqueFactorizationDomain logic
    obtain ⟨q, hq_irr, hq_dvd_a⟩ := WfDvdMonoid.exists_irreducible_factor ha_nu h_a_ne_zero
    use q
    refine ⟨hq_irr, dvd_trans hq_dvd_a (Dvd.intro b h_eq.symm), ?_⟩
    -- deg(q) ≤ deg(a) ≤ 64
    apply le_trans (Polynomial.natDegree_le_of_dvd hq_dvd_a h_a_ne_zero) h_deg_a
  · -- Case: b is the small one
    push_neg at h_le
    have h_deg_b : b.natDegree ≤ 64 := by omega
    obtain ⟨q, hq_irr, hq_dvd_b⟩ := WfDvdMonoid.exists_irreducible_factor hb_nu h_b_ne_zero
    use q
    refine ⟨hq_irr, dvd_trans hq_dvd_b (Dvd.intro_left a h_eq.symm), ?_⟩
    apply le_trans (Polynomial.natDegree_le_of_dvd hq_dvd_b h_b_ne_zero) h_deg_b

end PolynomialHelperLemmas

/-! ## Section 3: BitVec Operations -/

namespace BinaryField

open Polynomial

section BitVecHelperLemmas

lemma BitVec.toNat_of_cast {w w2 : ℕ} (x : BitVec w) (h_width_eq : w = w2) :
    BitVec.toNat ((cast (h := by rw [h_width_eq]) x) : BitVec w2) = BitVec.toNat x := by
  subst h_width_eq
  simp only [_root_.cast_eq]

end BitVecHelperLemmas

section BitVecOperations

-- We use BitVec 256 to ensure no overflows during squaring
abbrev B128 := BitVec 128
abbrev B256 := BitVec 256

-- Extend 128 to 256
def to256 (v : B128) : B256 := BitVec.zeroExtend 256 v

lemma to256_toNat (v : B128) : (to256 v).toNat = v.toNat := by
  simp only [to256, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.reducePow,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  change BitVec.toNat v < 2^256
  have h_toNat_lt := BitVec.toNat_lt_twoPow_of_le (n := 256) (x := v) (h := by omega)
  omega

-- Std.Commutative and Std.Associative instances for Nat.xor required by Finset.fold
instance : Std.Commutative Nat.xor where
  comm := Nat.xor_comm

instance : Std.Associative Nat.xor where
  assoc := Nat.xor_assoc

-- Std.Commutative and Std.Associative instances for BitVec.xor required by Finset.fold
instance {w : Nat} : Std.Commutative (α := BitVec w) BitVec.xor where
  comm := fun a b => by
    ext i
    simp only [BitVec.xor_eq, BitVec.getElem_xor]
    rw [Bool.xor_comm]

instance {w : Nat} : Std.Associative (α := BitVec w) BitVec.xor where
  assoc := fun a b c => by
    ext i
    simp only [BitVec.xor_eq, BitVec.getElem_xor, Bool.bne_assoc]

-- TODO: optimize clMul, potentially using Karatsuba decomposition
/-- Carry-less (polynomial) multiplication of two 256-bit vectors. -/
def clMul (a b : B256) : B256 :=
  (Finset.univ : Finset (Fin 256)).fold BitVec.xor 0
      (fun i => if a.getLsb i then b <<< i.val else 0)

/-- Carry-less squaring of a 128-bit vector. -/
def clSq (a : B128) : B256 :=
  let a256 := to256 a
  clMul a256 a256

end BitVecOperations

/-! ## Section 4: BitVec ↔ Polynomial Isomorphism -/

section PolynomialIsomorphism

-- We define toPoly as a Sum of Monomials using Fin.foldl
-- Note: noncomputable because Polynomial doesn't have computable operations
noncomputable def toPoly {w : Nat} (v : BitVec w) : (ZMod 2)[X] :=
  ∑ i : Fin w, if v.getLsb i then X^i.val else 0

-- 2. The clMul Definition in Fold Form
-- We define this lemma to exactly match the structure above:
-- s = Finset.univ (Fin 256)
-- f = fun i => if a[i] then b <<< i else 0
lemma clMul_eq_fold (a b : B256) :
    clMul a b = (Finset.univ : Finset (Fin 256)).fold BitVec.xor 0
      (fun i => if a.getLsb i then b <<< i.val else 0) := by rfl

lemma toPoly_one_eq_one {w : Nat} (h_w_pos : w > 0) : toPoly (BitVec.ofNat w 1) = 1 := by
  unfold toPoly
  -- For BitVec.ofNat w 1, only bit 0 is set, so only X^0 = 1 contributes
  let i0 : Fin w := ⟨0, h_w_pos⟩
  have h_i0_val : i0.val = 0 := by rfl
  -- Use h_ite pattern: show each term equals if b = i0 then 1 else 0
  have h_ite: ∀ b : Fin w, (if (BitVec.ofNat w 1).getLsb b then (X : (ZMod 2)[X])^b.val else 0) =
      if b = i0 then 1 else 0 := by
    intro b
    by_cases h_eq : b = i0
    · -- b = i0, so the bit is set and X^0 = 1
      simp only [h_eq, BitVec.getLsb_eq_getElem, Fin.getElem_fin, h_i0_val, BitVec.getElem_one,
        decide_true, ↓reduceIte, pow_zero]
    · -- b ≠ i0, so b.val ≠ 0, so the bit is not set
      have h_val_ne_zero : b.val ≠ 0 := by omega
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_one, decide_eq_true_eq,
        h_eq, ↓reduceIte, ite_eq_right_iff, pow_eq_zero_iff', X_ne_zero, ne_eq, false_and,
        imp_false]
      exact h_val_ne_zero
  simp only [h_ite]
  rw [Finset.sum_eq_single (a := i0) (h₀ := fun b hb_univ hb_ne_i0 => by
    simp only [hb_ne_i0, ↓reduceIte]
  ) (h₁ := fun h_i0_ne_mem_univ => by
    simp only [Finset.mem_univ, not_true_eq_false] at h_i0_ne_mem_univ
  )]
  simp only [↓reduceIte]

lemma toPoly_zero_eq_zero {w : Nat} : toPoly (BitVec.ofNat w 0) = 0 := by
  unfold toPoly
  apply Finset.sum_eq_zero
  intro i hi_mem_univ
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_zero, Bool.false_eq_true,
    ↓reduceIte]

lemma toPoly_ne_zero_iff_ne_zero {w : Nat} (v : BitVec w) :
  toPoly v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro hToPoly_ne_zero
    by_contra h_v_eq_zero
    have h_toPoly_zero : toPoly v = 0 := by
      rw [h_v_eq_zero]; change toPoly (BitVec.ofNat w 0) = 0; rw [toPoly_zero_eq_zero]
    exact hToPoly_ne_zero h_toPoly_zero
  · intro h_v_ne_zero
    by_contra hToPoly_eq_zero
    -- If toPoly v = 0, then all coefficients must be zero
    have h_all_coeff_zero : ∀ i : Fin w, (toPoly v).coeff i.val = 0 := by
      intro i
      rw [hToPoly_eq_zero, Polynomial.coeff_zero]
    -- Extract coefficients: (toPoly v).coeff i.val = if v.getLsb i then 1 else 0
    have h_coeff_formula : ∀ i : Fin w, (toPoly v).coeff i.val = if v.getLsb i then 1 else 0 := by
      intro i
      unfold toPoly
      rw [finset_sum_coeff]
      have h_ite: ∀ b : Fin w, (if v.getLsb b then (X : (ZMod 2)[X])^b.val else 0).coeff i.val =
          if v.getLsb b then (if b = i then 1 else 0) else 0 := by
        intro b
        by_cases h_bit : v.getLsb b
        · -- v.getLsb b = true
          simp only [h_bit, ↓reduceIte]
          rw [Polynomial.coeff_X_pow]
          by_cases h_val_eq : b.val = i.val
          · -- b.val = i.val, so b = i
            have h_b_eq_i : b = i := Fin.ext h_val_eq
            simp only [h_b_eq_i, ↓reduceIte]
          · -- b.val ≠ i.val, so b ≠ i
            have h_b_ne_i : b ≠ i := by
              intro h_eq
              have h_val_eq' : b.val = i.val := by rw [h_eq]
              exact h_val_eq h_val_eq'
            simp only [if_neg (Ne.symm h_val_eq), h_b_ne_i, ↓reduceIte]
        · -- v.getLsb b = false
          split_ifs
          · simp only [coeff_zero]
      simp only [h_ite]
      rw [Finset.sum_eq_single (a := i) (h₀ := fun b hb_univ hb_ne_i => by
        simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, hb_ne_i, ↓reduceIte, ite_self]
      ) (h₁ := fun h_i_ne_mem_univ => by -- impossible
        simp only [Finset.mem_univ, not_true_eq_false] at h_i_ne_mem_univ;)
      ]
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, ↓reduceIte]
    -- Combine: if v.getLsb i then 1 else 0 = 0, so v.getLsb i must be false
    have h_all_bits_false : ∀ i : Fin w, ¬v.getLsb i := by
      intro i
      have h_coeff_eq_zero : (toPoly v).coeff i.val = 0 := h_all_coeff_zero i
      rw [h_coeff_formula i] at h_coeff_eq_zero
      split_ifs at h_coeff_eq_zero with h_bit
      · -- If bit is set, coeff = 1, but we need 0, contradiction
        norm_num at h_coeff_eq_zero
      · -- Bit is not set
        exact h_bit
    -- All bits are false, so v = 0
    have h_v_eq_zero : v = 0 := by
      ext bitIdx
      simp only [BitVec.ofNat_eq_ofNat, BitVec.getElem_zero]
      (expose_names; exact eq_false_of_ne_true (h_all_bits_false ⟨bitIdx, hi⟩))
    exact h_v_ne_zero h_v_eq_zero

/-- ToPoly degree is less than width -/
lemma toPoly_degree_lt_w {w : ℕ} (h_w_pos : w > 0) (v : BitVec w) :
  (toPoly v).degree < w := by
  dsimp only [toPoly, BitVec.getLsb]
  have h_lt: (BitVec.toNat v) < 2^w := BitVec.isLt v
  have h_2_pow_x_gt_0: ∀ x, 2^x > 0 := fun x => by simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos]
  have h_degree_of_sum_le_w_sub_1 : (∑ (x : Fin w),
    if (BitVec.toNat v).testBit ↑x = true
    then (X : (ZMod 2)[X]) ^ (x : ℕ) else 0).degree ≤ ((w - 1) : ℕ) := by
    apply (Polynomial.degree_sum_le _ _).trans
    rw [Finset.sup_le_iff]
    intro x _
    split_ifs
    · rw [Polynomial.degree_X_pow]
      norm_cast
      have h_x_lt : x.val < w := by exact x.isLt
      exact Nat.le_sub_one_of_lt h_x_lt
    · rw [Polynomial.degree_zero]
      exact bot_le
  apply lt_of_le_of_lt h_degree_of_sum_le_w_sub_1
  norm_cast
  exact Nat.sub_one_lt_of_lt h_w_pos

lemma toPoly_degree_of_lt_two_pow {w d : ℕ} (v : BitVec w)
    (hv : v.toNat < 2 ^ d) : (toPoly v).degree < d := by
  dsimp only [toPoly]
  apply (Polynomial.degree_sum_le _ _).trans_lt
  rw [Finset.sup_lt_iff]
  · intro i _
    split_ifs with h_bit
    · -- Term is X^i
      rw [Polynomial.degree_X_pow]
      norm_cast
      -- Goal: i < d
      rw [BitVec.getLsb] at h_bit
      have h_le : 2^i.val ≤ v.toNat := by
        have h_sh_pos : 0 < v.toNat >>> i.val := by
          rw [Nat.pos_iff_ne_zero]
          intro h_z
          simp only [Nat.testBit, h_z, Nat.and_zero, bne_self_eq_false,
            Bool.false_eq_true] at h_bit
        rw [Nat.shiftRight_eq_div_pow] at h_sh_pos
        have h_mul := Nat.mul_le_mul_right (2^i.val) h_sh_pos
        simp only [Nat.succ_eq_add_one, zero_add, one_mul, Nat.ofNat_pos, pow_pos,
          le_mul_iff_one_le_left] at h_mul
        exact Nat.ge_two_pow_of_testBit h_bit
      have h_pow_lt : 2^i.val < 2^d := Nat.lt_of_le_of_lt h_le hv
      apply (Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mp h_pow_lt
    · -- Term is 0
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe d
  · exact compareOfLessAndEq_eq_lt.mp rfl

lemma BitVec_lt_two_pow_of_toPoly_degree_lt {w d : ℕ} (v : BitVec w)
  (h_toPoly_degree_lt : (toPoly v).degree < d) : v.toNat < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro i h_i_ge_d
  by_cases hi_ge_w : i ≥ w
  · refine Nat.testBit_lt_two_pow ?_
    exact BitVec.toNat_lt_twoPow_of_le hi_ge_w
  · by_contra h_v_testBit_i_true
    simp only [Bool.not_eq_false] at h_v_testBit_i_true
    have h_i_lt_w : i < w := by omega
    have h_coeff_one : (toPoly v).coeff i = 1 := by
      unfold toPoly
      rw [finset_sum_coeff]
      rw [Finset.sum_eq_single ⟨i, h_i_lt_w⟩]
      · have h_getLsb_eq_testBit : v.getLsb ⟨i, h_i_lt_w⟩ = v.toNat.testBit i := by
          rfl
        rw [h_getLsb_eq_testBit, h_v_testBit_i_true]
        simp only [↓reduceIte]
        rw [Polynomial.coeff_X_pow]
        split_ifs
        · rfl
        · exfalso
          omega
      · intro b _ hb_ne
        split_ifs with h_bit
        · rw [Polynomial.coeff_X_pow]
          split_ifs with h_b_val_eq_i
          · exfalso
            apply hb_ne
            apply Fin.ext
            simp only
            exact h_b_val_eq_i.symm
          · rfl
        · rw [Polynomial.coeff_zero]
      · intro h_absurd
        simp only [Finset.mem_univ, not_true_eq_false] at h_absurd
    have h_deg_ge : (toPoly v).degree ≥ i := by
      rw [ge_iff_le]
      apply Polynomial.le_degree_of_ne_zero
      rw [h_coeff_one]
      exact Ne.symm (zero_ne_one' (ZMod 2))
    have h_deg_ne_lt : ¬((toPoly v).degree < i) := by
      exact LE.le.not_gt h_deg_ge
    have h_toPoly_v_degree_lt_i : (toPoly v).degree < i := by
      apply lt_of_lt_of_le h_toPoly_degree_lt
      exact Nat.cast_le.mpr h_i_ge_d
    exact h_deg_ne_lt h_toPoly_v_degree_lt_i

-- Lemma: XOR corresponds to Addition
lemma toPoly_xor {w} (a b : BitVec w) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  simp_rw [toPoly]
  rw [← Finset.sum_add_distrib]
  congr 1
  funext i
  have h_getBit_i: (a ^^^ b).getLsb i = ((a.getLsb i) != (b.getLsb i)) := by
    rw [BitVec.getLsb, BitVec.getLsb, BitVec.getLsb, BitVec.toNat_xor]
    rw [Nat.testBit_xor]
  rw [h_getBit_i]
  by_cases ha : a.getLsb i <;> by_cases hb : b.getLsb i
  · -- both true: xor = false, and X^i + X^i = 0 in ZMod 2
    rw [ha, hb]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, CharTwo.add_self_eq_zero]
  · -- a true, b false: xor = true
    have h_b_getLsb_i : b.getLsb i = false := by
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, Bool.not_eq_true] at hb; exact hb
    rw [ha, h_b_getLsb_i]
    simp only [Bool.bne_false, ↓reduceIte, Bool.false_eq_true, add_zero]
  · -- a false, b true: xor = true
    have h_a_getLsb_i : a.getLsb i = false := by
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, Bool.not_eq_true] at ha; exact ha
    rw [h_a_getLsb_i, hb]
    simp only [Bool.bne_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true, zero_add]
  · -- both false: xor = false
    have h_a_getLsb_i : a.getLsb i = false := by
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, Bool.not_eq_true] at ha; exact ha
    have h_b_getLsb_i : b.getLsb i = false := by
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, Bool.not_eq_true] at hb; exact hb
    rw [h_a_getLsb_i, h_b_getLsb_i]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, add_zero]

/--
The "Homomorphism" Lemma.
Since toPoly(a ^^^ b) = toPoly a + toPoly b,
toPoly preserves the structure from Fold-XOR to Sum-Add.
-/
lemma toPoly_fold_xor {α} {w} (s : Finset α) (f : α → (BitVec w)) :
    toPoly (s.fold BitVec.xor 0 f) = ∑ i ∈ s, toPoly (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [BitVec.ofNat_eq_ofNat, Finset.fold_empty, Finset.sum_empty]
    rw [toPoly_zero_eq_zero]
  | cons x s h_not_mem ih =>
    rw [Finset.fold_cons, Finset.sum_cons]
    change toPoly (f x ^^^ s.fold BitVec.xor 0 f) = toPoly (f x) + ∑ i ∈ s, toPoly (f i)
    rw [toPoly_xor]
    rw [ih]

lemma toPoly_128_extend_256 (a : B128) :
    toPoly (to256 a) = toPoly a := by
  unfold toPoly
  -- 1. Split the sum of B256 (0..255) into (0..127) and (128..255)
  let f : Fin 256 → Polynomial (ZMod 2) :=
    fun i => if (to256 a).getLsb i then X ^ i.val else 0
  have h_split_256: 256 = 128 + 128 := by rfl
  conv_lhs =>
    rw! (castMode := .all) [h_split_256]
    rw [Fin.sum_univ_add]
    rw [←Finset.sum_add_distrib]
    simp only [Nat.reduceAdd, Fin.getElem_fin, Fin.coe_castAdd, Fin.natAdd_eq_addNat,
      Fin.coe_addNat]
  apply Finset.sum_congr (h := by rfl)
  intro (i : Fin (128)) hi_mem_univ
  dsimp only [BitVec.getLsb]
  simp_rw [to256_toNat]
  simp only [Fin.coe_castAdd, Fin.coe_addNat, add_eq_left, ite_eq_right_iff, ne_eq, Nat.add_eq_zero,
    Fin.val_eq_zero_iff, Fin.isValue, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
    pow_eq_zero_iff, X_ne_zero, imp_false, Bool.not_eq_true]
  -- ⊢ (BitVec.toNat a).testBit (↑i + 128) = false
  apply Nat.testBit_lt_two_pow
  have h_toNat_lt := BitVec.toNat_lt_twoPow_of_le (n := i.val + 128) (x := a) (h := by omega)
  exact h_toNat_lt

-- Lemma: Left Shift corresponds to Multiplication by X^k
lemma toPoly_shiftLeft_no_overflow {w} {d} (a : BitVec w) (ha : a.toNat < 2 ^ d)
    {shift : ℕ} (h_no_overflow : d + shift ≤ w) :
    toPoly (a <<< shift) = (toPoly a) * X^shift := by
  simp_rw [toPoly]
  rw [Finset.sum_mul]
  have h_w_lhs_eq: w = shift + (d + (w - (shift + d))) := by omega
  conv_lhs =>
    rw! (castMode := .all) [h_w_lhs_eq]
    rw [Fin.sum_univ_add]
    enter [1];
    simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, Fin.coe_castAdd,
      BitVec.getElem_shiftLeft, Fin.is_lt, decide_true, Bool.not_true, Fin.is_le',
      Nat.sub_eq_zero_of_le, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero]
  have h_testBit_out_of_range : ∀ (x : ℕ), a.toNat.testBit (d + x) = false := by
    intro x
    apply Nat.testBit_lt_two_pow
    rw [Nat.pow_add]
    apply lt_of_lt_of_le ha
    simp only [Nat.ofNat_pos, pow_pos, le_mul_iff_one_le_right]; exact Nat.one_le_two_pow
  have h_top_bit_of_a_shl_shift_eq_0: ∀ (i : Fin (w - (shift + d))),
    ((@cast (BitVec w) (BitVec (shift + (d + (w - (shift + d)))))
    (h := by exact congrArg BitVec h_w_lhs_eq) a) <<< shift).getLsb
      (Fin.natAdd shift (Fin.natAdd d i)) = False := by
    intro i
    simp only [BitVec.getLsb, BitVec.toNat_shiftLeft, Fin.coe_natAdd]
    rw [Nat.testBit_mod_two_pow]
    have h_idx_lt : shift + (d + ↑i) < shift + (d + (w - (shift + d))) := by
      apply add_lt_add_right
      apply add_lt_add_right
      exact i.isLt
    simp only [h_idx_lt, decide_true, Bool.true_and]
    rw [Nat.testBit_shiftLeft]
    simp only [le_add_iff_nonneg_right, zero_le, decide_true, add_tsub_cancel_left, Bool.true_and]
    rw [BitVec.toNat_of_cast (h_width_eq := by omega)]
    simp only [eq_iff_iff, iff_false, Bool.not_eq_true]
    rw [h_testBit_out_of_range]
  conv_lhs =>
    rw [Fin.sum_univ_add, zero_add]
    enter [2]; rw [eqRec_eq_cast]; simp only [h_top_bit_of_a_shl_shift_eq_0]
    simp only [↓reduceIte, Finset.sum_const_zero]
  conv_lhs => rw [add_zero]
  have h_w_rhs_eq: w = d + (w - d) := by omega
  have h_top_bit_of_a_eq_0 : ∀ (i : Fin (w - d)), (@cast (BitVec w) (BitVec (d + (w - d)))
    (h := by exact congrArg BitVec h_w_rhs_eq) a).getLsb (Fin.natAdd d i) = False := by
    intro i
    simp only [BitVec.getLsb, Fin.coe_natAdd, eq_iff_iff, iff_false, Bool.not_eq_true]
    rw [BitVec.toNat_of_cast (h_width_eq := by omega)]
    rw [h_testBit_out_of_range]
  conv_rhs =>
    rw! (castMode := .all) [h_w_rhs_eq]
    rw [Fin.sum_univ_add]
    enter [2];
    simp only [Fin.getElem_fin, Fin.coe_natAdd, ite_mul, zero_mul, eqRec_eq_cast]
    simp only [h_top_bit_of_a_eq_0]
    simp only [↓reduceIte, Finset.sum_const_zero]
  simp_rw [BitVec.getLsb]
  simp only [BitVec.toNat_shiftLeft, Fin.coe_natAdd, Fin.coe_castAdd, Nat.testBit_mod_two_pow,
    add_lt_add_iff_left, Nat.testBit_shiftLeft, ge_iff_le, le_add_iff_nonneg_right, zero_le,
    decide_true, add_tsub_cancel_left, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, ite_mul,
    zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro (i: Fin d) h_i_mem_univ
  have h_lhs_cond1: i.val < d + (w - (shift + d)) := by omega
  simp only [h_lhs_cond1, true_and, eqRec_eq_cast]
  conv_lhs => rw [BitVec.toNat_of_cast (h_width_eq := by omega)]
  conv_rhs => rw [BitVec.toNat_of_cast (h_width_eq := by omega)]
  by_cases h_bit: a.toNat.testBit i.val = true
  · simp only [h_bit, ↓reduceIte, pow_add, mul_comm]
  · simp only [h_bit, Bool.false_eq_true, ↓reduceIte]

/--
Generalized No-Overflow Multiplication.
Safe to use whenever the bit-widths sum to ≤ 257.
This covers both squaring (128+128=256) and reduction check (128+129=257).
-/
lemma toPoly_clMul_no_overflow {da db : ℕ} (a b : B256)
    (ha : a.toNat < 2 ^ da)
    (hb : b.toNat < 2 ^ db)
    (h_sum : da + db ≤ 257) :
    toPoly (clMul a b) = toPoly a * toPoly b := by

  rw [clMul_eq_fold]
  rw [toPoly_fold_xor]

  conv_rhs => rw [toPoly]
  rw [Finset.sum_mul]

  apply Finset.sum_congr rfl
  intro i _

  split_ifs with h_bit
  · rw [mul_comm]
    rw [toPoly_shiftLeft_no_overflow (d := db) (ha := hb)]
    · have h_i_lt_da : i.val < da := by
        simp only [BitVec.getLsb] at h_bit
        by_contra h_i_ge_da
        simp only [not_lt] at h_i_ge_da
        have h_testBit_lt_2_pow := Nat.testBit_lt_two_pow (i := i) (x := BitVec.toNat a)
          (lt := by
            apply lt_of_lt_of_le (b := 2^da) (by omega) (by
              apply Nat.pow_le_pow_right (hx := by omega) (by omega)))
        rw [h_testBit_lt_2_pow] at h_bit
        exact (Bool.eq_not_self false).mp h_bit
      omega

  · simp [toPoly_zero_eq_zero]

/-- Helper lemma to chain the modular squaring steps -/
lemma chain_step {P : Polynomial (ZMod 2)} (hP : P ≠ 0) {k : ℕ}
    {prev next : Polynomial (ZMod 2)} {q_val : B128}
    (h_prev : X ^ (2 ^ k) % P = prev % P)
    (h_step : prev ^ 2 = (toPoly (to256 q_val)) * P + next) :
    X^(2^(k+1)) % P = next % P := by
  rw [pow_succ', pow_mul, ←pow_mul, mul_comm, pow_mul, pow_two]
  rw [CanonicalEuclideanDomain.mul_mod_eq (hn := hP), h_prev]
  rw [←CanonicalEuclideanDomain.mul_mod_eq (hn := hP), ←pow_two]
  conv_lhs => rw [h_step, toPoly_128_extend_256]
  conv_lhs => rw [CanonicalEuclideanDomain.add_mod_eq (hn := hP)]
  conv_lhs => rw [CanonicalEuclideanDomain.mul_mod_eq (hn := hP)]
  conv_lhs => simp only [EuclideanDomain.mod_self, mul_zero, zero_add]
  conv_lhs => rw [EuclideanDomain.zero_mod, zero_add]
  rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := hP)]

end PolynomialIsomorphism

/-! ## Section 5: GCD Verification Helpers -/

section VerificationHelpers

-- Helper for GCD Chaining
-- If a = q * b + r, then gcd(a, b) = gcd(b, r)
lemma gcd_eq_gcd_next_step {a b q r : Polynomial (ZMod 2)} (hb : b ≠ 0) (h : a = q * b + r) :
  EuclideanDomain.gcd a b = EuclideanDomain.gcd b r := by
  rw [ZMod2Poly.euclidean_gcd_comm]
  rw [EuclideanDomain.gcd_val]
  conv_lhs =>
    rw [h, ZMod2Poly.euclidean_gcd_comm, CanonicalEuclideanDomain.add_mod_eq (hn := hb)]
    rw [CanonicalEuclideanDomain.mul_mod_eq (hn := hb),
      EuclideanDomain.mod_self, mul_zero, EuclideanDomain.zero_mod]
    rw [zero_add, CanonicalEuclideanDomain.mod_mod_eq_mod (hn := hb)]
  conv_rhs => rw [EuclideanDomain.gcd_val, ZMod2Poly.euclidean_gcd_comm]

-- gcd(1, 0) = 1
lemma gcd_one_zero : EuclideanDomain.gcd (1 : Polynomial (ZMod 2)) 0 = 1 := by
  exact EuclideanDomain.gcd_one_left 0

end VerificationHelpers

end BinaryField
