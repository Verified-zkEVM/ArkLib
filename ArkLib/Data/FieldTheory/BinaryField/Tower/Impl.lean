/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.FieldTheory.BinaryField.Tower.Basic
import ArkLib.Data.Math.DepCast

/-!
# Computable Binary Tower Fields

This file provides executable implementations for binary tower fields

## Main Definitions

- `ConcreteBinaryTower k`: the concrete binary tower fields of level k whose elements are
  reprensented via bit vectors of size 2^k

## TODOs
- Proof of mul_inv_cancel
- Optimization of multiplication via lookup
- Proof of isomorphism with the abstract binary tower fields and derive theorems about multilinear
  basis

## References

- [Wie88] Doug Wiedemann. "An Iterated Quadratic Extension of GF(2)" In: The Fibonacci Quarterly
  26.4 (1988), pp. 290–295.

- [FP97] John L. Fan and Christof Paar. "On efficient inversion in tower fields of characteristic
  two". In: Proceedings of IEEE International Symposium on Information Theory. 1997.
-/

namespace BinaryTower
namespace ConcreteDefinition
open Polynomial

section BaseDefinitions

def ConcreteBinaryTower : ℕ → Type := fun k => BitVec (2^k)

section BitVecDepCast
instance BitVec.instDepCast : DepCast Nat BitVec where
  dcast h := BitVec.cast h
  dcast_id := by
    intro n
    funext bv -- bv: BitVec n
    rw [BitVec.cast_eq, id_eq]

theorem BitVec.bitvec_cast_eq_dcast {n m : Nat} (h : n = m) (bv : BitVec n) :
  BitVec.cast h bv = DepCast.dcast h bv := by
  simp only [BitVec.cast, BitVec.instDepCast]

theorem BitVec.dcast_id {n : Nat} (bv : BitVec n) :
  DepCast.dcast (Eq.refl n) bv = bv := by
  simp only [BitVec.instDepCast.dcast_id, id_eq]

theorem BitVec.dcast_bitvec_eq {l r val: ℕ} (h_width_eq: l = r):
    dcast h_width_eq (BitVec.ofNat l val) = BitVec.ofNat r val := by
  subst h_width_eq
  rw [dcast_eq]

@[simp] theorem BitVec.cast_zero {n m: ℕ} (h : n = m) : BitVec.cast h 0 = 0 := rfl
@[simp] theorem BitVec.cast_one {n m: ℕ} (h : n = m) : BitVec.cast h 1 = 1#m := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.cast_ofNat]
@[simp] theorem BitVec.dcast_zero {n m: ℕ} (h : n = m) : DepCast.dcast h (0#n) = 0#m := rfl
@[simp] theorem BitVec.dcast_one {n m: ℕ} (h : n = m) : DepCast.dcast h (1#n) = 1#m := by
  rw [←BitVec.bitvec_cast_eq_dcast]
  exact BitVec.cast_one (h:=h)

theorem BitVec.dcast_bitvec_toNat_eq {w w2: ℕ} (x: BitVec w) (h_width_eq: w = w2):
    BitVec.toNat x = BitVec.toNat (dcast (h_width_eq) x) := by
  subst h_width_eq
  rw [dcast_eq]

theorem BitVec.dcast_bitvec_eq_zero {l r: ℕ} (h_width_eq: l = r):
  dcast (h_width_eq) 0#(l) = 0#(r) := by
  exact BitVec.dcast_bitvec_eq (l:=l) (r:=r) (val:=0) (h_width_eq:=h_width_eq)

theorem BitVec.dcast_bitvec_extractLsb_eq {w hi1 lo1 hi2 lo2 : ℕ} (x: BitVec w) (h_lo_eq: lo1 = lo2)
  (h_width_eq: hi1 - lo1 + 1 = hi2 - lo2 + 1):
  dcast h_width_eq (BitVec.extractLsb (hi:=hi1) (lo:=lo1) x)
    = BitVec.extractLsb (hi:=hi2) (lo:=lo2) (x) := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  have xToNat_eq: x.toNat >>> lo1 = x.toNat >>> lo2 := by rw [h_lo_eq]
  rw [xToNat_eq]
  rw! [h_width_eq]
  rw [BitVec.dcast_id]

theorem BitVec.dcast_dcast_bitvec_extractLsb_eq {w hi lo: ℕ} (x: BitVec w)
  (h_width_eq: w = hi - lo + 1): dcast h_width_eq (dcast (h_width_eq.symm)
  (BitVec.extractLsb (hi:=hi) (lo:=lo) x)) = BitVec.extractLsb (hi:=hi) (lo:=lo) x := by
  simp only [dcast, BitVec.cast_cast, BitVec.cast_eq]

theorem BitVec.eq_mp_eq_dcast {w w2: ℕ} (x: BitVec w) (h_width_eq: w = w2)
  (h_bitvec_eq: BitVec w = BitVec w2 := by rw [h_width_eq]):
  Eq.mp (h:=h_bitvec_eq) (a:=x) = dcast (h_width_eq) (x) := by
  rw [eq_mp_eq_cast] -- convert Eq.mp into root.cast
  rw [dcast_eq_root_cast]

theorem BitVec.extractLsb_concat_hi {hi_size lo_size : ℕ} (hi : BitVec hi_size)
  (lo : BitVec lo_size) (h_hi: hi_size > 0):
  BitVec.extractLsb (hi:=hi_size + lo_size - 1) (lo:=lo_size)
  (BitVec.append (msbs:=hi) (lsbs:=lo)) = dcast (by
    rw [←Nat.sub_add_comm (by omega), Nat.sub_add_cancel (by omega), Nat.add_sub_cancel]
  ) hi := by
  simp only [BitVec.extractLsb]
  simp [BitVec.extractLsb'_append_eq_of_le (Nat.le_refl lo_size)]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]
  have hi_eq: hi = BitVec.ofNat hi_size (hi.toNat) := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hi_eq]
  rw [dcast_bitvec_eq] -- un-dcast
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem BitVec.extractLsb_concat_lo {hi_size lo_size : ℕ} (hi : BitVec hi_size)
  (lo : BitVec lo_size) (h_lo: lo_size > 0): BitVec.extractLsb (hi:=lo_size-1) (lo:=0)
  (BitVec.append (msbs:=hi) (lsbs:=lo)) = dcast (by
    rw [←Nat.sub_add_comm (h:=by omega), Nat.sub_add_cancel (h:=by omega), Nat.sub_zero]
  ) lo := by
  simp only [BitVec.extractLsb]
  simp [BitVec.extractLsb'_append_eq_ite (start:=0) (len:=lo_size)]
  simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]
  have lo_eq: lo = BitVec.ofNat lo_size (lo.toNat) := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [lo_eq]
  rw [dcast_bitvec_eq] -- un-dcast
  simp only [dcast_bitvec_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- ⊢ BitVec.setWidth (n - 1 + 1) (hi ++ lo) = BitVec.setWidth (n - 1 + 1) lo
  rw [BitVec.setWidth_append]
  have h_le: lo_size - 1 + 1 ≤ lo_size := by rw [Nat.sub_add_cancel (by omega)]
  simp only [h_le, ↓reduceDIte]

theorem Nat.shiftRight_eq_sub_mod_then_div_two_pow {n lo_len : ℕ}:
  n >>> lo_len = (n - n % 2^lo_len) / 2^lo_len := by
  rw [Nat.shiftRight_eq_div_pow]
  rw (occs := .pos [1]) [Nat.div_eq_sub_mod_div]

theorem Nat.shiftRight_lo_mod_2_pow_hi_shiftLeft_lo (n hi_len lo_len : ℕ)
  (h_n: n < 2^(hi_len + lo_len)):
  (((n >>> lo_len) % (2^hi_len)) <<< lo_len) = (n - n % 2^lo_len) := by
  rw [Nat.shiftLeft_eq]
  have n_shr_lo_mod_2_pow_hi: (n >>> lo_len) % 2 ^ hi_len = n >>> lo_len := by
    have shr_lt: n >>> lo_len < 2^hi_len := by
      rw [Nat.shiftRight_eq_div_pow]
      have n_lt: n < 2 ^ lo_len * 2 ^ hi_len := by
        rw [←Nat.pow_add]
        rw [Nat.add_comm]
        exact h_n
      exact Nat.div_lt_of_lt_mul n_lt
    have shr_mod: (n >>> lo_len) % 2 ^ hi_len = n >>> lo_len := by
      rw [Nat.mod_eq_of_lt]
      exact shr_lt
    rw [shr_mod]

  rw [n_shr_lo_mod_2_pow_hi] -- ⊢ n = n >>> lo_len * 2 ^ lo_len + n % 2 ^ lo_len
  rw [Nat.shiftRight_eq_div_pow]
  -- ⊢ n = n / 2 ^ lo_len * 2 ^ lo_len + n % 2 ^ lo_len
  have n_div_eq: (n / 2^lo_len) = (n - n % 2^lo_len) / 2^lo_len := by
    exact Nat.div_eq_sub_mod_div
  rw [n_div_eq]
  have h_div1: 2 ^ lo_len ∣ n - n % 2 ^ lo_len := by
    exact Nat.dvd_sub_mod n
  rw [Nat.div_mul_cancel h_div1]

theorem Nat.reconstruct_from_hi_and_lo_parts (n hi_len lo_len : ℕ) (h_n: n < 2^(hi_len + lo_len)):
    n = (((n >>> lo_len) % (2^hi_len)) <<< lo_len) + (n % (2^lo_len)) := by
  rw [Nat.shiftRight_lo_mod_2_pow_hi_shiftLeft_lo (n:=n) (hi_len:=hi_len)
    (lo_len:=lo_len) (h_n:=h_n)]
  -- ⊢ n = n - n % 2 ^ lo_len + n % 2 ^ lo_len
  have h_mod_le: n % 2 ^ lo_len ≤ n := by
    exact Nat.mod_le n (2^lo_len)
  rw [Nat.sub_add_cancel h_mod_le]

theorem Nat.reconstruct_from_hi_and_lo_parts_or_ver (n hi_len lo_len : ℕ)
  (h_n: n < 2^(hi_len + lo_len)):
    n = (((n >>> lo_len) % (2^hi_len)) <<< lo_len) ||| (n % (2^lo_len)) := by
  rw (occs := .pos [1]) [Nat.reconstruct_from_hi_and_lo_parts (n:=n) (hi_len:=hi_len)
    (lo_len:=lo_len) (h_n:=h_n)]
  -- ⊢ (n >>> lo_len % 2 ^ hi_len) <<< lo_len + n % 2 ^ lo_len
  -- = (n >>> lo_len % 2 ^ hi_len) <<< lo_len ||| n % 2 ^ lo_len
  rw [Nat.shiftLeft_add_eq_or_of_lt (a:=n >>> lo_len % 2 ^ hi_len) (b:=n % 2 ^ lo_len)
    (b_lt:=by exact Nat.mod_lt n (by norm_num))]

theorem BitVec.eq_append_iff_extract {lo_size hi_size: ℕ} (lo: BitVec lo_size) (hi: BitVec hi_size)
  (h_hi_gt_0: hi_size > 0) (h_lo_gt_0: lo_size > 0) (x: BitVec (hi_size + lo_size)):
  x = dcast (by rfl) (BitVec.append (msbs:=hi) (lsbs:=lo)) ↔
  hi = dcast (by omega) (BitVec.extractLsb (hi:=hi_size+lo_size-1) (lo:=lo_size) x) ∧
  lo = dcast (by omega) (BitVec.extractLsb (hi:=lo_size-1) (lo:=0) x) := by
  -- idea: use BitVec.extractLsb_concat_hi and BitVec.extractLsb_concat_lo
  have h_hi := dcast_symm (hb:=(BitVec.extractLsb_concat_hi (hi:=hi) (lo:=lo)
    (h_hi:=h_hi_gt_0)).symm)
  have h_lo := dcast_symm (hb:=(BitVec.extractLsb_concat_lo (hi:=hi) (lo:=lo)
    (h_lo:=h_lo_gt_0)).symm)
  constructor
  · intro h_x -- x = dcast ⋯ (hi.append lo)
    rw [h_x]
    apply And.intro
    · -- rewrite only the first goal
      rw (occs := .pos [1]) [←h_hi]
      unfold BitVec.extractLsb BitVec.extractLsb'
      rw [←dcast_bitvec_toNat_eq] -- cancel INNER dcast via BitVec.toNat
    · rw (occs := .pos [1]) [←h_lo]
      unfold BitVec.extractLsb BitVec.extractLsb'
      rw [←dcast_bitvec_toNat_eq] -- cancel INNER dcast via BitVec.toNat
  · -- Right to left
    intro h_extract_eq_parts
    obtain ⟨h_hi_eq_extract, h_lo_eq_extract⟩ := h_extract_eq_parts
    apply BitVec.eq_of_toNat_eq (x:=x) (y:=(BitVec.append (n:=hi_size)
      (m:=lo_size) (msbs:=hi) (lsbs:=lo)))
    rw [BitVec.append_eq, BitVec.toNat_append]
    -- Convert goal to Nat equality: ⊢ x.toNat = hi.toNat <<< lo_size ||| lo.toNat
    rw [h_hi_eq_extract, h_lo_eq_extract]
    -- convert all BitVec.toNat (dcast bitvec) to Nat
    rw [←BitVec.dcast_bitvec_toNat_eq, ←BitVec.dcast_bitvec_toNat_eq]
    rw [BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', BitVec.extractLsb']
    rw [Nat.shiftRight_zero]
    rw [BitVec.ofNat_toNat]
    rw [BitVec.toNat_ofNat, Nat.sub_zero, BitVec.toNat_setWidth]
    -- ⊢ x.toNat = (x.toNat >>> lo_size % 2 ^ (hi_size + lo_size - 1 - lo_size + 1))
      --- <<< lo_size ||| x.toNat % 2 ^ (lo_size - 1 + 1)
    have h0: lo_size ≤ hi_size + lo_size - 1 := by omega
    have h1: 2 ^ (hi_size + lo_size - 1 - lo_size + 1) = 2 ^ hi_size := by
      rw [←Nat.sub_add_comm (h:=h0)]
      simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀]
      omega
    have h2: lo_size - 1 + 1 = lo_size := by rw [Nat.sub_add_cancel (h_lo_gt_0)]
    rw [h1, h2] -- ⊢ x.toNat = (x.toNat >>> lo_size % 2 ^ hi_size)
      --- <<< lo_size ||| x.toNat % 2 ^ lo_size
    exact Nat.reconstruct_from_hi_and_lo_parts_or_ver (n:=x.toNat)
      (hi_len:=hi_size) (lo_len:=lo_size) (h_n:=by exact BitVec.isLt (x:=x))

end BitVecDepCast

def bitVecToString (width : ℕ) (bv : BitVec width) : String :=
  Fin.foldl width (fun (s : String) (idx : Fin width) =>
    -- idx is the MSB-oriented loop index (0 to width-1)
    -- Fin.rev idx converts it to an LSB-oriented index
    s.push (if BitVec.getLsb' bv (Fin.rev idx) then '1' else '0')
  ) ""

def ConcreteBinaryTower.toBitString {k: ℕ} (bv: ConcreteBinaryTower k): String :=
  bitVecToString (2^k) (bv)

-- Helper: Bit width for ConcreteBinaryTower
def width (k : ℕ) : ℕ := 2^k

-- Convert Nat to ConcreteBinaryTower
def fromNat {k : ℕ} (n : Nat) : ConcreteBinaryTower k :=
  BitVec.ofNat (2^k) n

@[simp] theorem fromNat_toNat_eq_self {k : ℕ} (bv : BitVec (2^k)) :
  (fromNat (BitVec.toNat bv) : ConcreteBinaryTower k) = bv := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, fromNat, ConcreteBinaryTower]

instance ConcreteBinaryTower.instDepCast_local : DepCast ℕ ConcreteBinaryTower where
  dcast h_k_eq term_k1 := BitVec.cast (congrArg (fun n => 2^n) h_k_eq) term_k1
  dcast_id := by
    intro k_idx; funext x
    simp only [id_eq, BitVec.cast, BitVec.ofNatLT_toNat]

-- Zero element
def zero {k : ℕ} : ConcreteBinaryTower k := BitVec.zero (2^k)

-- One element
def one {k : ℕ} : ConcreteBinaryTower k := 1#(2^k)

instance instZeroConcreteBinaryTower (k : ℕ) : Zero (ConcreteBinaryTower k) where
  zero := zero
instance instOneConcreteBinaryTower (k : ℕ) : One (ConcreteBinaryTower k) where
  one := one

-- Generic OfNat instance for ConcreteBinaryTower
-- instance (k : ℕ) (n : Nat): OfNat (ConcreteBinaryTower k) n where
  -- ofNat := fromNat n

-- Special element Z_k for each level k
def Z (k : ℕ) : ConcreteBinaryTower k :=
  if k = 0 then one
  else BitVec.ofNat (2^k) (1 <<< 2^(k-1))
  -- fromNat (2^(2^(k-1)))
    -- For k > 0, Z_k is defined based on the irreducible polynomial
    -- TODO: Define Z_k properly for k > 0

-- Algebraic map from level k to level k+1
def algebraMap {k : ℕ} : ConcreteBinaryTower k → ConcreteBinaryTower (k+1) :=
  fun x => fromNat (BitVec.toNat x)

-- Define the irreducible polynomial for level k
noncomputable def definingPoly {k : ℕ} [Semiring (ConcreteBinaryTower k)] :
  Polynomial (ConcreteBinaryTower k) :=
  -- it depends on 'Polynomial.add'', and it does not have executable code
  X^2 + (C (Z k) * X + 1)

-- Basic operations
def add {k : ℕ} (x y : ConcreteBinaryTower k) : ConcreteBinaryTower k := BitVec.xor x y
def neg {k : ℕ} (x : ConcreteBinaryTower k) : ConcreteBinaryTower k := x

-- Type class instances
instance (k : ℕ) : HAdd (ConcreteBinaryTower k) (ConcreteBinaryTower k) (ConcreteBinaryTower k)
  where hAdd := add

-- Type class instances
instance (k : ℕ) : Add (ConcreteBinaryTower k) where
  add := add

-- instance (k: ℕ) : OfNat (ConcreteBinaryTower k) 0 where
  -- ofNat := zero
-- instance (k: ℕ) : OfNat (ConcreteBinaryTower k) 1 where
  -- ofNat := one

theorem sum_fromNat_eq_from_xor_Nat {k : ℕ} (x y : Nat) :
  fromNat (k:=k) (x ^^^ y) = fromNat (k:=k) x + fromNat (k:=k) y := by
  unfold fromNat
  simp only [instHAddConcreteBinaryTower, add, BitVec.xor_eq]
  rw [BitVec.ofNat_xor]

-- Basic lemmas for addition
lemma add_self_cancel {k : ℕ} (a : ConcreteBinaryTower k) : a + a = 0 := by
  exact BitVec.xor_self (x:=a)

lemma add_eq_zero_iff_eq {k : ℕ} (a b : ConcreteBinaryTower k) : a + b = 0 ↔ a = b := by
  exact BitVec.xor_eq_zero_iff

lemma add_assoc {k: ℕ}: ∀ (a b c : ConcreteBinaryTower k), a + b + c = a + (b + c) := by
  exact BitVec.xor_assoc

-- Addition is commutative
lemma add_comm {k : ℕ} (a b : ConcreteBinaryTower k) : a + b = b + a := by
  exact BitVec.xor_comm a b

-- Zero is identity
lemma zero_add {k : ℕ} (a : ConcreteBinaryTower k) : 0 + a = a := by
  exact BitVec.zero_xor (x:=a)

lemma add_zero {k : ℕ} (a : ConcreteBinaryTower k) : a + 0 = a := by
  exact BitVec.xor_zero (x:=a)

-- Negation is additive inverse (in char 2, neg = id)
lemma neg_add_cancel {k : ℕ} (a : ConcreteBinaryTower k) : neg a + a = 0 := by
  exact BitVec.xor_self (x:=a)

lemma if_self_rfl {α : Type*} [DecidableEq α] (a b : α) :
  (if a = b then b else a) = a := by
  by_cases h : a = b
  · rw [if_pos h, h]
  · rw [if_neg h]


-- Isomorphism between ConcreteBinaryTower 0 and GF(2)
-- Ensure GF(2) has decidable equality
noncomputable instance : DecidableEq (GF(2)) :=
  fun x y =>
    -- Use the isomorphism between GF(2) and ZMod 2
    let φ : GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2
    -- ZMod 2 has decidable equality
    if h : φ x = φ y then
      isTrue (by
        -- φ is injective, so φ x = φ y implies x = y
        exact φ.injective h)
    else
      isFalse (by
        intro h_eq
        -- If x = y, then φ x = φ y
        apply h
        exact congrArg φ h_eq)

instance (k : ℕ) : DecidableEq (ConcreteBinaryTower k) :=
  fun x y =>
    let p := BitVec.toNat x = BitVec.toNat y
    let q := x = y
    let hp : Decidable p := Nat.decEq (BitVec.toNat x) (BitVec.toNat y)
    let h_iff_pq : p ↔ q := (BitVec.toNat_eq).symm -- p is (toNat x = toNat y), q is (x = y)
    match hp with
    | isTrue (proof_p : p) =>
      -- We have a proof of p (toNat x = toNat y). We need a proof of q (x = y).
      -- h_iff_pq.mp gives p → q. So, (h_iff_pq.mp proof_p) is a proof of q.
      isTrue (h_iff_pq.mp proof_p)
    | isFalse (nproof_p : ¬p) =>
      -- We have a proof of ¬p. We need a proof of ¬q (which is q → False).
      -- So, assume proof_q : q. We need to derive False.
      -- h_iff_pq.mpr gives q → p. So, (h_iff_pq.mpr proof_q) is a proof of p.
      -- This contradicts nproof_p.
      isFalse (fun (proof_q : q) => nproof_p (h_iff_pq.mpr proof_q))

noncomputable def toConcreteBTF0 : GF(2) → ConcreteBinaryTower 0 :=
  fun x => if decide (x = 0) then zero else one -- it depends on 'instFieldGaloisField'

noncomputable def fromConcreteBTF0 : ConcreteBinaryTower 0 → (GF(2)) :=
  fun x => if decide (x = zero) then 0 else 1

lemma nsmul_succ {k : ℕ} (n : ℕ) (x : ConcreteBinaryTower k) :
  (if ↑n.succ % 2 = 0 then zero else x) = (if ↑n % 2 = 0 then zero else x) + x := by
  have h : ↑n.succ % 2 = (↑n % 2 + 1) % 2 := by
    simp [Nat.cast_succ]
  have zero_is_0: (zero: ConcreteBinaryTower k) = 0 := by rfl
  have h_n_mod_le: n % 2 < 2 := Nat.mod_lt n (by norm_num)
  match h_n_mod: n % 2 with
  | Nat.zero =>
    rw [h]
    have h1 : (n + 1) % 2 = 1 := by simp [Nat.add_mod, h_n_mod, zero_add]
    simp [h1]; rw [(add_zero x).symm]; rw [←add_assoc, ←add_comm];
    rw [zero_is_0];
    rw [zero_add];
    rw [add_zero]
  | Nat.succ x' => -- h_n_mod : n % 2 = x'.succ
    match x' with
    | Nat.zero => -- h_n_mod : n % 2 = Nat.zero.succ => h_n_mod automatically updates
      rw [h]
      have h_n_mod_eq_1 : n % 2 = 1 := by rw [h_n_mod]
      rw [h_n_mod_eq_1]
      have h1 : (1 + 1 : ℤ) % 2 = 0 := by norm_num
      simp [h1]
      rw [zero_is_0, add_self_cancel]
    | Nat.succ _ => -- h_n_mod : n % 2 = n✝.succ.succ
      have h_n_mod_ge_2 : n % 2 ≥ 2 := by
        rw [h_n_mod]
        apply Nat.le_add_left
      rw [h_n_mod] at h_n_mod_le
      linarith

lemma zsmul_succ {k : ℕ} (n : ℕ) (x : ConcreteBinaryTower k) :
  (if (↑n.succ: ℤ) % 2 = 0 then zero else x) = (if (↑n: ℤ) % 2 = 0 then zero else x) + x := by
  norm_cast
  exact nsmul_succ n x

lemma neg_mod_2_eq_0_iff_mod_2_eq_0 {n : ℤ} : (-n) % 2 = 0 ↔ n % 2 = 0 := by
  constructor
  · intro h
    apply Int.dvd_iff_emod_eq_zero.mp
    apply Int.dvd_neg.mp
    exact Int.dvd_iff_emod_eq_zero.mpr h
  · intro h
    apply Int.dvd_iff_emod_eq_zero.mp
    apply Int.dvd_neg.mpr
    exact Int.dvd_iff_emod_eq_zero.mpr h

-- Int.negSucc n = -(n+1)
lemma zsmul_neg' {k : ℕ} (n : ℕ) (a : ConcreteBinaryTower k) :
  (if ((Int.negSucc n):ℤ) % (2:ℤ) = (0:ℤ) then zero else a) =
    neg (if (↑n.succ: ℤ) % (2:ℤ) = (0:ℤ) then zero else a) :=
by
  have negSucc_eq_minus_of_n_plus_1: Int.negSucc n = -(n + 1) := by rfl
  rw [negSucc_eq_minus_of_n_plus_1]
  have n_succ_eq_n_plus_1: (↑n.succ: ℤ) = (↑n: ℤ) + 1 := by rfl
  rw [n_succ_eq_n_plus_1]
  -- Split on two cases of the `if ... else` statement
  by_cases h : (n + 1) % 2 = 0
  { -- h: (n + 1) % 2 = 0
    have n_succ_mod_2_eq_0: ((↑n: ℤ) + 1) % 2 = 0 := by norm_cast
    rw [n_succ_mod_2_eq_0]
    -- ⊢ (if -(↑n + 1) % 2 = 0 then zero else a) = neg (if 0 = 0 then zero else a)
    have neg_n_succ_mod_2_eq_0: (-((↑n: ℤ) + 1)) % 2 = 0 := by
      exact (neg_mod_2_eq_0_iff_mod_2_eq_0 (n:=((n: ℤ) + 1))).mpr n_succ_mod_2_eq_0
    -- ⊢ (if 0 = 0 then zero else a) = neg (if 0 = 0 then zero else a)
    rw [neg_n_succ_mod_2_eq_0]
    simp
    rfl
  }
  { -- h : ¬(n + 1) % 2 = 0
    push_neg at h -- h : (n + 1) % 2 ≠ 0
    have n_succ_mod_2_ne_1: ((↑n: ℤ) + 1) % 2 = 1 := by
      have h_mod : (n + 1) % 2 = 1 := by -- prove the ℕ-version of the hypothesis & use norm_cast
        have tmp := Nat.mod_two_eq_zero_or_one (n:=n+1)
        match tmp with
        | Or.inl h_mod_eq_0 =>
          rw [h_mod_eq_0]
          contradiction
        | Or.inr h_mod_eq_1 =>
          rw [h_mod_eq_1]
      norm_cast
    rw [n_succ_mod_2_ne_1]
    have neg_n_succ_mod_2_ne_0: (-((↑n: ℤ) + 1)) % 2 ≠ 0 := by
      by_contra h_eq_0
      have neg_succ_mod_2_eq_0: ((↑n: ℤ) + 1) % 2 = 0 :=
        (neg_mod_2_eq_0_iff_mod_2_eq_0 (n:=((n: ℤ) + 1))).mp h_eq_0
      have neg_succ_mod_2_eq_0_nat: (n + 1) % 2 = 0 := by
        have : ↑((n + 1) % 2) = ((↑n : ℤ) + 1) % 2 := by norm_cast
        rw [neg_succ_mod_2_eq_0] at this
        apply Int.ofNat_eq_zero.mp -- simp [Int.ofNat_emod]
        exact this
      rw [neg_succ_mod_2_eq_0_nat] at h
      contradiction
    -- ⊢ (if -(↑n + 1) % 2 = 0 then zero else a) = neg (if 1 = 0 then zero else a)
    rw [if_neg one_ne_zero, neg]
    rw [if_neg neg_n_succ_mod_2_ne_0]
  }

instance (k : ℕ) : AddCommGroup (ConcreteBinaryTower k) where
  toZero := inferInstance
  neg := neg
  sub := fun x y => add x y
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := fun n x => if n % 2 = (0:ℕ) then zero else x
  zsmul := fun (n:ℤ) x => if n % 2 = 0 then zero else x  -- Changed to n : ℤ
  neg_add_cancel := neg_add_cancel
  nsmul_succ := nsmul_succ
  zsmul_succ' := fun n a => zsmul_succ n a
  add := add
  zsmul_neg' := zsmul_neg' (k := k)

lemma zero_is_0 {k: ℕ}: (zero (k:=k)) = (0: ConcreteBinaryTower k) := by rfl
lemma one_is_1 {k: ℕ}: (one (k:=k)) = 1 := by rfl
lemma concrete_one_ne_zero {k : ℕ} : (one (k:=k)) ≠ (zero (k:=k)) := by
  intro h_eq
  have h_toNat_eq : (one (k:=k)).toNat = (zero (k:=k)).toNat := congrArg BitVec.toNat h_eq
  simp [one, zero, BitVec.toNat_ofNat] at h_toNat_eq

instance {k: ℕ}: NeZero (1 : ConcreteBinaryTower k) := by
  unfold ConcreteBinaryTower
  exact {out := concrete_one_ne_zero (k:=k) }

section NumericLemmas

lemma one_le_sub_middle_of_pow2 {k: ℕ} (h_k: 1 ≤ k): 1 ≤ 2 ^ k - 2 ^ (k - 1) := by
  have l1: 2 ^ (k - 1 + 1) = 2^k := by congr 1; omega
  have res := one_le_sub_consecutive_two_pow (n:=k-1)
  rw [l1] at res
  exact res

lemma sub_middle_of_pow2_with_one_canceled {k: ℕ} (h_k: 1 ≤ k): 2 ^ k - 1 - 2 ^ (k - 1) + 1
  = 2 ^ (k - 1) := by
  calc 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ k - 2 ^ (k - 1) - 1 + 1 := by omega
    _ = 2 ^ k - 2 ^ (k - 1) := by
      rw [Nat.sub_add_cancel];exact one_le_sub_middle_of_pow2 (h_k:=h_k)
    _ = 2^(k-1) * 2 - 2 ^ (k - 1):= by
      congr 1
      rw [← Nat.pow_succ]
      congr
      simp only [Nat.succ_eq_add_one]
      rw [Nat.sub_add_cancel]
      omega
    _ = 2^(k-1) + 2^(k-1) - 2^(k-1) := by rw [Nat.mul_two]
    _ = 2^(k-1) := Nat.add_sub_self_left (2 ^ (k - 1)) (2 ^ (k - 1))

lemma h_sub_middle {k: ℕ} (h_pos: k > 0): 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ (k - 1) := by
  exact sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=h_pos)

lemma h_middle_sub {k: ℕ}: 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) := by
  rw [Nat.sub_zero, Nat.sub_add_cancel (h:=one_le_two_pow_n (n:=k-1))]

lemma h_sum_two_same_pow2 {k: ℕ} (h_pos: k > 0): 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
  rw [← Nat.mul_two, Nat.mul_comm, Nat.mul_comm, Nat.two_pow_pred_mul_two h_pos]

end NumericLemmas

-- Split a field element into high and low parts
def split {k : ℕ} (h : k > 0) (x : ConcreteBinaryTower k) :
    ConcreteBinaryTower (k - 1) × ConcreteBinaryTower (k - 1) :=
  let lo_bits: BitVec (2 ^ (k - 1) - 1 - 0 + 1) :=
    BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x
  let hi_bits: BitVec (2 ^ k - 1 - 2 ^ (k - 1) + 1) :=
    BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x
  have h_lo: 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) := by
    calc 2 ^ (k - 1) - 1 - 0 + 1 = 2 ^ (k - 1) - 1 + 1 := by norm_num
      _ = 2^(k-1) := by rw [Nat.sub_add_cancel]; exact one_le_two_pow_n (n:=k-1)
  have h_hi := sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=by omega)
  -- Use cast to avoid overuse of fromNat & toNat
  let lo: BitVec (2^(k-1)) := dcast h_lo lo_bits
  let hi: BitVec (2^(k-1)) := dcast h_hi hi_bits
  (hi, lo)

def join {k : ℕ} (h_pos : k > 0)  (hi lo : ConcreteBinaryTower (k-1)) : ConcreteBinaryTower k := by
  let res := BitVec.append (msbs:=hi) (lsbs:=lo)
  rw [h_sum_two_same_pow2 (h_pos:=h_pos)] at res
  exact res

theorem BitVec.extractLsb_eq_shift_ofNat {n : Nat} (x : BitVec n) (l r : Nat) :
    BitVec.extractLsb r l x = BitVec.ofNat (r - l + 1) (x.toNat >>> l) := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  rfl

theorem setWidth_eq_ofNat_mod {n num_bits : Nat} (x : BitVec n) :
  BitVec.setWidth num_bits x = BitVec.ofNat num_bits (x.toNat % 2 ^ num_bits) := by
  simp only [BitVec.ofNat_toNat, ← BitVec.toNat_setWidth, BitVec.setWidth_eq]

theorem BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat {n num_bits : Nat}
  (h_num_bits: num_bits > 0) (x : BitVec n) :
  BitVec.extractLsb (hi:= num_bits-1) (lo := 0) x =
    BitVec.ofNat (num_bits - 1 - 0 + 1) (x.toNat &&& (2^num_bits-1)) := by
  unfold BitVec.extractLsb BitVec.extractLsb'
  simp only [Nat.sub_zero, Nat.add_zero, Nat.shiftRight_zero]
  have eq: num_bits - 1 + 1 = num_bits := Nat.sub_add_cancel (h:=h_num_bits)
  rw [eq]
  have lhs: BitVec.ofNat num_bits x.toNat = BitVec.ofNat num_bits (x.toNat % 2^num_bits) := by
    simp only [BitVec.ofNat_toNat, setWidth_eq_ofNat_mod]
  have rhs: BitVec.ofNat num_bits (x.toNat &&& 2 ^ num_bits - 1) =
    BitVec.ofNat num_bits (x.toNat % 2^num_bits) := by
    congr
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat num_bits
  rw [lhs, ←rhs]

theorem split_bitvec_eq_iff_fromNat {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
  (hi_btf lo_btf : ConcreteBinaryTower (k - 1)):
  split h_pos x = (hi_btf, lo_btf) ↔
  (hi_btf = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) ∧
  lo_btf = fromNat (k:=k-1) (x.toNat &&& (2^(2^(k-1)) - 1))) := by
  have lhs_lo_case := BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat (num_bits:=2^(k-1))
    (n:=2^k) (Nat.two_pow_pos (k - 1)) (x:=x)
  have rhs_hi_case_bitvec_eq := BitVec.extractLsb_eq_shift_ofNat (n:=2^k) (r:=2^k - 1)
    (l:=2^(k-1)) (x:=x)
  constructor
  · -- Forward direction: split x = (hi_btf, lo_btf) → bitwise operations
    intro h_split
    unfold split at h_split
    have ⟨h_hi, h_lo⟩ := Prod.ext_iff.mp h_split
    simp only at h_hi h_lo
    have hi_eq: hi_btf = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) := by
      unfold fromNat
      rw [←h_hi]
      rw [dcast_symm (h_sub_middle h_pos).symm]
      rw [rhs_hi_case_bitvec_eq]
      rw [BitVec.dcast_bitvec_eq]
    have lo_eq: lo_btf = fromNat (k:=k-1) (x.toNat &&& ((2^(2^(k-1)) - 1))) := by
      unfold fromNat
      rw [←h_lo]
      have rhs_lo_case_bitvec_eq :=
        BitVec.extractLsb_eq_shift_ofNat (n:=2^k) (r:=2^(k-1)-1) (l:=0) (x:=x)
      rw [dcast_symm (h_middle_sub).symm]
      rw [rhs_lo_case_bitvec_eq]
      rw [BitVec.dcast_bitvec_eq] -- remove dcast
      rw [←lhs_lo_case]
      exact rhs_lo_case_bitvec_eq
    exact ⟨hi_eq, lo_eq⟩
  · -- Backward direction: bitwise operations → split x = (hi_btf, lo_btf)
    intro h_bits
    unfold split
    have ⟨h_hi, h_lo⟩ := h_bits
    have hi_extract_eq: dcast (h_sub_middle h_pos) (BitVec.extractLsb (hi := 2 ^ k - 1)
      (lo := 2 ^ (k - 1)) x) = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) := by
      unfold fromNat
      rw [dcast_symm (h_sub_middle h_pos).symm]
      rw [rhs_hi_case_bitvec_eq]
      rw [BitVec.dcast_bitvec_eq]

    have lo_extract_eq: dcast (h_middle_sub) (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1)
      (lo := 0) x) = fromNat (k:=k-1) (x.toNat &&& ((2^(2^(k-1)) - 1))) := by
      unfold fromNat
      rw [lhs_lo_case]
      rw [BitVec.dcast_bitvec_eq]

    simp only [hi_extract_eq, Nat.sub_zero, lo_extract_eq, Nat.and_two_pow_sub_one_eq_mod, h_hi,
      h_lo]

theorem join_eq_iff_dcast_extractLsb {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
  (hi_btf lo_btf : ConcreteBinaryTower (k - 1)) :
  x = join h_pos hi_btf lo_btf ↔
  (hi_btf = dcast (h_sub_middle h_pos) (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) ∧
  lo_btf = dcast (h_middle_sub) (BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) x)) := by
  constructor
  · intro h_join
    unfold join at h_join
    have h_two_pow_k_minus_1_gt_0: 2 ^ (k - 1) > 0 := by exact Nat.two_pow_pos (k - 1)
    have h_x: x = dcast (h_sum_two_same_pow2 h_pos)
      (BitVec.append (msbs:=hi_btf) (lsbs:=lo_btf)) := by
      rw [h_join]
      simp only [BitVec.cast_eq]
      rw [BitVec.eq_mp_eq_dcast]
    have h_x_symm := dcast_symm (hb:=h_x.symm)
    have h_hi : hi_btf = dcast (h_sub_middle h_pos)
      (BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) x) := by
      have hi_btf_is_dcast_extract := (dcast_symm (hb:=(BitVec.extractLsb_concat_hi (hi:=hi_btf)
        (lo:=lo_btf) (h_hi:=h_two_pow_k_minus_1_gt_0)).symm)).symm
      rw [hi_btf_is_dcast_extract]
      rw [dcast_eq_dcast_iff] -- undcast in lhs
      rw [h_x]
      rw [BitVec.dcast_bitvec_extractLsb_eq (h_lo_eq:=rfl)]
      rfl
    have h_lo :
      lo_btf = dcast (h_middle_sub) (BitVec.extractLsb (hi := 2^(k-1) - 1) (lo :=0) x) := by
      have lo_btf_is_dcast_extract := (dcast_symm (hb:=(BitVec.extractLsb_concat_lo (hi:=hi_btf)
        (lo:=lo_btf) (h_lo:=h_two_pow_k_minus_1_gt_0)).symm)).symm
      rw [lo_btf_is_dcast_extract]
      rw [dcast_eq_dcast_iff] -- undcast in lhs
      rw [h_x]
      rw [BitVec.dcast_bitvec_extractLsb_eq (h_lo_eq:=rfl)]
      rfl
    exact ⟨h_hi, h_lo⟩
  -- Backward direction: bitwise operations → x = join h_pos hi_btf lo_btf
  · intro h_bits
    -- ⊢ x = join h_pos hi_btf lo_btf
    have two_pow_k_minus_1_gt_0: 2 ^ (k - 1) > 0 := by
      simp only [Nat.two_pow_pos]
    have sum1:= h_sum_two_same_pow2 (k:=k) (h_pos:=by omega).symm
    have res := BitVec.eq_append_iff_extract (lo:=lo_btf) (hi:=hi_btf)
      (h_hi_gt_0:=two_pow_k_minus_1_gt_0) (h_lo_gt_0:=two_pow_k_minus_1_gt_0)
        (x:=dcast (by exact sum1) x).mpr
    have ⟨h_hi, h_lo⟩ := h_bits
    have sum2: 2 ^ k - 1 = 2 ^ (k - 1) + 2 ^ (k - 1) - 1 := by omega
    rw! [sum2] at h_hi
    have h_x_eq := res ⟨h_hi, h_lo⟩
    rw [dcast_eq_dcast_iff] at h_x_eq
    unfold join
    rw [BitVec.eq_mp_eq_dcast (h_width_eq:=by exact sum1.symm) (h_bitvec_eq:=by rw [sum1.symm])]
    rw [h_x_eq]

theorem join_eq_join_iff {k: ℕ} (h_pos: k > 0) (hi₀ lo₀ hi₁ lo₁: ConcreteBinaryTower (k-1)):
  join h_pos hi₀ lo₀ = join h_pos hi₁ lo₁ ↔ (hi₀ = hi₁ ∧ lo₀ = lo₁) := by
  constructor
  · intro h_join
    let x₀ := join h_pos hi₀ lo₀
    let x₁ := join h_pos hi₁ lo₁
    have h_x₀: x₀ = join h_pos hi₀ lo₀ := by rfl
    have h_x₁: x₁ = join h_pos hi₁ lo₁ := by rfl
    have h₀ := join_eq_iff_dcast_extractLsb h_pos x₀ hi₀ lo₀
    have h₁ := join_eq_iff_dcast_extractLsb h_pos x₁ hi₁ lo₁
    have h_x₀_eq_x₁: x₀ = x₁ := by rw [h_x₀, h_x₁, h_join]
    have ⟨h_hi₀, h_lo₀⟩ := h₀.mp h_x₀
    have ⟨h_hi₁, h_lo₁⟩ := h₁.mp h_x₁
    rw [h_hi₁, h_hi₀, h_lo₀, h_lo₁]
    rw [h_x₀_eq_x₁]
    exact ⟨rfl, rfl⟩
  · intro h_eq
    rw [h_eq.1, h_eq.2]

theorem join_eq_bitvec_iff_fromNat {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
  (hi_btf lo_btf : ConcreteBinaryTower (k - 1)) :
  x = join h_pos hi_btf lo_btf ↔
  (hi_btf = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) ∧
  lo_btf = fromNat (k:=k-1) (x.toNat &&& (2^(2^(k-1)) - 1))) := by
  -- Idea: derive from theorem join_eq_iff_dcast_extractLsb
  constructor
  · -- Forward direction
    intro h_join
    have h := join_eq_iff_dcast_extractLsb h_pos x hi_btf lo_btf
    have ⟨h_hi, h_lo⟩ := h.mp h_join
    have hi_eq : hi_btf = fromNat (k:=k-1) (x.toNat >>> 2^(k-1)) := by
      rw [h_hi]
      have := BitVec.extractLsb_eq_shift_ofNat (n:=2^k) (r:=2^k - 1) (l:=2^(k-1)) (x:=x)
      rw [this]
      unfold fromNat
      rw [BitVec.dcast_bitvec_eq]
    have lo_eq : lo_btf = fromNat (k:=k-1) (x.toNat &&& (2^(2^(k-1)) - 1)) := by
      rw [h_lo]
      have := BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat (num_bits:=2^(k-1)) (n:=2^k)
                (Nat.two_pow_pos (k - 1)) (x:=x)
      rw [this]
      unfold fromNat
      rw [BitVec.dcast_bitvec_eq]
    exact ⟨hi_eq, lo_eq⟩
  · -- Backward direction
    intro h_bits
    have ⟨h_hi, h_lo⟩ := h_bits
    have h := join_eq_iff_dcast_extractLsb h_pos x hi_btf lo_btf
    have hi_eq : hi_btf = dcast (h_sub_middle h_pos)
      (BitVec.extractLsb (hi := 2^k - 1) (lo := 2^(k-1)) x) := by
      rw [h_hi]
      unfold fromNat
      have := BitVec.extractLsb_eq_shift_ofNat (n:=2^k) (r:=2^k - 1) (l:=2^(k-1)) (x:=x)
      rw [this]
      rw [BitVec.dcast_bitvec_eq]
    have lo_eq : lo_btf = dcast (h_middle_sub)
      (BitVec.extractLsb (hi := 2^(k-1) - 1) (lo := 0) x) := by
      rw [h_lo]
      unfold fromNat
      have := BitVec.extractLsb_eq_and_pow_2_minus_1_ofNat (num_bits:=2^(k-1)) (n:=2^k)
                (Nat.two_pow_pos (k - 1)) (x:=x)
      rw [this]
      rw [BitVec.dcast_bitvec_eq]
    exact h.mpr ⟨hi_eq, lo_eq⟩

theorem join_of_split {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
    (hi_btf lo_btf : ConcreteBinaryTower (k - 1))
    (h_split_eq : split h_pos x = (hi_btf, lo_btf)):
    x = join h_pos hi_btf lo_btf := by
  have h_split := (split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) x hi_btf lo_btf).mp h_split_eq
  obtain ⟨h_hi, h_lo⟩ := h_split
  exact (join_eq_bitvec_iff_fromNat h_pos x hi_btf lo_btf).mpr ⟨h_hi, h_lo⟩

theorem split_of_join {k : ℕ} (h_pos : k > 0) (x : ConcreteBinaryTower k)
    (hi_btf lo_btf : ConcreteBinaryTower (k - 1))
    (h_join: x = join h_pos hi_btf lo_btf):
    (hi_btf, lo_btf) = split h_pos x := by
  have ⟨h_hi, h_lo⟩ := (join_eq_bitvec_iff_fromNat h_pos x hi_btf lo_btf).mp h_join
  exact ((split_bitvec_eq_iff_fromNat h_pos x hi_btf lo_btf).mpr ⟨h_hi, h_lo⟩).symm

theorem bitvec_eq_iff_split_eq {k: ℕ} (h_pos: k > 0) (x₀ x₁: ConcreteBinaryTower k):
  x₀ = x₁ ↔ (split h_pos x₀ = split h_pos x₁) := by
  constructor
  · intro h_eq
    rw [h_eq]
  · intro h_split
    let p₀ := split h_pos x₀
    let hi₀ := p₀.fst
    let lo₀ := p₀.snd
    have h_split_x₀: split h_pos x₀ = (hi₀, lo₀) := by rfl
    have h_split_x₁: split h_pos x₁ = (hi₀, lo₀) := by
      rw [h_split.symm]
    have h_x₀ := (split_bitvec_eq_iff_fromNat h_pos x₀ hi₀ lo₀).mp h_split_x₀
    have h_x₁ := (split_bitvec_eq_iff_fromNat h_pos x₁ hi₀ lo₀).mp h_split_x₁
    -- now prove that x₀ is join of hi₀ and lo₀, similarly for x₁, so they are equal
    have h_x₀_eq_join := join_of_split h_pos x₀ hi₀ lo₀ h_split_x₀
    have h_x₁_eq_join := join_of_split h_pos x₁ hi₀ lo₀ h_split_x₁
    rw [h_x₀_eq_join, h_x₁_eq_join]

theorem split_sum_eq_sum_split {k: ℕ} (h_pos: k > 0) (x₀ x₁: ConcreteBinaryTower k)
  (hi₀ lo₀ hi₁ lo₁: ConcreteBinaryTower (k-1))
  (h_split_x₀: split h_pos x₀ = (hi₀, lo₀))
  (h_split_x₁: split h_pos x₁ = (hi₁, lo₁)):
  split h_pos (x₀ + x₁) = (hi₀ + hi₁, lo₀ + lo₁) := by
  have h_x₀ := join_of_split h_pos x₀ hi₀ lo₀ h_split_x₀
  have h_x₁ := join_of_split h_pos x₁ hi₁ lo₁ h_split_x₁
  -- Approach: convert equation to Nat realm for simple proof
  have h₀ := (split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) x₀ hi₀ lo₀).mp h_split_x₀
  have h₁ := (split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) x₁ hi₁ lo₁).mp h_split_x₁
  have h_sum_hi : (hi₀ + hi₁) = fromNat (BitVec.toNat (x₀ + x₁) >>> 2 ^ (k - 1)) := by
    rw [h₀.1, h₁.1]
    rw [←sum_fromNat_eq_from_xor_Nat]
    have h_nat_eq: BitVec.toNat x₀ >>> 2 ^ (k - 1) ^^^ BitVec.toNat x₁ >>> 2 ^ (k - 1)
      = BitVec.toNat (x₀ + x₁) >>> 2 ^ (k - 1) := by
      -- unfold Concrete BTF addition into BitVec.xor
      simp only [instHAddConcreteBinaryTower, add, BitVec.xor_eq]
      rw [Nat.shiftRight_xor_distrib.symm]
      rw [BitVec.toNat_xor] -- distribution of BitVec.xor over BitVec.toNat
    rw [h_nat_eq]
  have h_sum_lo : (lo₀ + lo₁) = fromNat (BitVec.toNat (x₀ + x₁) &&& 2 ^ 2 ^ (k - 1) - 1) := by
    rw [h₀.2, h₁.2]
    rw [←sum_fromNat_eq_from_xor_Nat]
    have h_nat_eq: BitVec.toNat x₀ &&& 2 ^ 2 ^ (k - 1) - 1 ^^^ BitVec.toNat x₁
      &&& 2 ^ 2 ^ (k - 1) - 1 = BitVec.toNat (x₀ + x₁) &&& 2 ^ 2 ^ (k - 1) - 1 := by
      simp only [instHAddConcreteBinaryTower, add, BitVec.xor_eq]
      rw [BitVec.toNat_xor]
      rw [Nat.and_xor_distrib_right.symm]
    rw [h_nat_eq]
  have h_sum_hi_lo : (hi₀ + hi₁, lo₀ + lo₁) = split h_pos (x₀ + x₁) := by
    rw [(split_bitvec_eq_iff_fromNat (k:=k) (h_pos:=h_pos) (x₀ + x₁)
      (hi₀ + hi₁) (lo₀ + lo₁)).mpr ⟨h_sum_hi, h_sum_lo⟩]
  exact h_sum_hi_lo.symm

theorem join_add_join {k: ℕ} (h_pos: k > 0) (hi₀ lo₀ hi₁ lo₁: ConcreteBinaryTower (k-1)):
  join h_pos hi₀ lo₀ + join h_pos hi₁ lo₁ = join h_pos (hi₀ + hi₁) (lo₀ + lo₁) := by
  set x₀ := join h_pos hi₀ lo₀
  set x₁ := join h_pos hi₁ lo₁
  set x₂ := join h_pos (hi₀ + hi₁) (lo₀ + lo₁)
  have h_x₀: x₀ = join h_pos hi₀ lo₀ := by rfl
  have h_x₁: x₁ = join h_pos hi₁ lo₁ := by rfl
  have h_x₂: x₂ = join h_pos (hi₀ + hi₁) (lo₀ + lo₁) := by rfl
  -- proof: x₀ + x₁ = x₂, utilize split_sum_eq_sum_split and bitvec_eq_iff_split_eq
  have h_split_x₀ := split_of_join h_pos x₀ hi₀ lo₀ h_x₀
  have h_split_x₁ := split_of_join h_pos x₁ hi₁ lo₁ h_x₁
  have h_split_x₂ := split_of_join h_pos x₂ (hi₀ + hi₁) (lo₀ + lo₁) h_x₂
  have h_split_x₂_via_sum := split_sum_eq_sum_split h_pos x₀ x₁ hi₀ lo₀ hi₁
    lo₁ h_split_x₀.symm h_split_x₁.symm
  rw [h_split_x₂_via_sum.symm] at h_split_x₂
  have h_eq := (bitvec_eq_iff_split_eq h_pos (x₀ + x₁) x₂).mpr h_split_x₂
  exact h_eq

theorem split_zero {k: ℕ} (h_pos: k > 0): split h_pos zero = (zero, zero) := by
  rw [split]
  simp only [zero, BitVec.zero_eq, BitVec.extractLsb_ofNat, Nat.zero_mod, Nat.zero_shiftRight,
    Nat.sub_zero, Nat.shiftRight_zero, Prod.mk.injEq, BitVec.dcast_bitvec_eq_zero, and_self]

lemma one_bitvec_toNat {width: ℕ} (h_width: width > 0): (1#width).toNat = 1 := by
  simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow_eq_one, h_width]

lemma one_bitvec_shiftRight {d: ℕ} (h_d: d > 0): 1 >>> d = 0 := by
  apply Nat.shiftRight_eq_zero
  rw [Nat.one_lt_two_pow_iff]
  exact Nat.ne_zero_of_lt h_d

lemma split_one {k : ℕ} (h_k : k > 0) : split h_k (one (k:=k)) = (zero (k:=k-1), one (k:=k-1)) := by
  rw [split]
  let lo_bits := BitVec.extractLsb (hi := 2 ^ (k - 1) - 1) (lo := 0) (one (k:=k))
  let hi_bits := BitVec.extractLsb (hi := 2 ^ k - 1) (lo := 2 ^ (k - 1)) (one (k:=k))
  apply Prod.ext
  · simp only
    simp only [BitVec.extractLsb, BitVec.extractLsb']
    rw [one]
    have one_toNat_eq := one_bitvec_toNat (width:=2^k)
      (h_width:=zero_lt_pow_n (m:=2) (n:=k) (h_m:=Nat.zero_lt_two))
    rw [one_toNat_eq]
    have one_shiftRight_eq: 1 >>> 2 ^ (k - 1) = 0 :=
      one_bitvec_shiftRight (d:=2^(k-1)) (h_d:=by exact Nat.two_pow_pos (k - 1))
    rw [one_shiftRight_eq]
    rw [zero, BitVec.zero_eq]
    have h_sub_middle := sub_middle_of_pow2_with_one_canceled (k:=k) (h_k:=h_k)
    rw [BitVec.dcast_bitvec_eq_zero]
  · simp only
    simp only [BitVec.extractLsb, BitVec.extractLsb']
    simp only [Nat.sub_zero, one, BitVec.toNat_ofNat, Nat.ofNat_pos, pow_pos, Nat.one_mod_two_pow,
      Nat.shiftRight_zero] -- converts BitVec.toNat one >>> 0 into 1#(2 ^ (k - 1))
    rw [BitVec.dcast_bitvec_eq]

lemma join_zero_zero {k : ℕ} (h_k : k > 0) :
  join h_k (zero (k:=k-1)) (zero (k:=k-1)) = zero (k:=k) := by
  have h_1 := split_zero h_k
  exact (join_of_split h_k (zero) (zero) (zero) (h_1)).symm

theorem join_zero_one {k: ℕ} (h_k: k > 0): join h_k zero one = one := by
  have h_1 := split_one h_k
  have res := join_of_split (h_pos:=h_k) (x:=one) (hi_btf:=zero) (lo_btf:=one) (h_1)
  exact res.symm

def equivProd {k : ℕ} (h_k_pos : k > 0) :
  ConcreteBinaryTower k ≃ ConcreteBinaryTower (k - 1) × ConcreteBinaryTower (k - 1) where
  toFun := split h_k_pos
  invFun := fun (hi, lo) => join h_k_pos hi lo
  left_inv := fun x => Eq.symm (join_of_split h_k_pos x _ _ rfl)
  right_inv := fun ⟨hi, lo⟩ => Eq.symm (split_of_join h_k_pos _ hi lo rfl)

lemma mul_trans_inequality {k : ℕ} (x: ℕ) (h_k: k ≤ 2) (h_x: x ≤ 2^(2^k) - 1): x < 16 := by
  have x_le_1: x ≤ 2^(2^k) - 1 := by omega
  have x_le_2: x ≤ 2^(2^2) - 1 := by
    apply le_trans x_le_1 -- 2^(2^k) - 1 ≤ 2^(2^2) - 1
    rw [Nat.sub_le_sub_iff_right]
    rw [Nat.pow_le_pow_iff_right, Nat.pow_le_pow_iff_right]
    exact h_k
    norm_num
    norm_num
    norm_num
  have x_le_15: x ≤ 15 := by omega
  have x_lt_16: x < 16 := by omega
  exact x_lt_16

-- Helper: Convert coefficients back to BitVec
def coeffsToBitVec {n : ℕ} (coeffs : List (ZMod 2)) : BitVec n :=
  let val := List.foldr (fun c acc => acc * 2 + c.val) 0 (coeffs.take n)
  BitVec.ofNat n val

-- Karatsuba-like multiplication for binary tower fields
def concrete_mul {k : ℕ} (a b : ConcreteBinaryTower k) : ConcreteBinaryTower k :=
  if h_k_zero: k = 0 then
    if a = zero then zero
    else if b = zero then zero
    else if a = one then b
    else if b = one then a
    else zero -- This case never happens in GF(2)
  else
    have h_k_gt_0 : k > 0 := by omega
    let (a₁, a₀) := split h_k_gt_0 a -- (hi, lo)
    let (b₁, b₀) := split h_k_gt_0 b
    let a_sum := a₁ + a₀
    let b_sum := b₁ + b₀
    let sum_mul := concrete_mul a_sum b_sum
    let prevX := Z (k - 1)
    -- Karatsuba-like step
    let mult_hi := concrete_mul a₁ b₁  -- Recursive call at k-1
    let mult_lo := concrete_mul a₀ b₀  -- Recursive call at k-1
    let lo_res := mult_lo + mult_hi -- a₀b₀ + a₁b₁
    let hi_res := sum_mul + lo_res + (concrete_mul mult_hi prevX)
    have h_eq : k - 1 + 1 = k := by omega
    -- Use the proof to cast the type
    have res := join (k:=k) (by omega) hi_res lo_res
    res
termination_by (k, a.toNat, b.toNat)

-- Multiplication instance
instance (k : ℕ) : HMul (ConcreteBinaryTower k) (ConcreteBinaryTower k) (ConcreteBinaryTower k)
  where hMul := concrete_mul

instance (k : ℕ) : LT (ConcreteBinaryTower k) where
  lt := fun x y => by
    unfold ConcreteBinaryTower at x y
    exact x < y

instance (k : ℕ) : LE (ConcreteBinaryTower k) where
  le := fun x y => by
    unfold ConcreteBinaryTower at x y
    exact x ≤ y

instance (k: ℕ) : Preorder (ConcreteBinaryTower k) where
  le_refl := fun x => BitVec.le_refl x
  le_trans := fun x y z hxy hyz => BitVec.le_trans hxy hyz
  lt := fun x y => x < y
  lt_iff_le_not_le := fun x y => by
    unfold ConcreteBinaryTower at x y
    have bitvec_statement := (BitVec.not_lt_iff_le : ¬x < y ↔ y ≤ x)
    -- We need to prove: x < y ↔ x ≤ y ∧ ¬y ≤ x
    constructor
    · -- Forward direction: x < y → x ≤ y ∧ ¬y ≤ x
      intro h_lt
      constructor
      · -- x < y → x ≤ y
        exact BitVec.le_of_lt h_lt
      · -- x < y → ¬y ≤ x
        intro h_le_yx
        have h_not_le := mt bitvec_statement.mpr
        push_neg at h_not_le
        have neg_y_le_x := h_not_le h_lt
        contradiction
    · -- Reverse direction: x ≤ y ∧ ¬y ≤ x → x < y
      intro h
      cases h with | intro h_le_xy h_not_le_yx =>
      have x_lt_y:= mt bitvec_statement.mp h_not_le_yx
      push_neg at x_lt_y
      exact x_lt_y

theorem toNatInRange {k: ℕ} (b: ConcreteBinaryTower k) : BitVec.toNat b ≤ 2 ^ (2 ^ k) - 1 := by
  unfold ConcreteBinaryTower at b
  have le_symm: 2^k ≤ 2^k := by omega
  have toNat_le_2pow:= BitVec.toNat_lt_twoPow_of_le (m:=2^k) (n:=(2^k))
  have b_le := toNat_le_2pow le_symm (x:=b)
  omega

theorem eq_zero_or_eq_one {a : ConcreteBinaryTower 0} : a = zero ∨ a = one := by
  unfold ConcreteBinaryTower at a -- Now a is a BitVec (2^0) = BitVec 1
  have h := BitVec.eq_zero_or_eq_one a
  cases h with
  | inl h_zero =>
    left
    unfold zero
    exact h_zero
  | inr h_one =>
    right
    unfold one
    exact h_one

theorem concrete_eq_zero_or_eq_one {k: ℕ} {a : ConcreteBinaryTower k} (h_k_zero: k = 0)
  : a = zero ∨ a = one := by
  if h_k_zero: k = 0 then
    have h_2_pow_k_eq_1: 2 ^ k = 1 := by rw [h_k_zero]; norm_num
    let a0 : ConcreteBinaryTower 0 := Eq.mp (congrArg ConcreteBinaryTower h_k_zero) a
    have a0_is_eq_mp_a: a0 = Eq.mp (congrArg ConcreteBinaryTower h_k_zero) a := by rfl
    -- Approach: convert to BitVec.cast and derive equality of the cast for 0 and 1
    rcases eq_zero_or_eq_one (a := a0) with (ha0 | ha1)
    · -- a0 = zero
      left
      -- Transport equality back to ConcreteBinaryTower k
      have : a = Eq.mpr (congrArg ConcreteBinaryTower h_k_zero) a0 := by
        simp only [a0_is_eq_mp_a, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
      rw [this, ha0]
      -- zero (k:=k) = Eq.mpr ... (zero (k:=0))
      have : zero = Eq.mpr (congrArg ConcreteBinaryTower h_k_zero) (zero (k:=0)) := by
        simp only [zero, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast, cast_eq, BitVec.zero]
        rw [←dcast_eq_root_cast]
        simp [BitVec.dcast_bitvec_eq]
        rw [BitVec.dcast_zero] -- ⊢ 1 = 2^k
        exact h_2_pow_k_eq_1.symm
      rw [this]
    · -- a0 = one
      right
      have : a = Eq.mpr (congrArg ConcreteBinaryTower h_k_zero) a0 := by
        simp only [a0_is_eq_mp_a, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
      rw [this, ha1]
      have : one = Eq.mpr (congrArg ConcreteBinaryTower h_k_zero) (one (k:=0)) := by
        simp only [one, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast, cast_eq]
        rw [←dcast_eq_root_cast]
        simp [BitVec.dcast_bitvec_eq]
        rw [BitVec.dcast_one] -- ⊢ 1 = 2^k
        exact h_2_pow_k_eq_1.symm
      rw [this]
  else
    contradiction

lemma add_eq_one_iff (a b : ConcreteBinaryTower 0) :
  a + b = 1 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul, add_self_cancel, zero_is_0]  -- a = zero
  · simp [ha, one_is_1]

def concrete_pow_nat {k: ℕ} (x : ConcreteBinaryTower k) (n : ℕ) : ConcreteBinaryTower k :=
  if n = 0 then one
  else if n % 2 = 0 then concrete_pow_nat (concrete_mul x x) (n / 2)
  else concrete_mul x (concrete_pow_nat (concrete_mul x x) (n / 2))

-- Multiplicative inverse
def concrete_inv {k : ℕ} (a : ConcreteBinaryTower k) : ConcreteBinaryTower k :=
  if h_k_zero: k = 0 then
    if a = 0 then 0 else 1
  else
    if h_a_zero: a = 0 then 0
    else if h_a_one: a = 1 then 1
    else
      let h_k_gt_0 : k > 0 := Nat.zero_lt_of_ne_zero h_k_zero
      let (a_hi, a_lo) := split (k:=k) (h:=h_k_gt_0) a
      let prevZ := Z (k-1)
      let a_lo_next := a_lo + concrete_mul a_hi prevZ
      let delta := concrete_mul a_lo a_lo_next + concrete_mul a_hi a_hi
      let delta_inverse := concrete_inv delta
      let out_hi := concrete_mul delta_inverse a_hi
      let out_lo := concrete_mul delta_inverse a_lo_next
      let res := join (k:=k) (by omega) out_hi out_lo
      res

lemma concrete_inv_zero {k: ℕ} : concrete_inv (k:=k) 0 = 0 := by
  unfold concrete_inv
  by_cases h_k_zero : k = 0
  · rw [dif_pos h_k_zero]; norm_num
  · rw [dif_neg h_k_zero]; norm_num

lemma concrete_exists_pair_ne {k:ℕ}: ∃ x y : ConcreteBinaryTower k, x ≠ y :=
  ⟨zero (k:=k), one (k:=k), (concrete_one_ne_zero (k:=k)).symm⟩

lemma concrete_zero_mul0 (b : ConcreteBinaryTower 0) :
  concrete_mul (zero (k:=0)) b = zero (k:=0) := by
  unfold concrete_mul
  simp only [↓reduceDIte, zero, Nat.pow_zero, BitVec.zero_eq, ↓reduceIte]

lemma concrete_mul_zero0 (a : ConcreteBinaryTower 0) :
  concrete_mul a (zero (k:=0)) = zero (k:=0) := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp only [↓reduceDIte, h, ↓reduceIte]
  · simp only [↓reduceDIte, zero, Nat.pow_zero, BitVec.zero_eq, ↓reduceIte, ite_self]

lemma concrete_one_mul0 (a : ConcreteBinaryTower 0) :
  concrete_mul (one (k:=0)) a = a := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp [h, zero]
  · norm_num; simp only [concrete_one_ne_zero, ↓reduceIte, h]

lemma concrete_mul_one0 (a : ConcreteBinaryTower 0) :
  concrete_mul a (one (k:=0)) = a := by
  unfold concrete_mul
  by_cases h : a = zero
  · simp [h]
  · norm_num; simp [h, concrete_one_ne_zero]; intro h_eq; exact h_eq.symm

lemma concrete_mul_assoc0 (a b c : ConcreteBinaryTower 0) :
  concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c) := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul]  -- a = zero case
  · rcases eq_zero_or_eq_one (a := b) with (hb | hb)
    · simp [ha, hb, concrete_mul]  -- a = one, b = zero
    · rcases eq_zero_or_eq_one (a := c) with (hc | hc)
      · simp [ha, hb, hc, concrete_mul]  -- a = one, b = one, c = zero
      · simp [ha, hb, hc, concrete_mul, concrete_one_ne_zero]  -- a = one, b = one, c = one

lemma concrete_mul_comm0 (a b : ConcreteBinaryTower 0) :
  concrete_mul a b = concrete_mul b a := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul]  -- a = zero
  · rcases eq_zero_or_eq_one (a := b) with (hb | hb)
    · simp [ha, hb, concrete_mul]  -- a = one, b = zero
    · simp [ha, hb, concrete_mul]  -- a = one, b = one

-- Helper lemma: For GF(2), `if x = 0 then 0 else x` is just `x`.
lemma if_zero_then_zero_else_self (x : ConcreteBinaryTower 0) :
  (if x = zero then zero else x) = x := by
  rcases eq_zero_or_eq_one (a := x) with (hx_zero | hx_one)
  · simp only [hx_zero, ↓reduceIte]
  · simp only [hx_one, concrete_one_ne_zero, ↓reduceIte]

lemma concrete_mul_left_distrib0 (a b c : ConcreteBinaryTower 0) :
  concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c := by
  rcases eq_zero_or_eq_one (a := a) with (ha | ha)
  · simp [ha, concrete_mul, add_self_cancel, zero_is_0]  -- a = zero
  · simp [ha, concrete_mul, add_self_cancel, zero_is_0, concrete_one_ne_zero, one_is_1];
    rcases eq_zero_or_eq_one (a := b + c) with (hb_add_c | hb_add_c)
    · simp [hb_add_c, zero_is_0];
      rw [zero_is_0] at hb_add_c
      have b_eq_c: b = c := (add_eq_zero_iff_eq b c).mp hb_add_c
      simp only [b_eq_c, add_self_cancel]
    · simp [hb_add_c, concrete_one_ne_zero, one_is_1, zero_is_0];
      have c_cases := (add_eq_one_iff b c).mp hb_add_c
      rcases eq_zero_or_eq_one (a := b) with (hb | hb)
      · simp [hb, zero_is_0];
        rw [one_is_1] at hb_add_c
        rw [zero_is_0] at hb
        simp [hb] at c_cases
        have c_ne_0: c ≠ 0 := by
          simp only [c_cases, ne_eq, one_ne_zero, not_false_eq_true]
        rw [if_neg c_ne_0]
        exact c_cases.symm
      · rw [one_is_1] at hb; simp [hb, concrete_one_ne_zero];
        simp [hb] at c_cases
        exact c_cases

lemma concrete_mul_right_distrib0 (a b c : ConcreteBinaryTower 0) :
  concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c := by
  rw [concrete_mul_comm0 (a:=(a+b)) (b:=c)]
  rw [concrete_mul_comm0 (a:=a) (b:=c)]
  rw [concrete_mul_comm0 (a:=b) (b:=c)]
  exact concrete_mul_left_distrib0 (a:=c) (b:=a) (c:=b)

-- Natural number casting
def natCast {k: ℕ} (n : ℕ) : ConcreteBinaryTower k := if n % 2 = 0 then zero else one
def natCast_zero {k: ℕ} : natCast (k:=k) 0 = zero := by rfl

def natCast_succ {k: ℕ} (n : ℕ) : natCast (k:=k) (n + 1) = natCast (k:=k) n + 1 := by
  by_cases h : n % 2 = 0
  · -- If n % 2 = 0, then (n+1) % 2 = 1
    have h_succ : (n + 1) % 2 = 1 := by omega
    simp only [natCast, h, h_succ]; norm_num; rw [one_is_1, zero_is_0]; norm_num
  · -- If n % 2 = 1, then (n+1) % 2 = 0
    have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [natCast, h, h_succ]; norm_num; rw [one_is_1, zero_is_0, add_self_cancel]

instance {k: ℕ} : NatCast (ConcreteBinaryTower k) where
  natCast n:= natCast n

@[simp]
lemma concrete_natCast_zero_eq_zero {k:ℕ} : natCast 0 = (0: ConcreteBinaryTower k) := by
  simp only [natCast, Nat.zero_mod, ↓reduceIte, zero_is_0]

@[simp]
lemma concrete_natCast_one_eq_one {k:ℕ} : natCast 1 = (1: ConcreteBinaryTower k) := by
  simp only [natCast, Nat.mod_succ, one_ne_zero, ↓reduceIte, one_is_1]

-- help simp recognize the NatCast coercion
@[simp] lemma natCast_eq {k: ℕ} (n : ℕ) : (↑n : ConcreteBinaryTower k) = natCast n := rfl

-- Integer casting
def intCast {k: ℕ} (n : ℤ) : ConcreteBinaryTower k := if n % 2 = 0 then zero else one

instance {k:ℕ} : IntCast (ConcreteBinaryTower k) where
  intCast n:= intCast n

def intCast_ofNat {k:ℕ} (n : ℕ) : intCast (k:=k) (n : ℤ) = natCast n := by
  have h_mod_eq : (n : ℤ) % 2 = 0 ↔ n % 2 = 0 := by omega
  by_cases h : n % 2 = 0
  · -- Case: n % 2 = 0
    have h_int : (n : ℤ) % 2 = 0 := h_mod_eq.mpr h
    simp only [intCast, natCast, h, h_int]
  · -- Case: n % 2 ≠ 0
    have h' : n % 2 = 1 := by omega  -- For n : ℕ, if not 0, then 1
    have h_int : (n : ℤ) % 2 = 1 := by omega  -- Coercion preserves modulo
    simp only [intCast, natCast, h, h_int, h']
    rfl

@[simp] lemma my_neg_mod_two (m : ℤ) : (-m) % 2 = if m % 2 = 0 then 0 else 1 := by omega
@[simp] lemma mod_two_eq_zero (m: ℤ): m % 2 = (-m) % 2 := by omega

def intCast_negSucc {k:ℕ} (n : ℕ) : intCast (k:=k) (Int.negSucc n)
  = - (↑(n + 1) : ConcreteBinaryTower k) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · -- ⊢ intCast (Int.negSucc n) = -↑(n + 1)
    have h_neg : (-(n + 1 : ℤ)) % 2 = 0 := by omega
    unfold intCast
    have int_neg_succ: Int.negSucc n = -(n+1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    have h_nat : (↑(n + 1) : ConcreteBinaryTower k) = (zero : ConcreteBinaryTower k) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl
  · -- ⊢ intCast (Int.negSucc n) = -↑(n + 1)
    have h_neg : (-(n + 1 : ℤ)) % 2 = 1 := by omega
    unfold intCast
    have int_neg_succ: Int.negSucc n = -(n+1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    rw [if_neg (by simp)]
    have h_nat : (↑(n + 1) : ConcreteBinaryTower k) = (one : ConcreteBinaryTower k) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl

end BaseDefinitions

-------------------------------------------------------------------------------------------
-- Structure to hold properties at a given level k
structure ConcreteBTFStepResult (k : ℕ) where
  mul_eq : ∀ (a b : ConcreteBinaryTower k) (h_k : k > 0)
    {a₁ a₀ b₁ b₀ : ConcreteBinaryTower (k-1)}
    (_h_a : (a₁, a₀) = split h_k a) (_h_b : (b₁, b₀) = split h_k b),
    concrete_mul a b = join h_k
      (hi:=concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)))
      (lo:=concrete_mul a₀ b₀ + concrete_mul a₁ b₁)
  zero_mul : ∀ a : ConcreteBinaryTower k, concrete_mul zero a = zero
  zero_mul' : ∀ a : ConcreteBinaryTower k, concrete_mul 0 a = 0
  mul_zero : ∀ a : ConcreteBinaryTower k, concrete_mul a zero = zero
  mul_zero' : ∀ a : ConcreteBinaryTower k, concrete_mul a 0 = 0
  one_mul : ∀ a : ConcreteBinaryTower k, concrete_mul one a = a
  mul_one : ∀ a : ConcreteBinaryTower k, concrete_mul a one = a
  mul_assoc : ∀ a b c : ConcreteBinaryTower k, concrete_mul (concrete_mul a b) c
    = concrete_mul a (concrete_mul b c)
  mul_comm : ∀ a b : ConcreteBinaryTower k, concrete_mul a b = concrete_mul b a
  mul_left_distrib : ∀ a b c : ConcreteBinaryTower k, concrete_mul a (b + c)
    = concrete_mul a b + concrete_mul a c
  mul_right_distrib : ∀ a b c : ConcreteBinaryTower k, concrete_mul (a + b) c
    = concrete_mul a c + concrete_mul b c
  add_assoc : ∀ a b c : ConcreteBinaryTower k, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : ConcreteBinaryTower k, a + b = b + a
  add_zero : ∀ a : ConcreteBinaryTower k, a + zero = a
  zero_add : ∀ a : ConcreteBinaryTower k, zero + a = a
  add_neg : ∀ a : ConcreteBinaryTower k, a + (neg a) = zero
  mul_inv_cancel : ∀ a : ConcreteBinaryTower k, a ≠ zero → concrete_mul a (concrete_inv a) = one

-------------------------------------------------------------------------------------------
section InductiveConcreteBTFPropertiesProofs -- for k > 0
variable {k : ℕ}

theorem concrete_mul_eq {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m}
  (a b: ConcreteBinaryTower k) (h_k: k > 0) {a₁ a₀ b₁ b₀: ConcreteBinaryTower (k-1)}
  (h_a: (a₁, a₀) = split h_k a) (h_b: (b₁, b₀) = split h_k b):
  concrete_mul a b = join h_k
    (hi:=concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)))
    (lo:=concrete_mul a₀ b₀ + concrete_mul a₁ b₁) := by
  have h_a₁ : (split h_k a).1 = a₁ := by rw [h_a.symm]
  have h_a₀ : (split h_k a).2 = a₀ := by rw [h_a.symm]
  have h_b₁ : (split h_k b).1 = b₁ := by rw [h_b.symm]
  have h_b₀ : (split h_k b).2 = b₀ := by rw [h_b.symm]
  conv =>
    lhs
    unfold concrete_mul
    rw [dif_neg (Nat.ne_of_gt h_k)]
    simp only [h_a₁, h_a₀, h_b₁, h_b₀] -- Do this to resolve the two nested matches (of the splits)
    -- while still allowing substitution of a₀ a₁ b₀ b₁ (components of the splits) into the goal
  rw [join_eq_join_iff]
  split_ands
  · -- ⊢ concrete_mul (a₁ + a₀) (b₁ + b₀) + (concrete_mul a₀ b₀ + concrete_mul a₁ b₁) +
    -- concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))
    -- = concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))
    have h_add_left_inj := (add_left_inj (a:=concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)))
      (b:=concrete_mul (a₁ + a₀) (b₁ + b₀) + (concrete_mul a₀ b₀ + concrete_mul a₁ b₁) +
      concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))) (c:=concrete_mul a₀ b₁ + concrete_mul b₀ a₁
        + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)))).mp
    rw [h_add_left_inj]
    rw [add_assoc, add_self_cancel, add_zero, add_assoc, add_self_cancel, add_zero]
    -- ⊢ concrete_mul (a₁ + a₀) (b₁ + b₀) + (concrete_mul a₀ b₀ + concrete_mul a₁ b₁)
    -- = concrete_mul a₀ b₁ + concrete_mul b₀ a₁
    have recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k)
    rw [recArgPrevLevel.mul_left_distrib, recArgPrevLevel.mul_right_distrib,
      recArgPrevLevel.mul_right_distrib]
    have h_a₁_b₀: concrete_mul a₁ b₀ = concrete_mul b₀ a₁ := by
      rw [recArgPrevLevel.mul_comm (a:=a₁) (b:=b₀)]
    have h_a₀_b₁: concrete_mul a₀ b₁ = concrete_mul b₁ a₀ := by
      rw [recArgPrevLevel.mul_comm (a:=a₀) (b:=b₁)]
    rw [h_a₁_b₀, h_a₀_b₁]
    -- ⊢ concrete_mul a₁ b₁ + concrete_mul b₁ a₀ + (concrete_mul b₀ a₁ + concrete_mul a₀ b₀) +
    -- (concrete_mul a₀ b₀ + concrete_mul a₁ b₁) = concrete_mul b₁ a₀ + concrete_mul b₀ a₁
    conv =>
      lhs
      rw [←add_assoc, ←add_assoc]
      rw [add_assoc (b:=concrete_mul a₀ b₀) (c:=concrete_mul a₀ b₀), add_self_cancel, add_zero]
      rw [add_comm (b:=concrete_mul a₁ b₁), ←add_assoc, ←add_assoc, add_self_cancel, zero_add]
  · rfl

lemma concrete_zero_mul {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m}
  (a : ConcreteBinaryTower k) : concrete_mul (zero (k:=k)) a = zero (k:=k) := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp only [h_k_zero, ↓reduceDIte, zero, dif_pos, ite_true]
  · -- Inductive case: k > 0
    simp only [dif_neg h_k_zero]
    -- Obtain h_k_gt_0 from h_k_zero
    have h_k_gt_0_proof : k > 0 := by omega
    -- Split zero into (zero, zero)
    have h_zero_split : split h_k_gt_0_proof (zero (k:=k)) = (zero, zero) := by rw [split_zero]
    let (a₁, a₀) := (zero (k:=k-1), zero (k:=k-1))
    let (b₁, b₀) := split h_k_gt_0_proof a
    rw [h_zero_split]
    simp only
    -- Apply the inductive hypothesis to a₁*b₁, a₀*b₀, a₁*b₀, a₀*b₁
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0_proof)
    simp only [zero_is_0, zero_add, recArgPrevLevel.zero_mul']
    simp only [← zero_is_0, join_zero_zero h_k_gt_0_proof]

lemma concrete_mul_zero {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m}
  (a : ConcreteBinaryTower k) : concrete_mul a (zero (k:=k)) = zero (k:=k) := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp only [h_k_zero, ↓reduceDIte, zero, BitVec.zero_eq, ↓reduceIte, ite_self]
  · -- Inductive case: k > 0
    simp only [dif_neg h_k_zero]
    -- Obtain h_k_gt_0 from h_k_zero
    have h_k_gt_0_proof : k > 0 := by omega
    -- Split zero into (zero, zero)
    have h_zero_split : split h_k_gt_0_proof (zero (k:=k)) = (zero, zero) := by rw [split_zero]
    -- Split a into (a₁, a₀)
    let (a₁, a₀) := split h_k_gt_0_proof a
    let (b₁, b₀) := (zero (k:=k-1), zero (k:=k-1))
    -- Rewrite with the zero split
    rw [h_zero_split]
    simp only
    -- Apply the inductive hypothesis
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0_proof)
    simp only [zero_is_0, zero_add, recArgPrevLevel.mul_zero']
    -- Use join_zero to complete the proof
    simp only [← zero_is_0, recArgPrevLevel.zero_mul, join_zero_zero h_k_gt_0_proof]

lemma concrete_one_mul {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m}
  (a : ConcreteBinaryTower k) : concrete_mul (one (k:=k)) a = a := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp [h_k_zero, ↓reduceDIte, dif_pos, one_is_1, zero_is_0]; intro h; exact h.symm
  · -- Inductive case: k > 0
    have h_k_gt_0 : k > 0 := by omega
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0)
    simp only [dif_neg h_k_zero]
    let p := split h_k_gt_0 a
    let a₁ := p.fst
    let a₀ := p.snd
    have h_split_a : split h_k_gt_0 a = (a₁, a₀) := by rfl
    rw [split_one]
    simp only [zero_is_0, zero_add, recArgPrevLevel.one_mul, recArgPrevLevel.zero_mul', add_zero]
    simp [add_assoc, add_self_cancel]
    have join_result : join h_k_gt_0 a₁ a₀ = a := by
      have split_join := join_of_split h_k_gt_0 a a₁ a₀
      exact (split_join h_split_a).symm
    exact join_result

lemma concrete_mul_one {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m}
  (a : ConcreteBinaryTower k) : concrete_mul a (one (k:=k)) = a := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case: k = 0
    simp [h_k_zero, ↓reduceDIte, dif_pos, one_is_1, zero_is_0];
    conv =>
      lhs
      simp only [if_self_rfl]
  · -- Inductive case: k > 0
    have h_k_gt_0 : k > 0 := by omega
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0)
    simp only [dif_neg h_k_zero]
    let p := split h_k_gt_0 a
    let a₁ := p.fst
    let a₀ := p.snd
    have h_split_a : split h_k_gt_0 a = (a₁, a₀) := by rfl
    rw [split_one]
    simp only [zero_is_0, zero_add, recArgPrevLevel.mul_one, recArgPrevLevel.mul_zero',
      recArgPrevLevel.zero_mul', add_zero]
    simp [add_assoc, add_self_cancel]
    have join_result : join h_k_gt_0 a₁ a₀ = a := by
      have split_join := join_of_split h_k_gt_0 a a₁ a₀
      exact (split_join h_split_a).symm
    exact join_result

lemma concrete_pow_base_one {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} (n : ℕ) :
  concrete_pow_nat (k:=k) (x:=1) n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- ih: ∀ m, m < n → concrete_pow_nat (k:=k) (x:=1) m = 1
    unfold concrete_pow_nat
    by_cases h_n_zero : n = 0
    · -- Base case: n = 0
      rw [if_pos h_n_zero]
      exact one_is_1  -- one = 1
    · -- Inductive step: n ≠ 0
      rw [if_neg h_n_zero]
      by_cases h_mod : n % 2 = 0
      · -- Even case: n % 2 = 0
        rw [if_pos h_mod]
        have h_square : concrete_mul (1 : ConcreteBinaryTower k) 1 = 1 := by
          rw [← one_is_1]
          rw [concrete_one_mul (recArg:=recArg)]  -- Assume concrete_mul 1 1 = 1
        rw [h_square]
        have h_div_lt : n / 2 < n := by
          apply Nat.div_lt_self
          simp [Nat.ne_zero_iff_zero_lt.mp h_n_zero]
          exact Nat.le_refl 2
        apply ih (n / 2) h_div_lt  -- Use ih for n / 2 < n
      · -- Odd case: n % 2 ≠ 0
        rw [if_neg h_mod]
        have h_square : concrete_mul (1 : ConcreteBinaryTower k) 1 = 1 := by
          rw [← one_is_1]
          rw [concrete_one_mul (recArg:=recArg)]  -- Assume concrete_mul 1 1 = 1
        rw [h_square]
        have h_div_lt : n / 2 < n := by
          apply Nat.div_lt_self
          simp [Nat.ne_zero_iff_zero_lt.mp h_n_zero]
          exact Nat.le_refl 2
        rw [ih (n / 2) h_div_lt]  -- Use ih for n / 2 < n
        rw [← one_is_1]
        rw [concrete_one_mul (recArg:=recArg)]  -- Assume concrete_mul 1 1 = 1

lemma concrete_mul_comm {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} {h_k: k > 0}
  (a b : ConcreteBinaryTower k) :
  concrete_mul a b = concrete_mul b a := by
  by_cases h_k_zero : k = 0
  · linarith
  · -- Inductive case: k > 0
    -- Approach: utilize concrete_mul_eq of level (k - 1)
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k)
    let p1 := split h_k a
    let p2 := split h_k b
    let a₁ := p1.fst
    let a₀ := p1.snd
    let b₁ := p2.fst
    let b₀ := p2.snd
    have h_split_a : split h_k a = (a₁, a₀) := by rfl
    have h_split_b : split h_k b = (b₁, b₀) := by rfl
    have h_a₁_a₀ : a = join h_k a₁ a₀ := by exact (join_of_split h_k a a₁ a₀) h_split_a
    have h_b₁_b₀ : b = join h_k b₁ b₀ := by exact (join_of_split h_k b b₁ b₀) h_split_b
    have h_a₁ : (split h_k a).1 = a₁ := by rw [h_split_a]
    have h_a₀ : (split h_k a).2 = a₀ := by rw [h_split_a]
    have h_b₁ : (split h_k b).1 = b₁ := by rw [h_split_b]
    have h_b₀ : (split h_k b).2 = b₀ := by rw [h_split_b]
    have h_lhs := concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=b) (a₁:=a₁)
      (a₀:=a₀) (b₁:=b₁) (b₀:=b₀) (h_a:=h_split_a) (h_b:=h_split_b)
    have h_rhs := concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=b) (b:=a) (a₁:=b₁)
      (a₀:=b₀) (b₁:=a₁) (b₀:=a₀) (h_a:=h_split_b) (h_b:=h_split_a)
    rw [h_lhs, h_rhs]
    rw [join_eq_join_iff]
    rw [recArgPrevLevel.mul_comm (a:=b₀) (b:=a₀), recArgPrevLevel.mul_comm (a:=a₁) (b:=b₁)]
    split_ands
    · rw [recArgPrevLevel.add_comm (a:=concrete_mul a₀ b₁) (b:=concrete_mul b₀ a₁)]
    · rfl

lemma concrete_mul_assoc {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} {h_k: k > 0}
  (a b c : ConcreteBinaryTower k) :
  concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c) := by
  by_cases h_k_zero : k = 0
  · linarith
  · -- Inductive case: k > 0
    -- Approach: utilize concrete_mul_eq of level (k - 1)
    -- ⊢ concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k)
    let p1 := split h_k a
    let p2 := split h_k b
    let p3 := split h_k c
    let a₁ := p1.fst
    let a₀ := p1.snd
    let b₁ := p2.fst
    let b₀ := p2.snd
    let c₁ := p3.fst
    let c₀ := p3.snd
    have h_split_a : split h_k a = (a₁, a₀) := by rfl
    have h_split_b : split h_k b = (b₁, b₀) := by rfl
    have h_split_c : split h_k c = (c₁, c₀) := by rfl
    have h_a₁_a₀ : a = join h_k a₁ a₀ := by exact (join_of_split h_k a a₁ a₀) h_split_a
    have h_b₁_b₀ : b = join h_k b₁ b₀ := by exact (join_of_split h_k b b₁ b₀) h_split_b
    have h_c₁_c₀ : c = join h_k c₁ c₀ := by exact (join_of_split h_k c c₁ c₀) h_split_c
    -- ⊢ concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
    have a_mul_b_eq := concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=b) (a₁:=a₁)
      (a₀:=a₀) (b₁:=b₁) (b₀:=b₀) (h_a:=h_split_a) (h_b:=h_split_b)
    have b_mul_c_eq := concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=b) (b:=c) (a₁:=b₁)
      (a₀:=b₀) (b₁:=c₁) (b₀:=c₀) (h_a:=h_split_b) (h_b:=h_split_c)
    set ab₁ := concrete_mul a₀ b₁ + concrete_mul b₀ a₁
      + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))
    set ab₀ := concrete_mul a₀ b₀ + concrete_mul a₁ b₁
    have h_split_a_mul_b: split h_k (concrete_mul a b) = (ab₁, ab₀) := by
      exact (split_of_join h_k (concrete_mul a b) ab₁ ab₀ a_mul_b_eq).symm
    set bc₁ := concrete_mul b₀ c₁ + concrete_mul c₀ b₁
      + concrete_mul (concrete_mul b₁ c₁) (Z (k - 1))
    set bc₀ := concrete_mul b₀ c₀ + concrete_mul b₁ c₁
    have h_split_b_mul_c: split h_k (concrete_mul b c) = (bc₁, bc₀) := by
      exact (split_of_join h_k (concrete_mul b c) bc₁ bc₀ b_mul_c_eq).symm

    set ab := concrete_mul a b
    set bc := concrete_mul b c
    -- rw [a_mul_b_eq, b_mul_c_eq]
    -- ⊢ concrete_mul ab c = concrete_mul a bc
    have a_mul_bc_eq := concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=bc) (a₁:=a₁)
      (a₀:=a₀) (b₁:=bc₁) (b₀:=bc₀) (h_a:=h_split_a) (h_b:=h_split_b_mul_c.symm)
    have ab_mul_c_eq := concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=ab) (b:=c) (a₁:=ab₁)
      (a₀:=ab₀) (b₁:=c₁) (b₀:=c₀) (h_a:=h_split_a_mul_b.symm) (h_b:=h_split_c)
    set a_bc₁ := concrete_mul a₀ bc₁ + concrete_mul bc₀ a₁
      + concrete_mul (concrete_mul a₁ bc₁) (Z (k - 1))
    set a_bc₀ := concrete_mul a₀ bc₀ + concrete_mul a₁ bc₁
    have h_split_a_bc: split h_k (concrete_mul a bc) = (a_bc₁, a_bc₀) := by
      exact (split_of_join h_k (concrete_mul a bc) a_bc₁ a_bc₀ a_mul_bc_eq).symm
    set ab_c₁ := concrete_mul ab₀ c₁ + concrete_mul c₀ ab₁
      + concrete_mul (concrete_mul ab₁ c₁) (Z (k - 1))
    set ab_c₀ := concrete_mul ab₀ c₀ + concrete_mul ab₁ c₁
    have h_split_ab_c: split h_k (concrete_mul ab c) = (ab_c₁, ab_c₀) := by
      exact (split_of_join h_k (concrete_mul ab c) ab_c₁ ab_c₀ ab_mul_c_eq).symm

    rw [a_mul_bc_eq, ab_mul_c_eq] -- convert concrete mul to join
    rw [join_eq_join_iff]
    -- ⊢ ab_c₁ = a_bc₁ ∧ ab_c₀ = a_bc₀
    unfold a_bc₁ ab_c₁ ab_c₀ a_bc₀ ab₀ ab₁ bc₀ bc₁ -- unfold all
    simp only [recArgPrevLevel.mul_right_distrib,
      recArgPrevLevel.mul_left_distrib] -- distribute all
    split_ands
    · -- ⊢ ab_c₁ = a_bc₁
      have t0 : concrete_mul (concrete_mul a₀ b₀) c₁ = concrete_mul a₀ (concrete_mul b₀ c₁) := by
        rw [recArgPrevLevel.mul_assoc (a:=a₀) (b:=b₀) (c:=c₁)]
      have t1: concrete_mul (concrete_mul a₁ b₁) c₁ = concrete_mul (concrete_mul b₁ c₁) a₁ := by
        rw [recArgPrevLevel.mul_assoc (a:=a₁) (b:=b₁) (c:=c₁)]
        rw [recArgPrevLevel.mul_comm (a:=a₁) (b:=concrete_mul b₁ c₁)]
      have t2: concrete_mul c₀ (concrete_mul a₀ b₁) = concrete_mul a₀ (concrete_mul c₀ b₁) := by
        rw [← recArgPrevLevel.mul_assoc (a:=c₀) (b:=a₀) (c:=b₁),
          ← recArgPrevLevel.mul_assoc (a:=a₀) (b:=c₀) (c:=b₁)]
        rw [recArgPrevLevel.mul_comm (a:=c₀) (b:=a₀)]
      have t3: concrete_mul c₀ (concrete_mul b₀ a₁) = (concrete_mul (concrete_mul b₀ c₀) a₁) := by
        rw [← recArgPrevLevel.mul_assoc (a:=c₀) (b:=b₀) (c:=a₁)]
        rw [recArgPrevLevel.mul_comm (a:=c₀) (b:=b₀)]
      have t4: concrete_mul (concrete_mul a₁ (concrete_mul c₀ b₁)) (Z (k - 1))
        = concrete_mul c₀ (concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))) := by
        rw [← recArgPrevLevel.mul_assoc (c:=Z (k-1))]
        rw [← recArgPrevLevel.mul_assoc (a:=c₀) (b:=a₁) (c:=b₁)]
        rw [recArgPrevLevel.mul_comm (a:=c₀) (b:=a₁),
          recArgPrevLevel.mul_assoc (a:=a₁) (b:=c₀) (c:=b₁)]
      have t5: concrete_mul a₀ (concrete_mul (concrete_mul b₁ c₁) (Z (k - 1)))
        = concrete_mul (concrete_mul (concrete_mul a₀ b₁) c₁) (Z (k - 1)) := by
        rw [← recArgPrevLevel.mul_assoc (c:=Z (k-1))]
        rw [← recArgPrevLevel.mul_assoc (a:=a₀) (b:=b₁) (c:=c₁)]
      have t6: concrete_mul (concrete_mul (concrete_mul b₀ a₁) c₁) (Z (k - 1))
        =  concrete_mul (concrete_mul a₁ (concrete_mul b₀ c₁)) (Z (k - 1)) := by
        rw [recArgPrevLevel.mul_comm (a:=b₀) (b:=a₁),
          recArgPrevLevel.mul_assoc (a:=a₁) (b:=b₀) (c:=c₁)]
      have t7: concrete_mul (concrete_mul (concrete_mul (concrete_mul a₁ b₁)
        (Z (k - 1))) c₁) (Z (k - 1)) = concrete_mul (concrete_mul a₁ (concrete_mul
          (concrete_mul b₁ c₁) (Z (k - 1)))) (Z (k - 1)) := by
        rw [← recArgPrevLevel.mul_assoc (c:=Z (k-1))]
        rw [recArgPrevLevel.mul_comm (a:=(concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)))) (b:=c₁)]
        rw [recArgPrevLevel.mul_comm (a:=a₁) (b:=b₁)]
        rw [← recArgPrevLevel.mul_assoc (c:=Z (k-1))]
        -- c1 (b1 a1) vs a1 (b1 c1) => convert to (c1 b1) a1 vs (c1 b) a1
        rw [recArgPrevLevel.mul_comm (a:=a₁) (b:=concrete_mul b₁ c₁)]
        rw [← recArgPrevLevel.mul_assoc (a:=c₁) (b:=b₁) (c:=a₁)]
        rw [recArgPrevLevel.mul_comm (a:=c₁) (b:=b₁)]
      rw [t0, t1, t2, t3, t4, t5, t6, t7]
      abel_nf
    · -- ⊢ ab_c₀ = a_bc₀
      have t_a₀_b₀_c₀ : concrete_mul (concrete_mul a₀ b₀) c₀
        = concrete_mul a₀ (concrete_mul b₀ c₀) := by
        rw [recArgPrevLevel.mul_assoc (a:=a₀) (b:=b₀) (c:=c₀)]
      have t_a₁_b₁_c₀ : concrete_mul (concrete_mul a₁ b₁) c₀
        = concrete_mul a₁ (concrete_mul c₀ b₁) := by
        rw [recArgPrevLevel.mul_assoc (a:=a₁) (b:=b₁) (c:=c₀),
        recArgPrevLevel.mul_comm (a:=c₀) (b:=b₁)]
      have t_a₀_b₁_c₁ : concrete_mul (concrete_mul a₀ b₁) c₁
        = concrete_mul a₀ (concrete_mul b₁ c₁) := by
        rw [recArgPrevLevel.mul_assoc (a:=a₀) (b:=b₁) (c:=c₁)]
      have t_b₀_a₁_c₁ : concrete_mul (concrete_mul b₀ a₁) c₁
        = concrete_mul a₁ (concrete_mul b₀ c₁) := by
        rw [recArgPrevLevel.mul_comm (a:=b₀) (b:=a₁),
        recArgPrevLevel.mul_assoc (a:=a₁) (b:=b₀) (c:=c₁)]
      have t_a₁_b₁_c₁_z : concrete_mul (concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))) c₁
        = concrete_mul a₁ (concrete_mul (concrete_mul b₁ c₁) (Z (k - 1))) := by
        rw [recArgPrevLevel.mul_comm (a:=concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))) (b:=c₁)]
        rw [←recArgPrevLevel.mul_assoc (c:=Z (k-1)), ←recArgPrevLevel.mul_assoc (c:=Z (k-1))]
        -- rewrite both sides
        rw [recArgPrevLevel.mul_comm (a:=b₁) (b:=c₁)]
        rw [←recArgPrevLevel.mul_assoc (a:=c₁) (b:=a₁)
          (c:=b₁), recArgPrevLevel.mul_comm (a:=c₁) (b:=a₁)]
        rw [recArgPrevLevel.mul_assoc (a:=a₁) (b:=c₁) (c:=b₁)]
      rw [t_a₀_b₀_c₀, t_a₁_b₁_c₀, t_a₀_b₁_c₁, t_b₀_a₁_c₁, t_a₁_b₁_c₁_z]
      abel_nf

lemma concrete_mul_left_distrib {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} {h_k: k > 0}
  (a b c : ConcreteBinaryTower k) :
    concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c := by
  by_cases h_k_zero : k = 0
  · linarith
  · -- Inductive case: k > 0
    -- Approach: utilize concrete_mul_eq of level (k - 1)
    -- ⊢ concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
    let recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k)
    let p1 := split h_k a
    let p2 := split h_k b
    let p3 := split h_k c
    let a₁ := p1.fst
    let a₀ := p1.snd
    let b₁ := p2.fst
    let b₀ := p2.snd
    let c₁ := p3.fst
    let c₀ := p3.snd
    have h_split_a : split h_k a = (a₁, a₀) := by rfl
    have h_split_b : split h_k b = (b₁, b₀) := by rfl
    have h_split_c : split h_k c = (c₁, c₀) := by rfl
    have h_a₁_a₀ : a = join h_k a₁ a₀ := by exact (join_of_split h_k a a₁ a₀) h_split_a
    have h_b₁_b₀ : b = join h_k b₁ b₀ := by exact (join_of_split h_k b b₁ b₀) h_split_b
    have h_c₁_c₀ : c = join h_k c₁ c₀ := by exact (join_of_split h_k c c₁ c₀) h_split_c
    have h_split_b_add_c : split h_k (b + c) = (b₁ + c₁, b₀ + c₀) := by
      exact split_sum_eq_sum_split h_k (x₀:=b) (x₁:=c) (hi₀:=b₁) (lo₀:=b₀)
        (hi₁:=c₁) (lo₁:=c₀) (h_split_x₀:=h_split_b) (h_split_x₁:=h_split_c)
    -- ⊢ concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c
    conv =>
      lhs
      -- rewrite a * (b + c)
      rw [concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=b+c) (a₁:=a₁)
        (a₀:=a₀) (b₁:=b₁ + c₁) (b₀:=b₀ + c₀) (h_a:=h_split_a) (h_b:=h_split_b_add_c.symm)]
    conv =>
      rhs
      rw [concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=b) (a₁:=a₁)
        (a₀:=a₀) (b₁:=b₁) (b₀:=b₀) (h_a:=h_split_a) (h_b:=h_split_b)]
      rw [concrete_mul_eq (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=c) (a₁:=a₁)
        (a₀:=a₀) (b₁:=c₁) (b₀:=c₀) (h_a:=h_split_a) (h_b:=h_split_c)]
    rw [join_add_join]
    rw [join_eq_join_iff]
    split_ands
    · -- ⊢ concrete_mul a₀ (b₁ + c₁) + concrete_mul (b₀ + c₀) a₁
      -- + concrete_mul (concrete_mul a₁ (b₁ + c₁)) (Z (k - 1)) =
      -- concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)) +
      -- (concrete_mul a₀ c₁ + concrete_mul c₀ a₁ + concrete_mul (concrete_mul a₁ c₁) (Z (k - 1)))
      set a := concrete_mul a₀ b₁ + concrete_mul b₀ a₁
      set b := concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))
      set c := (concrete_mul a₀ c₁ + concrete_mul c₀ a₁
        + concrete_mul (concrete_mul a₁ c₁) (Z (k - 1)))
      -- rhs is like a + b + c, but we have to bring it to a + (b + c) then a + (c + b)
      conv =>
        rhs
        rw [recArgPrevLevel.add_assoc (a:=a) (b:=b) (c:=c), recArgPrevLevel.add_comm (a:=b) (b:=c)]
        unfold a b c
        -- set t2 :=
      set t1 := concrete_mul a₁ c₁
      set t2 := concrete_mul a₁ b₁
      rw [add_assoc (b:=concrete_mul t1 (Z (k - 1))) (c:=concrete_mul t2 (Z (k - 1)))]
      have de_distrib := recArgPrevLevel.mul_right_distrib (a:=t1) (b:=t2) (c:=Z (k-1))
      rw [←de_distrib]
      unfold t1 t2
      have de_distrib_a₁_mul_sum_b₁_c₁ := recArgPrevLevel.mul_left_distrib (a:=a₁) (b:=b₁) (c:=c₁)
      rw [add_comm (a:=concrete_mul a₁ b₁) (b:=concrete_mul a₁ c₁)] at de_distrib_a₁_mul_sum_b₁_c₁
      rw [←de_distrib_a₁_mul_sum_b₁_c₁]
      rw [←recArgPrevLevel.add_assoc]
      have de_distrib_left_a₀_mul_sum_b₁_c₁ :=
        recArgPrevLevel.mul_left_distrib (a:=a₀) (b:=b₁) (c:=c₁)
      have de_distrib_right_a₁_mul_sum_b₀_c₀ :=
        recArgPrevLevel.mul_right_distrib (a:=b₀) (b:=c₀) (c:=a₁)
      conv =>
        rhs
        rw [←add_assoc, add_assoc (b:=concrete_mul b₀ a₁) (c:=concrete_mul a₀ c₁),
           add_comm (a:=concrete_mul b₀ a₁) (b:=concrete_mul a₀ c₁)]
        rw [←add_assoc, ←de_distrib_left_a₀_mul_sum_b₁_c₁]
        rw [add_assoc (b:=concrete_mul b₀ a₁) (c:=concrete_mul c₀ a₁)]
        rw [←de_distrib_right_a₁_mul_sum_b₀_c₀]
    · -- ⊢ concrete_mul a₀ (b₀ + c₀) + concrete_mul a₁ (b₁ + c₁) =
      -- concrete_mul a₀ b₀ + concrete_mul a₁ b₁ + (concrete_mul a₀ c₀ + concrete_mul a₁ c₁)
      rw [recArgPrevLevel.mul_left_distrib, recArgPrevLevel.mul_left_distrib]
      rw [←recArgPrevLevel.add_assoc, ←recArgPrevLevel.add_assoc]
      conv =>
        rhs
        rw [recArgPrevLevel.add_assoc (a:=concrete_mul a₀ b₀) (b:=concrete_mul a₁ b₁)
          (c:=concrete_mul a₀ c₀), recArgPrevLevel.add_comm (a:=concrete_mul a₁ b₁)
          (b:=concrete_mul a₀ c₀), ←recArgPrevLevel.add_assoc]

lemma concrete_mul_right_distrib {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m} {h_k: k > 0}
  (a b c : ConcreteBinaryTower k) :
    concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c := by
  rw [concrete_mul_comm (recArg:=recArg) (h_k:=h_k) (a:=(a+b)) (b:=c)]
  rw [concrete_mul_comm (recArg:=recArg) (h_k:=h_k) (a:=a) (b:=c)]
  rw [concrete_mul_comm (recArg:=recArg) (h_k:=h_k) (a:=b) (b:=c)]
  exact concrete_mul_left_distrib (recArg:=recArg) (h_k:=h_k) (a:=c) (b:=a) (c:=b)

instance instInvConcreteBTF: Inv (ConcreteBinaryTower k) where
  inv := concrete_inv

lemma concrete_mul_inv_cancel {recArg : (m : ℕ) → m < k → ConcreteBTFStepResult m}
  (a : ConcreteBinaryTower k) (h : a ≠ 0) :
  concrete_mul a (concrete_inv a) = one := by
  unfold concrete_inv
  by_cases h_k_zero : k = 0
  · rw [dif_pos h_k_zero]
    have h_2_pow_k_eq_1: 2 ^ k = 1 := by rw [h_k_zero]; norm_num
    let a0 : ConcreteBinaryTower 0 := Eq.mp (congrArg ConcreteBinaryTower h_k_zero) a
    have a0_is_eq_mp_a: a0 = Eq.mp (congrArg ConcreteBinaryTower h_k_zero) a := by rfl
    rcases concrete_eq_zero_or_eq_one (a := a) (h_k_zero:=h_k_zero) with (ha0 | ha1)
    · -- ha0: a = zero (k:=k)
      have a_is_zero: a = zero (k:=k) := ha0
      have a_is_0: a = 0 := by rw [←zero_is_0, a_is_zero]
      contradiction
    · -- ha1: a = 1
      have a_is_1: a = 1 := ha1
      have a_ne_0: a ≠ 0 := by rw [a_is_1]; exact one_ne_zero
      rw [if_neg a_ne_0]
      rw [←one_is_1]
      rw [concrete_mul_one (a:=a) (recArg:=recArg)]
      rw [ha1]
  · by_cases h_a_zero : a = 0
    · contradiction
    · rw [dif_neg h_k_zero]
      rw [dif_neg h_a_zero]

      by_cases h_a_one : a = 1
      · rw [dif_pos h_a_one]
        rw [←one_is_1]
        rw [concrete_mul_one (a:=a) (recArg:=recArg)]
        rw [h_a_one, one_is_1]
      · rw [dif_neg h_a_one]
        have h_k_gt_0 : k > 0 := Nat.zero_lt_of_ne_zero h_k_zero
        have recArgPrevLevel := recArg (k-1) (Nat.sub_one_lt_of_lt h_k_gt_0)
        let split_a := split h_k_gt_0 a
        let a₁ := split_a.fst
        let a₀ := split_a.snd
        have h_a_split : split h_k_gt_0 a = (a₁, a₀) := by rfl
        have h_a₁ : (split h_k_gt_0 a).1 = a₁ := by rfl
        have h_a₀ : (split h_k_gt_0 a).2 = a₀ := by rfl
        simp [h_a₁, h_a₀] -- resolve the match of split a
        -- distribute all concrete_mul over the addition
        simp only [recArgPrevLevel.mul_right_distrib, recArgPrevLevel.mul_left_distrib]
        -- NOTE: we have to exploit the special structure of concrete_inv for this
        sorry

lemma concrete_inv_one:
  concrete_inv (k:=k) 1 = 1 := by
  unfold concrete_inv
  by_cases h_k_zero : k = 0
  · simp only [h_k_zero, ↓reduceIte]; norm_num
  · simp only [h_k_zero, ↓reduceIte]; norm_num

instance instHDivConcreteBTF: HDiv (ConcreteBinaryTower k) (ConcreteBinaryTower k)
  (ConcreteBinaryTower k) where hDiv a b := a * (concrete_inv b)

lemma concrete_div_eq_mul_inv (a b : ConcreteBinaryTower k) : a / b = a * (concrete_inv b) := by
  rfl

instance instHPowConcreteBTF: HPow (ConcreteBinaryTower k) ℤ (ConcreteBinaryTower k) where
  hPow a n :=
    match n with
    | Int.ofNat m => concrete_pow_nat a m
    | Int.negSucc m =>
      -- n = -(m+1)
      if a = 0 then 0
      else concrete_pow_nat (concrete_inv a) (m + 1) -- a^(-(m+1)) = (a^(-1))^(m+1)

instance : Div (ConcreteBinaryTower k) where
  div a b := a * (concrete_inv b)

end InductiveConcreteBTFPropertiesProofs
-------------------------------------------------------------------------------------------

def InductiveConcreteBTFPropertiesAux (k : ℕ) (rec : ∀ m : ℕ, m < k → ConcreteBTFStepResult m):
  ConcreteBTFStepResult k :=
  match k with
  | 0 =>
    let result: ConcreteBTFStepResult 0 :={
      mul_eq := fun a b h_k _ _ _ _ _ _ => by
        have h_l_ne_lt_0 := Nat.not_lt_zero 0
        exact absurd h_k h_l_ne_lt_0,
      zero_mul := concrete_zero_mul0,
      zero_mul' := concrete_zero_mul0,
      mul_zero := concrete_mul_zero0,
      mul_zero' := concrete_mul_zero0,
      one_mul := concrete_one_mul0,
      mul_one := concrete_mul_one0,
      mul_assoc := concrete_mul_assoc0,
      mul_comm := concrete_mul_comm0,
      mul_left_distrib := concrete_mul_left_distrib0,
      mul_right_distrib := concrete_mul_right_distrib0,
      add_assoc := add_assoc,
      add_comm := add_comm,
      add_zero := add_zero,
      zero_add := zero_add,
      add_neg := neg_add_cancel,
      mul_inv_cancel := concrete_mul_inv_cancel (k:=0) (recArg := rec)
    }
    result
  | k + 1 =>
    -- rec : (m : ℕ) → m < k + 1 → ConcreteBTFStepResult m
    let result: ConcreteBTFStepResult (k+1) :={
      zero_mul := concrete_zero_mul (recArg := rec),
      zero_mul' := fun a => by rw [←zero_is_0]; exact concrete_zero_mul (recArg := rec) a
      mul_zero := concrete_mul_zero (recArg := rec),
      mul_zero' := fun a => by rw [←zero_is_0]; exact concrete_mul_zero (recArg := rec) a
      one_mul := concrete_one_mul (recArg := rec),
      mul_one := concrete_mul_one (recArg := rec),
      mul_assoc := concrete_mul_assoc (recArg := rec) (h_k := Nat.succ_pos k),
      mul_comm := concrete_mul_comm (recArg := rec) (h_k := Nat.succ_pos k),
      mul_left_distrib := concrete_mul_left_distrib (recArg := rec) (h_k := Nat.succ_pos k),
      mul_right_distrib := concrete_mul_right_distrib (recArg := rec) (h_k := Nat.succ_pos k),
      add_assoc := add_assoc,
      add_comm := add_comm,
      add_zero := add_zero,
      zero_add := zero_add,
      add_neg := neg_add_cancel,
      mul_inv_cancel := concrete_mul_inv_cancel (k:=k+1) (recArg := rec),
      mul_eq := concrete_mul_eq (k:=k+1) (recArg := rec),
    }
    result

def InductiveConcreteBTFProperties (k : ℕ) : ConcreteBTFStepResult k :=
  WellFounded.fix (measure id).wf (fun k rec => InductiveConcreteBTFPropertiesAux k rec) k

instance instRingConcrete {k:ℕ}: Ring (ConcreteBinaryTower k) where
  toAddCommGroup := inferInstance
  toOne := inferInstance
  mul := concrete_mul
  mul_assoc := (InductiveConcreteBTFProperties (k:=k)).mul_assoc
  one_mul := (InductiveConcreteBTFProperties (k:=k)).one_mul
  mul_one := (InductiveConcreteBTFProperties (k:=k)).mul_one
  left_distrib := (InductiveConcreteBTFProperties (k:=k)).mul_left_distrib
  right_distrib := (InductiveConcreteBTFProperties (k:=k)).mul_right_distrib
  zero_mul := (InductiveConcreteBTFProperties (k:=k)).zero_mul
  mul_zero := (InductiveConcreteBTFProperties (k:=k)).mul_zero

  natCast n := natCast n
  natCast_zero := natCast_zero
  natCast_succ n := natCast_succ n
  intCast n := intCast n
  intCast_ofNat n := intCast_ofNat n
  intCast_negSucc n := intCast_negSucc n

instance instDivisionRingConcrete {k:ℕ}: DivisionRing (ConcreteBinaryTower k) where
  toRing := instRingConcrete (k:=k)
  inv := concrete_inv
  exists_pair_ne := concrete_exists_pair_ne (k := k)
  mul_inv_cancel := (InductiveConcreteBTFProperties (k:=k)).mul_inv_cancel
  inv_zero := concrete_inv_zero
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

instance instFieldConcrete {k:ℕ}: Field (ConcreteBinaryTower k) where
  toDivisionRing := instDivisionRingConcrete (k:=k)
  mul_comm := (InductiveConcreteBTFProperties (k:=k)).mul_comm

section Tests

#check instFieldConcrete (k:=0)
#check instFieldConcrete (k:=5)

#eval bitVecToString 5 (BitVec.ofNat 5 1)  -- 5 in 4 bits is 0101
#eval split (k:=5) (by omega) (fromNat (k:=5) 1) -- 1 => (0, 1)
#eval (Z 2).toBitString -- 01|00
#eval (one (k:=2)).toBitString -- 0001
#eval (zero (k:=2)).toBitString -- 0000

#eval (fromNat (k:=2) 3).toBitString
#eval (fromNat (k:=3) 3).toBitString
#eval (fromNat (k:=4) 3).toBitString

#eval Z (0)
#eval Z (1)
#eval Z (2)
#eval Z (3)
#eval Z (4)
#eval Z (5)
#eval Z (6)

#eval (fromNat (k:=1) 3) * (fromNat (k:=1) 3) -- 9#4
#eval (fromNat (k:=4) 3) * (fromNat (k:=4) 3) -- 9#4
#eval (fromNat (k:=2) 3) * (fromNat (k:=2) 3) -- 9#4
#eval (fromNat (k:=5) 7) * (fromNat (k:=5) 20) -- 9#4
#eval add (fromNat (k:=9) 1) (fromNat (k:=9) 7) -- -- 000001 xor 001101 = 001100 = 6#512
#eval (fromNat (k:=9) 1) + (fromNat (k:=9) 7)

-- Test function to bundle multiple evaluations
def runTests : IO Unit := do
  -- Test k = 0 (field of order 2, like GF(2))
  let k0 : ℕ := 0
  let zero0 := zero (k := k0)
  let one0 := one (k := k0)
  let five0 := fromNat (k := k0) 5  -- 5 mod 2 = 1 in k=0
  IO.println s!"--- Tests for k = {k0} (width = {width k0}) ---"
  IO.println s!"zero = {zero0.toBitString}"
  IO.println s!"one = {one0.toBitString}"
  IO.println s!"fromNat 5 = {five0.toBitString}"
  IO.println s!"zero + one = {(add zero0 one0).toBitString}"
  IO.println s!"one + one = {(add one0 one0).toBitString}"
  IO.println s!"one * one = {(concrete_mul one0 one0).toBitString}"
  IO.println s!"zero * one = {(concrete_mul zero0 one0).toBitString}"

  -- Test k = 1 (field of order 4, like GF(4))
  let k1 : ℕ := 1
  let zero1 := zero (k := k1)
  let one1 := one (k := k1)
  let two1 := fromNat (k := k1) 2
  let three1 := fromNat (k := k1) 3
  IO.println s!"--- Tests for k = {k1} (width = {width k1}) ---"
  IO.println s!"zero = {zero1.toBitString}"
  IO.println s!"one = {one1.toBitString}"
  IO.println s!"fromNat 2 = {two1.toBitString}"
  IO.println s!"fromNat 3 = {three1.toBitString}"
  IO.println s!"one + two = {(add one1 two1).toBitString}"
  IO.println s!"two + three = {(add two1 three1).toBitString}"
  IO.println s!"one * two = {(concrete_mul one1 two1).toBitString}"
  IO.println s!"two * three = {(concrete_mul two1 three1).toBitString}"

  -- Test k = 2 (field of order 16, like GF(16))
  let k2 : ℕ := 2
  let zero2 := zero (k := k2)
  let one2 := one (k := k2)
  let five2 := fromNat (k := k2) 5
  let seven2 := fromNat (k := k2) 7
  IO.println s!"--- Tests for k = {k2} (width = {width k2}) ---"
  IO.println s!"zero = {zero2.toBitString}"
  IO.println s!"one = {one2.toBitString}"
  IO.println s!"fromNat 5 = {five2.toBitString}"
  IO.println s!"fromNat 7 = {seven2.toBitString}"
  IO.println s!"five + seven = {(add five2 seven2).toBitString}"
  IO.println s!"five * one = {(concrete_mul five2 one2).toBitString}"
  IO.println s!"five * seven = {(concrete_mul five2 seven2).toBitString}"

-- Run the tests
#eval runTests

end Tests

end ConcreteDefinition
end BinaryTower

#check BinaryTower.ConcreteDefinition.instFieldConcrete (k:=2)
