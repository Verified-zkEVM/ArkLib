/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CNat.Defs

/-!
# Level One of the CNat Hierarchy: CNat

This file defines `CNat`, the first level of the Cayley transformation hierarchy.
`CNat` is isomorphic to the original `AssocNat` and has the property that addition
is definitionally associative.

`CNat` is defined as `Cayley Nat`.
-/

/-- `CNat` is `Cayley Nat`. -/
abbrev CNat := Cayley Nat

namespace CNat

-- ToNat instance for CNat. This unfolds to `fun a => a.toFun 0`.
instance : ToNat CNat := inferInstance

/-- `0` is the identity function on `Nat`. -/
@[inline] abbrev zero : CNat := Cayley.zero

/-- `1` is the successor function on `Nat`. -/
@[inline] abbrev one : CNat := Cayley.one

/-- Addition on `CNat` is function composition. -/
@[inline] abbrev add : CNat → CNat → CNat := Cayley.add

/-- Subtraction for `CNat`. -/
@[inline] abbrev sub : CNat → CNat → CNat := Cayley.sub

/-- Multiplication for `CNat`. -/
@[inline] abbrev mul : CNat → CNat → CNat := Cayley.mul

/-- Division for `CNat`. -/
@[inline] abbrev div : CNat → CNat → CNat := Cayley.div

/-- Exponentiation for `CNat`. -/
@[inline] abbrev pow : CNat → CNat → CNat := Cayley.pow

/-- Successor for `CNat`. -/
@[inline] abbrev succ : CNat → CNat := Cayley.succ

/-- Predecessor for `CNat`. -/
@[inline] abbrev pred : CNat → CNat := Cayley.pred

/-- Less than for `CNat`. -/
abbrev lt : CNat → CNat → Prop := Cayley.lt

/-- Less than or equal for `CNat`. -/
abbrev le : CNat → CNat → Prop := Cayley.le

/-- Minimum for `CNat`. -/
abbrev min : CNat → CNat → CNat := Cayley.min

/-- Maximum for `CNat`. -/
abbrev max : CNat → CNat → CNat := Cayley.max

/-- Convert a `k : Nat` into a `CNat`, which represents the function `λ m, m + k`. -/
@[inline] abbrev ofNat (k : Nat) : CNat :=
  ⟨fun m => m + k, fun m => Nat.succ_add m k⟩

-- Typeclass instances

instance : HasPred CNat where
  pred := pred

instance : LT CNat where
  lt := lt

instance : LE CNat where
  le := le

instance : Min CNat where
  min := min

instance : Max CNat where
  max := max

instance : DecidableEq CNat := by
  intro a b
  by_cases h : ToNat.toNat a = ToNat.toNat b
  · right
    ext t
    -- This needs more work to prove properly
    sorry
  · left
    intro heq
    exact h (by rw [heq])

-- Definitional equality theorems

/-- `a + 0 = a` holds definitionally. -/
@[simp] theorem add_zero {a : CNat} : a + 0 = a := rfl

/-- `0 + a = a` holds definitionally. -/
@[simp] theorem zero_add {a : CNat} : 0 + a = a := rfl

/-- Addition is definitionally associative. -/
theorem add_assoc (a b c : CNat) : (a + b) + c = a + (b + c) := rfl

/-- `a * 0 = 0` holds definitionally. -/
@[simp] theorem mul_zero {a : CNat} : a * 0 = 0 := rfl

/-- `a * 1 = a` holds definitionally. -/
@[simp] theorem mul_one {a : CNat} : a * 1 = a := rfl

-- Propositional theorems (mirroring AssocNat.lean)

/-- `0 * a = 0` holds only propositionally. -/
theorem zero_mul {a : CNat} : 0 * a = 0 := by
  change mul zero a = zero
  ext n
  simp [mul, zero]
  induction h : a.toNat with
  | zero => simp [zero, Cayley.mulAux, toNat, Cayley.mul, Cayley.zero]
  | succ n ih => simp [Cayley.mulAux, toNat, ih, h, Cayley.mul, Cayley.add, Cayley.one]

/-- `1 * a = a` holds only propositionally. -/
@[simp] theorem one_mul {a : CNat} : 1 * a = a := by
  change mul one a = a
  ext n
  simp [mul, one]
  induction h : a.toNat with
  | zero => simp [zero, Cayley.mulAux, toNat]; simp [toNat] at h; sorry
  | succ n ih => simp [Cayley.mulAux, toNat, ih, h]; sorry

/-- `(succ a) * b = a * b + b` holds only propositionally. -/
theorem succ_mul {a b : CNat} : (succ a) * b = a * b + b := by sorry

/-- `a * (b + c) = a * b + a * c` holds only propositionally. -/
theorem mul_add {a b c : CNat} : a * (b + c) = a * b + a * c := by sorry

/-- `toNat` commutes with successor. -/
@[simp] theorem toNat_succ (t : CNat) : toNat (succ t) = (toNat t).succ := by
  simp [succ, toNat, add, one]

/-- Extensionality theorem for `CNat`. -/
@[ext]
theorem ext' {a b : CNat} (h : a.toFun 0 = b.toFun 0) : a = b := by
  ext m
  induction m with
  | zero => simp [h]
  | succ m ih => simp [ih]

/-- `ofNat` commutes with successor. -/
@[simp] theorem ofNat_succ (n : Nat) : ofNat n.succ = succ (ofNat n) := by
  ext
  simp [ofNat, succ, one, add, Nat.add_comm]

/-- Every endomap commuting with `Nat.succ` is addition by a constant. -/
theorem toFun_eq_const_plus (t : CNat) : ∀ m : Nat, t.toFun m = t.toFun 0 + m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => simp [ih, Nat.add_assoc]

/-- `toNat` turns composition into addition. -/
@[simp] theorem toNat_add (a b : CNat) : toNat (add a b) = toNat a + toNat b := by
  -- (a ∘ b) 0 = a (b 0)
  dsimp [toNat, add, Function.comp]
  have := toFun_eq_const_plus a (b.toFun 0)
  simpa using this

/-- `toNat` turns multiplication into multiplication. -/
private theorem toNat_mulNat (a : CNat) (k : Nat) : toNat (Cayley.mulNat a k) = toNat a * k := by
  induction k with
  | zero => simp [Cayley.mulNat, toNat, zero]
  | succ k ih => sorry

@[simp] theorem toNat_mul (a b : CNat) : toNat (mul a b) = toNat a * toNat b := by
  dsimp [mul]
  exact toNat_mulNat a (toNat b)

/-- `ofNat` respects addition. -/
@[simp] theorem ofNat_add (n m : Nat) : ofNat (n + m) = add (ofNat n) (ofNat m) := by
  ext
  simp [ofNat, add, Nat.add_comm, Nat.add_left_comm]

/-- `toNat` is the left inverse of `ofNat`. -/
@[simp] theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  simp [toNat, ofNat]

/-- `ofNat` is the right inverse of `toNat`. -/
@[simp] theorem ofNat_toNat (t : CNat) : ofNat (toNat t) = t := by
  ext
  simp [ofNat, toNat]

/-- The explicit equivalence `Nat ≃ CNat`. -/
@[simps] def equivNat : Nat ≃ CNat where
  toFun := ofNat
  invFun := toNat
  left_inv := by
    intro n; simp
  right_inv := by
    intro t; simp

/-- The less-than relation is well-defined. -/
theorem lt_iff_toNat_lt (a b : CNat) : a < b ↔ toNat a < toNat b := by
  rfl

/-- The less-equal relation is well-defined. -/
theorem le_iff_toNat_le (a b : CNat) : a ≤ b ↔ toNat a ≤ toNat b := by
  rfl

end CNat
