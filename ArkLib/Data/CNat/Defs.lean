/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib
import ArkLib.Data.Classes.HasSucc
import ArkLib.Data.Classes.HasPred
import ArkLib.Data.Classes.ToNat

/-!
# General Cayley Transformation Framework

This file implements a general framework for the Cayley transformation that generalizes
the `AssocNat` construction. The transformation takes a type `T` with a successor operation
and produces `Cayley T` where addition is definitionally associative.

By iteratively applying this transformation, we create the `CNat` hierarchy where
higher-order operations gain definitional associativity properties.
-/

universe u v w

/-- The `Cayley T` type is a structure containing an endomorphism on `T` along with a proof
that this function commutes with `succ`. This is the key property that enables definitional
associativity. -/
@[ext]
structure Cayley (T : Type u) [HasSucc T] where
  /-- The underlying endomorphism on T. -/
  toFun : T → T
  /-- The proof that the function commutes with `succ`.
      This is the key property that enables definitional associativity. -/
  toFun_succ : ∀ (t : T), toFun (succ' t) = succ' (toFun t)

export Cayley (toFun_succ)

attribute [simp] toFun_succ

-- We provide a coercion to let elements of `Cayley T` act like functions.
instance {T} [HasSucc T] : CoeFun (Cayley T) (fun _ => T → T) := ⟨Cayley.toFun⟩

namespace Cayley

variable {T : Type u} [HasSucc T]

-- Universal Operations (requiring only `HasSucc`)

/-- Zero is the identity function -/
@[inline] def zero : Cayley T :=
  ⟨id, by intro t; rfl⟩

/-- Addition on `Cayley T` is function composition. This is definitionally associative. -/
@[inline] def add (a b : Cayley T) : Cayley T :=
  ⟨a.toFun ∘ b.toFun, by intro t; simp [Function.comp, a.toFun_succ, b.toFun_succ]⟩

/-- One is defined as the `succ` function itself. -/
@[inline] def one : Cayley T :=
  ⟨succ', by intro t; rfl⟩

/-- Successor on `Cayley T`, defined as adding `one`.
This ensures `n.succ = n + 1` holds definitionally. -/
@[inline] def succ (a : Cayley T) : Cayley T := add a one

instance : Zero (Cayley T) where
  zero := zero

instance : One (Cayley T) where
  one := one

instance : Add (Cayley T) where
  add := add

/-- Crucially, `Cayley T` always has a `succ` operation, so it always has an instance of `HasSucc`.
This guarantees that the transformation can be iterated indefinitely. -/
instance : HasSucc (Cayley T) where
  succ' := succ

/-- Create a `Cayley T` element from a `Nat` by iterating the `succ` function. -/
@[inline] def ofNat (n : Nat) : Cayley T :=
  ⟨fun t => succ'^[n] t, Function.iterate_succ_apply' succ' n⟩

/-- `Cayley T` has an `OfNat` instance for all `Nat`s defined by iterating the `succ` function. -/
instance {n : ℕ} : OfNat (Cayley T) n where
  ofNat := ofNat n

-- Conditional Operations (requiring more structure on `T`)

/-- Evaluation function to get a value in `T` back from `Cayley T` by evaluating
at the base point zero. Requires `T` to have a zero. -/
@[inline] def toT [Zero T] (c : Cayley T) : T := c.toFun 0

instance [Zero T] [ToNat T] : ToNat (Cayley T) where
  toNat := ToNat.toNat ∘ toT

/-- Multiply a `Cayley T` element by a `Nat`, via recursion on the second argument. -/
def mulNat [Zero T] (a : Cayley T) : Nat → Cayley T
  | 0        => zero
  | .succ k  => add a (mulNat a k)

/-- Multiplication on `Cayley T`, defined by iterating addition.
Requires `T` to have zero and a `ToNat` instance. -/
@[inline] def mul [Zero T] [ToNat T] (a b : Cayley T) : Cayley T :=
  mulNat a ↑b

instance [Zero T] [ToNat T] : Mul (Cayley T) where
  mul := mul

/-- Predecessor operation implemented by converting to the base type,
    applying predecessor there, and converting back. This avoids the need
    for HasPred.pred to commute with HasSucc.succ. -/
@[inline] def pred [Zero T] [ToNat T] (a : Cayley T) : Cayley T :=
  match (↑a : Nat) with
  | 0 => zero
  | Nat.succ n => ofNat n

theorem pred_succ {T : Type u} [HasSucc T] [Zero T] [ToNat T] (x : Cayley T) :
    pred (succ x) = x := by
  simp [pred, succ, add, one]
  sorry

instance [Zero T] [ToNat T] : HasPred (Cayley T) where
  pred' := pred

-- instance [Zero T] [ToNat T] : LawfulHasPred (Cayley T) where
--   pred'_succ := pred_succ

/-- Helper function for subtraction, recursing on a Nat.
    This mirrors AssocNat.subNat - it recurses on the second argument
    but keeps the first argument unchanged (does not use predecessor). -/
def subNat [Zero T] [ToNat T] (a : Cayley T) : Nat → Cayley T
  | 0        => a
  | .succ k  => pred (subNat a k)

/-- Truncated subtraction on `Cayley T`, following the AssocNat pattern.
Requires `T` to have zero and a `ToNat` instance. -/
@[inline] def sub [Zero T] [ToNat T] (a b : Cayley T) : Cayley T :=
  subNat a ↑b

instance [Zero T] [ToNat T] : Sub (Cayley T) where
  sub := sub

/-- Helper function for exponentiation, recursing on a Nat. -/
def powNat [Zero T] [One T] [ToNat T] (a : Cayley T) : Nat → Cayley T
  | 0        => one  -- a^0 = 1
  | .succ k  => mul a (powNat a k)  -- a^(n+1) = a * a^n

instance [Zero T] [One T] [ToNat T] : NatPow (Cayley T) where
  pow := powNat

/-- Exponentiation on `Cayley T`, defined by iterating multiplication.
Requires `T` to have zero, one, and a `ToNat` instance. -/
@[inline] def pow [Zero T] [One T] [ToNat T] (a b : Cayley T) : Cayley T :=
  powNat a ↑b

instance [Zero T] [One T] [ToNat T] : HomogeneousPow (Cayley T) where
  pow := pow

/-- Helper function for division, recursing on a Nat fuel parameter.
    This implements division by repeated subtraction, following the pattern of Nat.div. -/
def divNat [Zero T] [DecidableEq T] [ToNat T]
    (dividend divisor : Cayley T) : Nat → Cayley T
  | 0        => zero  -- out of fuel, return 0
  | .succ fuel =>
    -- Check if divisor is zero (division by zero case)
    if (↑divisor : Nat) = 0 then
      zero
    else
      -- Check if divisor ≤ dividend (i.e., we can subtract)
      if (↑divisor : Nat) ≤ (↑dividend : Nat) then
        -- dividend / divisor = 1 + (dividend - divisor) / divisor
        add one (divNat (sub dividend divisor) divisor fuel)
      else
        zero

/-- Division on `Cayley T`, defined using repeated subtraction.
Requires `T` to have zero, predecessor, decidable equality, and a `ToNat` instance. -/
@[inline] def div [Zero T] [DecidableEq T] [ToNat T]
    (dividend divisor : Cayley T) : Cayley T :=
  -- Use dividend + 1 as fuel (following Nat.div pattern)
  letI fuel := (↑dividend : Nat) + 1
  divNat dividend divisor fuel

instance [Zero T] [DecidableEq T] [ToNat T] : Div (Cayley T) where
  div := div

/-- Helper function for modulo, recursing on a Nat fuel parameter.
    This implements modulo by repeated subtraction. -/
def modNat [Zero T] [DecidableEq T] [ToNat T]
    (dividend divisor : Cayley T) : Nat → Cayley T
  | 0        => dividend  -- out of fuel, return dividend
  | .succ fuel =>
    -- Check if divisor is zero (mod zero case - undefined, return dividend)
    if (↑divisor : Nat) = 0 then
      dividend
    else
      -- Check if divisor ≤ dividend (i.e., we can subtract)
      if (↑divisor : Nat) ≤ (↑dividend : Nat) then
        -- dividend % divisor = (dividend - divisor) % divisor
        modNat (sub dividend divisor) divisor fuel
      else
        dividend

/-- Modulo operation on `Cayley T`, defined using repeated subtraction.
Requires `T` to have zero, decidable equality, and a `ToNat` instance. -/
@[inline] def mod [Zero T] [DecidableEq T] [ToNat T]
    (dividend divisor : Cayley T) : Cayley T :=
  -- Use dividend + 1 as fuel (following Nat.mod pattern)
  letI fuel := (↑dividend : Nat) + 1
  modNat dividend divisor fuel

instance [Zero T] [DecidableEq T] [ToNat T] : Mod (Cayley T) where
  mod := mod

-- Comparison Operations

/-- Less than comparison for `Cayley T`. -/
@[inline] def lt [Zero T] [ToNat T] (a b : Cayley T) : Prop :=
  (↑a : Nat) < (↑b : Nat)

instance [Zero T] [ToNat T] : LT (Cayley T) where
  lt := lt

/-- Less than or equal comparison for `Cayley T`. -/
@[inline] def le [Zero T] [ToNat T] (a b : Cayley T) : Prop :=
  (↑a : Nat) ≤ (↑b : Nat)

instance [Zero T] [ToNat T] : LE (Cayley T) where
  le := le

/-- Greater than comparison for `Cayley T`. -/
@[inline] def gt [Zero T] [ToNat T] (a b : Cayley T) : Prop :=
  (↑a : Nat) > (↑b : Nat)

/-- Greater than or equal comparison for `Cayley T`. -/
@[inline] def ge [Zero T] [ToNat T] (a b : Cayley T) : Prop :=
  (a : Nat) ≥ (b : Nat)

/-- Minimum of two `Cayley T` elements. -/
@[inline] def min [Zero T] [ToNat T] (a b : Cayley T) : Cayley T :=
  if (a : Nat) ≤ (b : Nat) then a else b

/-- Maximum of two `Cayley T` elements. -/
@[inline] def max [Zero T] [ToNat T] (a b : Cayley T) : Cayley T :=
  if (a : Nat) ≥ (b : Nat) then a else b

-- Decidable instances

/-- Decidable equality for `Cayley T` based on `ToNat` conversion.
    Note: This is a simplified implementation that assumes `ToNat` determines equality. -/
instance [Zero T] [ToNat T] : DecidableEq (Cayley T) := fun a b =>
  if h : (↑a : Nat) = (↑b : Nat) then
    isTrue (by
      -- For now, we use the extensionality theorem and assume that
      -- elements with the same ToNat value are equal.
      -- A full proof would require showing that successor-preserving functions
      -- are uniquely determined by their value at 0.
      ext x
      sorry)
  else
    isFalse (fun heq => h (by simp [heq]))

/-- Decidable less-than for `Cayley T`. -/
instance [Zero T] [ToNat T] : DecidableRel (@LT.lt (Cayley T) _) := fun a b =>
  Nat.decLt (↑a) (↑b)

/-- Decidable less-equal for `Cayley T`. -/
instance [Zero T] [ToNat T] : DecidableRel (@LE.le (Cayley T) _) := fun a b =>
  Nat.decLe (↑a) (↑b)

end Cayley

/-- The iterations of the Cayley construction, which inductively builds the `i`-th iterated Cayley
  encoding of `Nat` along with the successor operation for the `i`-th level. -/
def CayleyCons (n : ℕ) : (T : Type) × (HasSucc T) := match n with
| 0 => ⟨Nat, HasSucc.instNat⟩
| .succ n => ⟨@Cayley (CayleyCons n).1 (CayleyCons n).2,
  @Cayley.instHasSucc (CayleyCons n).1 (CayleyCons n).2⟩

/-- The `i`-th iterated Cayley encoding of `Nat`. -/
def CayleyNat (n : ℕ) : Type := (CayleyCons n).1

/-- The `HasSucc` instance for the `i`-th iterated Cayley encoding of `Nat`. -/
instance {n : ℕ} : HasSucc (CayleyNat n) := (CayleyCons n).2
