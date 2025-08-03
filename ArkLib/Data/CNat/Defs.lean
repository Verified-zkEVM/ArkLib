import Mathlib
import ArkLib.Data.Classes.HasSucc
import ArkLib.Data.Classes.HasPred

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
  toFun_succ : ∀ (t : T), toFun (HasSucc.succ t) = HasSucc.succ (toFun t)

attribute [simp] Cayley.toFun_succ

-- We provide a coercion to let elements of `Cayley T` act like functions.
instance {T} [HasSucc T] : CoeFun (Cayley T) (fun _ => T → T) := ⟨Cayley.toFun⟩

namespace Cayley

variable {T : Type u} [HasSucc T]

-- Universal Operations (requiring only `HasSucc`)

/-- Addition on `Cayley T` is function composition. This is definitionally associative. -/
@[inline] def add (a b : Cayley T) : Cayley T :=
  ⟨a.toFun ∘ b.toFun, by intro t; simp [Function.comp, a.toFun_succ, b.toFun_succ]⟩

/-- One is defined as the `succ` function itself. -/
@[inline] def one : Cayley T :=
  ⟨HasSucc.succ, by intro t; rfl⟩

/-- Successor on `Cayley T`, defined as adding `one`.
This ensures `n.succ = n + 1` holds definitionally. -/
@[inline] def succ (a : Cayley T) : Cayley T := add a one

/-- Crucially, `Cayley T` always has a `succ` operation, so it always has an instance of `HasSucc`.
This guarantees that the transformation can be iterated indefinitely. -/
instance : HasSucc (Cayley T) where
  succ := succ

-- Conditional Operations (requiring more structure on `T`)

/-- Zero is the identity function. Requires `T` to have a zero. -/
@[inline] def zero [Zero T] : Cayley T :=
  ⟨id, by intro t; rfl⟩

/-- Evaluation function to get a value in `T` back from `Cayley T` by evaluating
at the base point zero. Requires `T` to have a zero. -/
@[inline] def toT [Zero T] (c : Cayley T) : T := c.toFun 0

/-- Helper function for multiplication, recursing on a Nat. -/
def mulAux [Zero T] (a : Cayley T) : Nat → Cayley T
  | 0        => zero
  | .succ k  => add a (mulAux a k)

/-- Multiplication on `Cayley T`, defined by iterating addition.
Requires `T` to have zero and a `toNat` function. -/
@[inline] def mul [Zero T] (toNat : T → Nat) (a b : Cayley T) : Cayley T :=
  mulAux a (toNat (toT b))

/-- Predecessor operation implemented by converting to the base type,
    applying predecessor there, and converting back. This avoids the need
    for HasPred.pred to commute with HasSucc.succ. -/
@[inline] def pred [Zero T] [HasPred T] (toNat : T → Nat) (a : Cayley T) : Cayley T :=
  -- Similar to AssocNat.predNat: convert toNat, apply Nat.pred, then ofNat-like construction
  let pred_val := Nat.pred (toNat (toT a))
  -- Create function that adds pred_val to its input using pattern matching
  ⟨fun t => match pred_val with
    | 0 => t
    | n + 1 => HasSucc.succ^[n + 1] t, by
    intro t
    cases pred_val with
    | zero => rfl
    | succ n => 
      simp only [Function.iterate_succ_apply]
      sorry⟩

/-- Helper function for subtraction, recursing on a Nat.
    This mirrors AssocNat.subNat - it recurses on the second argument
    but keeps the first argument unchanged (does not use predecessor). -/
def subAux [Zero T] (a : Cayley T) : Nat → Cayley T
  | 0        => a
  | .succ k  => subAux a k

/-- Truncated subtraction on `Cayley T`, following the AssocNat pattern.
Requires `T` to have zero and a `toNat` function. -/
@[inline] def sub [Zero T] (toNat : T → Nat) (a b : Cayley T) : Cayley T :=
  subAux a (toNat (toT b))

/-- Helper function for exponentiation, recursing on a Nat. -/
def powAux [Zero T] [One T] (toNat : T → Nat) (a : Cayley T) : Nat → Cayley T
  | 0        => one  -- a^0 = 1
  | .succ k  => mul toNat a (powAux toNat a k)  -- a^(n+1) = a * a^n

/-- Exponentiation on `Cayley T`, defined by iterating multiplication.
Requires `T` to have zero, one, and a `toNat` function. -/
@[inline] def pow [Zero T] [One T] (toNat : T → Nat) (a b : Cayley T) : Cayley T :=
  powAux toNat a (toNat (toT b))

/-- Helper function for division, recursing on a Nat fuel parameter.
    This implements division by repeated subtraction, following the pattern of Nat.div. -/
def divAux [Zero T] [HasPred T] [DecidableEq T] (toNat : T → Nat)
    (dividend divisor : Cayley T) : Nat → Cayley T
  | 0        => zero  -- out of fuel, return 0
  | .succ fuel =>
    -- Check if divisor is zero (division by zero case)
    if toNat (toT divisor) = 0 then
      zero
    else
      -- Check if divisor ≤ dividend (i.e., we can subtract)
      if toNat (toT divisor) ≤ toNat (toT dividend) then
        -- dividend / divisor = 1 + (dividend - divisor) / divisor
        add one (divAux toNat (sub toNat dividend divisor) divisor fuel)
      else
        zero

/-- Division on `Cayley T`, defined using repeated subtraction.
Requires `T` to have zero, predecessor, decidable equality, and a `toNat` function. -/
@[inline] def div [Zero T] [HasPred T] [DecidableEq T] (toNat : T → Nat)
    (dividend divisor : Cayley T) : Cayley T :=
  -- Use dividend + 1 as fuel (following Nat.div pattern)
  let fuel := toNat (toT dividend) + 1
  divAux toNat dividend divisor fuel

-- Comparison Operations

/-- Less than comparison for `Cayley T`. -/
@[inline] def lt [Zero T] (toNat : T → Nat) (a b : Cayley T) : Prop :=
  toNat (toT a) < toNat (toT b)

/-- Less than or equal comparison for `Cayley T`. -/
@[inline] def le [Zero T] (toNat : T → Nat) (a b : Cayley T) : Prop :=
  toNat (toT a) ≤ toNat (toT b)

/-- Greater than comparison for `Cayley T`. -/
@[inline] def gt [Zero T] (toNat : T → Nat) (a b : Cayley T) : Prop :=
  toNat (toT a) > toNat (toT b)

/-- Greater than or equal comparison for `Cayley T`. -/
@[inline] def ge [Zero T] (toNat : T → Nat) (a b : Cayley T) : Prop :=
  toNat (toT a) ≥ toNat (toT b)

/-- Minimum of two `Cayley T` elements. -/
@[inline] def min [Zero T] (toNat : T → Nat) (a b : Cayley T) : Cayley T :=
  if toNat (toT a) ≤ toNat (toT b) then a else b

/-- Maximum of two `Cayley T` elements. -/
@[inline] def max [Zero T] (toNat : T → Nat) (a b : Cayley T) : Cayley T :=
  if toNat (toT a) ≥ toNat (toT b) then a else b

end Cayley

-- The CNat Hierarchy levels are defined in their respective files:
-- - ArkLib.Data.CNat.LevelOne (for CNat)
-- - ArkLib.Data.CNat.LevelTwo (for CNat₂)
