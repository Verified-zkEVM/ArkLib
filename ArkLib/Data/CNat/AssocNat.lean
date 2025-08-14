import Mathlib
import ArkLib.Data.Classes.ToNat

/-!
# Alternate representation of `Nat` with definitional associativity

We define `AssocNat`, following the (Zulip comment by Trebor
Huang)[https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Nat.20add.20is.20not.20associative/near/396000000].

It's mostly a curiosity for now. The motivation is that one could define `Fin` on `AssocNat`, so
that one can define an append operation on `Fin n → α` (fin vectors) that is definitionally
associative.
-/

/-
AssocNat: natural numbers represented by endomorphisms of `Nat`
that commute with `Nat.succ`.

• The data is just `Nat → Nat`.
• The commuting-with-succ proof lives in `Prop`, so it is erased
  by the kernel; two values that differ only in that proof are
  definitionally equal (`Prop` is a definitional subsingleton).
• "Addition'' is composition, whose associativity is judgmental
  (`rfl`) in lambda calculus.
-/

/-- A natural number as a successor-preserving endomap of `Nat`. This allows addition to be
defined as composition, which is definitionally associative.

TODO: figure out compiler optimization for this representation.
-/
@[ext]
structure AssocNat where
  toFun : Nat → Nat
  presSucc : ∀ n, toFun (n.succ) = (toFun n).succ

attribute [simp] AssocNat.presSucc

instance : CoeFun AssocNat (fun _ => Nat → Nat) := ⟨AssocNat.toFun⟩

namespace AssocNat

/-- `0` is the identity function `ℕ → ℕ`. -/
@[inline] def zero : AssocNat :=
  ⟨id, by intro n; rfl⟩

/-- `1` is the successor of `0`, defined as `Nat.succ`. -/
@[inline] def one : AssocNat :=
  ⟨Nat.succ, by intro n; rfl⟩

/-- Addition on `AssocNat` is just function composition. -/
@[inline] def add (a b : AssocNat) : AssocNat :=
  ⟨a ∘ b, by intro n; simp [Function.comp]⟩

/-- Successor on `AssocNat`, defined as addition by `1` on the right to ensure that
`n.succ = n + 1` holds definitionally. -/
@[inline] def succ (n : AssocNat) : AssocNat :=
  add n one

/-- Convert a `k : Nat` into an `AssocNat`, which is the function `λ m, m + k`. -/
@[inline] def ofNat (k : Nat) : AssocNat :=
  ⟨fun m => m + k, fun m => Nat.succ_add m k⟩

/-- Convert a `k : Nat` into an `AssocNat`, which is the function `λ m, k + m`. -/
@[inline] def ofNat' (k : Nat) : AssocNat :=
  ⟨fun m => k + m, fun m => Nat.add_assoc k m 1⟩

/-- Evaluate an `AssocNat` at `0` to recover a `Nat`. -/
@[inline] def toNat (t : AssocNat) : Nat := t 0

/-- Predecessor of `AssocNat`. -/
@[inline] def pred : AssocNat → AssocNat :=
  fun a => match a.toNat with
  | 0 => zero
  | Nat.succ k => ofNat k

/-- Truncated subtraction on `AssocNat`, implemented by recursion on the **second** argument.
    This mirrors the definition of `Nat.sub`, so we get the same definitional equalities:

    • `a - 0 = a` (rfl)
    • `(succ a) - (succ b) = a - b` (rfl)

    Internally we recurse on `toNat b`, updating the running constant.  The resulting
    endomap is always of the form `λ m, (c - k) + m`, so it is successor‐preserving. -/
def subNat (c : AssocNat) : Nat → AssocNat
| 0            => c -- c - 0 = c
| Nat.succ k   => pred (subNat c k) -- c - (k + 1) = (c - k).pred?

/-- Truncated subtraction on `AssocNat`, defined as `subAux` on the `toNat` of the arguments. -/
def sub (a b : AssocNat) : AssocNat :=
  subNat a b.toNat

/-- Multiplication on `AssocNat`, obtained by *iterating* `a + _` on the **second** argument.
    This gives the usual judgmental equalities

    • `a * 0 = 0`  (rfl)
    • `a * (succ k) = a + a * k` (rfl)
    • in particular `a * 2 = a + a` (rfl).

    We implement it by a simple `Nat.rec` on `toNat b`. -/
def mulNat (a : AssocNat) : Nat → AssocNat
| 0            => zero
| Nat.succ k   => add a (mulNat a k)

def mul (a b : AssocNat) : AssocNat :=
  mulNat a b.toNat

instance : Zero AssocNat where
  zero := zero

instance : One AssocNat where
  one := one

instance : Add AssocNat where
  add := add

instance : Sub AssocNat where
  sub := sub

instance : Mul AssocNat where
  mul := mul

instance : ToNat AssocNat where
  toNat := toNat

/-- `a + 0 = a` holds definitionally. -/
@[simp] theorem add_zero {a : AssocNat} : a + 0 = a := rfl

/-- `0 + a = a` holds definitionally. -/
@[simp] theorem zero_add {a : AssocNat} : 0 + a = a := rfl

/-- Composition is definitionally associative. -/
theorem add_assoc (a b c : AssocNat) : (a + b) + c = a + (b + c) := rfl

/-- `a * 0 = 0` holds definitionally. -/
@[simp] theorem mul_zero {a : AssocNat} : a * 0 = 0 := rfl

/-- `0 * a = 0` holds only propositionally. -/
theorem zero_mul {a : AssocNat} : 0 * a = 0 := by
  change mul zero a = zero
  ext n
  simp [mul, zero]
  induction h : a.toNat with
  | zero => simp [zero, mulNat, toNat]
  | succ n ih => simp [mulNat, toNat, ih, h]; sorry

/-- `a * 1 = a` holds definitionally. -/
@[simp] theorem mul_one {a : AssocNat} : a * 1 = a := rfl

-- /-- `a * (succ b) = a + a * b` holds only propositionally. -/
-- theorem mul_succ {a b : AssocNat} : a * (succ b) = a + a * b := by
--   dsimp

/-- `(succ a) * b = a * b + b` holds only propositionally. -/
theorem succ_mul {a b : AssocNat} : (succ a) * b = a * b + b := by sorry

/-- `a * (b + c) = a * b + a * c` holds only propositionally. -/
theorem mul_add {a b c : AssocNat} : a * (b + c) = a * b + a * c := by sorry

/-- `1 * a = a` holds only propositionally. -/
@[simp] theorem one_mul {a : AssocNat} : 1 * a = a := by
  change mul one a = a
  ext n
  simp [mul, one]
  induction h : a.toNat with
  | zero => simp [zero, mulNat, toNat]; simp [toNat] at h; sorry
  | succ n ih => simp [mulNat, toNat, ih, h]; sorry

/-- `toNat` commutes with successor. -/
@[simp] theorem toNat_succ (t : AssocNat) : toNat (succ t) = (toNat t).succ := by
  simp [succ, toNat, add, one]

/-- Extensionality theorem for `AssocNat`, defined as equality of the endomaps evaluated at `0`. -/
@[ext]
theorem ext' {a b : AssocNat} (h : a 0 = b 0) : a = b := by
  ext m
  induction m with
  | zero => simp [h]
  | succ m ih => simp [ih]

/-- `ofNat` commutes with successor (pointwise equality of functions). -/
@[simp] theorem ofNat_succ (n : Nat) : ofNat n.succ = succ (ofNat n) := by
  ext
  simp [ofNat, succ, one, add, Nat.add_comm]

/-- Every endomap commuting with `Nat.succ` is addition by a constant. -/
theorem toFun_eq_const_plus (t : AssocNat) : ∀ m : Nat, t m = t 0 + m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => simp [ih, Nat.add_assoc]

/-- `toNat` turns composition into addition. -/
@[simp] theorem toNat_add (a b : AssocNat) : toNat (add a b) = toNat a + toNat b := by
  -- (a ∘ b) 0 = a (b 0)
  dsimp [toNat, add, Function.comp]
  have := toFun_eq_const_plus a (b 0)
  simpa using this

-- /-- `toNat` turns subtraction into truncated subtraction. -/
-- private theorem toNat_subNat (c : AssocNat) (k : Nat) : toNat (subNat c k) = c - k := by
--   induction k with
--   | zero => simp [subNat, toNat]; sorry
--   | succ k ih => sorry

-- @[simp] theorem toNat_sub (a b : AssocNat) : toNat (sub a b) = toNat a - toNat b := by
--   dsimp [sub]
--   exact toNat_subAux (toNat a) (toNat b)

/-- `toNat` turns multiplication into multiplication. -/
private theorem toNat_mulNat (a : AssocNat) (k : Nat) : toNat (mulNat a k) = toNat a * k := by
  induction k with
  | zero => simp [mulNat, toNat, zero]
  | succ k ih => sorry

@[simp] theorem toNat_mul (a b : AssocNat) : toNat (mul a b) = toNat a * toNat b := by
  dsimp [mul]
  exact toNat_mulNat a (toNat b)

/-- `ofNat` respects addition (pointwise equality of functions). -/
@[simp] theorem ofNat_add (n m : Nat) : ofNat (n + m) = add (ofNat n) (ofNat m) := by
  ext
  simp [ofNat, add, Nat.add_comm, Nat.add_left_comm]

/-- `toNat` is the left inverse of `ofNat`. -/
@[simp] theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  simp [toNat, ofNat]

/-- `ofNat` is the right inverse of `toNat`. -/
@[simp] theorem ofNat_toNat (t : AssocNat) : ofNat (toNat t) = t := by
  ext
  simp [ofNat, toNat]

/-- The explicit equivalence `Nat ≃ AssocNat`. -/
@[simps] def equivNat : Nat ≃ AssocNat where
  toFun := ofNat
  invFun := toNat
  left_inv := by
    intro n; simp
  right_inv := by
    intro t; simp

/-- Less-than relation on `AssocNat`, defined directly without going through `Nat`. -/
instance : LT AssocNat where
  lt a b := a 0 < b 0

/-- Less-equal relation on `AssocNat`. -/
instance : LE AssocNat where
  le a b := a 0 ≤ b 0

/-- The less-than relation is well-defined (does not depend on choice of representative). -/
theorem lt_iff_toNat_lt (a b : AssocNat) : a < b ↔ toNat a < toNat b := by
  rfl

/-- The less-equal relation is well-defined. -/
theorem le_iff_toNat_le (a b : AssocNat) : a ≤ b ↔ toNat a ≤ toNat b := by
  rfl

/-- `AssocNat` has decidable equality. -/
instance : DecidableEq AssocNat := by
  intro a b
  by_cases h : a 0 = b 0
  · right; exact ext' h
  · left; intro heq; exact h (by rw [heq])

-- /-- `AssocNat` forms a linear order. -/
-- instance : LinearOrder AssocNat := sorry

end AssocNat

-- -----------------------------------------------------------------
-- AssocFin: finite types based on AssocNat
-- -----------------------------------------------------------------

/-- `AssocFin n` is the type of `AssocNat` numbers less than `n`. -/
@[ext]
structure AssocFin (n : AssocNat) where
  val : AssocNat
  isLt : val < n

attribute [simp] AssocFin.isLt

namespace AssocFin

variable {n : AssocNat}

instance : CoeFun (AssocFin n) (fun _ => Nat → Nat) := ⟨fun f => f.val.toFun⟩

/-- The value of an `AssocFin` as an `AssocNat`. -/
def toAssocNat (f : AssocFin n) : AssocNat := f.val

/-- Convert an `AssocFin` to a regular `Fin` via the isomorphism. -/
def toFin (f : AssocFin n) : Fin (AssocNat.toNat n) :=
  ⟨AssocNat.toNat f.val, f.isLt⟩

/-- Convert a regular `Fin` to an `AssocFin` via the isomorphism. -/
def ofFin {n : AssocNat} (f : Fin (AssocNat.toNat n)) : AssocFin n :=
  ⟨AssocNat.ofNat f.val, by simp [AssocNat.lt_iff_toNat_lt, AssocNat.toNat_ofNat]⟩

/-- `AssocFin 0` is empty. -/
instance : IsEmpty (AssocFin AssocNat.zero) := by
  constructor
  intro f
  have : f.val.toNat < 0 := f.isLt
  exact Nat.not_lt_zero _ this

/-- `AssocFin` has decidable equality. -/
instance (n : AssocNat) : DecidableEq (AssocFin n) := by
  intro a b
  by_cases h : a.val = b.val
  · right; exact AssocFin.ext h
  · left; intro heq; exact h (by rw [heq])

end AssocFin
