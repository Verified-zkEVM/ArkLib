/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Fin.Tuple.Take

/-!
# Custom Fin functions with better definitional equality

This file provides improved versions of some `Fin` functions that use pattern matching
for better definitional equality. The standard library versions rely on complex constructions
like `cases`, `addCases`, and conditional statements with casts, which can make reasoning
about definitional equality difficult.

## Definitions:

- `vecEmpty`: Empty (dependent) vector

- `vecCons`: Improved homogeneous version of `cons` using pattern matching

- `dvecCons`: Improved dependent version of `cons` using pattern matching

- `vecConcat`: Improved homogeneous version of `snoc` using pattern matching

- `dvecConcat`: Improved dependent version of `snoc` using pattern matching

- `vecAppend`: Improved homogeneous version of `append` using pattern matching

- `dvecAppend`: Improved dependent version of `append` using pattern matching

- `rtake`: Taking from the right (i.e. the end) of a (dependent) vector

- `drop`: Dropping from the left (i.e. the beginning) of a (dependent) vector

- `rdrop`: Dropping from the right (i.e. the end) of a (dependent) vector

- `rightpad`: Padding (or truncation) on the right of a (dependent) vector

- `leftpad`: Padding (or truncation) on the left of a (dependent) vector

The prime versions use pattern matching on the size parameter for better definitional behavior,
which minimizes casting needed in `OracleReduction.Cast`.
-/

universe u v w

namespace Fin

/-- `vecCons a v` prepends an entry `a : α` to a vector `v : Fin n → α` via pattern matching.

This is meant to replace `Matrix.vecCons` for our use cases, as this definition offers better
definitional equality.
-/
def vecCons {α : Sort*} {n : ℕ} (a : α) (v : Fin n → α) : Fin (n + 1) → α :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => fun i =>
    match h : i.val with
    | 0 => a
    | k + 1 => v ⟨k, Nat.lt_of_succ_lt_succ (h ▸ i.isLt)⟩

/-- `dvecCons a b` prepends an entry `a : α` to a dependent or heterogeneous vector
`b : (i : Fin n) → β i`, where `α : Sort u` and `β : Fin n → Sort u` is a vector of sorts,
via pattern matching.

This is meant to replace `Fin.cons` for our use cases, as this definition offers better
definitional equality.
-/
def dvecCons {n : ℕ} {α : Sort u} {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    (i : Fin (n + 1)) → vecCons α β i :=
  match n with
  | 0 => fun i => a
  | _ + 1 => fun i => by
    dsimp [vecCons]
    split
    next hi => exact a
    next k hi => exact b ⟨k, Nat.lt_of_succ_lt_succ (hi ▸ i.isLt)⟩

/-- `vecConcat v a` concatenates an entry `a : α` to the _end_ of a vector `v : Fin n → α`
via pattern matching.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
def vecConcat {α : Sort*} {n : ℕ} (v : Fin n → α) (a : α) : Fin (n + 1) → α :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => vecCons (v 0) (vecConcat (v ∘ succ) a)

/-- `dvecConcat u a` concatenates an entry `a : β` to the _end_ of a dependent or heterogeneous
vector `u : (i : Fin n) → α i` via pattern matching, where `α : Fin n → Sort u` is a vector of
sorts and `β : Sort u` is a sort.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
def dvecConcat {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : (i : Fin n) → α i) (a : β) :
    (i : Fin (n + 1)) → vecConcat α β i :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => dvecCons (u 0) (dvecConcat (fun i => u i.succ) a)

/-- `vecAppend u v` appends two vectors `u : Fin m → α` and `v : Fin n → α` via pattern matching.

This is meant to replace `Fin.append` for our use cases, as this definition offers better
definitional equality. -/
def vecAppend {α : Sort*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) : Fin (m + n) → α :=
  match n with
  | 0 => u
  | n + 1 => vecConcat (vecAppend u (v ∘ castSucc)) (v (last n))

/-- `dvecAppend u v` appends two dependent or heterogeneous vectors `u : (i : Fin m) → α i` and
`v : (i : Fin n) → β i`, on `α : Fin m → Sort u` and `β : Fin n → Sort u` respectively, via
pattern matching.

This is meant to replace `Fin.addCases` for our use cases, as this definition offers better
definitional equality.
-/
def dvecAppend {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
    (i : Fin (m + n)) → vecAppend α β i :=
  match n with
  | 0 => u
  | n + 1 => dvecConcat (dvecAppend u (fun i => v i.castSucc)) (v (last n))

/-- Take the last `m` elements of a finite vector -/
def rtake {n : ℕ} {α : Fin n → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin m) → α (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) :=
  fun i => v (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i))

/-- Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. -/
def drop {n : ℕ} {α : Fin n → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (Fin.cast (Nat.sub_add_cancel h) (addNat i m)) :=
  fun i ↦ v (Fin.cast (Nat.sub_add_cancel h) (addNat i m))

/-- Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.

This is defined to be taking the first `n - m` elements of the tuple. Thus, one should not use this
and use `Fin.take` instead. -/
abbrev rdrop {n : ℕ} {α : Fin n → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (Fin.cast (Nat.sub_add_cancel h) (i.castAdd m)) :=
  take (n - m) (by omega) v

/-- Pad a `Fin`-indexed vector on the right with an element `a`.

This becomes truncation if `n < m`. -/
def rightpad {m : ℕ} {α : Sort*} (n : ℕ) (a : α) (v : Fin m → α) : Fin n → α :=
  fun i => if h : i < m then v ⟨i, h⟩ else a

/-- Pad a `Fin`-indexed vector on the left with an element `a`.

This becomes truncation if `n < m`. -/
def leftpad {m : ℕ} {α : Sort*} (n : ℕ) (a : α) (v : Fin m → α) : Fin n → α :=
  fun i => if h : n - m ≤ i then v ⟨i - (n - m), by omega⟩ else a

end Fin

/-- A `FinVec` is a `FinTuple` with a constant type family, i.e. `Fin n → α`. -/
abbrev FinVec (α : Sort u) (n : ℕ) : Sort _ := Fin n → α

namespace FinVec

variable {α : Sort u} {n : ℕ}

def cons (a : α) (v : Fin n → α) : Fin (n + 1) → α :=
  Fin.vecCons a v

end FinVec

/-- A `FinTuple` of size `n` and type family `α` is a dependent function `(i : Fin n) → α i`. -/
abbrev FinTuple (n : ℕ) (α : FinVec (Sort u) n) : Sort _ := (i : Fin n) → α i

/-- Cast a `FinTuple` across an equality `n' = n` and a family of equalities
  `∀ i, α (Fin.cast h i) = α' i`.

  Since this is a pull-back, we state the equalities in the other direction (i.e. `n' = n` instead
  of `n = n'`) -/
def FinTuple.cast {n n' : ℕ} {α : Fin n → Sort u} {α' : Fin n' → Sort u}
    (h : n' = n) (hα : ∀ i, α (Fin.cast h i) = α' i) (v : FinTuple n α) :
      FinTuple n' α' :=
  fun i => _root_.cast (hα i) (v (Fin.cast h i))
