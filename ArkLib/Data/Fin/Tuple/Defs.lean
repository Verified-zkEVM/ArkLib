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

- `FinVec.empty`: Empty (dependent) vector

- `FinVec.cons`: Improved homogeneous version of `cons` using pattern matching

- `FinVec.concat`: Improved homogeneous version of `snoc` using pattern matching

- `FinVec.append`: Improved homogeneous version of `append` using pattern matching

- `FinTuple.empty`: Empty (dependent) tuple

- `FinTuple.cons`: Improved dependent version of `cons` using pattern matching

- `FinTuple.concat`: Improved dependent version of `snoc` using pattern matching

- `FinTuple.append`: Improved dependent version of `append` using pattern matching

- `Fin.rtake`: Taking from the right (i.e. the end) of a (dependent) vector

- `Fin.drop`: Dropping from the left (i.e. the beginning) of a (dependent) vector

- `Fin.rdrop`: Dropping from the right (i.e. the end) of a (dependent) vector

- `Fin.rightpad`: Padding (or truncation) on the right of a (dependent) vector

- `Fin.leftpad`: Padding (or truncation) on the left of a (dependent) vector

The prime versions use pattern matching on the size parameter for better definitional behavior,
which minimizes casting needed in `OracleReduction.Cast`.
-/

universe u v w

namespace Fin

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

/-- Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`. -/
def extract {n : ℕ} {α : Fin n → Sort*} (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n)
    (v : (i : Fin n) → α i) : (i : Fin (stop - start)) → α ⟨i + start, by omega⟩ :=
  fun i ↦ v ⟨i + start, by omega⟩

/-- Extracting with `start = 0` is the same as taking the first `stop` elements. -/
lemma extract_start_zero_eq_take {n : ℕ} {α : Fin n → Sort*} (stop : ℕ) (h : stop ≤ n)
    (v : (i : Fin n) → α i) : extract 0 stop (Nat.zero_le _) h v = take stop h v :=
  rfl

/-- Extracting with `stop = n` is the same as dropping the first `start` elements. -/
lemma extract_stop_last_eq_drop {n : ℕ} {α : Fin n → Sort*} (start : ℕ) (h : start ≤ n)
    (v : (i : Fin n) → α i) : extract start n h (Nat.le_refl _) v = drop start h v :=
  rfl

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

/-- `empty` is the empty vector, and a wrapper around `Fin.elim0`. Write this as `!v[]`. -/
def empty {α : Sort u} : FinVec α 0 := Fin.elim0

/-- `cons a v` prepends an entry `a : α` to a vector `v : FinVec α n` via pattern matching.

This is meant to replace `Matrix.vecCons` for our use cases, as this definition offers better
definitional equality.
-/
@[inline]
def cons {α : Sort u} {n : ℕ} (a : α) (v : FinVec α n) : FinVec α (n + 1) :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => fun i => match i with
    | 0 => a
    | ⟨k + 1, hk⟩ => v ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- `concat v a` concatenates an entry `a : α` to the _end_ of a vector `v : FinVec α n`
via pattern matching.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
@[inline]
def concat {α : Sort u} {n : ℕ} (v : FinVec α n) (a : α) : FinVec α (n + 1) :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => cons (v 0) (concat (v ∘ Fin.succ) a)

/-- `append u v` appends two vectors `u : FinVec α m` and `v : FinVec α n`, written as `u ++ v`.

This is meant to replace `Fin.append` for our use cases, as this definition offers better
definitional equality. -/
@[inline]
def append {α : Sort u} {m n : ℕ} (u : FinVec α m) (v : FinVec α n) : FinVec α (m + n) :=
  match n with
  | 0 => u
  | _ + 1 => concat (append u (v ∘ Fin.castSucc)) (v (Fin.last _))

end FinVec

/-- A `FinTuple` of size `n` and type family `α` is a dependent function `(i : Fin n) → α i`. -/
abbrev FinTuple (n : ℕ) (α : FinVec (Sort u) n) : Sort _ := (i : Fin n) → α i

namespace FinTuple

/-- `empty` is the empty tuple, and a wrapper around `Fin.elim0`. Write this as `!t[]`. -/
def empty {α : Fin 0 → Sort u} : FinTuple 0 α := fun i => Fin.elim0 i

/-- `cons a b` prepends an entry `a : α` to a dependent or heterogeneous vector
`b : FinTuple n β`, where `α : Sort u` and `β : Fin n → Sort u` is a vector of sorts,
via pattern matching.

This is meant to replace `Fin.cons` for our use cases, as this definition offers better
definitional equality.
-/
@[inline]
def cons {n : ℕ} {α : Sort u} {β : Fin n → Sort u} (a : α) (b : FinTuple n β) :
    FinTuple (n + 1) (FinVec.cons α β) :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => fun i => match i with
    | 0 => a
    | ⟨k + 1, hk⟩ => b ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

/-- `concat u a` concatenates an entry `a : β` to the _end_ of a dependent or heterogeneous
vector `u : FinTuple n α` via pattern matching, where `α : Fin n → Sort u` is a vector of
sorts and `β : Sort u` is a sort.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
@[inline]
def concat {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : FinTuple n α) (a : β) :
    FinTuple (n + 1) (FinVec.concat α β) :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => cons (u 0) (concat (fun i => u (Fin.succ i)) a)

/-- `append u v` appends two dependent or heterogeneous vectors `u : FinTuple m α` and
`v : FinTuple n β`, on `α : Fin m → Sort u` and `β : Fin n → Sort u` respectively, via
pattern matching.

This is meant to replace `Fin.addCases` for our use cases, as this definition offers better
definitional equality.
-/
@[inline]
def append {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) : FinTuple (m + n) (FinVec.append α β) :=
  match n with
  | 0 => u
  | k + 1 => concat (append u (fun i => v (Fin.castSucc i))) (v (Fin.last k))

/-- Cast a `FinTuple` across an equality `n' = n` and a family of equalities
  `∀ i, α (Fin.cast h i) = α' i`.

  Since this is a pull-back, we state the equalities in the other direction (i.e. `n' = n` instead
  of `n = n'`) -/
protected def cast {n n' : ℕ} {α : Fin n → Sort u} {α' : Fin n' → Sort u}
    (h : n' = n) (hα : ∀ i, α (Fin.cast h i) = α' i) (v : FinTuple n α) :
      FinTuple n' α' :=
  fun i => _root_.cast (hα i) (v (Fin.cast h i))

end FinTuple
