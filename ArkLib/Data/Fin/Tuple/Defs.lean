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

- `Fin.vempty`: Empty (dependent) vector

- `Fin.vcons`: Improved homogeneous version of `cons` using pattern matching

- `Fin.vconcat`: Improved homogeneous version of `snoc` using pattern matching

- `Fin.vappend`: Improved homogeneous version of `append` using pattern matching

- `Fin.dempty`: Empty (dependent) tuple

- `Fin.dcons`: Improved dependent version of `cons` using pattern matching

- `Fin.dconcat`: Improved dependent version of `snoc` using pattern matching

- `Fin.dappend`: Improved dependent version of `append` using pattern matching

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

section Vec

variable {α : Sort*}

/-- `vempty` is the empty vector, and a wrapper around `Fin.elim0`. Write this as `!v[]`. -/
abbrev vempty {α : Sort*} : Fin 0 → α := Fin.elim0

/-- `vcons a v` prepends an entry `a : α` to a vector `v : Fin n → α` via pattern matching.

This is meant to replace `Matrix.vecCons` and `Fin.cons` for our use cases, as this definition
offers better definitional equality.
-/
def vcons {n : ℕ} (a : α) (v : Fin n → α) : Fin (n + 1) → α :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => fun i => match i with
    | 0 => a
    | ⟨k + 1, hk⟩ => v ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- `vconcat v a` concatenates an entry `a : α` to the _end_ of a vector `v : Fin n → α`
via pattern matching.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
def vconcat {α : Sort u} {n : ℕ} (v : Fin n → α) (a : α) : Fin (n + 1) → α :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => vcons (v 0) (vconcat (v ∘ Fin.succ) a)

/-- `vappend u v` appends two vectors `u : Fin m → α` and `v : Fin n → α`, written as `u ++ v`.

This is meant to replace `Fin.append` for our use cases, as this definition offers better
definitional equality. -/
def vappend {α : Sort u} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) : Fin (m + n) → α :=
  match n with
  | 0 => u
  | _ + 1 => vconcat (vappend u (v ∘ Fin.castSucc)) (v (Fin.last _))

end Vec

/-- `dempty` is the dependent empty tuple. Write this as `!t[]`. -/
def dempty {α : Fin 0 → Sort u} : (i : Fin 0) → α i := fun i => Fin.elim0 i

/-- `dcons a b` prepends an entry `a : α` to a dependent or heterogeneous vector
`b : (i : Fin n) → β i`,
where `α : Sort u` and `β : Fin n → Sort u` is a vector of sorts, via pattern matching.

This is meant to replace `Fin.cons` for our use cases, as this definition offers better
definitional equality.
-/
def dcons {n : ℕ} {α : Sort u} {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    (i : Fin (n + 1)) → Fin.vcons α β i :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => fun i => match i with
    | 0 => a
    | ⟨k + 1, hk⟩ => b ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

/-- `dconcat u a` concatenates an entry `a : β` to the _end_ of a dependent or heterogeneous
vector `u : (i : Fin n) → α i` via pattern matching, where `α : Fin n → Sort u` is a vector of
sorts and `β : Sort u` is a sort.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
def dconcat {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : (i : Fin n) → α i) (a : β) :
    (i : Fin (n + 1)) → Fin.vconcat α β i :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => dcons (u 0) (dconcat (fun i => u (Fin.succ i)) a)

/-- `dappend u v` appends two dependent or heterogeneous vectors `u : (i : Fin m) → α i` and
`v : (i : Fin n) → β i`, on `α : Fin m → Sort u` and `β : Fin n → Sort u` respectively, via
pattern matching.

This is meant to replace `Fin.addCases` for our use cases, as this definition offers better
definitional equality.
-/
def dappend {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) : (i : Fin (m + n)) → Fin.vappend α β i :=
  match n with
  | 0 => u
  | k + 1 => dconcat (dappend u (fun i => v (Fin.castSucc i))) (v (Fin.last k))

/-- Cast a dependent or heterogeneous vector across an equality `n' = n` and a family of equalities
  `∀ i, α (Fin.cast h i) = α' i`.

This is meant to replace `Fin.cast` for our use cases, as this definition offers better
definitional equality. -/
def dcast {n n' : ℕ} {α : Fin n → Sort u} {α' : Fin n' → Sort u}
    (h : n' = n) (hα : ∀ i, α (Fin.cast h i) = α' i) (v : (i : Fin n) → α i) :
      (i : Fin n') → α' i :=
  fun i => _root_.cast (hα i) (v (Fin.cast h i))

end Fin
