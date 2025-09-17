/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.BigOperators.Fin
import ArkLib.Data.Fin.Basic
import ArkLib.Data.Fin.Fold
import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# Fin Sigma Equivalences

We re-define big-operators sum and product over `Fin` to have good definitional equalities.
-/

universe u v w

open Finset

namespace Fin

def addCast {n : ℕ} (m : ℕ) (i : Fin n) : Fin (m + n) := ⟨i, Nat.lt_add_left m i.2⟩

section BigOperators

variable {α : Type*}

/-- Version of multiplying over `Fin` vectors with good definitional equalities, using `dfoldl'`.

The definitional equality we want is that:
`vprod a = a 0 * (a 1 * (... * (a (n-1) * 1)))`
-/
@[to_additive vsum
"Version of summing over `Fin` vectors with good definitional equalities, using `dfoldl'`.

The definitional equality we want is that: `vsum a = a 0 + (a 1 + (... + (a (n-1) + 0)))`.

When `x + 0 = x` definitionally in `α`, we have the following definitional equalities:
- `vsum !v[] = 0`
- `vsum !v[a] = a`
- `vsum !v[a, b] = a + b`
- `vsum !v[a, b, c] = a + (b + c)`
- and so on
"]
def vprod [CommMonoid α] {n : ℕ} (a : Fin n → α) : α :=
  Fin.dfoldr' n (fun _ => α) (fun i acc => a i * acc) 1

variable {n : ℕ}

@[to_additive (attr := simp) vsum_zero]
lemma vprod_zero [CommMonoid α] {a : Fin 0 → α} : vprod a = 1 := rfl

@[to_additive (attr := simp) vsum_succ]
lemma vprod_succ [CommMonoid α] {a : Fin (n + 1) → α} : vprod a = a 0 * vprod (a ∘ Fin.succ) := rfl

/-- `vprod a` is equivalent to the standard `Finset`-based definition, `∏ i, a i`. -/
@[to_additive vsum_eq_univ_sum]
lemma vprod_eq_univ_prod [CommMonoid α] {a : Fin n → α} : vprod a = ∏ i, a i := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Fin.prod_univ_succ]

@[to_additive vsum_castSucc]
lemma vprod_castSucc [CommMonoid α] {a : Fin (n + 1) → α} :
    vprod a = vprod (a ∘ Fin.castSucc) * a (last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [vprod_succ, ih, vprod_succ]
    simp only [Function.comp_apply, succ_last, Nat.succ_eq_add_one, castSucc_zero]
    have : (a ∘ succ) ∘ castSucc = (a ∘ castSucc) ∘ succ := by ext i; simp
    rw [this, mul_assoc (a 0)]

end BigOperators

end Fin

namespace Fin

section Sigma

variable {m : ℕ} {n : Fin m → ℕ}

/-- Embed nested indices `(i : Fin m, j : Fin (n i))` into a single index `Fin (vsum n)`. This
  converts from nested indexing to indexing into the vector sum, preserving lexicographic order. -/
def embedSum {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (j : Fin (n i)) : Fin (vsum n) := match m with
  | 0 => i
  | _ + 1 => match i with
    | 0 => Fin.castAdd _ j
    | ⟨i + 1, h⟩ => Fin.natAdd _ (embedSum ⟨i, Nat.succ_lt_succ_iff.mp h⟩ j)

@[simp]
theorem embedSum_zero {n : Fin 0 → ℕ} {i : Fin 0} (j : Fin (n i)) : embedSum i j = i := rfl

theorem embedSum_succ {m : ℕ} {n : Fin (m + 1) → ℕ} {i : Fin (m + 1)} (j : Fin (n i)) :
    embedSum i j = (match i with
    | 0 => Fin.castAdd _ j
    | ⟨i + 1, h⟩ => Fin.natAdd _ (embedSum ⟨i, Nat.succ_lt_succ_iff.mp h⟩ j)) := rfl

@[simp]
theorem embedSum_succ_zero {n : Fin (m + 1) → ℕ} {j : Fin (n 0)} :
    embedSum 0 j = Fin.castAdd _ j := rfl

@[simp]
theorem embedSum_succ_succ {n : Fin (m + 1) → ℕ} {i : Fin m} (j : Fin (n i.succ)) :
    embedSum (i.succ) j = Fin.natAdd _ (embedSum i j) := rfl

/-- Split a vector sum index `k : Fin (vsum n)` into nested indices `(i : Fin m) × Fin (n i)`.
This converts from indexing into the vector sum back to nested indexing, inverse of `embedSum`. -/
def splitSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (vsum n)) : (i : Fin m) × Fin (n i) := match m with
  | 0 => Fin.elim0 k
  | _ + 1 => Fin.dappend
    (fun k => ⟨0, k⟩)
    (fun k => ⟨(splitSum k).1.succ, (splitSum k).2⟩)
    k

@[simp]
theorem splitSum_zero {n : Fin 0 → ℕ} {k : Fin (vsum n)} : splitSum k = Fin.elim0 k := rfl

@[simp]
theorem splitSum_succ {n : Fin (m + 1) → ℕ} {k : Fin (vsum n)} :
    splitSum k = Fin.dappend
      (fun k => ⟨0, k⟩)
      (fun k => ⟨(splitSum k).1.succ, (splitSum k).2⟩)
      k := rfl

@[simp]
theorem embedSum_splitSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (vsum n)) :
    embedSum (splitSum k).1 (splitSum k).2 = k := by
  induction m with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    simp [embedSum]
    split
    next i j j' h1 h2 => sorry
    next i j j' h' j'' h1 h2 => sorry

@[simp]
theorem splitSum_embedSum {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (j : Fin (n i)) :
    splitSum (embedSum i j) = ⟨i, j⟩ := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    simp [embedSum, splitSum]
    split
    next j => simp
    next j => sorry

def finSum'FinEquiv' {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (vsum n) where
  toFun := fun ij => embedSum ij.1 ij.2
  invFun := splitSum
  left_inv := fun ij => splitSum_embedSum ij.1 ij.2
  right_inv := embedSum_splitSum

end Sigma

end Fin

namespace Fin

variable {α : Sort*}

/-- Dependent flatten with unified motive: flattens a nested dependent vector
`(i : Fin m) → (j : Fin (n i)) → motive (embedSum i j)` into a single dependent vector
`(k : Fin (vsum n)) → motive k`, preserving element order.

This is meant to replace nested iteration for dependent families with a unified motive. -/
@[elab_as_elim]
def dflatten {m : ℕ} {n : Fin m → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    (v : (i : Fin m) → (j : Fin (n i)) → motive (embedSum i j)) (k : Fin (vsum n)) : motive k :=
  match m with
  | 0 => Fin.elim0 k
  | _ + 1 =>
    dappend
      (fun j => v 0 j)
      (fun j => dflatten (motive := fun j => motive (natAdd _ j)) (fun i => v i.succ) j)
      k

@[simp]
theorem dflatten_zero {n : Fin 0 → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    {v : (i : Fin 0) → (j : Fin (n i)) → motive (embedSum i j)} :
    dflatten (motive := motive) v = fun k => Fin.elim0 k := rfl

@[simp]
theorem dflatten_succ {m : ℕ} {n : Fin (m + 1) → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    {v : (i : Fin (m + 1)) → (j : Fin (n i)) → motive (embedSum i j)} :
    dflatten (motive := motive) v = dappend (v 0) (dflatten (fun i => v i.succ)) := rfl

@[simp]
theorem dflatten_one {n : Fin 1 → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    {v : (i : Fin 1) → (j : Fin (n i)) → motive (embedSum i j)} :
    dflatten (motive := motive) v = v 0 := rfl

@[simp]
theorem dflatten_two_eq_append {n : Fin 2 → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    {v : (i : Fin 2) → (j : Fin (n i)) → motive (embedSum i j)} :
    dflatten (motive := motive) v = dappend (v 0) (v 1) := rfl

-- theorem dflatten_eq_append_last {m : ℕ} {n : Fin (m + 1) → ℕ}
--     {motive : (k : Fin (vsum n)) → Sort*}
--     {v : (i : Fin (m + 1)) → (j : Fin (n i)) → motive (embedSum i j)} (k : Fin (vsum n)) :
--     dflatten (motive := motive) v k =
--       dappend (dflatten (motive := sorry) (fun i => v i.castSucc)) (v (last _)) := by
--   induction m with
--   | zero => exact Fin.elim0 k
--   | succ m ih => sorry

@[simp]
theorem dflatten_splitSum {m : ℕ} {n : Fin m → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    (v : (k : Fin (vsum n)) → motive k) (k : Fin (vsum n)) :
    dflatten (motive := motive) (fun i j => v (embedSum i j)) k = v k := by
  induction m with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    simp; sorry

@[simp]
theorem dflatten_embedSum {m : ℕ} {n : Fin m → ℕ} {motive : (k : Fin (vsum n)) → Sort*}
    (v : (i : Fin m) → (j : Fin (n i)) → motive (embedSum i j)) (i : Fin m) (j : Fin (n i)) :
    dflatten (motive := motive) v (embedSum i j) = v i j := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    induction i using induction with
    | zero => simp
    | succ i ih' =>
      simp
      exact ih (motive := fun i => motive (natAdd (n 0) i)) (fun i => v i.succ) i j

/-- Homogeneous flatten: flattens a nested homogeneous vector
`(i : Fin m) → (j : Fin (n i)) → α` into a single homogeneous vector `Fin (vsum n) → α`
by specializing `dflatten` to the constant-type motive `fun _ => α`. -/
def vflatten {m : ℕ} {n : Fin m → ℕ} (v : (i : Fin m) → Fin (n i) → α) :
    Fin (vsum n) → α :=
  dflatten v

@[simp]
theorem vflatten_zero {n : Fin 0 → ℕ} {v : (i : Fin 0) → Fin (n i) → α} : vflatten v = !v[] := rfl

@[simp]
theorem vflatten_succ {m : ℕ} {n : Fin (m + 1) → ℕ} {v : (i : Fin (m + 1)) → Fin (n i) → α} :
    vflatten v = vappend (v 0) (vflatten (fun i => v i.succ)) := rfl

@[simp]
theorem vflatten_one {n : Fin 1 → ℕ} {v : (i : Fin 1) → Fin (n i) → α} :
    vflatten v = v 0 := rfl

@[simp]
theorem vflatten_two_eq_append {n : Fin 2 → ℕ} {v : (i : Fin 2) → Fin (n i) → α} :
    vflatten v = vappend (v 0) (v 1) := rfl

theorem vflatten_eq_vappend_last {m : ℕ} {n : Fin (m + 1) → ℕ}
    {v : (i : Fin (m + 1)) → Fin (n i) → α} :
    vflatten v =
      vappend (vflatten (fun i => v i.castSucc)) (v (last _)) ∘ Fin.cast vsum_castSucc := by
  induction m with
  | zero => ext i; simp
  | succ m ih =>
    ext i
    rw [vflatten_succ, ih, vflatten_succ, vappend_assoc]
    simp
    sorry

@[simp]
theorem vflatten_splitSum {m : ℕ} {n : Fin m → ℕ} (v : (k : Fin (vsum n)) → α) (k : Fin (vsum n)) :
    vflatten (fun i j => v (embedSum i j)) k = v k :=
  dflatten_splitSum v k

@[simp]
theorem vflatten_embedSum {m : ℕ} {n : Fin m → ℕ} (v : (i : Fin m) → Fin (n i) → α) (i : Fin m)
    (j : Fin (n i)) : vflatten v (embedSum i j) = v i j :=
  dflatten_embedSum (motive := fun _ => α) v i j

/-- Functorial flatten: flattens a nested heterogeneous tuple
`(i : Fin m) → (j : Fin (n i)) → F (α i j)` into a single heterogeneous tuple with type
`(k : Fin (vsum n)) → F (vflatten α k)` where `vflatten` operates on the vector of types `α`.

Unlike `dflatten` which requires an explicit unified motive, `fflatten` uses `vflatten` to
automatically construct the motive from the input type family. -/
def fflatten {A : Sort u} {F : A → Sort v} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin m) → (j : Fin (n i)) → A}
    (v : (i : Fin m) → (j : Fin (n i)) → F (α i j)) : (k : Fin (vsum n)) → F (Fin.vflatten α k) :=
  match m with
  | 0 => !h[]
  | _ + 1 => fappend (v 0) (fflatten (fun i => v i.succ))

@[simp]
theorem fflatten_zero {A : Sort u} {F : A → Sort v} {n : Fin 0 → ℕ}
    {α : (i : Fin 0) → (j : Fin (n i)) → A}
    {v : (i : Fin 0) → (j : Fin (n i)) → F (α i j)} : fflatten v = !h[] := rfl

@[simp]
theorem fflatten_succ {A : Sort u} {F : A → Sort v} {m : ℕ} {n : Fin (m + 1) → ℕ}
    {α : (i : Fin (m + 1)) → (j : Fin (n i)) → A}
    {v : (i : Fin (m + 1)) → (j : Fin (n i)) → F (α i j)} :
    fflatten v = fappend (v 0) (fflatten (fun i => v i.succ)) := rfl

@[simp]
theorem fflatten_one {A : Sort u} {F : A → Sort v} {n : Fin 1 → ℕ}
    {α : (i : Fin 1) → (j : Fin (n i)) → A}
    {v : (i : Fin 1) → (j : Fin (n i)) → F (α i j)} :
    fflatten v = v 0 := rfl

@[simp]
theorem fflatten_two_eq_append {A : Sort u} {F : A → Sort v} {n : Fin 2 → ℕ}
    {α : (i : Fin 2) → (j : Fin (n i)) → A}
    {v : (i : Fin 2) → (j : Fin (n i)) → F (α i j)} :
    fflatten v = fappend (F := F) (v 0) (v 1) := rfl

@[simp]
theorem fflatten_splitSum {A : Sort u} {F : A → Sort v} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin (vsum n)) → A}
    (v : (k : Fin (vsum n)) → F (α k)) (k : Fin (vsum n)) :
    fflatten (fun i j => v (embedSum i j)) k = cast (by simp) (v k) := by
  sorry

@[simp]
theorem fflatten_embedSum {A : Sort u} {F : A → Sort v} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin m) → (j : Fin (n i)) → A}
    (v : (i : Fin m) → (j : Fin (n i)) → F (α i j)) (i : Fin m) (j : Fin (n i)) :
    fflatten v (embedSum i j) = cast (by simp) (v i j) := by
  sorry

/-- Functorial flatten with two arguments: flattens two nested heterogeneous tuple
`(i : Fin m) → (j : Fin (n i)) → F (α i j)` into a single heterogeneous tuple with type
`(k : Fin (vsum n)) → F (vflatten α k)` where `vflatten` operates on the vector of types `α`.

Unlike `dflatten` which requires an explicit unified motive, `fflatten` uses `vflatten` to
automatically construct the motive from the input type family. -/
def fflatten₂ {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin m) → (j : Fin (n i)) → A} {β : (i : Fin m) → (j : Fin (n i)) → B}
    (v : (i : Fin m) → (j : Fin (n i)) → F (α i j) (β i j)) :
    (k : Fin (vsum n)) → F (Fin.vflatten α k) (Fin.vflatten β k) :=
  match m with
  | 0 => !h[]
  | _ + 1 => fappend₂ (v 0) (fflatten₂ (fun i => v i.succ))

@[simp]
theorem fflatten₂_zero {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : Fin 0 → ℕ}
    {α : (i : Fin 0) → (j : Fin (n i)) → A}
    {β : (i : Fin 0) → (j : Fin (n i)) → B}
    {v : (i : Fin 0) → (j : Fin (n i)) → F (α i j) (β i j)} : fflatten₂ v = !h[] := rfl

@[simp]
theorem fflatten₂_succ {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m : ℕ} {n : Fin (m + 1) → ℕ}
    {α : (i : Fin (m + 1)) → (j : Fin (n i)) → A}
    {β : (i : Fin (m + 1)) → (j : Fin (n i)) → B}
    {v : (i : Fin (m + 1)) → (j : Fin (n i)) → F (α i j) (β i j)} :
    fflatten₂ v = fappend₂ (v 0) (fflatten₂ (fun i => v i.succ)) := rfl

@[simp]
theorem fflatten₂_one {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : Fin 1 → ℕ}
    {α : (i : Fin 1) → (j : Fin (n i)) → A}
    {β : (i : Fin 1) → (j : Fin (n i)) → B}
    {v : (i : Fin 1) → (j : Fin (n i)) → F (α i j) (β i j)} :
    fflatten₂ v = v 0 := rfl

@[simp]
theorem fflatten₂_two_eq_append {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : Fin 2 → ℕ}
    {α : (i : Fin 2) → (j : Fin (n i)) → A}
    {β : (i : Fin 2) → (j : Fin (n i)) → B}
    {v : (i : Fin 2) → (j : Fin (n i)) → F (α i j) (β i j)} :
    fflatten₂ v = fappend₂ (F := F) (v 0) (v 1) := rfl

@[simp]
theorem fflatten₂_splitSum {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin m) → (j : Fin (n i)) → A}
    {β : (i : Fin m) → (j : Fin (n i)) → B}
    (v : (k : Fin (vsum n)) → F (vflatten α k) (vflatten β k)) (k : Fin (vsum n)) :
    fflatten₂ (fun i j => v (embedSum i j)) k = cast (by simp) (v k) := by
  sorry

@[simp]
theorem fflatten₂_embedSum {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m : ℕ} {n : Fin m → ℕ}
    {α : (i : Fin m) → (j : Fin (n i)) → A}
    {β : (i : Fin m) → (j : Fin (n i)) → B}
    (v : (i : Fin m) → (j : Fin (n i)) → F (α i j) (β i j)) (i : Fin m) (j : Fin (n i)) :
    fflatten₂ v (embedSum i j) = cast (by simp) (v i j) := by
  sorry

/-- Heterogeneous flatten: flattens a nested heterogeneous tuple
`(i : Fin m) → (j : Fin (n i)) → α i j` into a single heterogeneous tuple with type
`(k : Fin (vsum n)) → vflatten α k` where `vflatten` operates on the vector of types `α`.

Unlike `dflatten` which requires an explicit unified motive, `hflatten` uses `vflatten` to
automatically construct the motive from the input type family. -/
def hflatten {m : ℕ} {n : Fin m → ℕ} {α : (i : Fin m) → (j : Fin (n i)) → Sort*}
    (v : (i : Fin m) → (j : Fin (n i)) → α i j) : (k : Fin (vsum n)) → Fin.vflatten α k :=
  fflatten (F := id) v
  -- match m with
  -- | 0 => !h[]
  -- | _ + 1 => happend (v 0) (hflatten (fun i => v i.succ))

@[simp]
theorem hflatten_zero {n : Fin 0 → ℕ} {α : (i : Fin 0) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin 0) → (j : Fin (n i)) → α i j} : hflatten v = !h[] :=
  fflatten_zero (F := id)

@[simp]
theorem hflatten_succ {m : ℕ} {n : Fin (m + 1) → ℕ}
    {α : (i : Fin (m + 1)) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin (m + 1)) → (j : Fin (n i)) → α i j} :
    hflatten v = happend (v 0) (hflatten (fun i => v i.succ)) :=
  fflatten_succ (F := id)

@[simp]
theorem hflatten_one {n : Fin 1 → ℕ} {α : (i : Fin 1) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin 1) → (j : Fin (n i)) → α i j} : hflatten v = v 0 :=
  fflatten_one (F := id)

@[simp]
theorem hflatten_two_eq_append {n : Fin 2 → ℕ} {α : (i : Fin 2) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin 2) → (j : Fin (n i)) → α i j} : hflatten v = happend (v 0) (v 1) :=
  fflatten_two_eq_append (F := id)

@[simp]
theorem hflatten_splitSum {m : ℕ} {n : Fin m → ℕ} {α : (k : Fin (vsum n)) → Sort*}
    (v : (k : Fin (vsum n)) → α k) (k : Fin (vsum n)) :
    hflatten (fun i j => v (embedSum i j)) k = cast (vflatten_splitSum α k).symm (v k) :=
  fflatten_splitSum (F := id) v k

@[simp]
theorem hflatten_embedSum {m : ℕ} {n : Fin m → ℕ} {α : (i : Fin m) → (j : Fin (n i)) → Sort*}
    (v : (i : Fin m) → (j : Fin (n i)) → α i j) (i : Fin m) (j : Fin (n i)) :
    hflatten v (embedSum i j) = cast (vflatten_embedSum α i j).symm (v i j) :=
  fflatten_embedSum (F := id) v i j

/- The rest are old stuff... -/

section FinSigmaFinEquiv

variable {n : ℕ}

def map {α β : Fin n → Sort*} (f : (i : Fin n) → α i → β i) (a : (i : Fin n) → α i) :
    (i : Fin n) → β i := fun i => f i (a i)

def range (n : ℕ) : Fin n → ℕ := fun i => i

def ranges {n : ℕ} (a : Fin n → ℕ) : (i : Fin n) → Fin (a i) → ℕ :=
  match n with
  | 0 => fun i => elim0 i
  | n + 1 => fun i => by
    by_cases h : i = 0
    · exact val
    · letI rest := ranges (tail a) (i.pred h)
      simp only [tail, pred, subNat_one_succ] at rest
      exact fun j => rest j + a 0

/-- Find the first index `i` such that `k` is smaller than `∑ j < i, a j`, and return `none`
  otherwise.

  This is the dependent version of `Fin.divNat`.
-/
def divSum? {m : ℕ} (n : Fin m → ℕ) (k : ℕ) : Option (Fin m) :=
  find (fun i => k < ∑ j, n (castLE i.isLt j))

theorem divSum?_is_some_iff_lt_sum {m : ℕ} {n : Fin m → ℕ} {k : ℕ} :
    (divSum? n k).isSome ↔ k < ∑ i, n i := by
  constructor
  · intro h
    simp only [divSum?, Nat.succ_eq_add_one, castLE, isSome_find_iff] at h
    obtain ⟨i, hi⟩ := h
    have : i.val + 1 + (m - i.val - 1) = m := by omega
    rw [← Fin.sum_congr' _ this, Fin.sum_univ_add]
    simp only [gt_iff_lt]
    exact Nat.lt_add_right _ hi
  · intro isLt
    have : m ≠ 0 := fun h => by subst h; simp at isLt
    refine Fin.isSome_find_iff.mpr ?_
    have hm : (m - 1) + 1 = m := by omega
    refine ⟨Fin.cast hm (Fin.last (m - 1)), ?_⟩
    simp only [coe_cast, val_last, Nat.succ_eq_add_one, Fin.castLE_of_eq hm,
        Fin.sum_congr' n hm, isLt]

def divSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (∑ j, n j)) : Fin m :=
  (divSum? n k).get (divSum?_is_some_iff_lt_sum.mpr k.isLt)

theorem sum_le_of_divSum?_eq_some {m : ℕ} {n : Fin m → ℕ} {k : Fin (∑ j, n j)} {i : Fin m}
    (hi : divSum? n k = some i) : ∑ j : Fin i, n (castLE i.isLt.le j) ≤ k := by
  by_cases hi' : 0 = i.val
  · rw [← Fin.sum_congr' _ hi']
    simp only [Finset.univ_eq_empty, Finset.sum_empty, _root_.zero_le]
  · have : (i.val - 1) + 1 = i.val := by omega
    rw [← Fin.sum_congr' _ this]
    have := Fin.find_min (Option.mem_def.mp hi) (j := ⟨i.val - 1, by omega⟩) <| Fin.lt_def.mpr
      (by simp only; omega)
    exact not_lt.mp this

def modSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (∑ j, n j)) : Fin (n (divSum k)) :=
  ⟨k - ∑ j, n (Fin.castLE (divSum k).isLt.le j), by
    have divSum_mem : divSum k ∈ divSum? n k := by
      simp only [divSum, divSum?, Option.mem_def, Option.some_get]
    have hk : k < ∑ j, n (Fin.castLE (divSum k).isLt j) := Fin.find_spec _ divSum_mem
    simp only [Fin.sum_univ_succAbove _ (Fin.last (divSum k)), succAbove_last] at hk
    rw [Nat.sub_lt_iff_lt_add' (sum_le_of_divSum?_eq_some divSum_mem)]
    rw [add_comm]
    exact hk⟩

/-- Equivalence between `(i : Fin m) × Fin (n i)` and `Fin (∑ i, n i)`.

Put this as the prime version since it already exists in mathlib (though with a different definition
that's not def'eq to this one). -/
def finSigmaFinEquiv' {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i, n i) :=
  .ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_sigma, Fintype.card_fin])
    (fun ⟨i, j⟩ => ⟨∑ k, n (Fin.castLE i.isLt.le k) + j, by
      have hi : i.val + 1 + (m - i.val - 1) = m := by omega
      conv_rhs => rw [← Fin.sum_congr' n hi, Fin.sum_univ_add, Fin.sum_univ_add, add_assoc]
      have hk {k : Fin i} : Fin.castLE i.isLt.le k =
            Fin.cast hi (Fin.castAdd (m - i - 1) (Fin.castAdd 1 k)) := by
        simp only [Fin.castLE, Fin.cast, Fin.coe_castAdd]
      simp_rw [hk, Nat.add_lt_add_iff_left, univ_unique, sum_singleton]
      exact Nat.lt_add_right _ (by simp only [Fin.cast, Fin.coe_castAdd, Fin.coe_natAdd,
          Fin.val_eq_zero, add_zero, Fin.is_lt])⟩)
    (fun k => ⟨k.divSum, k.modSum⟩)
    (by
      intro a
      induction n using Fin.consInduction with
      | h0 =>
        simp only [univ_eq_empty, sum_empty] at a
        exact Fin.elim0 a
      | h =>
        ext
        exact Nat.add_sub_cancel' (Fin.sum_le_of_divSum?_eq_some (Option.some_get _).symm))

@[simp]
theorem finSigmaFinEquiv'_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv' k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.isLt.le i) + k.2 := rfl

theorem finSigmaFinEquiv'_pair {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (k : Fin (n i)) :
    (finSigmaFinEquiv' ⟨i, k⟩ : ℕ) = ∑ j, n (Fin.castLE i.isLt.le j) + k := by
  simp only [finSigmaFinEquiv', Equiv.ofRightInverseOfCardLE_apply]

end FinSigmaFinEquiv

end Fin
