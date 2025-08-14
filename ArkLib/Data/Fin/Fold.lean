/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib
import ArkLib.Data.Classes.DCast

/-!
# Folding over `Fin`

This file defines the prime versions of `Fin.(d)fold{l/r}` which has better definitional equalities
(i.e. automatically unfold for `0` and for `n.succ`). We then show equivalences between the prime
and non-prime versions, so that when compiling, the non-prime versions (which are more efficient)
are used.

We also prove that the existing mathlib function `finSumFinEquiv : ∑ i, Fin (n i) ≃ Fin (∑ i, n i)`
is equivalent to a version defined via `Fin.dfoldl'`.
-/

universe u v

namespace Fin

variable {m : Type u → Type v} [Monad m]

/-- Heterogeneous left fold over `Fin n` in a monad, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
def dfoldlM' (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.castSucc → m (α i.succ)) (init : α 0) : m (α (last n)) :=
  match n with
  | 0 => pure init
  | n + 1 => do
    let x ← dfoldlM' n (α ∘ castSucc) (fun i => f i.castSucc) init
    f (last n) x

-- Zero and succ lemmas for dfoldlM' (should be rfl due to good defeq)
@[simp]
lemma dfoldlM'_zero {α : Fin 1 → Type u} (f : (i : Fin 0) → α i.castSucc → m (α i.succ)) (x : α 0) :
    dfoldlM' 0 α f x = pure x := rfl

@[simp]
lemma dfoldlM'_succ {n : ℕ} {α : Fin (n + 2) → Type u}
    (f : (i : Fin (n + 1)) → α i.castSucc → m (α i.succ)) (x : α 0) :
    dfoldlM' (n + 1) α f x = (do
      let y ← dfoldlM' n (α ∘ castSucc) (fun i => f i.castSucc) x
      f (last n) y) := rfl

/-- Heterogeneous left fold over `Fin n`, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
def dfoldl' (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.castSucc → α i.succ) (init : α 0) : α (last n) :=
  dfoldlM' (m := Id) n α f init

-- Zero and succ lemmas for dfoldl' (should be rfl due to good defeq)
@[simp]
lemma dfoldl'_zero {α : Fin 1 → Type u}
    (f : (i : Fin 0) → α i.castSucc → α i.succ) (x : α 0) :
    dfoldl' 0 α f x = x := rfl

@[simp]
lemma dfoldl'_succ_last {n : ℕ} {α : Fin (n + 2) → Type u}
    (f : (i : Fin (n + 1)) → α i.castSucc → α i.succ) (x : α 0) :
    dfoldl' (n + 1) α f x = f (last n) (dfoldl' n (α ∘ castSucc) (fun i => f i.castSucc) x) := rfl

/-- Compiler replacement rule: use `dfoldl'` instead of `dfoldl` for better defeq. -/
@[csimp] lemma dfoldl_eq_dfoldl' : @dfoldl = @dfoldl' := by
  funext n α f x
  induction n with
  | zero =>
    rw [dfoldl_zero, dfoldl'_zero]
  | succ n ih =>
    rw [dfoldl_succ_last, dfoldl'_succ_last]
    rw [ih]

/-- Left fold over `Fin n`, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
def foldl' {α : Type u} (n : ℕ) (f : (i : Fin n) → α → α) (init : α) : α :=
  dfoldl' n (fun _ => α) f init

-- Zero and succ lemmas for foldl' (should be rfl due to good defeq)
@[simp]
lemma foldl'_zero {α : Type u} (f : (i : Fin 0) → α → α) (x : α) :
    foldl' 0 f x = x := rfl

@[simp]
lemma foldl'_succ {n : ℕ} {α : Type u} (f : (i : Fin (n + 1)) → α → α) (x : α) :
    foldl' (n + 1) f x = f (last n) (foldl' n (fun i => f i.castSucc) x) := rfl

/-- Heterogeneous right fold over `Fin n` in a monad, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
def dfoldrM' {m : Type u → Type v} [Monad m]
    (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.succ → m (α i.castSucc)) (init : α (last n)) : m (α 0) :=
  match n with
  | 0 => pure init
  | n + 1 => do
    let x ← dfoldrM' n (α ∘ succ) (fun i => f i.succ) init
    f 0 x

-- Zero and succ lemmas for dfoldrM' (should be rfl due to good defeq)
@[simp]
lemma dfoldrM'_zero {α : Fin 1 → Type u}
    (f : (i : Fin 0) → α i.succ → m (α i.castSucc)) (x : α (last 0)) :
    dfoldrM' 0 α f x = pure x := rfl

@[simp]
lemma dfoldrM'_succ {n : ℕ} {α : Fin (n + 1 + 1) → Type u}
    (f : (i : Fin (n + 1)) → α i.succ → m (α i.castSucc)) (x : α (last (n + 1))) :
    dfoldrM' (n + 1) α f x = (do
      let y ← dfoldrM' n (α ∘ succ) (fun i => f i.succ) x
      f 0 y) := rfl

/-- Heterogeneous right fold over `Fin n`, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
def dfoldr' (n : ℕ) (α : Fin (n + 1) → Type u)
    (f : (i : Fin n) → α i.succ → α i.castSucc) (init : α (last n)) : α 0 :=
  dfoldrM' (m := Id) n α f init

-- Zero and succ lemmas for dfoldr' derived from dfoldrM' lemmas
@[simp]
lemma dfoldr'_zero {α : Fin 1 → Type u}
    (f : (i : Fin 0) → α i.succ → α i.castSucc) (x : α (last 0)) :
    dfoldr' 0 α f x = x :=
  rfl

@[simp]
lemma dfoldr'_succ {n : ℕ} {α : Fin (n + 1 + 1) → Type u}
    (f : (i : Fin (n + 1)) → α i.succ → α i.castSucc) (x : α (last (n + 1))) :
    dfoldr' (n + 1) α f x = f 0 (dfoldr' n (α ∘ succ) (fun i => f i.succ) x) :=
  rfl

/-- Compiler replacement rule: use `dfoldr'` instead of `dfoldr` for better defeq. -/
@[csimp] lemma dfoldr_eq_dfoldr' : @dfoldr = @dfoldr' := by
  funext n α f x
  induction n with
  | zero =>
    rw [dfoldr_zero, dfoldr'_zero]
  | succ n ih =>
    rw [dfoldr_succ, dfoldr'_succ]
    rw [ih]

/-- Right fold over `Fin n`, prime version with better defeq.
  Automatically unfolds for `0` and `n.succ`. -/
def foldr' {α : Type u} (n : ℕ) (f : (i : Fin n) → α → α) (init : α) : α :=
  dfoldr' n (fun _ => α) f init

@[simp]
lemma foldr'_zero {α : Type u} (f : (i : Fin 0) → α → α) (x : α) :
    foldr' 0 f x = x := rfl

@[simp]
lemma foldr'_succ {n : ℕ} {α : Type u} (f : (i : Fin (n + 1)) → α → α) (x : α) :
    foldr' (n + 1) f x = f 0 (foldr' n (f ∘ succ) x) := rfl

-- Generic examples demonstrating the rfl behavior for arbitrary n
section Examples

-- Define an iterated type using Fin fold
def IterType (n : ℕ) : Type := dfoldl' n (fun _ => Type) (fun _ T => T × T) Nat

-- The iterated type should unfold definitionally
example : IterType 0 = Nat := rfl
example (n : ℕ) : IterType (n + 1) = (IterType n × IterType n) := rfl

-- Define a generic computation that uses the fold
def PowerType (n : ℕ) : Type := dfoldr' n (fun _ => Type) (fun _ T => T → T) Nat

-- Show that PowerType unfolds definitionally for any n
example : PowerType 0 = Nat := rfl
example (n : ℕ) : PowerType (n + 1) = (PowerType n → PowerType n) := rfl

-- More complex: nested structure
def NestedList (n : ℕ) : Type := dfoldr' n (fun _ => Type) (fun _ T => List T) Nat

example : NestedList 0 = Nat := rfl
example (n : ℕ) : NestedList (n + 1) = List (NestedList n) := rfl

-- This demonstrates the key advantage: these type equalities are definitional!
-- With the non-prime version, you would need simp or rw to prove these.

#eval dfoldl' 3 (fun i => Fin (i + 1)) (fun _ => fun x => x.succ) 0
#eval dfoldl 3 (fun i => Fin (i + 1)) (fun _ => fun x => x.succ) 0

end Examples

section FoldCongr

/-- Congruence for `dfoldl` -/
theorem dfoldl_congr {n : ℕ}
    {α α' : Fin (n + 1) → Type u}
    {f : (i : Fin n) → α i.castSucc → α i.succ}
    {f' : (i : Fin n) → α' i.castSucc → α' i.succ}
    {init : α 0} {init' : α' 0}
    (hα : ∀ i, α i = α' i)
    (hf : ∀ i a, f i a = (cast (hα _).symm (f' i (cast (hα _) a))))
    (hinit : init = cast (hα 0).symm init') :
      dfoldl n α f init = cast (hα (last n)).symm (dfoldl n α' f' init') := by
  have hα' : α = α' := funext hα
  subst hα'
  simp_all only [cast_eq]
  have hf' : f = f' := funext₂ hf
  subst hf'
  subst hinit
  rfl

/-- Congruence for `dfoldl` whose type vectors are indexed by `ι` and have a `DCast` instance

Note that we put `cast` (instead of `dcast`) in the theorem statement for easier matching,
but `dcast` inside the hypotheses for downstream proving. -/
theorem dfoldl_congr_dcast {n : ℕ}
    {ι : Type v} {α α' : Fin (n + 1) → ι} {β : ι → Type u} [DCast ι β]
    {f : (i : Fin n) → β (α i.castSucc) → β (α i.succ)}
    {f' : (i : Fin n) → β (α' i.castSucc) → β (α' i.succ)}
    {init : β (α 0)} {init' : β (α' 0)}
    (hα : ∀ i, α i = α' i)
    (hf : ∀ i a, f i a = (dcast (hα _).symm (f' i (dcast (hα _) a))))
    (hinit : init = dcast (hα 0).symm init') :
      dfoldl n (fun i => β (α i)) f init =
        cast (by have := funext hα; subst this; simp) (dfoldl n (fun i => β (α' i)) f' init') := by
  have hα' : α = α' := funext hα
  cases hα'
  simp_all only [dcast_eq, cast_eq]
  simp at hf
  have hf' : f = f' := funext₂ hf
  cases hf'
  cases hinit
  rfl

/-- Distribute `dcast` inside `dfoldl`. Requires the minimal condition of `α = α'` -/
theorem dfoldl_dcast {ι : Type v} {β : ι → Type u} [DCast ι β]
    {n : ℕ} {α α' : Fin (n + 1) → ι}
    {f : (i : Fin n) → β (α i.castSucc) → β (α i.succ)} {init : β (α 0)}
    (hα : ∀ i, α i = α' i) :
      dcast (hα (last n)) (dfoldl n (fun i => β (α i)) f init) =
        dfoldl n (fun i => β (α' i))
          (fun i a => dcast (hα _) (f i (dcast (hα _).symm a))) (dcast (hα 0) init) := by
  have hα' : α = α' := funext hα
  subst hα'
  simp_all only [dcast_eq]

end FoldCongr

end Fin
