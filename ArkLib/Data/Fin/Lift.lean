/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši
-/

import ArkLib.Data.Fin.Basic

/-!
  # Lifting of `Fin`-indexed vectors
-/

namespace Fin

section Lift

variable {α : Type*}
         {m n : ℕ}

/-
  Basic ad-hoc lifting;
  - `liftF : (Fin n → α) → ℕ → α`
  - `liftF` : (ℕ → α) → Fin n → α
  These invert each other assuming appropriately-bounded domains.

  These are specialised versions of true lifts that uses `Nonempty` / `Inhabited`
  and take the complement of the finite set which is the domain of the function being lifted.
-/

variable [Zero α] {f : ℕ → α} {f' : Fin n → α}

/--
  `liftF` lifts functions over domains `Fin n` to functions over domains `ℕ`
  by returning `0` on points `≥ n`.
-/
def liftF (f : Fin n → α) : ℕ → α :=
  fun m ↦ if h : m < n then f ⟨m, h⟩ else 0

/--
  `liftF'` lifts functions over domains `ℕ` to functions over domains `Fin n`
  by taking the obvious injection.
-/
def liftF' (f : ℕ → α) : Fin n → α :=
  fun m ↦ f m.1

open Fin (liftF' liftF)

@[simp]
lemma liftF_succ {f : Fin (n + 1) → α} : liftF f n = f ⟨n, Nat.lt_add_one _⟩ := by
  aesop (add simp liftF)

lemma liftF'_liftF_of_lt {k : Fin m} (h : k < n) :
  liftF' (n := m) (liftF (n := n) f') k = f' ⟨k, by omega⟩ := by
  aesop (add simp [liftF, liftF'])

@[simp]
lemma liftF'_liftF_succ {f : Fin (n + 1) → α} {x : Fin n} :
  liftF' (liftF (n := n + 1) f) x = f x.castSucc := by
  aesop (add simp [liftF, liftF']) (add safe (by omega))

@[simp]
lemma liftF'_liftF : Function.LeftInverse liftF' (liftF (α := α) (n := n)) := by
  aesop (add simp [Function.LeftInverse, liftF, liftF'])

@[simp]
lemma liftF'_liftF_eq : liftF' (liftF f') = f' := by unfold liftF' liftF; simp

lemma liftF_liftF'_of_lt (h : m < n) : liftF (liftF' (n := n) f) m = f m := by
  aesop (add simp liftF)

@[simp]
lemma liftF_liftF'_succ : liftF (liftF' (n := n + 1) f) n = f n := by
  aesop (add simp liftF)

lemma liftF_eval {f : Fin n → α} {i : Fin n} :
  liftF f i.val = f i := by
  aesop (add simp liftF)

lemma lt_of_liftF_ne_zero {f : Fin n → α} {i : ℕ}
  (h : liftF f i ≠ 0)
  : i < n := by
  aesop (add simp liftF)

lemma liftF_ne_zero_of_lt {i : ℕ} (h : i < n) : liftF f' i ≠ 0 ↔ f' ⟨i, h⟩ ≠ 0 := by
  aesop (add simp liftF)

lemma liftF_eq_of_lt {i : ℕ} (h : i < n) : liftF f' i = f' ⟨i, h⟩ := by
  aesop (add simp liftF)

@[simp]
lemma liftF_zero_eq_zero
  : liftF (fun (_ : Fin n) ↦ (0 : α)) = (fun _ ↦ (0 : α)) := by
  aesop (add simp liftF)

@[simp]
lemma liftF'_zero_eq_zero
  : liftF' (fun _ ↦ (0 : α)) = (fun (_ : Fin n) ↦ (0 : α)) := by
  aesop (add simp liftF')

abbrev contract (m : ℕ) (f : Fin n → α) := liftF (liftF' (n := m) (liftF f))

open Fin (contract)

lemma contract_eq_liftF_of_lt {k : ℕ} (h₁ : k < m) :
  contract m f' k = liftF f' k := by
  aesop (add simp [contract, liftF, liftF'])

attribute [simp] contract.eq_def

variable {F : Type*} [Semiring F] {p : Polynomial F}

open Polynomial

lemma eval_liftF_of_lt {f : Fin m → F} (h : n < m) :
  eval (liftF f n) p = eval (f ⟨n, h⟩) p := by
  aesop (add simp liftF)

@[simp]
lemma liftF'_p_coeff {p : F[X]} {k : ℕ} {i : Fin k} : liftF' p.coeff i = p.coeff i := by
  simp [liftF']

end Lift

end Fin
