/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Tuple.Notation

/-!
  # Lemmas for `Fin`-indexed vectors
-/

universe u

namespace FinVec

variable {m n : ℕ} {α : Sort u}

@[simp]
theorem cons_zero (a : α) (v : Fin n → α) : cons a v 0 = a := by
  induction n with
  | zero => simp [cons]
  | succ n ih => simp [cons]; rfl

@[simp]
theorem cons_succ (a : α) (v : Fin n → α) (i : Fin n) :
    cons a v i.succ = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => simp [cons, Fin.succ]

theorem cons_eq_fin_cons (a : α) (v : Fin n → α) :
    cons a v = Fin.cons (α := fun _ => α) a v := by
  ext i
  induction i using Fin.induction <;> simp

@[simp]
theorem concat_zero (a : α) : concat (Fin.elim0 : Fin 0 → α) a = fun _ => a := by
  simp [concat]

@[simp]
theorem concat_last (v : Fin n → α) (a : α) : concat v a (Fin.last n) = a := by
  induction n with
  | zero => simp [concat]
  | succ n ih =>
    simp [concat, cons, Fin.last]
    exact ih _

@[simp]
theorem concat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    concat v a (Fin.castSucc i) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [concat]
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [ih]

@[simp]
theorem append_zero (u : Fin m → α) : append u (Fin.elim0 : Fin 0 → α) = u := by
  simp [append]

-- Basic property about structure of append
theorem append_succ (u : Fin m → α) (v : Fin (n + 1) → α) :
    append u v = concat (append u (v ∘ Fin.castSucc)) (v (Fin.last n)) := by
  simp [append]

end FinVec

namespace FinTuple

variable {m n : ℕ} {α : Sort u}

@[simp]
theorem cons_zero {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    cons a b 0 = cast (FinVec.cons_zero α β).symm a := by
  induction n with
  | zero => simp [cons]
  | succ n ih => simp [cons]; rfl

@[simp]
theorem cons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    cons a v i.succ = cast (FinVec.cons_succ α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => simp [cons]; rfl

theorem cons_eq_fin_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    cons a v = Fin.cons (α := FinVec.cons α β) (cons a v 0) (fun i => cons a v i.succ) := by
  ext i
  induction i using Fin.induction <;> simp

@[simp]
theorem concat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    concat (FinTuple.empty : FinTuple 0 α) a = fun _ => a := rfl

@[simp]
theorem append_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    append u (FinTuple.empty : FinTuple 0 α) = u := rfl

end FinTuple

namespace Fin

variable {m n : ℕ} {α : Sort u}

-- @[simp, grind =]
-- theorem concat_eq_append {α : Sort u} {n : ℕ} (v : FinVec α n) (a : α) :
--     concat v a = append v (FinVec.cons a FinVec.empty) := by
--   ext i; fin_cases i <;> rfl

section padding

@[simp]
theorem rightpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < m) : rightpad n a v i = v ⟨i.val, h⟩ := by
  simp [rightpad, h]

@[simp]
theorem rightpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : m ≤ i.val) : rightpad n a v i = a := by
  simp [rightpad]
  omega

@[simp]
theorem leftpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < n - m) : leftpad n a v i = a := by
  simp [leftpad]
  omega

@[simp]
theorem leftpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : n - m ≤ i.val) : leftpad n a v i = v ⟨i.val - (n - m), by omega⟩ := by
  simp [leftpad, h]

theorem rightpad_eq_self (v : Fin n → α) (a : α) : rightpad n a v = v := by
  ext i
  simp [rightpad_apply_lt]

theorem leftpad_eq_self (v : Fin n → α) (a : α) : leftpad n a v = v := by
  ext i
  simp [leftpad_apply_ge]

end padding

end Fin
