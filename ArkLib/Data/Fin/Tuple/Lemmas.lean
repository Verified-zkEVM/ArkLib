/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Vec.Notation

/-!
  # Lemmas for `Fin`-indexed vectors
-/

universe u

namespace Fin

variable {m n : ℕ} {α : Sort u}

section vecCons

@[simp]
theorem vecCons_zero (a : α) (v : Fin n → α) : vecCons a v 0 = a := by
  induction n with
  | zero => simp [vecCons]
  | succ n ih => simp [vecCons]; rfl

@[simp]
theorem vecCons_succ (a : α) (v : Fin n → α) (i : Fin n) :
    vecCons a v i.succ = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => simp [vecCons]

theorem vecCons_eq_cons (a : α) (v : Fin n → α) :
    vecCons a v = cons (α := fun _ => α) a v := by
  ext i
  induction i using Fin.induction <;> simp

end vecCons

section dvecCons

@[simp]
theorem dvecCons_zero {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    dvecCons a v 0 = cast (vecCons_zero α β).symm a := by
  induction n with
  | zero => simp [dvecCons]
  | succ n ih => simp [dvecCons]; rfl

@[simp]
theorem dvecCons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    dvecCons a v i.succ = cast (vecCons_succ α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => simp [dvecCons]; rfl

theorem dvecCons_eq_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    dvecCons a v = cons (α := vecCons α β) (dvecCons a v 0) (fun i => dvecCons a v i.succ) := by
  ext i
  induction i using Fin.induction <;> simp

end dvecCons

section vecConcat

@[simp]
theorem vecConcat_zero (a : α) : vecConcat (elim0 : Fin 0 → α) a = fun _ => a := by
  simp [vecConcat]

@[simp]
theorem vecConcat_last (v : Fin n → α) (a : α) : vecConcat v a (last n) = a := by
  induction n with
  | zero => simp [vecConcat]
  | succ n ih =>
    dsimp [vecConcat]
    rw [vecCons_succ]
    exact ih

@[simp]
theorem vecConcat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    vecConcat v a (castSucc i) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [vecConcat]
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [ih]

end vecConcat

section dvecConcat

@[simp]
theorem dvecConcat_zero {β : Sort u} (a : β) :
    dvecConcat (elim0 : (i : Fin 0) → Empty) a = fun _ => a := by
  ext i
  simp [dvecConcat]

end dvecConcat

section vecAppend

@[simp]
theorem vecAppend_zero (u : Fin m → α) : vecAppend u (elim0 : Fin 0 → α) = u := by
  simp [vecAppend]

-- Basic property about structure of vecAppend
theorem vecAppend_succ (u : Fin m → α) (v : Fin (n + 1) → α) :
    vecAppend u v = vecConcat (vecAppend u (v ∘ castSucc)) (v (last n)) := by
  simp [vecAppend]

end vecAppend

section dvecAppend

@[simp]
theorem dvecAppend_zero {β : Fin m → Sort u} (u : (i : Fin m) → β i) :
    dvecAppend u (elim0 : (i : Fin 0) → Empty) = u := by
  ext i
  simp [dvecAppend]

end dvecAppend

section rtake

@[simp]
theorem rtake_zero {β : Fin n → Sort u} (h : 0 ≤ n) (v : (i : Fin n) → β i) :
    rtake 0 h v = elim0 := by
  ext i
  exact Fin.elim0 i

end rtake

section drop

@[simp]
theorem drop_zero {β : Fin n → Sort u} (h : 0 ≤ n) (v : (i : Fin n) → β i) :
    drop 0 h v = v := by
  ext i
  simp [drop, addNat]

end drop

section padding

@[simp]
theorem rightpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < m) : rightpad n a v i = v ⟨i.val, h⟩ := by
  simp [rightpad, h]

@[simp]
theorem rightpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : m ≤ i.val) : rightpad n a v i = a := by
  simp [rightpad]
  rw [if_neg]
  omega

@[simp]
theorem leftpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < n - m) : leftpad n a v i = a := by
  simp [leftpad]
  rw [if_neg]
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
