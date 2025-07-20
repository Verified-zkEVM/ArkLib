/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Basic

/-!
  # Padding of `Fin`-indexed vectors
-/

namespace Fin

-- Is it worth it defining a dependent version of padding?

variable {α : Sort*}

/-- Pad a `Fin`-indexed vector on the right with an element `a`.

This becomes truncation if `n < m`. -/
def rightpad (n : ℕ) (a : α) {m : ℕ} (v : Fin m → α) : Fin n → α :=
  fun i => if h : i < m then v ⟨i, h⟩ else a

/-- Pad a `Fin`-indexed vector on the left with an element `a`.

This becomes truncation if `n < m`. -/
def leftpad (n : ℕ) (a : α) {m : ℕ} (v : Fin m → α) : Fin n → α :=
  fun i => if h : n - m ≤ i then v ⟨i - (n - m), by omega⟩ else a

end Fin
