/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Even and odd rows of a `Fin (2 ^ (m + 1))`-indexed family

A family of `2 ^ (m + 1)` rows splits into its even-indexed rows and its odd-indexed rows, each
a family of `2 ^ m` rows. Interleaving two families of `2 ^ m` rows is the inverse operation.

## Main definitions

* `Fin.evenRows`, `Fin.oddRows`: the rows `0, 2, 4, …` and the rows `1, 3, 5, …`.
* `Fin.interleaveRows`: the rows `u 0, v 0, u 1, v 1, …`.

## Main statements

* `Fin.evenRows_interleaveRows`, `Fin.oddRows_interleaveRows`: splitting recovers the two inputs
  to interleaving.
* `Fin.exists_eq_evenRows_or_eq_oddRows`: every row is an even row or an odd row.
-/

@[expose] public section

namespace Fin

variable {M : Type*} {m : ℕ}

/-- The rows `0, 2, 4, …` of `2^(m+1)` rows. -/
def evenRows (v : Fin (2 ^ (m + 1)) → M) (i : Fin (2 ^ m)) : M :=
  v ⟨2 * i, by have := i.isLt; have := pow_succ 2 m; omega⟩

/-- The rows `1, 3, 5, …` of `2^(m+1)` rows. -/
def oddRows (v : Fin (2 ^ (m + 1)) → M) (i : Fin (2 ^ m)) : M :=
  v ⟨2 * i + 1, by have := i.isLt; have := pow_succ 2 m; omega⟩

/-- The rows `u 0, v 0, u 1, v 1, …`, alternating between two families of `2^m` rows. -/
def interleaveRows (u v : Fin (2 ^ m) → M) (j : Fin (2 ^ (m + 1))) : M :=
  if (j : ℕ) % 2 = 0 then u ⟨j / 2, by have := j.isLt; have := pow_succ 2 m; omega⟩
  else v ⟨j / 2, by have := j.isLt; have := pow_succ 2 m; omega⟩

/-- The even rows recover the first input to interleaving. -/
@[simp]
theorem evenRows_interleaveRows (u v : Fin (2 ^ m) → M) : evenRows (interleaveRows u v) = u := by
  funext i
  simp [evenRows, interleaveRows]

/-- The odd rows recover the second input to interleaving. -/
@[simp]
theorem oddRows_interleaveRows (u v : Fin (2 ^ m) → M) : oddRows (interleaveRows u v) = v := by
  funext i
  have h : (2 * (i : ℕ) + 1) % 2 ≠ 0 := by omega
  simp only [oddRows, interleaveRows, h, ite_false]
  congr
  omega

/-- Every row is an even row or an odd row. -/
theorem exists_eq_evenRows_or_eq_oddRows (v : Fin (2 ^ (m + 1)) → M) (j : Fin (2 ^ (m + 1))) :
    ∃ i, v j = evenRows v i ∨ v j = oddRows v i := by
  refine ⟨⟨j / 2, by have := j.isLt; have := pow_succ 2 m; omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · exact Or.inl (congrArg v (Fin.ext (by simp only; omega)))
  · exact Or.inr (congrArg v (Fin.ext (by simp only; omega)))

end Fin
