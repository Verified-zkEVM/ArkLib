/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.TakeDrop
import Mathlib.Tactic.FinCases

/-!
# Python-like slice notation for Fin tuples

We define Python-like slice notation for range operations on Fin tuples:
- `v⟦:m⟧` takes the first `m` elements (equivalent to `Fin.take m (by omega) v`)
- `v⟦m:⟧` drops the first `m` elements (equivalent to `Fin.drop m (by omega) v`)
- `v⟦m₁:m₂⟧` takes elements from index `m₁` to `m₂`
(equivalent to `Fin.drop m₁ (by omega) (Fin.take m₂ (by omega) v)`)

Each notation also supports manual proof syntax with `'h`:
- `v⟦:m⟧'h` for `Fin.take m h v`
- `v⟦m:⟧'h` for `Fin.drop m h v`
- `v⟦m₁:m₂⟧'⟨h₁, h₂⟩` for `Fin.drop m₁ h₁ (Fin.take m₂ h₂ v)`

NOTE: this is somewhat duplicate work with `Init.Data.Slice`, though the slices there are not
"dependent", i.e. they do not encode the proofs of the bounds.

This is scoped to `Fin` namespace so one has to open it to use the notation.
-/

namespace Fin

/-- Notation `v⟦:m⟧` for taking the first `m` elements (indexed from `0` to `m - 1`) of a Fin tuple
-/
scoped syntax:max (name := finTakeSlice) term "⟦" ":" term "⟧" : term
scoped macro_rules (kind := finTakeSlice)
  | `($v⟦: $m⟧) => `(take $m (by omega) $v)

/-- Notation `v⟦:m⟧'h` for taking the first `m` elements (indexed from `0` to `m - 1`) with explicit
proof -/
syntax (name := finTakeSliceWithProof) term "⟦" ":" term "⟧'" term:max : term
scoped macro_rules (kind := finTakeSliceWithProof)
  | `($v⟦: $m⟧' $h) => `(take $m $h $v)

/-- Notation `v⟦m:⟧` for dropping the first `m` elements of a Fin tuple -/
scoped syntax:max (name := finDropSlice) term "⟦" term ":" "⟧" : term
scoped macro_rules (kind := finDropSlice)
  | `($v⟦$m :⟧) => `(drop $m (by omega) $v)

/-- Notation `v⟦m:⟧'h` for dropping the first `m` elements with explicit proof -/
scoped syntax (name := finDropSliceWithProof) term "⟦" term ":" "⟧'" term:max : term
scoped macro_rules (kind := finDropSliceWithProof)
  | `($v⟦$m :⟧' $h) => `(drop $m $h $v)

/-- Notation `v⟦m₁:m₂⟧` for taking elements from index `m₁` to `m₂ - 1`
(e.g., `v⟦1:3⟧ = v[1] ++ v[2]`), with range proofs automatically synthesized -/
scoped syntax:max (name := finSliceRange) term "⟦" term ":" term "⟧" : term
scoped macro_rules (kind := finSliceRange)
  | `($v⟦$m₁ : $m₂⟧) => `(drop $m₁ (by omega) (take $m₂ (by omega) $v))

/-- Notation `v⟦m₁:m₂⟧'⟨h₁, h₂⟩` for taking elements from index `m₁` to `m₂ - 1`
(e.g., `v⟦1:3⟧ = ![v 1, v 2]`), with explicit proofs -/
scoped syntax (name := finSliceRangeWithProof)
  term "⟦" term ":" term "⟧'⟨" term:max "," term:max "⟩" : term
scoped macro_rules (kind := finSliceRangeWithProof)
  | `($v⟦$m₁ : $m₂⟧'⟨$h₁, $h₂⟩) => `(drop $m₁ $h₁ (take $m₂ $h₂ $v))

/-! ## Note on Delaborators

For the best user experience, you may want to add delaborators to display
`Fin.take m h v` as `v⟦:m⟧`, `Fin.drop m h v` as `v⟦m:⟧`, and
`Fin.drop m₁ h₁ (Fin.take m₂ h₂ v)` as `v⟦m₁:m₂⟧` in goal states and error messages.

This would require implementing proper delaborators with the correct SubExpr navigation,
which depends on the specific Lean version and can be complex to get right.

For now, the notation works perfectly for input - you can write `v⟦1:4⟧` and it will
expand correctly. The only limitation is that in proof goals you'll see the expanded
form rather than the slice notation.
-/

end Fin

-- Add examples of notation

section Examples

open Fin

/-!
## Examples showing the Python-like slice notation works correctly
-/

variable {n : ℕ} (hn5 : 5 ≤ n) (hn10 : 10 ≤ n) (v : Fin n → ℕ)

example : v⟦:3⟧ = Fin.take 3 (by omega) v := rfl
example : v⟦2:⟧ = Fin.drop 2 (by omega) v := rfl
example : v⟦1:4⟧ = Fin.drop 1 (by omega) (Fin.take 4 (by omega) v) := rfl

-- Manual proof versions
example (h₂ : 4 ≤ n) : v⟦1:4⟧ = Fin.drop 1 (by omega) (Fin.take 4 h₂ v) := rfl
example (h : 3 ≤ n) : v⟦:3⟧'h = Fin.take 3 h v := rfl
example (h : 2 ≤ n) : v⟦2:⟧'h = Fin.drop 2 h v := rfl

-- Concrete examples with vector notation
example : (![0, 1, 2, 3, 4] : Fin 5 → ℕ)⟦:3⟧ = ![0, 1, 2] := by
  ext i; fin_cases i <;> simp [Fin.take]

example : (![0, 1, 2, 3, 4] : Fin 5 → ℕ)⟦2:⟧ = ![2, 3, 4] := by
  ext i; fin_cases i <;> simp [Fin.drop]

example : (![0, 1, 2, 3, 4] : Fin 5 → ℕ)⟦1:4⟧ = ![1, 2, 3] := by
  ext i; fin_cases i <;> simp [Fin.drop, Fin.take]

-- Heterogeneous type examples
variable {α : Fin n → Type*} (hv : (i : Fin n) → α i)

example (h : 3 ≤ n) : hv⟦:3⟧'h = Fin.take 3 h hv := rfl
example (h : 2 ≤ n) : hv⟦2:⟧'h = Fin.drop 2 h hv := rfl
example (h₂ : 4 ≤ n) : hv⟦1:4⟧ = Fin.drop 1 (by omega) (Fin.take 4 h₂ hv) := rfl

-- Show that slicing composes correctly
example : (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 10 → ℕ)⟦2:8⟧⟦1:4⟧ = ![3, 4, 5] := by
  ext i; fin_cases i <;> simp [Fin.drop, Fin.take]

-- Edge cases
example : (![0, 1, 2] : Fin 3 → ℕ)⟦:0⟧ = ![] := by
  ext i; exact Fin.elim0 i

example : (![0, 1, 2] : Fin 3 → ℕ)⟦3:⟧ = ![] := by
  ext i; simp at i; exact Fin.elim0 i

-- Show that the notation works in contexts where omega can prove bounds
variable (w : Fin 20 → ℕ)

example : w⟦:5⟧ = Fin.take 5 (by omega : 5 ≤ 20) w := rfl
example : w⟦15:⟧ = Fin.drop 15 (by omega : 15 ≤ 20) w := rfl
example : w⟦3:18⟧ = Fin.drop 3 (by omega) (Fin.take 18 (by omega) w) := rfl

example : w⟦2:4⟧ = ![w 2, w 3] := by ext i; fin_cases i <;> simp

end Examples
