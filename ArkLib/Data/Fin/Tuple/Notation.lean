/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.HDAppend
import ArkLib.Data.Fin.Vec.Defs
import ArkLib.Data.Fin.Basic
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

universe u v w

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

example : w⟦2:4⟧ = ![w 2, w 3] := by ext i; fin_cases i <;> simp [drop, take]

end Examples

namespace Fin

instance {α : Type*} {m n : ℕ} : HAppend (Fin m → α) (Fin n → α) (Fin (m + n) → α) where
  hAppend := vecAppend

instance {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u} :
    HDAppend ((i : Fin m) → α i) ((i : Fin n) → β i) ((i : Fin (m + n)) → vecAppend α β i) where
  hDAppend := dvecAppend

section Examples

#eval tail (vecAppend
  (vecCons 1 (vecCons 2 (vecCons 3 (elim0))))
  (vecCons 4 (elim0)))

example : tail (vecAppend
  (vecCons 1 (vecCons 2 (vecCons 3 (elim0))))
  (vecCons 4 (elim0))) =
    vecCons 2 (vecCons 3 (vecCons 4 (elim0))) := by rfl

-- Understanding why some examples need ext and others don't
section DefEqAnalysis

-- Even when comparing with standard cons using the same construction, we need ext
example : vecCons 1 (vecCons 2 (elim0)) = (cons 1 (cons 2 (elim0))) := by
  ext i; fin_cases i <;> rfl

-- This DOES work with rfl because we're comparing abstract functions
example {v : Fin 2 → ℕ} : tail (vecCons (v 0) (tail v)) = tail v := rfl

-- Here's the key difference illustrated:
example : vecCons 1 (fun _ : Fin 1 => 2) = fun i : Fin 2 => if i = 0 then 1 else 2 := by
  -- vecCons unfolds to pattern matching which doesn't match the if-then-else
  ext i; fin_cases i <;> rfl

-- But with abstract functions, the pattern matching aligns perfectly:
example {a : ℕ} {f : Fin 1 → ℕ} : vecCons a f = fun i =>
  match h : i.val with
  | 0 => a
  | k + 1 => f ⟨k, Nat.lt_of_succ_lt_succ (h ▸ i.isLt)⟩ := rfl

end DefEqAnalysis

end Examples

/-!
## Custom Vector Notation with Better Definitional Equality

We create a new vector notation `!⟦a, b, c⟧` that uses our custom functions with better
definitional equality. This is similar to Mathlib's `Matrix.vecCons` and `Matrix.vecEmpty`
used in `![]` notation, but uses our custom `vecCons` which provides better definitional
equality through pattern matching instead of `cases`.
-/

variable {α : Sort*}

/-- `!⟦⟧` is the empty vector using `elim0`.
Similar to `Matrix.vecEmpty` but provides better definitional equality. -/
def vecEmpty : Fin 0 → α :=
  elim0

/-- `!⟦...⟧` notation constructs a vector using our custom functions.
Uses `⟦` and `⟧` (input with `\[[` and `\]]`) to distinguish from standard `![]`. -/
syntax (name := vecNotation') "!⟦" term,* "⟧" : term

macro_rules
  | `(!⟦$term:term, $terms:term,*⟧) => `(vecCons $term !⟦$terms,*⟧)
  | `(!⟦$term:term⟧) => `(vecCons $term !⟦⟧)
  | `(!⟦⟧) => `(vecEmpty)

/-- Unexpander for the `!⟦x, y, ...⟧` notation. -/
@[app_unexpander vecCons]
def vecConsUnexpander' : Lean.PrettyPrinter.Unexpander
  | `($_ $term !⟦$term2, $terms,*⟧) => `(!⟦$term, $term2, $terms,*⟧)
  | `($_ $term !⟦$term2⟧) => `(!⟦$term, $term2⟧)
  | `($_ $term !⟦⟧) => `(!⟦$term⟧)
  | _ => throw ()

/-- Unexpander for the `!⟦⟧` notation. -/
@[app_unexpander vecEmpty]
def vecEmptyUnexpander' : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!⟦⟧)
  | _ => throw ()

-- Test the new notation
section NewNotationTests

-- These should work with rfl!
example : vecCons 1 !⟦2⟧ = !⟦1, 2⟧ := rfl

example : tail !⟦1, 2, 3⟧ = !⟦2, 3⟧ := rfl

example : vecConcat !⟦1, 2⟧ 3 = !⟦1, 2, 3⟧ := rfl

example : vecAppend !⟦1, 2⟧ !⟦3, 4⟧ = !⟦1, 2, 3, 4⟧ := rfl

example : vecAppend !⟦(true, Nat)⟧
    (vecAppend !⟦⟧ (vecAppend !⟦(false, Int)⟧ !⟦⟧)) =
      !⟦(true, Nat), (false, Int)⟧ := rfl

example : vecAppend (!⟦(true, Nat)⟧ ++ !⟦(false, Int)⟧)
    (vecAppend !⟦(false, Int)⟧ !⟦⟧) = !⟦(true, Nat), (false, Int), (false, Int)⟧ := rfl

-- Test that roundtrip works with pure rfl
example : vecAppend (take 2 (by omega) !⟦1, 2, 3, 4⟧)
    (drop 2 (by omega) !⟦1, 2, 3, 4⟧) = !⟦1, 2, 3, 4⟧ := rfl

-- Complex expression that should compute cleanly
example : tail (vecAppend
    (vecCons 1 (vecCons 2 (vecCons 3 (elim0))))
    (vecCons 4 (elim0))) = !⟦2, 3, 4⟧ := rfl

-- Even more complex combinations work with rfl
example : init (vecConcat !⟦Nat, Int⟧ Bool) = !⟦Nat, Int⟧ := by
  dsimp [init, vecConcat, vecCons, vecCons]
  ext i; fin_cases i <;> rfl

example : vecConcat (init !⟦Nat, Int, Unit⟧) Bool = !⟦Nat, Int, Bool⟧ := by rfl

example {v : Fin 3 → ℕ} : vecConcat (init v) (v (last 2)) = v := by
  ext i; fin_cases i <;> rfl

-- Multiple operations compose cleanly
example : tail (vecCons 0 (vecAppend !⟦1, 2⟧ !⟦3, 4⟧)) =
    !⟦1, 2, 3, 4⟧ := rfl

/-- Test that our new notation gives the same result as the old one (extensionally) -/
example : !⟦1, 2, 3⟧ = ![1, 2, 3] := by ext i; fin_cases i <;> rfl

/-!
### Usage Guidelines for `!⟦⟧` vs `![]` Notation

**Use `!⟦⟧` when:**
- You need better definitional equality and want proofs to close with `rfl`
- Working with custom Fin functions (`vecCons`, `tail`, `vecConcat`, `vecAppend`, etc.)
- Building complex expressions that should compute cleanly
- Minimizing casts in your code

**Use `![]` when:**
- Interfacing with existing Mathlib code that expects standard `Matrix.vecCons`
- You don't need the improved definitional behavior
- Working with standard library Fin functions (`init`, `tail`, `cons`, `snoc`, `append`)

**Examples of the difference:**
```lean
-- ✅ Works with rfl using new notation
example : vecCons 1 !⟦2, 3⟧ = !⟦1, 2, 3⟧ := rfl

-- ❌ Needs ext with old notation
example : vecCons 1 ![2, 3] = ![1, 2, 3] := by ext i; fin_cases i <;> rfl

-- ✅ Complex operations work with rfl
example : vecAppend !⟦1, 2⟧ !⟦3, 4⟧ = !⟦1, 2, 3, 4⟧ := rfl
```

The new notation can significantly reduce the need for casting in `OracleReduction.Cast`!
-/

-- Test dependent vector functions for definitional equality
section DependentVectorTests

-- Test that the ++ᵈ notation is properly defined
example : (fun _ : Fin 1 => (42 : ℕ)) ++ᵈ (fun _ : Fin 1 => (true : Bool)) =
          dvecAppend (fun _ : Fin 1 => (42 : ℕ)) (fun _ : Fin 1 => (true : Bool)) := rfl

-- Test that the notation can be chained and is associative
example : ((fun _ : Fin 1 => (1 : ℕ)) ++ᵈ (fun _ : Fin 1 => (true : Bool))) ++ᵈ
          (fun _ : Fin 1 => ("test" : String)) =
          (fun _ : Fin 1 => (1 : ℕ)) ++ᵈ
          ((fun _ : Fin 1 => (true : Bool)) ++ᵈ (fun _ : Fin 1 => ("test" : String))) := rfl

-- Test that type vectors compute correctly
example : vecCons ℕ (fun _ : Fin 1 => Bool) 0 = ℕ := rfl

example : vecCons ℕ (fun _ : Fin 1 => Bool) 1 = Bool := rfl

-- Test vecAppend on types
example : vecAppend (fun _ : Fin 1 => ℕ) (fun _ : Fin 1 => Bool) 0 = ℕ := rfl

example : vecAppend (fun _ : Fin 1 => ℕ) (fun _ : Fin 1 => Bool) 1 = Bool := rfl

-- Test vecConcat on types
example : vecConcat (fun _ : Fin 1 => ℕ) Bool 0 = ℕ := rfl

example : vecConcat (fun _ : Fin 1 => ℕ) Bool 1 = Bool := rfl

-- Test that regular vector functions work with the !⟦⟧ notation
example : vecCons 1 !⟦2, 3⟧ = !⟦1, 2, 3⟧ := rfl

example : vecConcat !⟦1, 2⟧ 3 = !⟦1, 2, 3⟧ := rfl

example : vecAppend !⟦1, 2⟧ !⟦3, 4⟧ = !⟦1, 2, 3, 4⟧ := rfl

-- Test that the dependent versions provide good definitional equality
example : vecCons ℕ (vecCons Bool (fun _ : Fin 0 => Empty)) =
    fun i : Fin 2 => if i = 0 then ℕ else Bool := by
  ext i; fin_cases i <;> rfl

end DependentVectorTests

end NewNotationTests

end Fin
