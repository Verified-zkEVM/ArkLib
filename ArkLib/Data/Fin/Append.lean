/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Basic
import ArkLib.Data.Fin.TakeDrop

/-!
# Custom Fin functions with better definitional equality

This file provides improved versions of some `Fin` functions that use pattern matching
for better definitional equality. The standard library versions rely on complex constructions
like `cases`, `addCases`, and conditional statements with casts, which can make reasoning
about definitional equality difficult.

## Functions provided:
- `vecCons`: Improved version of `cons` using pattern matching
- `vecSnoc`: Improved version of `snoc` using pattern matching
- `vecAppend`: Improved version of `append` using pattern matching
- `vecEmpty`/`vecCons`: Custom vector constructors for `!⟦⟧` notation

## Standard functions that are sufficient:
- `init`: The standard version provides good enough definitional equality
- `tail`: The standard version is sufficient for most cases
- `take`/`drop`: Available in mathlib with adequate definitional behavior

The prime versions use pattern matching on the size parameter for better definitional behavior,
which minimizes casting needed in `OracleReduction.Cast`.
-/

universe u v w

/-- Class for heterogeneous & dependent append, such as `Fin.dvecAppend`. -/
class HDAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ++ᵈ b` is the result of concatenating `a` and `b`, usually read "dependent append".
  The meaning of this notation is type-dependent. -/
  hDAppend : α → β → γ

@[inherit_doc HDAppend.hDAppend] infixl:65 " ++ᵈ " => HDAppend.hDAppend
macro_rules | `($x ++ᵈ $y)  => `(binop% HDAppend.hDAppend $x $y)

namespace Fin

/-- `vecCons a v` prepends an entry `a : α` to a vector `v : Fin n → α` via pattern matching.

This is meant to replace `Matrix.vecCons` for our use cases, as this definition offers better
definitional equality.
-/
def vecCons {α : Sort*} {n : ℕ} (a : α) (v : Fin n → α) : Fin (n + 1) → α :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => fun i =>
    match h : i.val with
    | 0 => a
    | k + 1 => v ⟨k, Nat.lt_of_succ_lt_succ (h ▸ i.isLt)⟩

/-- `dvecCons a b` prepends an entry `a : α` to a dependent or heterogeneous vector
`b : (i : Fin n) → β i`, where `α : Sort u` and `β : Fin n → Sort u` is a vector of sorts,
via pattern matching.

This is meant to replace `Fin.cons` for our use cases, as this definition offers better
definitional equality.
-/
def dvecCons {n : ℕ} {α : Sort u} {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    (i : Fin (n + 1)) → vecCons α β i :=
  match n with
  | 0 => fun i => a
  | _ + 1 => fun i => by
    dsimp [vecCons]
    split
    next hi => exact a
    next k hi => exact b ⟨k, Nat.lt_of_succ_lt_succ (hi ▸ i.isLt)⟩

/-- `vecSnoc v a` appends a vector `v : Fin n → α` with an entry `a : α` via pattern matching.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better definitional
equality.
-/
def vecSnoc {α : Sort*} {n : ℕ} (v : Fin n → α) (a : α) : Fin (n + 1) → α :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => vecCons (v 0) (vecSnoc (v ∘ succ) a)

/-- `dvecSnoc u a` appends a dependent or heterogeneous vector `u : (i : Fin n) → α i` with an
entry `a : β` via pattern matching, where `α : Fin n → Sort u` is a vector of sorts and `β : Sort u`
is a sort.

This is meant to replace `Fin.snoc` for our use cases, as this definition offers better
definitional equality.
-/
def dvecSnoc {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : (i : Fin n) → α i) (a : β) :
    (i : Fin (n + 1)) → vecSnoc α β i :=
  match n with
  | 0 => fun _ => a
  | _ + 1 => dvecCons (u 0) (dvecSnoc (fun i => u i.succ) a)

/-- `vecAppend u v` appends two vectors `u : Fin m → α` and `v : Fin n → α` via pattern matching.

This is meant to replace `Fin.append` for our use cases, as this definition offers better
definitional equality. -/
def vecAppend {α : Sort*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) : Fin (m + n) → α :=
  match n with
  | 0 => u
  | n + 1 => vecSnoc (vecAppend u (v ∘ castSucc)) (v (last n))

/-- `dvecAppend u v` appends two dependent or heterogeneous vectors `u : (i : Fin m) → α i` and
`v : (i : Fin n) → β i`, on `α : Fin m → Sort u` and `β : Fin n → Sort u` respectively, via
pattern matching.

This is meant to replace `Fin.addCases` for our use cases, as this definition offers better
definitional equality.
-/
def dvecAppend {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
    (i : Fin (m + n)) → vecAppend α β i :=
  match n with
  | 0 => u
  | n + 1 => dvecSnoc (dvecAppend u (fun i => v i.castSucc)) (v (last n))

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

example : vecSnoc !⟦1, 2⟧ 3 = !⟦1, 2, 3⟧ := rfl

example : vecAppend !⟦1, 2⟧ !⟦3, 4⟧ = !⟦1, 2, 3, 4⟧ := rfl

instance {α : Type*} {m n : ℕ} : HAppend (Fin m → α) (Fin n → α) (Fin (m + n) → α) where
  hAppend := vecAppend

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
example : init (vecSnoc !⟦Nat, Int⟧ Bool) = !⟦Nat, Int⟧ := by
  dsimp [init, vecSnoc, vecCons, vecCons]
  ext i; fin_cases i <;> rfl

example : vecSnoc (init !⟦Nat, Int, Unit⟧) Bool = !⟦Nat, Int, Bool⟧ := by rfl

example {v : Fin 3 → ℕ} : vecSnoc (init v) (v (last 2)) = v := by
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
- Working with custom Fin functions (`vecCons`, `tail`, `vecSnoc`, `vecAppend`, etc.)
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

end NewNotationTests

end Fin
