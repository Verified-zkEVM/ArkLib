/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.Slice
import ArkLib.Data.Fin.Tuple.Defs
import ArkLib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Slice notation instances for Fin tuples

This file provides instances of the generic slice type classes (`SliceLT`, `SliceGE`, `Slice`)
for Fin tuples, enabling Python-like slice notation:
- `v⟦:m⟧` takes the first `m` elements
- `v⟦m:⟧` drops the first `m` elements
- `v⟦m₁:m₂⟧` takes elements from index `m₁` to `m₂ - 1`

The instances work for both homogeneous (`Fin n → α`) and heterogeneous (`(i : Fin n) → α i`)
Fin tuples, delegating to the existing `Fin.take` and `Fin.drop` operations.

Each notation also supports manual proof syntax with `'h`:
- `v⟦:m⟧'h` for explicit proof in take operations
- `v⟦m:⟧'h` for explicit proof in drop operations
- `v⟦m₁:m₂⟧'⟨h₁, h₂⟩` for explicit proofs in range operations

## Examples

```lean
variable (v : Fin 10 → ℕ)

#check v⟦:5⟧   -- Takes first 5 elements: Fin 5 → ℕ
#check v⟦3:⟧   -- Drops first 3 elements: Fin 7 → ℕ
#check v⟦2:8⟧  -- Elements 2 through 7: Fin 6 → ℕ
```
-/

universe u v v' w

/-! ## Instances for Fin tuples -/

namespace Fin

instance {n : ℕ} {α : Fin n → Type*} : SliceLT ((i : Fin n) → α i) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop h => (i : Fin stop) → α (i.castLE h))
    where
  sliceLT := fun v stop h => take stop h v

instance {n : ℕ} {α : Fin n → Type*} : SliceGE ((i : Fin n) → α i) ℕ
    (fun _ start => start ≤ n)
    (fun _ start h =>
      (i : Fin (n - start)) → α (Fin.cast (Nat.sub_add_cancel h) (i.addNat start)))
    where
  sliceGE := fun v start h => drop start h v

instance {n : ℕ} {α : Fin n → Type*} : Slice ((i : Fin n) → α i) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop h =>
      (i : Fin (stop - start)) →
        α (castLE h.2 (Fin.cast (Nat.sub_add_cancel h.1) (i.addNat start))))
    where
  slice := fun v start stop h => Fin.drop start h.1 (Fin.take stop h.2 v)

end Fin

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
  ext i; fin_cases i <;> simp [SliceLT.sliceLT]

example : (![0, 1, 2, 3, 4] : Fin 5 → ℕ)⟦2:⟧ = ![2, 3, 4] := by
  ext i; fin_cases i <;> simp [SliceGE.sliceGE, drop]

example : (![0, 1, 2, 3, 4] : Fin 5 → ℕ)⟦1:4⟧ = ![1, 2, 3] := by
  ext i; fin_cases i <;> simp [Fin.drop, Fin.take, Slice.slice]

-- Heterogeneous type examples
variable {α : Fin n → Type*} (hv : (i : Fin n) → α i)

example (h : 3 ≤ n) : hv⟦:3⟧'h = Fin.take 3 h hv := rfl
example (h : 2 ≤ n) : hv⟦2:⟧'h = Fin.drop 2 h hv := rfl
example (h₂ : 4 ≤ n) : hv⟦1:4⟧ = Fin.drop 1 (by omega) (Fin.take 4 h₂ hv) := rfl

-- Show that slicing composes correctly
example : (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 10 → ℕ)⟦2:8⟧⟦1:4⟧ = ![3, 4, 5] := by
  ext i; fin_cases i <;> simp [Fin.drop, Fin.take, Slice.slice]

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

example : w⟦2:4⟧ = ![w 2, w 3] := by ext i; fin_cases i <;> simp [drop, take, Slice.slice]

end Examples

/-!
## Comprehensive Tuple Notation System with Better Definitional Equality

This file provides a unified notation system for Fin-indexed tuples with better definitional
equality through pattern matching. The system supports homogeneous vectors, heterogeneous tuples,
dependent tuples, and functorial operations, all with consistent notation patterns.

### Vector and Tuple Construction Notation:

**Homogeneous Vectors** (all elements have the same type):
- `!v[a, b, c]` - basic homogeneous vector
- `!v⟨α⟩[a, b, c]` - with explicit type ascription

**Heterogeneous Tuples** (elements can have different types):
- `!h[a, b, c]` - basic heterogeneous tuple (uses `hcons`)
- `!h⟨α⟩[a, b, c]` - heterogeneous tuple with type vector ascription
- `!h⦃F⦄[a, b, c]` - functorial with explicit unary functor F but implicit type vector
- `!h⦃F⦄⟨α⟩[a, b, c]` - functorial with unary functor F and type vector α
- `!h⦃F⦄⟨α₁⟩⟨α₂⟩[a, b, c]` - functorial with binary functor F and type vectors α₁ and α₂

**Dependent Tuples** (with explicit motive specification):
- `!d[a, b, c]` - basic dependent tuple (uses `dcons`)
- `!d⟨motive⟩[a, b, c]` - with explicit motive

### Infix Operations:

**Cons Operations** (prepend element):
- `a ::ᵛ v` - homogeneous cons
- `a ::ᵛ⟨α⟩ v` - homogeneous cons with explicit type ascription
- `a ::ʰ t` - heterogeneous cons
- `a ::ʰ⟨α ; β⟩ t` - heterogeneous cons with explicit type ascription
- `a ::ʰ⦃F⦄ t` - functorial cons (unary) with type besides `F` inferred
- `a ::ʰ⦃F⦄⟨α ; β⟩ t` - functorial cons (unary) with explicit type ascription
- `a ::ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩ t` - functorial cons (binary) with explicit type ascription
- `a ::ᵈ t` - dependent cons
- `a ::ᵈ⟨motive⟩ t` - dependent cons with explicit motive

**Concat Operations** (append element):
- `v :+ᵛ a` - homogeneous concat
- `v :+ᵛ⟨α⟩ a` - homogeneous concat with explicit type ascription
- `t :+ʰ a` - heterogeneous concat
- `t :+ʰ⟨α ; β⟩ a` - heterogeneous concat with explicit type ascription
- `t :+ʰ⦃F⦄ a` - functorial concat (unary) with type besides `F` inferred
- `t :+ʰ⦃F⦄⟨α ; β⟩ a` - functorial concat (unary)
- `t :+ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩ a` - functorial concat (binary)
- `t :+ᵈ a` - dependent concat
- `t :+ᵈ⟨motive⟩ a` - dependent concat with explicit motive

**Append Operations** (concatenate two tuples):
- `u ++ᵛ v` - homogeneous append
- `u ++ᵛ⟨α⟩ v` - homogeneous append with explicit type ascription
- `u ++ʰ v` - heterogeneous append
- `u ++ʰ⟨α ; β⟩ v` - heterogeneous append with explicit type ascription
- `u ++ʰ⦃F⦄ v` - functorial append (unary) with type besides `F` inferred
- `u ++ʰ⦃F⦄⟨α ; β⟩ v` - functorial append (unary)
- `u ++ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩ v` - functorial append (binary)
- `u ++ᵈ v` - dependent append
- `u ++ᵈ⟨motive⟩ v` - dependent append with explicit motive

### Design Principles:

1. **Better Definitional Equality**: All operations use pattern matching instead of `cases`,
   `addCases`, or conditional statements for superior computational behavior.

2. **Unified `h` Superscript**: All heterogeneous and functorial operations use the `h`
   superscript with explicit type ascriptions when needed.

3. **Semicolon Separators**: Functorial operations use `α ; β` syntax to clearly distinguish
   the two type arguments required for functor application.

4. **Consistent Type Ascriptions**: Explicit type information uses `⟨...⟩` brackets throughout.

5. **Unexpander Conflict Resolution**: Each construction function (`hcons`, `dcons`, etc.)
   has its own dedicated notation to prevent pretty-printing ambiguities.

This system replaces Mathlib's `Matrix.vecCons`/`Matrix.vecEmpty` approach with our custom
functions that provide better definitional equality and a more comprehensive type hierarchy.
-/

namespace Fin

-- Infix notation for cons operations, similar to Vector.cons
@[inherit_doc]
infixr:67 " ::ᵛ " => Fin.vcons

-- Infix notation for concat operations, following Scala convention
@[inherit_doc]
infixl:65 " :+ᵛ " => Fin.vconcat

/-- `::ᵛ⟨α⟩` notation for homogeneous cons with explicit element type. -/
syntax:67 term:68 " ::ᵛ⟨" term "⟩ " term:67 : term

/-- `:+ᵛ⟨α⟩` notation for homogeneous concat with explicit element type. -/
syntax:65 term:66 " :+ᵛ⟨" term "⟩ " term:65 : term

/-- `++ᵛ⟨α⟩` notation for homogeneous append with explicit element type. -/
syntax:65 term:66 " ++ᵛ⟨" term "⟩ " term:65 : term

macro_rules
  | `($a:term ::ᵛ⟨$α:term⟩ $v:term) => `(Fin.vcons (α := $α) $a $v)

macro_rules
  | `($v:term :+ᵛ⟨$α:term⟩ $a:term) => `(Fin.vconcat (α := $α) $v $a)

macro_rules
  | `($u:term ++ᵛ⟨$α:term⟩ $v:term) => `(Fin.vappend (α := $α) $u $v)

/-- `!v[...]` notation constructs a vector using our custom functions.
Uses `!v[...]` to distinguish from standard `![]`. -/
syntax (name := finVecNotation) "!v[" term,* "]" : term

/-- `!v⟨α⟩[...]` notation constructs a vector with explicit type ascription.
Uses angle brackets to specify the element type, then square brackets for values. -/
syntax (name := finVecNotationWithType) "!v⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!v[$term:term, $terms:term,*]) => `((Fin.vcons $term !v[$terms,*]))
  | `(!v[$term:term]) => `((Fin.vcons $term !v[]))
  | `(!v[]) => `(Fin.vempty)

macro_rules
  | `(!v⟨$α⟩[$term:term, $terms:term,*]) => `(Fin.vcons (α := $α) $term !v⟨$α⟩[$terms,*])
  | `(!v⟨$α⟩[$term:term]) => `(Fin.vcons (α := $α) $term !v⟨$α⟩[])
  | `(!v⟨$α⟩[]) => `((Fin.vempty : Fin 0 → $α))

/-- Unexpander for the `!v[x, y, ...]` notation. -/
@[app_unexpander Fin.vcons]
def vconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !v[$term2, $terms,*]) => `(!v[$term, $term2, $terms,*])
  | `($_ $term !v[$term2]) => `(!v[$term, $term2])
  | `($_ $term !v[]) => `(!v[$term])
  | _ => throw ()

/-- Unexpander for the `!v[]` notation. -/
@[app_unexpander Fin.vempty]
def vemptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!v[])
  | _ => throw ()

@[inherit_doc]
infixr:67 " ::ʰ " => Fin.hcons

@[inherit_doc]
infixl:65 " :+ʰ " => Fin.hconcat

/-- `::ʰ⟨α ; β⟩` notation for hcons with explicit type ascriptions -/
syntax:67 term:68 " ::ʰ⟨" term " ; " term "⟩ " term:67 : term

/-- `:+ʰ⟨α ; β⟩` notation for hconcat with explicit type ascriptions -/
syntax:65 term:66 " :+ʰ⟨" term " ; " term "⟩ " term:65 : term

/-- Functorial cons with explicit functor but inferred type families: `::ʰ⦃F⦄`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄ " term:67 : term

/-- Functorial cons (unary) with explicit types: `::ʰ⦃F⦄⟨α ; β⟩`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄⟨" term " ; " term "⟩ " term:67 : term

/-- Functorial cons (binary) with explicit types: `::ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄⟨" term " ; " term "⟩⟨" term " ; " term "⟩ " term:67 : term

@[inherit_doc]
infixr:67 " ::ᵈ " => Fin.dcons

@[inherit_doc]
infixl:65 " :+ᵈ " => Fin.dconcat

/-- `::ᵈ⟨motive⟩` notation for dcons with explicit motive specification -/
syntax:67 term:68 " ::ᵈ⟨" term "⟩ " term:67 : term

/-- `:+ᵈ⟨motive⟩` notation for dconcat with explicit motive specification -/
syntax:65 term:66 " :+ᵈ⟨" term "⟩ " term:65 : term

/-- `!h[...]` notation constructs a heterogeneous tuple using hcons.
For automatic type inference without explicit motive. -/
syntax (name := finHeterogeneousNotation) "!h[" term,* "]" : term

/-- `!h⟨α⟩[...]` notation constructs a heterogeneous tuple with explicit type vector ascription.
Uses angle brackets to specify the type vector, then square brackets for values. -/
syntax (name := finHeterogeneousNotationWithTypeVec) "!h⟨" term "⟩[" term,* "]" : term

/-- `!h⦃F⦄[...]` functorial heterogeneous tuple with explicit functor and implicit type vectors. -/
syntax (name := finFunctorialHeterogeneousNotationShorthand) "!h⦃" term "⦄[" term,* "]" : term

/-- `!d[...]` notation constructs a dependent tuple using our custom dependent functions.
Uses `!d[...]` for dependent tuples with explicit motives. -/
syntax (name := finDependentNotation) "!d[" term,* "]" : term

/-- `!d⟨motive⟩[...]` notation constructs a dependent tuple with explicit motive specification.
Uses angle brackets to specify the motive, then square brackets for values. -/
syntax (name := finDependentNotationWithmotive) "!d⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!h[$term:term, $terms:term,*]) => `(Fin.hcons $term !h[$terms,*])
  | `(!h[$term:term]) => `(Fin.hcons $term !h[])
  | `(!h[]) => `((Fin.dempty))

macro_rules
  | `(!h⟨$typeVec⟩[$term:term, $terms:term,*]) =>
      `(($term : $typeVec 0) ::ʰ !h⟨fun i => $typeVec (Fin.succ i)⟩[$terms,*])
  | `(!h⟨$typeVec⟩[$term:term]) => `(($term : $typeVec 0) ::ʰ !h⟨fun i => $typeVec (Fin.succ i)⟩[])
  | `(!h⟨$typeVec⟩[]) => `((Fin.dempty : (i : Fin 0) → $typeVec i))

/-! Functorial heterogeneous tuple constructors with explicit type vectors -/

/-- Unary functorial: `!h⦃F⦄⟨α⟩[...]` where `α : Fin n → Sort _`. -/
syntax (name := finFunctorialHeterogeneousNotation)
  "!h⦃" term "⦄⟨" term "⟩[" term,* "]" : term

/-- Binary functorial: `!h⦃F⦄⟨α₁⟩⟨α₂⟩[...]` where `α₁, α₂ : Fin n → Sort _`. -/
syntax (name := finFunctorialBinaryHeterogeneousNotation)
  "!h⦃" term "⦄⟨" term "⟩⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!h⦃$F⦄⟨$α:term⟩[$x:term, $xs:term,*]) =>
    `(Fin.fcons (F := $F) (α := $α 0) (β := fun i => $α (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α (Fin.succ i)⟩[$xs,*])
  | `(!h⦃$F⦄⟨$α:term⟩[$x:term]) =>
    `(Fin.fcons (F := $F) (α := $α 0) (β := fun i => $α (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α (Fin.succ i)⟩[])
  | `(!h⦃$F⦄⟨$α:term⟩[]) => `((Fin.dempty : (i : Fin 0) → $F ($α i)))

macro_rules
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[$x:term, $xs:term,*]) =>
    `(Fin.fcons₂ (F := $F)
        (α₁ := $α₁ 0) (β₁ := fun i => $α₁ (Fin.succ i))
        (α₂ := $α₂ 0) (β₂ := fun i => $α₂ (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α₁ (Fin.succ i)⟩⟨fun i => $α₂ (Fin.succ i)⟩[$xs,*])
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[$x:term]) =>
    `(Fin.fcons₂ (F := $F)
        (α₁ := $α₁ 0) (β₁ := fun i => $α₁ (Fin.succ i))
        (α₂ := $α₂ 0) (β₂ := fun i => $α₂ (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α₁ (Fin.succ i)⟩⟨fun i => $α₂ (Fin.succ i)⟩[])
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[]) =>
    `((Fin.dempty : (i : Fin 0) → $F ($α₁ i) ($α₂ i)))

@[app_unexpander Fin.fcons]
def fconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a !h⦃$F⦄⟨$α⟩[$b, $bs,*]) => `(!h⦃$F⦄⟨$α⟩[$a, $b, $bs,*])
  | `($_ $a !h⦃$F⦄⟨$α⟩[$b]) => `(!h⦃$F⦄⟨$α⟩[$a, $b])
  | `($_ $a !h⦃$F⦄⟨$α⟩[]) => `(!h⦃$F⦄⟨$α⟩[$a])
  | _ => throw ()

@[app_unexpander Fin.fcons₂]
def fcons₂Unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a !h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$b, $bs,*]) => `(!h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$a, $b, $bs,*])
  | `($_ $a !h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$b]) => `(!h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$a, $b])
  | `($_ $a !h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[]) => `(!h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$a])
  | _ => throw ()

macro_rules
  | `(!h⦃$F⦄[$term:term, $terms:term,*]) => `(Fin.fcons (F := $F) $term !h⦃$F⦄[$terms,*])
  | `(!h⦃$F⦄[$term:term]) => `(Fin.fcons (F := $F) $term !h⦃$F⦄[])
  | `(!h⦃$F⦄[]) => `((Fin.dempty : (i : Fin 0) → $F (_ i)))

macro_rules
  | `(!d[$term:term, $terms:term,*]) => `(Fin.dcons $term !d[$terms,*])
  | `(!d[$term:term]) => `(Fin.dcons $term !d[])
  | `(!d[]) => `(Fin.dempty)

macro_rules
  | `(!d⟨$motive⟩[$term:term, $terms:term,*]) =>
      `((Fin.dcons (motive := $motive) $term !d⟨fun i => $motive (Fin.succ i)⟩[$terms,*]))
  | `(!d⟨$motive⟩[$term:term]) => `((Fin.dcons (motive := $motive) $term !d[]))
  | `(!d⟨$motive⟩[]) => `((Fin.dempty : (i : Fin 0) → $motive i))

macro_rules
  | `($a:term ::ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dcons (motive := $motive) $a $b)

macro_rules
  | `($a:term :+ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dconcat (motive := $motive) $a $b)

macro_rules
  | `($a:term ::ʰ⟨$α:term ; $β:term⟩ $b:term) => `(Fin.hcons (α := $α) (β := $β) $a $b)

macro_rules
  | `($a:term ::ʰ⦃$F:term⦄ $b:term) => `(Fin.fcons (F := $F) $a $b)
  | `($a:term ::ʰ⦃$F:term⦄⟨$α:term ; $β:term⟩ $b:term) =>
    `(Fin.fcons (F := $F) (α := $α) (β := $β) $a $b)
  | `($a:term ::ʰ⦃$F:term⦄⟨$α₁:term ; $β₁:term⟩⟨$α₂:term ; $β₂:term⟩ $b:term) =>
    `(Fin.fcons₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $a $b)

macro_rules
  | `($a:term :+ʰ⟨$α:term ; $β:term⟩ $b:term) => `(Fin.hconcat (α := $α) (β := $β) $a $b)

/-! Functorial concat infix forms to match documentation -/
syntax:65 term:66 " :+ʰ⦃" term "⦄ " term:65 : term
syntax:65 term:66 " :+ʰ⦃" term "⦄⟨" term " ; " term "⟩ " term:65 : term
syntax:65 term:66 " :+ʰ⦃" term "⦄⟨" term " ; " term "⟩⟨" term " ; " term "⟩ " term:65 : term

macro_rules
  | `($u:term :+ʰ⦃$F:term⦄ $a:term) => `(Fin.fconcat (F := $F) $u $a)
  | `($u:term :+ʰ⦃$F:term⦄⟨$α:term ; $β:term⟩ $a:term) =>
    `(Fin.fconcat (F := $F) (α := $α) (β := $β) $u $a)
  | `($u:term :+ʰ⦃$F:term⦄⟨$α₁:term ; $β₁:term⟩⟨$α₂:term ; $β₂:term⟩ $a:term) =>
    `(Fin.fconcat₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $u $a)

/-- Unexpander for the `!h[x, y, ...]` notation using hcons. -/
@[app_unexpander Fin.hcons]
def hconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !h[$term2, $terms,*]) => `(!h[$term, $term2, $terms,*])
  | `($_ $term !h[$term2]) => `(!h[$term, $term2])
  | `($_ $term !h[]) => `(!h[$term])
  | _ => throw ()

/-- Unexpander for the `!h[]` and `!d[]` notation. -/
@[app_unexpander Fin.dempty]
def demptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!h[])
  | _ => throw ()

/-- Unexpander for the `!d[x, y, ...]` notation using dcons with explicit motive. -/
@[app_unexpander Fin.dcons]
def dconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !d[$term2, $terms,*]) => `(!d[$term, $term2, $terms,*])
  | `($_ $term !d[$term2]) => `(!d[$term, $term2])
  | `($_ $term !d[]) => `(!d[$term])
  | _ => throw ()

end Fin

-- Custom append notation with type ascriptions

/-- Homogeneous vector append notation `++ᵛ` -/
infixl:65 " ++ᵛ " => Fin.vappend

/-- Dependent append notation `++ᵈ` -/
infixl:65 " ++ᵈ " => Fin.dappend

/-- Heterogeneous append notation `++ʰ` -/
infixl:65 " ++ʰ " => Fin.happend

/-- Heterogeneous append with explicit type ascriptions: `++ʰ⟨α ; β⟩` -/
syntax:65 term:66 " ++ʰ⟨" term " ; " term "⟩ " term:65 : term

/-- Dependent append with explicit motive: `++ᵈ⟨motive⟩` -/
syntax:65 term:66 " ++ᵈ⟨" term "⟩ " term:65 : term

/-- Functorial heterogeneous append with explicit functor but inferred types: `++ʰ⦃F⦄`. -/
syntax:65 term:66 " ++ʰ⦃" term "⦄ " term:65 : term

/-- Functorial heterogeneous append with unary functor: `++ʰ⦃F⦄⟨α ; β⟩` -/
syntax:65 term:66 " ++ʰ⦃" term "⦄⟨" term " ; " term "⟩ " term:65 : term

/-- Functorial heterogeneous append with binary functor: `++ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩` -/
syntax:65 term:66 " ++ʰ⦃" term "⦄⟨" term " ; " term "⟩⟨" term " ; " term "⟩ " term:65 : term

macro_rules
  | `($a:term ++ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dappend (motive := $motive) $a $b)

macro_rules
  | `($a:term ++ʰ⟨$α:term ; $β:term⟩ $b:term) =>
  `(Fin.happend (α := fun i => $α) (β := fun i => $β) $a $b)

macro_rules
  | `($a:term ++ʰ⦃$F:term⦄ $b:term) => `(Fin.fappend (F := $F) $a $b)

macro_rules
  | `($a:term ++ʰ⦃$F:term⦄⟨$α:term ; $β:term⟩ $b:term) =>
    `(Fin.fappend (F := $F) (α := $α) (β := $β) $a $b)

macro_rules
  | `($a:term ++ʰ⦃$F:term⦄⟨$α₁:term ; $β₁:term⟩⟨$α₂:term ; $β₂:term⟩ $b:term) =>
    `(Fin.fappend₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $a $b)

-- End of core notation definitions

section Examples

-- Basic homogeneous vectors work fine
example : !v[1, 2, 3] = Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)) := rfl

-- Homogeneous vectors with type ascription
example : !v⟨ℕ⟩[1, 2, 3] = (!v[1, 2, 3] : Fin 3 → ℕ) := rfl

-- Heterogeneous tuples with type vector ascription (commented out due to type inference issues)
-- example : !h⟨!v[ℕ, Bool, String]⟩[(1 : ℕ), true, "hello"] =
--   !h[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Dependent tuples with explicit motive work
def Mymotive : Fin 3 → Type := !v[ℕ, Bool, String]

example : !d⟨Mymotive⟩[(1 : ℕ), (true : Bool), ("hello" : String)] =
  (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) (Fin.dcons ("hello" : String) Fin.dempty)) :
   (i : Fin 3) → Mymotive i) := rfl

-- Homogeneous vector operations work
example : !v[1, 2] ++ᵛ !v[3, 4] = !v[1, 2, 3, 4] := rfl
example : (0 : ℕ) ::ᵛ !v[1, 2] = !v[0, 1, 2] := rfl
example : !v[1, 2] :+ᵛ (3 : ℕ) = !v[1, 2, 3] := rfl

-- Basic heterogeneous operations (require explicit type annotations)
example : (1 : ℕ) ::ʰ (Fin.dempty : (i : Fin 0) → Fin.vempty i) =
  (!h[(1 : ℕ)] : (i : Fin 1) → !v[ℕ] i) := rfl

-- Basic heterogeneous tuple without type specification - now using !h[]
example : !h[(1 : ℕ), (true : Bool), ("hello" : String)] =
  Fin.hcons 1 (Fin.hcons true ("hello" ::ʰ⟨String ; !v[]⟩ !h[])) := rfl

-- With explicit type vector using predefined type
def MyTypeVec : Fin 3 → Type := !v[ℕ, Bool, String]

example : !d⟨MyTypeVec⟩[(1 : ℕ), true, "hello"] =
  (!h[1, true, "hello"] : (i : Fin 3) → MyTypeVec i) := rfl

-- Empty tuple with type specification
example : !d⟨!v[]⟩[] = (Fin.dempty : (i : Fin 0) → !v[] i) := rfl

-- Basic dependent tuple construction (commented due to type inference issues)
example : !d⟨ !v[ℕ, Bool, String] ⟩[(1 : ℕ), (true : Bool), ("hello" : String)] =
  Fin.dcons (1 : ℕ) (Fin.dcons true (Fin.dcons "hello" Fin.dempty)) := rfl

-- The dependent notation is most useful with explicit motive specification
example : let motive : Fin 2 → Type := fun i => if i = 0 then ℕ else Bool
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] =
          (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty) : (i : Fin 2) → motive i) := rfl

-- Test FinVec.cons (::ᵛ) notation
section FinVecConsTests

-- Basic cons operation
example : 1 ::ᵛ !v[2, 3] = !v[1, 2, 3] := rfl

-- Chaining cons operations (right associative)
example : 1 ::ᵛ 2 ::ᵛ 3 ::ᵛ Fin.vempty = !v[1, 2, 3] := rfl

-- Mixing cons and bracket notation
example : 0 ::ᵛ !v[1, 2] = !v[0, 1, 2] := rfl

-- Type inference works
example : let v : Fin 2 → ℕ := !v[1, 2]
          0 ::ᵛ v = !v[0, 1, 2] := rfl

-- Empty vector
example : 42 ::ᵛ Fin.vempty = !v[42] := rfl

end FinVecConsTests

-- Test FinVec.concat (:+ᵛ) notation
section FinVecConcatTests

-- Basic concat operation
example : !v[1, 2] :+ᵛ 3 = !v[1, 2, 3] := rfl

-- Chaining concat operations (left associative)
example : !v[1] :+ᵛ 2 :+ᵛ 3 = !v[1, 2, 3] := rfl

-- Mixing concat and bracket notation
example : !v[1, 2] :+ᵛ 3 = !v[1, 2, 3] := rfl

-- Type inference works
example : let v : Fin 2 → ℕ := !v[1, 2]
          v :+ᵛ 3 = !v[1, 2, 3] := rfl

-- Empty vector
example : Fin.vempty :+ᵛ 42 = !v[42] := rfl

-- Symmetric operations: cons vs concat
example : 0 ::ᵛ !v[1, 2] = !v[0, 1, 2] ∧ !v[1, 2] :+ᵛ 3 = !v[1, 2, 3] := ⟨rfl, rfl⟩

end FinVecConcatTests

-- Test FinTuple.cons (::ʰ) notation
section FinTupleConsTests

-- Basic heterogeneous cons
example : (1 : ℕ) ::ʰ ((true : Bool) ::ʰ⟨Bool ; !v[]⟩ !h[]) = !h[(1 : ℕ), (true : Bool)] := rfl

-- Chaining different types (right associative)
example : (1 : ℕ) ::ʰ (true : Bool) ::ʰ ("hello" : String) ::ʰ⟨_ ; !v[]⟩ !h[] =
          !h[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Mixing cons and bracket notation
example : (0 : ℕ) ::ʰ⟨ℕ ; !v[ℕ, Bool]⟩ !h[(1 : ℕ), (true : Bool)] =
          !h[(0 : ℕ), (1 : ℕ), (true : Bool)] := rfl

-- With explicit type annotation
example : (42 : ℕ) ::ʰ⟨ℕ ; !v[]⟩ !h[] =
          !h[(42 : ℕ)] := rfl

-- Complex nested example
example : let t1 : (i : Fin 2) → !v[Bool, String] i := !h[(true : Bool), ("test" : String)]
          let result := (1 : ℕ) ::ʰ t1
          result = !h[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

end FinTupleConsTests

-- Test FinTuple.concat (:+ʰ) notation
section FinTupleConcatTests

-- Basic heterogeneous concat
example : !h[(1 : ℕ), (true : Bool)] :+ʰ⟨ !v[ℕ, Bool] ; String⟩ ("hello" : String) =
          !h⟨ !v[ℕ, Bool, String] ⟩[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Chaining different types (left associative)
-- example : !h[(1 : ℕ)] :+ʰ⟨ _ ; _⟩ (true ) :+ʰ⟨ !v[Bool] ; _⟩ ("hello" : String) =
--           !h[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Mixing concat and bracket notation
example : !h[(1 : ℕ), (true : Bool)] :+ʰ⟨ !v[ℕ, Bool] ; String⟩ ("test" : String) =
          !h⟨!v[ℕ, Bool, String]⟩[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

-- With explicit type annotation
example : (Fin.dempty : (i : Fin 0) → Fin.vempty i) :+ʰ (42 : ℕ) =
          !h⟨!v[ℕ]⟩[(42 : ℕ)] := rfl

-- Symmetric operations: cons vs concat
example : (0 : ℕ) ::ʰ !h⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)] =
          !h⟨!v[ℕ, ℕ, Bool]⟩[(0 : ℕ), (1 : ℕ), (true : Bool)] ∧
          !h⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)] :+ʰ ("end" : String) =
          !h⟨!v[ℕ, Bool, String]⟩[(1 : ℕ), (true : Bool), ("end" : String)] := ⟨rfl, rfl⟩

end FinTupleConcatTests

-- Test dependent cons (::ᵈ) notation
section FinDependentConsTests

/- Note: The dependent cons notation ::ᵈ requires explicit typing in most cases.
   These examples show the intended usage but are commented due to type inference issues. -/

-- Working example with explicit motive annotation
example : let motive : Fin 1 → Type := fun _ => ℕ
          (42 : ℕ) ::ᵈ Fin.dempty = !d⟨motive⟩[(42 : ℕ)] := rfl

-- Test explicit motive cons notation (::ᵈ⟨⟩)
example : let motive := !v[ℕ, Bool]
          (1 : ℕ) ::ᵈ⟨motive⟩ ((true : Bool) ::ᵈ Fin.dempty) =
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

-- Simple case with explicit motive annotation
example : let motive : Fin 1 → Type := fun _ => ℕ
          (42 : ℕ) ::ᵈ⟨motive⟩ Fin.dempty = !d⟨motive⟩[(42 : ℕ)] := rfl

end FinDependentConsTests

-- Test dependent concat (:+ᵈ) notation
section FinDependentConcatTests

/- Note: The dependent concat notation :+ᵈ requires explicit typing in most cases.
   These examples show the intended usage with explicit motive annotation. -/

-- Simple case with explicit type annotation
example : (Fin.dempty : (i : Fin 0) → ℕ) :+ᵈ (42 : ℕ) =
          (!d[(42 : ℕ)] : (i : Fin 1) → ℕ) := rfl

-- Working example with compatible types
example : (!d[(1 : ℕ)] : (i : Fin 1) → ℕ) :+ᵈ (2 : ℕ) =
          (!d[(1 : ℕ), (2 : ℕ)] : (i : Fin 2) → ℕ) := rfl

-- Test explicit motive concat notation works with rfl
example : let motive := !v[ℕ, Bool]
          !d⟨motive ∘ Fin.castSucc⟩[(1 : ℕ)] :+ᵈ⟨motive⟩ (true : Bool) =
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

end FinDependentConcatTests

-- Test interaction between all notations
section MixedTests

-- FinVec used as type vector for FinTuple
example : let _typeVec := ℕ ::ᵛ Bool ::ᵛ !v[]
          !d⟨_typeVec⟩[(1 : ℕ), true] = !d[(1 : ℕ), (true : Bool)] := rfl

-- Building complex structures step by step
example : let _types := ℕ ::ᵛ Bool ::ᵛ !v[]
          let values := 1 ::ʰ true ::ʰ !d[]
          values = (!d⟨_types⟩[(1 : ℕ), true] : (i : Fin 2) → _types i) := rfl

-- FinVec used as motive for dependent tuples (commented due to type inference)
-- example : let motive := ℕ ::ᵛ Bool ::ᵛ !v[]
--           !d⟨motive⟩[1, true] = !d[(1 : ℕ), (true : Bool)] := rfl

-- Comparing different notations for the same structure
example : let motive := !v[ℕ, Bool, String]
          (!d⟨motive⟩[(1 : ℕ), true, "hello"] : (i : Fin 3) → motive i) =
          (!d[(1 : ℕ), (true : Bool), ("hello" : String)] : (i : Fin 3) → motive i) := rfl

end MixedTests

example : !v[1, 2] ++ᵛ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Append with empty vectors
example : !v[1, 2] ++ᵛ (!v[] : Fin 0 → ℕ) = !v[1, 2] := rfl
example : (!v[] : Fin 0 → ℕ) ++ᵛ !v[1, 2] = !v[1, 2] := rfl

-- Chaining appends (left associative)
example : !v[1] ++ᵛ !v[2] ++ᵛ !v[3] = !v[1, 2, 3] := rfl

-- Mixed with cons notation
example : (1 ::ᵛ !v[2]) ++ᵛ (3 ::ᵛ !v[4]) = !v[1, 2, 3, 4] := rfl

-- Different types
example : !v[true, false] ++ᵛ !v[true] = !v[true, false, true] := rfl

-- end FinVecAppendTests

-- Test FinTuple.append (heterogeneous ++ᵈ)
-- section FinTupleAppendTests

-- Basic heterogeneous append
example : !d[(1 : ℕ)] ++ᵈ⟨!v[ℕ, Bool]⟩ !d[true] = !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), true] := rfl

-- More complex heterogeneous append
example : !d[(1 : ℕ), (true : Bool)] ++ᵈ⟨!v[ℕ, Bool] ++ᵛ !v[String, Float]⟩
            !d[("hello" : String), (3.14 : Float)] =
          !d[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] := rfl

-- -- Append with empty tuple
-- example : Fin.dappend (motive := !v[ℕ, Bool]) !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)] !d[] =
--           !d[(1 : ℕ), (true : Bool)] := rfl

-- example : !d[] ++ᵈ⟨!v[ℕ, Bool]⟩ !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)] =
--           !d[(1 : ℕ), (true : Bool)] := rfl

-- -- Chaining heterogeneous appends
-- example : !d[(1 : ℕ)] ++ᵈ⟨!v[ℕ, Bool, String]⟩ !d[(true : Bool)] ++ᵈ⟨!v[ℕ, Bool, String]⟩
--           !d[("test" : String)] =
--           !d[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

-- -- Mixed with cons notation - simple case works
-- example : !d[(1 : ℕ)] ++ᵈ⟨!v[ℕ, Bool]⟩ !d[(true : Bool)] =
--           !d[(1 : ℕ), (true : Bool)] := rfl

-- -- Combining different tuple constructions
-- example : !d[(1 : ℕ), (2 : ℕ)] ++ᵈ⟨!v[ℕ, ℕ, Bool, String]⟩
--           !d[(true : Bool), ("hello" : String)] =
--           !d[(1 : ℕ), (2 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Note: More complex append examples may require explicit type annotations
-- due to type inference limitations with heterogeneous tuples

-- Complex nested example with multiple operations
-- example : let base := !d[(0 : ℕ)]
--           let middle := (true : Bool) ::ʰ !d[]
--           let final := !d[("final" : String)]
--           (base ++ᵈ middle) ++ᵈ final = !d[(0 : ℕ), (true : Bool), ("final" : String)] := rfl

-- end FinTupleAppendTests

-- Basic dependent append using explicit dappend
example : let motive := !v[ℕ, Bool]
          let d1 : (i : Fin 1) → motive (Fin.castAdd 1 i) := !d[(1 : ℕ)]
          let d2 : (i : Fin 1) → motive (Fin.natAdd 1 i) := !d[(true : Bool)]
          Fin.dappend d1 d2 = !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

-- More complex dependent append
example : let motive : Fin 4 → Type := !v[ℕ, Bool, String, Float]
          let d1 : (i : Fin 2) → motive (Fin.castAdd 2 i) := !d[(1 : ℕ), (true : Bool)]
          let d2 : (i : Fin 2) → motive (Fin.natAdd 2 i) := !d[("hello" : String), (3.14 : Float)]
          Fin.dappend (n := 2) d1 d2 =
            !d⟨motive⟩[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] := rfl

-- Append with empty dependent tuple
example : let motive := !v[ℕ, Bool]
          let d1 : (i : Fin 2) → motive (Fin.castAdd 0 i) := !d[(1 : ℕ), (true : Bool)]
          let d2 : (i : Fin 0) → motive (Fin.natAdd 2 i) := !d[]
          Fin.dappend (n := 0) d1 d2 = !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

-- end FinDependentAppendTests

-- Test interaction between all append types
-- section MixedAppendTests

-- Using FinVec append to build type vectors for FinTuple
-- example : let types1 : Fin 2 → Type := !v[ℕ, Bool]
--           let types2 : Fin 2 → Type := !v[String, Float]
--   let combined_types : Fin 4 → Type := types1 ++ᵛ types2
--           let t1 : (i : Fin 2) → types1 i := !d⟨types1⟩[(1 : ℕ), (true : Bool)]
--           let t2 : (i : Fin 2) → types2 i := !d⟨types2⟩[("hello" : String), (3.14 : Float)]
--   let result : (i : Fin 4) → combined_types i := t1 ++ᵈ⟨!v[ℕ, Bool] ++ᵛ !v[String, Float]⟩ t2
--   result =
--     (let rhs : (i : Fin 4) → combined_types i :=
--        !d[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)]
--      rhs) := by
--     ext i; fin_cases i <;> rfl

-- Using FinVec append to build motives for dependent tuples
example : let motive1 : Fin 2 → Type := !v[ℕ, Bool]
          let motive2 : Fin 2 → Type := !v[String, Float]
  let combined_motive : Fin 4 → Type := motive1 ++ᵛ motive2
          let d1 : (i : Fin 2) → combined_motive (Fin.castAdd 2 i) := !d[(1 : ℕ), (true : Bool)]
          let d2 : (i : Fin 2) → combined_motive (Fin.natAdd 2 i) :=
            !d[("hello" : String), (3.14 : Float)]
  Fin.dappend (n := 2) d1 d2 =
    (let rhs : (i : Fin 4) → combined_motive i :=
       !d[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)]
     rhs) := by
    ext i; fin_cases i <;> rfl

-- Append with different constructions
example : (!v[1, 2] ++ᵛ !v[3]) = !v[1, 2, 3] ∧
          (!d[(1 : ℕ)] ++ᵈ !d[(true : Bool)] = !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)]) ∧
          (let motive := !v[ℕ, Bool]
           let d1 : (i : Fin 1) → motive (Fin.castAdd 1 i) := !d[(1 : ℕ)]
           let d2 : (i : Fin 1) → motive (Fin.natAdd 1 i) := !d[(true : Bool)]
           Fin.dappend (n := 1) d1 d2 = !d⟨motive⟩[(1 : ℕ), (true : Bool)]) :=
          ⟨rfl, rfl, rfl⟩

-- Test the new notation
section NewNotationTests

-- These should work with rfl!
example : 1 ::ᵛ !v[2] = !v[1, 2] := rfl

example : Fin.tail !v[1, 2, 3] = !v[2, 3] := rfl

example : Fin.vconcat !v[1, 2] 3 = !v[1, 2, 3] := rfl

example : !v[1, 2] ++ᵛ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Test dependent notation with rfl
example : 1 ::ᵈ !d[2] = !d⟨fun _ => ℕ⟩[1, 2] := rfl

example : (1 : ℕ) ::ᵈ (true : Bool) ::ᵈ !d[] = !d⟨ !v[ℕ, Bool] ⟩[(1 : ℕ), (true : Bool)] := rfl

-- Test new explicit motive notation works with rfl
example : let motive := !v[ℕ]
          (1 : ℕ) ::ᵈ⟨motive⟩ Fin.dempty = !d⟨motive⟩[(1 : ℕ)] := rfl

-- Test explicit motive concat notation
example : let motive := !v[ℕ, Bool]
          !d⟨motive ∘ Fin.castSucc⟩[(1 : ℕ)] :+ᵈ⟨motive⟩ (true : Bool) =
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

example : !v[(true, Nat)] ++ᵛ
  ((!v[] : Fin 0 → Bool × Type) ++ᵛ
    (!v[(false, Int)] ++ᵛ (!v[] : Fin 0 → Bool × Type))) =
      !v[(true, Nat), (false, Int)] := rfl

example : !v[(true, Nat)] ++ᵛ !v[(false, Int)] ++ᵛ !v[(false, Int)] =
  !v[(true, Nat), (false, Int), (false, Int)] := rfl

-- Test that roundtrip works with pure rfl
example : Fin.take 2 (by omega) !v[1, 2, 3, 4] ++ᵛ
  Fin.drop 2 (by omega) !v[1, 2, 3, 4] = !v[1, 2, 3, 4] := rfl

-- Complex expression that should compute cleanly
example : Fin.tail (1 ::ᵛ 2 ::ᵛ 3 ::ᵛ !v[] ++ᵛ 4 ::ᵛ !v[]) = !v[2, 3, 4] := rfl

-- Even more complex combinations work with rfl
example : Fin.init (Fin.vconcat !v[Nat, Int] Bool) = !v[Nat, Int] := by
  dsimp [Fin.init, Fin.vconcat, Fin.vcons, Fin.vcons]
  ext i; fin_cases i <;> rfl

example : Fin.vconcat (Fin.init !v[Nat, Int, Unit]) Bool = !v[Nat, Int, Bool] := by rfl

example {v : Fin 3 → ℕ} : Fin.vconcat (Fin.init v) (v (Fin.last 2)) = v := by
  ext i; fin_cases i <;> rfl

-- Multiple operations compose cleanly
example : Fin.tail (0 ::ᵛ (!v[1, 2] ++ᵛ !v[3, 4])) = !v[1, 2, 3, 4] := rfl

/-- Test that our new notation gives the same result as the old one (extensionally) -/
example : !v[1, 2, 3] = ![1, 2, 3] := by ext i; fin_cases i <;> rfl

-- Test that concat notation works with rfl
example : !v[1, 2] :+ᵛ 3 = !v[1, 2, 3] := rfl

-- Test interaction between cons, concat, and append
example : (0 ::ᵛ !v[1]) :+ᵛ 2 ++ᵛ !v[3, 4] = !v[0, 1, 2, 3, 4] := rfl

-- Test tuple concat notation works with rfl
example : !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)] :+ʰ ("hello" : String) =
          !d[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Comprehensive test of all concat operations
example : (!v[1, 2] :+ᵛ 3 = !v[1, 2, 3]) ∧
          (!d⟨!v[ℕ]⟩[(1 : ℕ)] :+ʰ (true : Bool) = !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)]) ∧
          (!d[(1 : ℕ)]  :+ʰ⟨!v[ℕ] ; ℕ⟩ (2 : ℕ) = !d⟨!v[ℕ, ℕ]⟩[(1 : ℕ), (2 : ℕ)]) :=
          ⟨rfl, rfl, rfl⟩

-- Test dependent vector functions for definitional equality
section DependentVectorTests

-- Test that the ++ᵈ notation is properly defined
example : !d[(42 : ℕ)] ++ᵈ⟨ !v[ℕ, Bool] ⟩ !d[(true : Bool)] = !d[(42 : ℕ), (true : Bool)] := rfl

-- Test that type vectors compute correctly
example : (ℕ ::ᵛ !v[Bool]) 0 = ℕ := rfl

example : (ℕ ::ᵛ !v[Bool]) 1 = Bool := rfl

-- -- Test FinVec.append on types
example : (!v[ℕ] ++ᵛ !v[Bool]) 0 = ℕ := rfl

example : (!v[ℕ] ++ᵛ !v[Bool]) 1 = Bool := rfl

-- Test FinVec.concat on types
example : Fin.vconcat !v[ℕ] Bool 0 = ℕ := rfl

example : Fin.vconcat !v[ℕ] Bool 1 = Bool := rfl

-- Test that regular vector functions work with the !v[] notation
example : 1 ::ᵛ !v[2, 3] = !v[1, 2, 3] := rfl

example : Fin.vconcat !v[1, 2] 3 = !v[1, 2, 3] := rfl

example : !v[1, 2] ++ᵛ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Test that the dependent versions provide good definitional equality
example : ℕ ::ᵛ (Bool ::ᵛ (fun _ : Fin 0 => Empty)) =
    fun i : Fin 2 => if i = 0 then ℕ else Bool := by
  ext i; fin_cases i <;> rfl

end DependentVectorTests

end NewNotationTests

end Examples
