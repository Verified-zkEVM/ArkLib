/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.HDAppend
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
## Custom Vector Notation with Better Definitional Equality

We create a new vector notation `!v[a, b, c]` that uses our custom functions with better
definitional equality. This is similar to Mathlib's `Matrix.vecCons` and `Matrix.vecEmpty`
used in `![]` notation, but uses our custom `vecCons` which provides better definitional
equality through pattern matching instead of `cases`.
-/

namespace Fin

-- Infix notation for cons operations, similar to Vector.cons
@[inherit_doc]
infixr:67 " ::ᵛ " => Fin.vcons

-- Infix notation for concat operations, following Scala convention
@[inherit_doc]
infixl:65 " :+ᵛ " => Fin.vconcat

/-- `!v[...]` notation constructs a vector using our custom functions.
Uses `!v[...]` to distinguish from standard `![]`. -/
syntax (name := finVecNotation) "!v[" term,* "]" : term

macro_rules
  | `(!v[$term:term, $terms:term,*]) => `(Fin.vcons $term !v[$terms,*])
  | `(!v[$term:term]) => `(Fin.vcons $term !v[])
  | `(!v[]) => `(Fin.vempty)

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
infixr:67 " ::ᵗ " => Fin.tcons

@[inherit_doc]
infixl:65 " :+ᵗ " => Fin.tconcat

@[inherit_doc]
infixr:67 " ::ᵈ " => Fin.dcons

@[inherit_doc]
infixl:65 " :+ᵈ " => Fin.dconcat

/-- `::ᵈ⟨Motive⟩` notation for dcons with explicit motive specification -/
syntax:67 term:68 " ::ᵈ⟨" term "⟩ " term:67 : term

/-- `:+ᵈ⟨Motive⟩` notation for dconcat with explicit motive specification -/
syntax:65 term:66 " :+ᵈ⟨" term "⟩ " term:65 : term

/-- `!t[...]` notation constructs a tuple (heterogeneous vector) using our custom functions.
Uses `!t[...]` to distinguish from standard `![]`. -/
syntax (name := finTupleNotation) "!t[" term,* "]" : term

/-- `!t⟨TypeVec⟩[...]` notation constructs a tuple with explicit type vector specification.
Uses angle brackets to specify the type vector, then square brackets for values. -/
syntax (name := finTupleNotationWithTypes) "!t⟨" term "⟩[" term,* "]" : term

/-- `!d[...]` notation constructs a dependent tuple using our custom dependent functions.
Uses `!d[...]` to distinguish from `!t[]` notation. -/
syntax (name := finDependentNotation) "!d[" term,* "]" : term

/-- `!d⟨Motive⟩[...]` notation constructs a dependent tuple with explicit motive specification.
Uses angle brackets to specify the motive, then square brackets for values. -/
syntax (name := finDependentNotationWithMotive) "!d⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!t[$term:term, $terms:term,*]) => `(Fin.tcons $term !t[$terms,*])
  | `(!t[$term:term]) => `(Fin.tcons $term !t[])
  | `(!t[]) => `(@Fin.tempty (Fin.vempty))

macro_rules
  | `(!t⟨$typeVec⟩[$term:term, $terms:term,*]) =>
      `((!t[$term, $terms,*] : (i : Fin _) → $typeVec i))
  | `(!t⟨$typeVec⟩[$term:term]) => `((!t[$term] : (i : Fin _) → $typeVec i))
  | `(!t⟨$typeVec⟩[]) => `((Fin.tempty : (i : Fin 0) → $typeVec i))

macro_rules
  | `(!d[$term:term, $terms:term,*]) => `(Fin.dcons $term !d[$terms,*])
  | `(!d[$term:term]) => `(Fin.dcons $term !d[])
  | `(!d[]) => `(Fin.dempty)

macro_rules
  | `(!d⟨$motive⟩[$term:term, $terms:term,*]) =>
      `((Fin.dcons (motive := $motive) $term !d[$terms,*]))
  | `(!d⟨$motive⟩[$term:term]) => `((Fin.dcons (motive := $motive) $term !d[]))
  | `(!d⟨$motive⟩[]) => `((Fin.dempty : (i : Fin 0) → $motive i))

macro_rules
  | `($a:term ::ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dcons (motive := $motive) $a $b)

macro_rules
  | `($a:term :+ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dconcat (motive := $motive) $a $b)

/-- Unexpander for the `!t[x, y, ...]` notation. -/
@[app_unexpander Fin.tcons]
def tconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !t[$term2, $terms,*]) => `(!t[$term, $term2, $terms,*])
  | `($_ $term !t[$term2]) => `(!t[$term, $term2])
  | `($_ $term !t[]) => `(!t[$term])
  | _ => throw ()

/-- Unexpander for the `!t[]` notation. -/
@[app_unexpander Fin.tempty]
def temptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!t[])
  | _ => throw ()

/-- Unexpander for the `!d[x, y, ...]` notation. -/
@[app_unexpander Fin.dcons]
def dconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !d[$term2, $terms,*]) => `(!d[$term, $term2, $terms,*])
  | `($_ $term !d[$term2]) => `(!d[$term, $term2])
  | `($_ $term !d[]) => `(!d[$term])
  | _ => throw ()

end Fin

/-- `++` instance for Fin homogeneous vectors `vappend` -/
instance {α : Type*} {m n : ℕ} : HAppend (Fin m → α) (Fin n → α) (Fin (m + n) → α) where
  hAppend := Fin.vappend

/-- `++ᵈ` instance for Fin heterogeneous vectors `tappend` -/
instance {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u} :
    HDAppend ((i : Fin m) → α i) ((i : Fin n) → β i) ((i : Fin (m + n)) → Fin.vappend α β i) where
  hDAppend := Fin.tappend

/-- `++ᵈ` instance for dependent tuples with unified motive using `dappend` -/
instance {m n : ℕ} {motive : Fin (m + n) → Sort u} :
    HDAppend ((i : Fin m) → motive (Fin.castAdd n i)) ((i : Fin n) → motive (Fin.natAdd m i))
             ((i : Fin (m + n)) → motive i) where
  hDAppend := Fin.dappend

-- Test examples for the new tuple notations
section TupleNotationTests

-- Basic heterogeneous tuple without type specification
example : !t[(1 : ℕ), (true : Bool), ("hello" : String)] =
  Fin.tcons 1 (Fin.tcons true (Fin.tcons "hello" Fin.tempty)) := rfl

-- With explicit type vector using predefined type
def MyTypeVec : Fin 3 → Type := !v[ℕ, Bool, String]

example : !t⟨MyTypeVec⟩[1, true, "hello"] =
  (!t[1, true, "hello"] : (i : Fin 3) → MyTypeVec i) := rfl

-- With explicit type vector using !v[] notation
example : !t⟨ !v[ℕ, Bool, String] ⟩[1, true, "hello"] =
  (!t[1, true, "hello"] : (i : Fin 3) → !v[ℕ, Bool, String] i) := rfl

example : !t⟨ !v[ℕ, Bool, String] ⟩[1, true, "hello"] =
  !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Empty tuple with type specification
example : !t⟨!v[]⟩[] = (Fin.tempty : (i : Fin 0) → !v[] i) := rfl

end TupleNotationTests

-- Test examples for the new dependent notation
section DependentNotationTests

/- Note: The dependent notation !d[] requires explicit typing in most cases
   because Lean cannot automatically infer the motive. The examples below
   show the intended usage, but many require explicit type annotations. -/

-- Basic dependent tuple construction (commented due to type inference issues)
example : !d⟨ !v[ℕ, Bool, String] ⟩[(1 : ℕ), (true : Bool), ("hello" : String)] =
  Fin.dcons (1 : ℕ) (Fin.dcons true (Fin.dcons "hello" Fin.dempty)) := rfl

-- With explicit motive using predefined motive
def MyMotive : Fin 3 → Type := !v[ℕ, Bool, String]

example : !d⟨MyMotive⟩[(1 : ℕ), true, "hello"] =
  (!d[(1 : ℕ), true, "hello"] : (i : Fin 3) → MyMotive i) := rfl

-- Empty dependent tuple with motive specification
example : !d⟨!v[]⟩[] = (Fin.tempty : (i : Fin 0) → !v[] i) := rfl

-- The dependent notation is most useful with explicit motive specification
example : let motive : Fin 2 → Type := fun i => if i = 0 then ℕ else Bool
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] =
          (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.tempty) : (i : Fin 2) → motive i) := rfl

end DependentNotationTests

-- Test infix notation for cons operations
section InfixNotationTests

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

-- Test FinTuple.cons (::ᵗ) notation
section FinTupleConsTests

-- Basic heterogeneous cons
example : (1 : ℕ) ::ᵗ ((true : Bool) ::ᵗ Fin.tempty) =
          !t[(1 : ℕ), (true : Bool)] := rfl

-- Chaining different types (right associative)
example : (1 : ℕ) ::ᵗ (true : Bool) ::ᵗ ("hello" : String) ::ᵗ Fin.tempty =
          !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Mixing cons and bracket notation
example : (0 : ℕ) ::ᵗ !t[(1 : ℕ), (true : Bool)] =
          !t[(0 : ℕ), (1 : ℕ), (true : Bool)] := rfl

-- With explicit type annotation
example : (42 : ℕ) ::ᵗ (Fin.tempty : (i : Fin 0) → Fin.vempty i) =
          !t[(42 : ℕ)] := rfl

-- Complex nested example
example : let t1 : (i : Fin 2) → !v[Bool, String] i := !t[(true : Bool), ("test" : String)]
          let result := (1 : ℕ) ::ᵗ t1
          result = !t[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

end FinTupleConsTests

-- Test FinTuple.concat (:+ᵗ) notation
section FinTupleConcatTests

-- Basic heterogeneous concat
example : !t[(1 : ℕ), (true : Bool)] :+ᵗ ("hello" : String) =
          !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Chaining different types (left associative)
example : !t[(1 : ℕ)] :+ᵗ (true : Bool) :+ᵗ ("hello" : String) =
          !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Mixing concat and bracket notation
example : !t[(1 : ℕ), (true : Bool)] :+ᵗ ("test" : String) =
          !t[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

-- With explicit type annotation
example : (Fin.tempty : (i : Fin 0) → Fin.vempty i) :+ᵗ (42 : ℕ) =
          !t[(42 : ℕ)] := rfl

-- Symmetric operations: cons vs concat
example : (0 : ℕ) ::ᵗ !t[(1 : ℕ), (true : Bool)] =
          !t[(0 : ℕ), (1 : ℕ), (true : Bool)] ∧
          !t[(1 : ℕ), (true : Bool)] :+ᵗ ("end" : String) =
          !t[(1 : ℕ), (true : Bool), ("end" : String)] := ⟨rfl, rfl⟩

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
          (1 : ℕ) ::ᵈ⟨motive⟩ ((true : Bool) ::ᵈ Fin.tempty) =
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

-- Simple case with explicit motive annotation
example : let motive : Fin 1 → Type := fun _ => ℕ
          (42 : ℕ) ::ᵈ⟨motive⟩ Fin.tempty = !d⟨motive⟩[(42 : ℕ)] := rfl

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
example : let typeVec := ℕ ::ᵛ Bool ::ᵛ !v[]
          !t⟨typeVec⟩[1, true] = !t[(1 : ℕ), (true : Bool)] := rfl

-- Building complex structures step by step
example : let types := ℕ ::ᵛ Bool ::ᵛ !v[]
          let values := 1 ::ᵗ true ::ᵗ !t[]
          values = (!t⟨types⟩[1, true] : (i : Fin 2) → types i) := rfl

-- FinVec used as motive for dependent tuples (commented due to type inference)
-- example : let motive := ℕ ::ᵛ Bool ::ᵛ !v[]
--           !d⟨motive⟩[1, true] = !d[(1 : ℕ), (true : Bool)] := rfl

-- Comparing different notations for the same structure
example : let motive := !v[ℕ, Bool, String]
          (!t⟨motive⟩[1, true, "hello"] : (i : Fin 3) → motive i) =
          (!t[(1 : ℕ), (true : Bool), ("hello" : String)] : (i : Fin 3) → motive i) := rfl

end MixedTests

end InfixNotationTests

-- Test append operations (++ and ++ᵈ)
section AppendTests

-- Test FinVec.append (standard ++)
section FinVecAppendTests

-- Basic homogeneous append
example : !v[1, 2] ++ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Append with empty vectors
example : !v[1, 2] ++ (!v[] : Fin 0 → ℕ) = !v[1, 2] := rfl
example : (!v[] : Fin 0 → ℕ) ++ !v[1, 2] = !v[1, 2] := rfl

-- Chaining appends (left associative)
example : !v[1] ++ !v[2] ++ !v[3] = !v[1, 2, 3] := rfl

-- Mixed with cons notation
example : (1 ::ᵛ !v[2]) ++ (3 ::ᵛ !v[4]) = !v[1, 2, 3, 4] := rfl

-- Different types
example : !v[true, false] ++ !v[true] = !v[true, false, true] := rfl

end FinVecAppendTests

-- Test FinTuple.append (dependent ++ᵈ)
section FinTupleAppendTests

-- Basic heterogeneous append
example : !t[(1 : ℕ)] ++ᵈ !t[(true : Bool)] = !t[(1 : ℕ), (true : Bool)] := rfl

-- More complex heterogeneous append
example : !t[(1 : ℕ), (true : Bool)] ++ᵈ !t[("hello" : String), (3.14 : Float)] =
          !t[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] := rfl

-- Append with empty tuple
example : !t[(1 : ℕ), (true : Bool)] ++ᵈ !t[] =
          !t[(1 : ℕ), (true : Bool)] := rfl

example : !t[] ++ᵈ !t[(1 : ℕ), (true : Bool)] =
          !t[(1 : ℕ), (true : Bool)] := rfl

-- Chaining dependent appends
example : !t[(1 : ℕ)] ++ᵈ !t[(true : Bool)] ++ᵈ !t[("test" : String)] =
          !t[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

-- Mixed with cons notation - simple case works
example : !t[(1 : ℕ)] ++ᵈ !t[(true : Bool)] = !t[(1 : ℕ), (true : Bool)] := rfl

-- Combining different tuple constructions
example : !t[(1 : ℕ), (2 : ℕ)] ++ᵈ !t[(true : Bool), ("hello" : String)] =
          !t[(1 : ℕ), (2 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Note: More complex dependent append examples may require explicit type annotations
-- due to type inference limitations with heterogeneous tuples

-- Complex nested example with multiple operations
example : let base := !t[(0 : ℕ)]
          let middle := (true : Bool) ::ᵗ !t[]
          let final := !t[("final" : String)]
          (base ++ᵈ middle) ++ᵈ final = !t[(0 : ℕ), (true : Bool), ("final" : String)] := rfl

end FinTupleAppendTests

-- Test dependent append (using dappend with ++ᵈᵈ)
section FinDependentAppendTests

-- Note: These tests would use the ++ᵈᵈ instance, but since it requires
-- a specific motive structure, we'll show the underlying dappend usage

-- Basic dependent append using explicit dappend
example : let d1 : (i : Fin 1) → (!v[ℕ] ++ !v[Bool]) (Fin.castAdd 1 i) := !d[(1 : ℕ)]
          let d2 : (i : Fin 1) → (!v[ℕ] ++ !v[Bool]) (Fin.natAdd 1 i) := !d[(true : Bool)]
          Fin.dappend d1 d2 = !d⟨!v[ℕ, Bool]⟩[(1 : ℕ), (true : Bool)] := rfl

-- More complex dependent append
example : let motive := !v[ℕ, Bool, String, Float]
          let d1 : (i : Fin 2) → motive (Fin.castAdd 2 i) := !d[(1 : ℕ), (true : Bool)]
          let d2 : (i : Fin 2) → motive (Fin.natAdd 2 i) := !d[("hello" : String), (3.14 : Float)]
          Fin.dappend (n := 2) d1 d2 =
            !d⟨motive⟩[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] := rfl

-- Append with empty dependent tuple
example : let motive := !v[ℕ, Bool]
          let d1 : (i : Fin 2) → motive (Fin.castAdd 0 i) := !d[(1 : ℕ), (true : Bool)]
          let d2 : (i : Fin 0) → motive (Fin.natAdd 2 i) := !d[]
          Fin.dappend (n := 0) d1 d2 = !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

end FinDependentAppendTests

-- Test interaction between all append types
section MixedAppendTests

-- Using FinVec append to build type vectors for FinTuple
example : let types1 := !v[ℕ, Bool]
          let types2 := !v[String, Float]
          let combined_types := types1 ++ types2
          let t1 := !t⟨types1⟩[1, true]
          let t2 := !t⟨types2⟩["hello", 3.14]
          let result := t1 ++ᵈ t2
          result = (!t[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] :
                   (i : Fin 4) → combined_types i) := rfl

-- Using FinVec append to build motives for dependent tuples
example : let motive1 := !v[ℕ, Bool]
          let motive2 := !v[String, Float]
          let combined_motive := motive1 ++ motive2
          let d1 : (i : Fin 2) → combined_motive (Fin.castAdd 2 i) := !d[(1 : ℕ), (true : Bool)]
          let d2 : (i : Fin 2) → combined_motive (Fin.natAdd 2 i) :=
            !d[("hello" : String), (3.14 : Float)]
          Fin.dappend (n := 2) d1 d2 =
            (!d[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] :
                               (i : Fin 4) → combined_motive i) := rfl

-- Append with different constructions
example : (!v[1, 2] ++ !v[3]) = !v[1, 2, 3] ∧
          (!t[(1 : ℕ)] ++ᵈ !t[(true : Bool)] = !t[(1 : ℕ), (true : Bool)]) ∧
          (let motive := !v[ℕ, Bool]
           let d1 : (i : Fin 1) → motive (Fin.castAdd 1 i) := !d[(1 : ℕ)]
           let d2 : (i : Fin 1) → motive (Fin.natAdd 1 i) := !d[(true : Bool)]
           Fin.dappend (n := 1) d1 d2 = !d⟨motive⟩[(1 : ℕ), (true : Bool)]) :=
          ⟨rfl, rfl, rfl⟩

end MixedAppendTests

end AppendTests

-- Test the new notation
section NewNotationTests

-- These should work with rfl!
example : 1 ::ᵛ !v[2] = !v[1, 2] := rfl

example : Fin.tail !v[1, 2, 3] = !v[2, 3] := rfl

example : Fin.vconcat !v[1, 2] 3 = !v[1, 2, 3] := rfl

example : !v[1, 2] ++ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Test dependent notation with rfl
example : 1 ::ᵈ !d[2] = !d⟨fun _ => ℕ⟩[1, 2] := rfl

example : (1 : ℕ) ::ᵈ (true : Bool) ::ᵈ !d[] = !d⟨ !v[ℕ, Bool] ⟩[(1 : ℕ), (true : Bool)] := rfl

-- Test that dependent and tuple notations can be equivalent
example : !d[(1 : ℕ), (true : Bool)] = !t[(1 : ℕ), (true : Bool)] := rfl

-- Test new explicit motive notation works with rfl
example : let motive := !v[ℕ]
          (1 : ℕ) ::ᵈ⟨motive⟩ Fin.tempty = !d⟨motive⟩[(1 : ℕ)] := rfl

-- Test explicit motive concat notation
example : let motive := !v[ℕ, Bool]
          !d⟨motive ∘ Fin.castSucc⟩[(1 : ℕ)] :+ᵈ⟨motive⟩ (true : Bool) =
          !d⟨motive⟩[(1 : ℕ), (true : Bool)] := rfl

example : !v[(true, Nat)] ++
  ((!v[] : Fin 0 → Bool × Type) ++
    (!v[(false, Int)] ++ (!v[] : Fin 0 → Bool × Type))) =
      !v[(true, Nat), (false, Int)] := rfl

example : !v[(true, Nat)] ++ !v[(false, Int)] ++ !v[(false, Int)] =
  !v[(true, Nat), (false, Int), (false, Int)] := rfl

-- Test that roundtrip works with pure rfl
example : Fin.take 2 (by omega) !v[1, 2, 3, 4] ++
  Fin.drop 2 (by omega) !v[1, 2, 3, 4] = !v[1, 2, 3, 4] := rfl

-- Complex expression that should compute cleanly
example : Fin.tail (1 ::ᵛ 2 ::ᵛ 3 ::ᵛ !v[] ++ 4 ::ᵛ !v[]) = !v[2, 3, 4] := rfl

-- Even more complex combinations work with rfl
example : Fin.init (Fin.vconcat !v[Nat, Int] Bool) = !v[Nat, Int] := by
  dsimp [Fin.init, Fin.vconcat, Fin.vcons, Fin.vcons]
  ext i; fin_cases i <;> rfl

example : Fin.vconcat (Fin.init !v[Nat, Int, Unit]) Bool = !v[Nat, Int, Bool] := by rfl

example {v : Fin 3 → ℕ} : Fin.vconcat (Fin.init v) (v (Fin.last 2)) = v := by
  ext i; fin_cases i <;> rfl

-- Multiple operations compose cleanly
example : Fin.tail (0 ::ᵛ !v[1, 2] ++ !v[3, 4]) =
    !v[1, 2, 3, 4] := rfl

/-- Test that our new notation gives the same result as the old one (extensionally) -/
example : !v[1, 2, 3] = ![1, 2, 3] := by ext i; fin_cases i <;> rfl

-- Test that concat notation works with rfl
example : !v[1, 2] :+ᵛ 3 = !v[1, 2, 3] := rfl

-- Test interaction between cons, concat, and append
example : (0 ::ᵛ !v[1]) :+ᵛ 2 ++ !v[3, 4] = !v[0, 1, 2, 3, 4] := rfl

-- Test tuple concat notation works with rfl
example : !t[(1 : ℕ), (true : Bool)] :+ᵗ ("hello" : String) =
          !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Comprehensive test of all concat operations
example : (!v[1, 2] :+ᵛ 3 = !v[1, 2, 3]) ∧
          (!t[(1 : ℕ)] :+ᵗ (true : Bool) = !t[(1 : ℕ), (true : Bool)]) ∧
          ((!d[(1 : ℕ)] : (i : Fin 1) → ℕ) :+ᵈ (2 : ℕ) =
           (!d[(1 : ℕ), (2 : ℕ)] : (i : Fin 2) → ℕ)) :=
          ⟨rfl, rfl, rfl⟩

-- Test dependent vector functions for definitional equality
section DependentVectorTests

-- Test that the ++ᵈ notation is properly defined
example : !t[(42 : ℕ)] ++ᵈ !t[(true : Bool)] = !t[(42 : ℕ), (true : Bool)] := rfl

-- Test that the notation can be chained and is associative
example : !t[(1 : ℕ)] ++ᵈ !t[(true : Bool)] ++ᵈ !t[("test" : String)] =
          !t[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

-- Test that type vectors compute correctly
example : (ℕ ::ᵛ !v[Bool]) 0 = ℕ := rfl

example : (ℕ ::ᵛ !v[Bool]) 1 = Bool := rfl

-- Test FinVec.append on types
example : (!v[ℕ] ++ !v[Bool]) 0 = ℕ := rfl

example : (!v[ℕ] ++ !v[Bool]) 1 = Bool := rfl

-- Test FinVec.concat on types
example : Fin.vconcat !v[ℕ] Bool 0 = ℕ := rfl

example : Fin.vconcat !v[ℕ] Bool 1 = Bool := rfl

-- Test that regular vector functions work with the !v[] notation
example : 1 ::ᵛ !v[2, 3] = !v[1, 2, 3] := rfl

example : Fin.vconcat !v[1, 2] 3 = !v[1, 2, 3] := rfl

example : !v[1, 2] ++ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Test that the dependent versions provide good definitional equality
example : ℕ ::ᵛ (Bool ::ᵛ (fun _ : Fin 0 => Empty)) =
    fun i : Fin 2 => if i = 0 then ℕ else Bool := by
  ext i; fin_cases i <;> rfl

end DependentVectorTests

end NewNotationTests
