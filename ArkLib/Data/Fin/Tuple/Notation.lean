/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.HDAppend
import ArkLib.Data.Fin.Tuple.Defs
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

/-!
## Custom Vector Notation with Better Definitional Equality

We create a new vector notation `!v[a, b, c]` that uses our custom functions with better
definitional equality. This is similar to Mathlib's `Matrix.vecCons` and `Matrix.vecEmpty`
used in `![]` notation, but uses our custom `vecCons` which provides better definitional
equality through pattern matching instead of `cases`.
-/

namespace FinVec

-- Infix notation for cons operations, similar to Vector.cons
@[inherit_doc]
infixr:67 " ::ᵛ " => FinVec.cons

/-- `!v[...]` notation constructs a vector using our custom functions.
Uses `!v[...]` to distinguish from standard `![]`. -/
syntax (name := finVecNotation) "!v[" term,* "]" : term

macro_rules
  | `(!v[$term:term, $terms:term,*]) => `(FinVec.cons $term !v[$terms,*])
  | `(!v[$term:term]) => `(FinVec.cons $term !v[])
  | `(!v[]) => `(FinVec.empty)

/-- Unexpander for the `!v[x, y, ...]` notation. -/
@[app_unexpander FinVec.cons]
def consUnexpander' : Lean.PrettyPrinter.Unexpander
  | `($_ $term !v[$term2, $terms,*]) => `(!v[$term, $term2, $terms,*])
  | `($_ $term !v[$term2]) => `(!v[$term, $term2])
  | `($_ $term !v[]) => `(!v[$term])
  | _ => throw ()

/-- Unexpander for the `!v[]` notation. -/
@[app_unexpander FinVec.empty]
def emptyUnexpander' : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!v[])
  | _ => throw ()

end FinVec

namespace FinTuple

@[inherit_doc]
infixr:67 " ::ᵗ " => FinTuple.cons

/-- `!t[...]` notation constructs a tuple (heterogeneous vector) using our custom functions.
Uses `!t[...]` to distinguish from standard `![]`. -/
syntax (name := finTupleNotation) "!t[" term,* "]" : term

/-- `!t⟨TypeVec⟩[...]` notation constructs a tuple with explicit type vector specification.
Uses angle brackets to specify the type vector, then square brackets for values. -/
syntax (name := finTupleNotationWithTypes) "!t⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!t[$term:term, $terms:term,*]) => `(FinTuple.cons $term !t[$terms,*])
  | `(!t[$term:term]) => `(FinTuple.cons $term !t[])
  | `(!t[]) => `(@FinTuple.empty (FinVec.empty))

macro_rules
  | `(!t⟨$typeVec⟩[$term:term, $terms:term,*]) => `((!t[$term, $terms,*] : FinTuple _ $typeVec))
  | `(!t⟨$typeVec⟩[$term:term]) => `((!t[$term] : FinTuple _ $typeVec))
  | `(!t⟨$typeVec⟩[]) => `((FinTuple.empty : FinTuple 0 $typeVec))

/-- Unexpander for the `!t[x, y, ...]` notation. -/
@[app_unexpander FinTuple.cons]
def consUnexpander' : Lean.PrettyPrinter.Unexpander
  | `($_ $term !t[$term2, $terms,*]) => `(!t[$term, $term2, $terms,*])
  | `($_ $term !t[$term2]) => `(!t[$term, $term2])
  | `($_ $term !t[]) => `(!t[$term])
  | _ => throw ()

/-- Unexpander for the `!t[]` notation. -/
@[app_unexpander FinTuple.empty]
def emptyUnexpander' : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!t[])
  | _ => throw ()

end FinTuple

/-- `++` instance for FinVec -/
instance {α : Type*} {m n : ℕ} : HAppend (FinVec α m) (FinVec α n) (FinVec α (m + n)) where
  hAppend := FinVec.append

/-- `++ᵈ` instance for FinTuple -/
instance {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u} :
    HDAppend (FinTuple m α) (FinTuple n β) (FinTuple (m + n) (FinVec.append α β)) where
  hDAppend := FinTuple.append

-- Test examples for the new tuple notations
section TupleNotationTests

-- Basic heterogeneous tuple without type specification
example : !t[(1 : ℕ), (true : Bool), ("hello" : String)] =
  FinTuple.cons 1 (FinTuple.cons true (FinTuple.cons "hello" FinTuple.empty)) := rfl

-- With explicit type vector using predefined type
def MyTypeVec : FinVec Type 3 := !v[ℕ, Bool, String]

example : !t⟨MyTypeVec⟩[1, true, "hello"] =
  (!t[1, true, "hello"] : FinTuple 3 MyTypeVec) := rfl

-- With explicit type vector using !v[] notation
example : !t⟨ !v[ℕ, Bool, String] ⟩[1, true, "hello"] =
  (!t[1, true, "hello"] : FinTuple 3 !v[ℕ, Bool, String]) := rfl

example : !t⟨ !v[ℕ, Bool, String] ⟩[1, true, "hello"] =
  !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Empty tuple with type specification
example : !t⟨!v[]⟩[] = (FinTuple.empty : FinTuple 0 !v[]) := rfl

end TupleNotationTests

-- Test infix notation for cons operations
section InfixNotationTests

-- Test FinVec.cons (::ᵛ) notation
section FinVecConsTests

-- Basic cons operation
example : 1 ::ᵛ !v[2, 3] = !v[1, 2, 3] := rfl

-- Chaining cons operations (right associative)
example : 1 ::ᵛ 2 ::ᵛ 3 ::ᵛ FinVec.empty = !v[1, 2, 3] := rfl

-- Mixing cons and bracket notation
example : 0 ::ᵛ !v[1, 2] = !v[0, 1, 2] := rfl

-- Type inference works
example : let v : FinVec ℕ 2 := !v[1, 2]
          0 ::ᵛ v = !v[0, 1, 2] := rfl

-- Empty vector
example : 42 ::ᵛ FinVec.empty = !v[42] := rfl

end FinVecConsTests

-- Test FinTuple.cons (::ᵗ) notation
section FinTupleConsTests

-- Basic heterogeneous cons
example : (1 : ℕ) ::ᵗ ((true : Bool) ::ᵗ FinTuple.empty) =
          !t[(1 : ℕ), (true : Bool)] := rfl

-- Chaining different types (right associative)
example : (1 : ℕ) ::ᵗ (true : Bool) ::ᵗ ("hello" : String) ::ᵗ FinTuple.empty =
          !t[(1 : ℕ), (true : Bool), ("hello" : String)] := rfl

-- Mixing cons and bracket notation
example : (0 : ℕ) ::ᵗ !t[(1 : ℕ), (true : Bool)] =
          !t[(0 : ℕ), (1 : ℕ), (true : Bool)] := rfl

-- With explicit type annotation
example : (42 : ℕ) ::ᵗ (FinTuple.empty : FinTuple 0 FinVec.empty) =
          !t[(42 : ℕ)] := rfl

-- Complex nested example
example : let t1 : FinTuple 2 !v[Bool, String] := !t[(true : Bool), ("test" : String)]
          let result := (1 : ℕ) ::ᵗ t1
          result = !t[(1 : ℕ), (true : Bool), ("test" : String)] := rfl

end FinTupleConsTests

-- Test interaction between both notations
section MixedTests

-- FinVec used as type vector for FinTuple
example : let typeVec := ℕ ::ᵛ Bool ::ᵛ FinVec.empty
          !t⟨typeVec⟩[1, true] = !t[(1 : ℕ), (true : Bool)] := rfl

-- Building complex structures step by step
example : let types := ℕ ::ᵛ Bool ::ᵛ FinVec.empty
          let values := 1 ::ᵗ true ::ᵗ FinTuple.empty
          values = (!t⟨types⟩[1, true] : FinTuple 2 types) := rfl

end MixedTests

end InfixNotationTests

-- Test append operations (++ and ++ᵈ)
section AppendTests

-- Test FinVec.append (standard ++)
section FinVecAppendTests

-- Basic homogeneous append
example : !v[1, 2] ++ !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Append with empty vectors
example : !v[1, 2] ++ (!v[] : FinVec ℕ _) = !v[1, 2] := rfl
example : (FinVec.empty : FinVec ℕ 0) ++ !v[1, 2] = !v[1, 2] := rfl

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
          let middle := (true : Bool) ::ᵗ (FinTuple.empty : FinTuple 0 FinVec.empty)
          let final := !t[("final" : String)]
          (base ++ᵈ middle) ++ᵈ final = !t[(0 : ℕ), (true : Bool), ("final" : String)] := rfl

end FinTupleAppendTests

-- Test interaction between both append types
section MixedAppendTests

-- Using FinVec append to build type vectors for FinTuple
example : let types1 := !v[ℕ, Bool]
          let types2 := !v[String, Float]
          let combined_types := types1 ++ types2
          let t1 := !t⟨types1⟩[1, true]
          let t2 := !t⟨types2⟩["hello", 3.14]
          let result := t1 ++ᵈ t2
          result = (!t[(1 : ℕ), (true : Bool), ("hello" : String), (3.14 : Float)] :
                   FinTuple 4 combined_types) := rfl

-- Append with different constructions
example : (!v[1, 2] ++ !v[3]) = !v[1, 2, 3] ∧
          (!t[(1 : ℕ)] ++ᵈ !t[(true : Bool)] = !t[(1 : ℕ), (true : Bool)]) :=
          ⟨rfl, rfl⟩

end MixedAppendTests

end AppendTests

-- Test the new notation
section NewNotationTests

-- These should work with rfl!
example : FinVec.cons 1 !v[2] = !v[1, 2] := rfl

example : Fin.tail !v[1, 2, 3] = !v[2, 3] := rfl

example : FinVec.concat !v[1, 2] 3 = !v[1, 2, 3] := rfl

example : FinVec.append !v[1, 2] !v[3, 4] = !v[1, 2, 3, 4] := rfl

example : FinVec.append !v[(true, Nat)]
    (FinVec.append !v[] (FinVec.append !v[(false, Int)] !v[])) =
      !v[(true, Nat), (false, Int)] := rfl

example : FinVec.append (!v[(true, Nat)] ++ !v[(false, Int)])
    (FinVec.append !v[(false, Int)] !v[]) = !v[(true, Nat), (false, Int), (false, Int)] := rfl

-- Test that roundtrip works with pure rfl
example : FinVec.append (Fin.take 2 (by omega) !v[1, 2, 3, 4])
    (Fin.drop 2 (by omega) !v[1, 2, 3, 4]) = !v[1, 2, 3, 4] := rfl

-- Complex expression that should compute cleanly
example : Fin.tail (FinVec.append
    (FinVec.cons 1 (FinVec.cons 2 (FinVec.cons 3 (Fin.elim0))))
    (FinVec.cons 4 (Fin.elim0))) = !v[2, 3, 4] := rfl

-- Even more complex combinations work with rfl
example : Fin.init (FinVec.concat !v[Nat, Int] Bool) = !v[Nat, Int] := by
  dsimp [Fin.init, FinVec.concat, FinVec.cons, FinVec.cons]
  ext i; fin_cases i <;> rfl

example : FinVec.concat (Fin.init !v[Nat, Int, Unit]) Bool = !v[Nat, Int, Bool] := by rfl

example {v : Fin 3 → ℕ} : FinVec.concat (Fin.init v) (v (Fin.last 2)) = v := by
  ext i; fin_cases i <;> rfl

-- Multiple operations compose cleanly
example : Fin.tail (FinVec.cons 0 (FinVec.append !v[1, 2] !v[3, 4])) =
    !v[1, 2, 3, 4] := rfl

/-- Test that our new notation gives the same result as the old one (extensionally) -/
example : !v[1, 2, 3] = ![1, 2, 3] := by ext i; fin_cases i <;> rfl

-- Test dependent vector functions for definitional equality
section DependentVectorTests

-- Test that the ++ᵈ notation is properly defined
example : (fun _ : Fin 1 => (42 : ℕ)) ++ᵈ (fun _ : Fin 1 => (true : Bool)) =
          FinTuple.append (fun _ : Fin 1 => (42 : ℕ)) (fun _ : Fin 1 => (true : Bool)) := rfl

-- Test that the notation can be chained and is associative
example : ((fun _ : Fin 1 => (1 : ℕ)) ++ᵈ (fun _ : Fin 1 => (true : Bool))) ++ᵈ
          (fun _ : Fin 1 => ("test" : String)) =
          (fun _ : Fin 1 => (1 : ℕ)) ++ᵈ
          ((fun _ : Fin 1 => (true : Bool)) ++ᵈ (fun _ : Fin 1 => ("test" : String))) := rfl

-- Test that type vectors compute correctly
example : FinVec.cons ℕ (fun _ : Fin 1 => Bool) 0 = ℕ := rfl

example : FinVec.cons ℕ (fun _ : Fin 1 => Bool) 1 = Bool := rfl

-- Test FinVec.append on types
example : FinVec.append (fun _ : Fin 1 => ℕ) (fun _ : Fin 1 => Bool) 0 = ℕ := rfl

example : FinVec.append (fun _ : Fin 1 => ℕ) (fun _ : Fin 1 => Bool) 1 = Bool := rfl

-- Test FinVec.concat on types
example : FinVec.concat (fun _ : Fin 1 => ℕ) Bool 0 = ℕ := rfl

example : FinVec.concat (fun _ : Fin 1 => ℕ) Bool 1 = Bool := rfl

-- Test that regular vector functions work with the !v[] notation
example : FinVec.cons 1 !v[2, 3] = !v[1, 2, 3] := rfl

example : FinVec.concat !v[1, 2] 3 = !v[1, 2, 3] := rfl

example : FinVec.append !v[1, 2] !v[3, 4] = !v[1, 2, 3, 4] := rfl

-- Test that the dependent versions provide good definitional equality
example : FinVec.cons ℕ (FinVec.cons Bool (fun _ : Fin 0 => Empty)) =
    fun i : Fin 2 => if i = 0 then ℕ else Bool := by
  ext i; fin_cases i <;> rfl

end DependentVectorTests

end NewNotationTests
