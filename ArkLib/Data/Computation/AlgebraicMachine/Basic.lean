/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Field.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Atomic values and closed algebraic primitives

Registers and heap cells contain atoms; a heap cell stores exactly two atoms. A pointer
copy shares that cell and does not copy a list. Traversal, list construction, and scalar
exponentiation must therefore be programs composed from the primitive menu below.

Each primitive is one unit of abstract algebraic machine work. Field arithmetic, natural
arithmetic, and pointer access have unit cost in this model; this is not a bit-cost or
bounded-word model. Field inversion and natural division use their total Lean operations,
including their zero-divisor conventions. Ill-typed operands and dangling reads fail.
-/

@[expose] public section

namespace AlgebraicMachine

/-- A runtime atom contains no recursive data or executable host-language function. -/
inductive Value (F : Type*) where
  | field (value : F)
  | natural (value : ℕ)
  | boolean (value : Bool)
  | null
  | pointer (address : ℕ)
  deriving DecidableEq, Repr

/-- Pair cells with an allocation frontier. `Heap.WellFormed` restricts occupied cells to
the finite prefix below this frontier; only then is allocation globally non-overwriting. -/
structure Heap (F : Type*) where
  next : ℕ
  cells : ℕ → Option (Value F × Value F)

/-- An empty heap begins allocating at address zero. -/
def Heap.empty {F : Type*} : Heap F := ⟨0, fun _ => none⟩

/-- Allocate one pair of atoms at the next address. -/
def Heap.allocate {F : Type*} (h : Heap F) (a b : Value F) : Heap F :=
  ⟨h.next + 1, Function.update h.cells h.next (some (a, b))⟩

/-- A fixed finite register bank and a heap of pair cells. -/
structure State (F : Type*) (r : ℕ) where
  registers : Fin r → Value F
  heap : Heap F

/-- Initially all registers are null and the heap is empty. -/
def State.empty {F : Type*} {r : ℕ} : State F r :=
  ⟨fun _ => .null, Heap.empty⟩

/-- Replace one register atom, preserving every heap cell. -/
def State.write {F : Type*} {r : ℕ} (s : State F r) (dst : Fin r)
    (value : Value F) : State F r :=
  { s with registers := Function.update s.registers dst value }

/-- The closed primitive menu. There are no bulk data operations or callbacks.
Natural literals are fixed program constants: a uniform algorithm chooses its program
before receiving input values or their sizes. -/
inductive Primitive (r : ℕ) where
  | copy (dst src : Fin r)
  | fieldZero (dst : Fin r)
  | fieldOne (dst : Fin r)
  | fieldAdd (dst a b : Fin r)
  | fieldMul (dst a b : Fin r)
  | fieldNeg (dst src : Fin r)
  | fieldInv (dst src : Fin r)
  | fieldEq (dst a b : Fin r)
  | natLiteral (dst : Fin r) (n : ℕ)
  | natAdd (dst a b : Fin r)
  | natSub (dst a b : Fin r)
  | natMul (dst a b : Fin r)
  | natDiv (dst a b : Fin r)
  | natEq (dst a b : Fin r)
  | natLt (dst a b : Fin r)
  | boolNot (dst src : Fin r)
  | null (dst : Fin r)
  | isNull (dst src : Fin r)
  | pair (dst a b : Fin r)
  | first (dst src : Fin r)
  | second (dst src : Fin r)
  deriving DecidableEq, Repr

/-- Execute one primitive by inspecting boundedly many atoms. Pair allocation reads both
operands from the prestate, even when the destination aliases a source register. -/
def Primitive.eval {F : Type*} {r : ℕ} [Field F] [DecidableEq F] :
    Primitive r → State F r → Option (State F r)
  | .copy dst src, s => some (s.write dst (s.registers src))
  | .fieldZero dst, s => some (s.write dst (.field 0))
  | .fieldOne dst, s => some (s.write dst (.field 1))
  | .fieldAdd dst a b, s =>
      match s.registers a, s.registers b with
      | .field x, .field y => some (s.write dst (.field (x + y)))
      | _, _ => none
  | .fieldMul dst a b, s =>
      match s.registers a, s.registers b with
      | .field x, .field y => some (s.write dst (.field (x * y)))
      | _, _ => none
  | .fieldNeg dst src, s =>
      match s.registers src with
      | .field x => some (s.write dst (.field (-x)))
      | _ => none
  | .fieldInv dst src, s =>
      match s.registers src with
      | .field x => some (s.write dst (.field x⁻¹))
      | _ => none
  | .fieldEq dst a b, s =>
      match s.registers a, s.registers b with
      | .field x, .field y => some (s.write dst (.boolean (decide (x = y))))
      | _, _ => none
  | .natLiteral dst n, s => some (s.write dst (.natural n))
  | .natAdd dst a b, s =>
      match s.registers a, s.registers b with
      | .natural x, .natural y => some (s.write dst (.natural (x + y)))
      | _, _ => none
  | .natSub dst a b, s =>
      match s.registers a, s.registers b with
      | .natural x, .natural y => some (s.write dst (.natural (x - y)))
      | _, _ => none
  | .natMul dst a b, s =>
      match s.registers a, s.registers b with
      | .natural x, .natural y => some (s.write dst (.natural (x * y)))
      | _, _ => none
  | .natDiv dst a b, s =>
      match s.registers a, s.registers b with
      | .natural x, .natural y => some (s.write dst (.natural (x / y)))
      | _, _ => none
  | .natEq dst a b, s =>
      match s.registers a, s.registers b with
      | .natural x, .natural y => some (s.write dst (.boolean (decide (x = y))))
      | _, _ => none
  | .natLt dst a b, s =>
      match s.registers a, s.registers b with
      | .natural x, .natural y => some (s.write dst (.boolean (decide (x < y))))
      | _, _ => none
  | .boolNot dst src, s =>
      match s.registers src with
      | .boolean b => some (s.write dst (.boolean (!b)))
      | _ => none
  | .null dst, s => some (s.write dst .null)
  | .isNull dst src, s =>
      match s.registers src with
      | .null => some (s.write dst (.boolean true))
      | _ => some (s.write dst (.boolean false))
  | .pair dst a b, s =>
      let address := s.heap.next
      let allocated : State F r :=
        { s with heap := s.heap.allocate (s.registers a) (s.registers b) }
      some (allocated.write dst (.pointer address))
  | .first dst src, s =>
      match s.registers src with
      | .pointer address =>
          match s.heap.cells address with
          | some (a, _) => some (s.write dst a)
          | none => none
      | _ => none
  | .second dst src, s =>
      match s.registers src with
      | .pointer address =>
          match s.heap.cells address with
          | some (_, b) => some (s.write dst b)
          | none => none
      | _ => none

end AlgebraicMachine
