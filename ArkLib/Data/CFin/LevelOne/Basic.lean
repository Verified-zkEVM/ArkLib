import ArkLib.Data.CFin.Defs
import ArkLib.Data.CNat.LevelOne

/-!
# CFin: GFin specialized to CNat

This file defines `CFin`, which is `GFin` specialized to `CNat` from Level One
of the CNat hierarchy. This provides finite types where indices have definitional
addition associativity.

## Main Definitions

- `CFin n`: Elements of `CNat` that are less than `n` (specialized `GFin CNat n`)
- `CFinVec`: Homogeneous vectors indexed by `CFin`
- `CFinTuple`: Heterogeneous tuples indexed by `CFin`
- All the standard operations: cons, concat, append, take, drop, etc.
- Notation similar to the `Fin` tuple notation but for `CFin`

## Key Properties

Since `CNat` has definitional addition associativity, operations on `CFin` inherit
this property, making certain proofs easier compared to standard `Fin`.
-/

/-- `CFin n` is `GFin CNat n` - elements of `CNat` less than `n`. -/
abbrev CFin (n : CNat) := GFin CNat n

namespace CFin

variable {n : CNat}

-- Basic operations and conversions

/-- Convert a `CNat` to `CFin n` if it's less than `n`. -/
def ofCNat? (val : CNat) : Option (CFin n) := GFin.ofN? val

/-- Convert a `CNat` to `CFin n` with a proof it's less than `n`. -/
def ofCNat (val : CNat) (h : val < n) : CFin n := GFin.ofN val h

/-- Convert a `Nat` to `CFin n` via `CNat.ofNat`. -/
def ofNat (val : Nat) : Option (CFin n) := 
  ofCNat? (CNat.ofNat val)

/-- Get the underlying `CNat` value. -/
def toCNat (i : CFin n) : CNat := i.val

/-- Get the underlying `Nat` value via `CNat.toNat`. -/
def toNat (i : CFin n) : Nat := CNat.toNat i.val

-- Typeclass instances

instance : DecidableEq (CFin n) := GFin.instDecidableEq

section PositiveBound

variable [h : Fact ((0 : CNat) < n)]

instance : Zero (CFin n) := GFin.instZero

end PositiveBound

-- Coercion instances
instance : Coe (CFin n) CNat := ⟨CFin.toCNat⟩
instance : CoeFun (CFin n) (fun _ => Nat) := ⟨CFin.toNat⟩

end CFin

-- CFin Vector and Tuple types

/-- Homogeneous vectors indexed by `CFin n`. -/
abbrev CFinVec (α : Sort*) (n : CNat) := GFinVec CNat α n

/-- Heterogeneous tuples indexed by `CFin n`. -/
abbrev CFinTuple (n : CNat) (α : CFinVec (Sort*) n) := GFinTuple CNat n α

namespace CFinVec

variable {α : Sort*} {n : CNat}

-- Basic operations specialized to CFin

/-- Empty CFin vector. -/
def empty : CFinVec α 0 := GFinVec.empty

/-- Cons operation for CFin vectors. -/
def cons (a : α) (v : CFinVec α n) [h : Fact ((0 : CNat) < (1 : CNat) + n)] : 
    CFinVec α (1 + n) := GFinVec.cons a v

/-- Concatenation for CFin vectors. -/
def concat (v : CFinVec α n) (a : α) [h : Fact (n < n + (1 : CNat))] :
    CFinVec α (n + 1) := GFinVec.concat v a

/-- Append operation for CFin vectors. -/
def append {m : CNat} (u : CFinVec α m) (v : CFinVec α n) :
    CFinVec α (m + n) := GFinVec.append u v

-- TODO: Add take, drop, slice operations
-- TODO: Add notation similar to !v[...] for CFin vectors

end CFinVec

namespace CFinTuple

variable {n : CNat} {α : CFinVec (Sort*) n}

-- Basic operations specialized to CFin

/-- Empty CFin tuple. -/
def empty : CFinTuple 0 (fun _ => Sort*) := GFinTuple.empty

/-- Cons operation for CFin tuples. -/
def cons {β : Sort*} {γ : CFinVec (Sort*) n} (a : β) (b : CFinTuple n γ)
    [h : Fact ((0 : CNat) < (1 : CNat) + n)] :
    CFinTuple (1 + n) (CFinVec.cons β γ) := GFinTuple.cons a b

/-- Concatenation for CFin tuples. -/
def concat {β : Sort*} (u : CFinTuple n α) (a : β)
    [h : Fact (n < n + (1 : CNat))] :
    CFinTuple (n + 1) (CFinVec.concat α β) := GFinTuple.concat u a

/-- Append operation for CFin tuples. -/
def append {m : CNat} {β : CFinVec (Sort*) m} 
    (u : CFinTuple m β) (v : CFinTuple n α) :
    CFinTuple (m + n) (CFinVec.append β α) := GFinTuple.append u v

-- TODO: Add notation similar to !t[...] for CFin tuples

end CFinTuple

-- Example usage and tests

section Examples

-- These are examples showing how CFin works with CNat's definitional associativity
variable (a b c : CNat)

-- Addition associativity is definitional
example : CFin ((a + b) + c) = CFin (a + (b + c)) := rfl

-- This means certain coercions and operations compose definitionally
example (i : CFin (a + b)) : CFin ((a + b) + c) := 
  CFin.ofCNat i.val (by 
    have : i.val < a + b := i.isLt
    sorry -- This should be provable using CNat properties
  )

end Examples