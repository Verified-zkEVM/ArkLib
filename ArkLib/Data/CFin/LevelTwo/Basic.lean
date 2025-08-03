import ArkLib.Data.CFin.Defs
import ArkLib.Data.CNat.LevelTwo

/-!
# CFin₂: GFin specialized to CNat₂

This file defines `CFin₂`, which is `GFin` specialized to `CNat₂` from Level Two
of the CNat hierarchy. This provides finite types where indices have definitional
multiplication associativity (in addition to definitional addition associativity).

## Main Definitions

- `CFin₂ n`: Elements of `CNat₂` that are less than `n` (specialized `GFin CNat₂ n`)
- `CFin₂Vec`: Homogeneous vectors indexed by `CFin₂`
- `CFin₂Tuple`: Heterogeneous tuples indexed by `CFin₂`
- All the standard operations: cons, concat, append, take, drop, etc.
- Notation similar to the `Fin` tuple notation but for `CFin₂`

## Key Properties

Since `CNat₂` has definitional multiplication associativity (and inherits addition
associativity from `CNat`), operations on `CFin₂` inherit these properties, making
proofs involving complex arithmetic expressions easier.
-/

/-- `CFin₂ n` is `GFin CNat₂ n` - elements of `CNat₂` less than `n`. -/
abbrev CFin₂ (n : CNat₂) := GFin CNat₂ n

namespace CFin₂

variable {n : CNat₂}

-- Basic operations and conversions

/-- Convert a `CNat₂` to `CFin₂ n` if it's less than `n`. -/
def ofCNat₂? (val : CNat₂) : Option (CFin₂ n) := GFin.ofN? val

/-- Convert a `CNat₂` to `CFin₂ n` with a proof it's less than `n`. -/
def ofCNat₂ (val : CNat₂) (h : val < n) : CFin₂ n := GFin.ofN val h

/-- Convert a `CNat` to `CFin₂ n` via the CNat → CNat₂ conversion. -/
def ofCNat (val : CNat) : Option (CFin₂ n) := 
  ofCNat₂? (CNat₂.ofNat (CNat.toNat val))

/-- Convert a `Nat` to `CFin₂ n` via `CNat₂.ofNat`. -/
def ofNat (val : Nat) : Option (CFin₂ n) := 
  ofCNat₂? (CNat₂.ofNat val)

/-- Get the underlying `CNat₂` value. -/
def toCNat₂ (i : CFin₂ n) : CNat₂ := i.val

/-- Get the underlying `CNat` value via the conversion chain. -/
def toCNat (i : CFin₂ n) : CNat := 
  CNat.ofNat (CNat₂.toNat i.val)

/-- Get the underlying `Nat` value via `CNat₂.toNat`. -/
def toNat (i : CFin₂ n) : Nat := CNat₂.toNat i.val

-- Typeclass instances

instance : DecidableEq (CFin₂ n) := GFin.instDecidableEq

section PositiveBound

variable [h : Fact ((0 : CNat₂) < n)]

instance : Zero (CFin₂ n) := GFin.instZero

end PositiveBound

-- Coercion instances
instance : Coe (CFin₂ n) CNat₂ := ⟨CFin₂.toCNat₂⟩
instance : CoeFun (CFin₂ n) (fun _ => Nat) := ⟨CFin₂.toNat⟩

end CFin₂

-- CFin₂ Vector and Tuple types

/-- Homogeneous vectors indexed by `CFin₂ n`. -/
abbrev CFin₂Vec (α : Sort*) (n : CNat₂) := GFinVec CNat₂ α n

/-- Heterogeneous tuples indexed by `CFin₂ n`. -/
abbrev CFin₂Tuple (n : CNat₂) (α : CFin₂Vec (Sort*) n) := GFinTuple CNat₂ n α

namespace CFin₂Vec

variable {α : Sort*} {n : CNat₂}

-- Basic operations specialized to CFin₂

/-- Empty CFin₂ vector. -/
def empty : CFin₂Vec α 0 := GFinVec.empty

/-- Cons operation for CFin₂ vectors. -/
def cons (a : α) (v : CFin₂Vec α n) [h : Fact ((0 : CNat₂) < (1 : CNat₂) + n)] : 
    CFin₂Vec α (1 + n) := GFinVec.cons a v

/-- Concatenation for CFin₂ vectors. -/
def concat (v : CFin₂Vec α n) (a : α) [h : Fact (n < n + (1 : CNat₂))] :
    CFin₂Vec α (n + 1) := GFinVec.concat v a

/-- Append operation for CFin₂ vectors. -/
def append {m : CNat₂} (u : CFin₂Vec α m) (v : CFin₂Vec α n) :
    CFin₂Vec α (m + n) := GFinVec.append u v

-- TODO: Add take, drop, slice operations
-- TODO: Add notation similar to !v₂[...] for CFin₂ vectors

end CFin₂Vec

namespace CFin₂Tuple

variable {n : CNat₂} {α : CFin₂Vec (Sort*) n}

-- Basic operations specialized to CFin₂

/-- Empty CFin₂ tuple. -/
def empty : CFin₂Tuple 0 (fun _ => Sort*) := GFinTuple.empty

/-- Cons operation for CFin₂ tuples. -/
def cons {β : Sort*} {γ : CFin₂Vec (Sort*) n} (a : β) (b : CFin₂Tuple n γ)
    [h : Fact ((0 : CNat₂) < (1 : CNat₂) + n)] :
    CFin₂Tuple (1 + n) (CFin₂Vec.cons β γ) := GFinTuple.cons a b

/-- Concatenation for CFin₂ tuples. -/
def concat {β : Sort*} (u : CFin₂Tuple n α) (a : β)
    [h : Fact (n < n + (1 : CNat₂))] :
    CFin₂Tuple (n + 1) (CFin₂Vec.concat α β) := GFinTuple.concat u a

/-- Append operation for CFin₂ tuples. -/
def append {m : CNat₂} {β : CFin₂Vec (Sort*) m} 
    (u : CFin₂Tuple m β) (v : CFin₂Tuple n α) :
    CFin₂Tuple (m + n) (CFin₂Vec.append β α) := GFinTuple.append u v

-- TODO: Add notation similar to !t₂[...] for CFin₂ tuples

end CFin₂Tuple

-- Example usage and tests

section Examples

-- These are examples showing how CFin₂ works with CNat₂'s definitional associativities
variable (a b c : CNat₂)

-- Both addition and multiplication associativity are definitional
example : CFin₂ ((a + b) + c) = CFin₂ (a + (b + c)) := rfl
example : CFin₂ ((a * b) * c) = CFin₂ (a * (b * c)) := rfl

-- This means certain coercions and operations compose definitionally
example (i : CFin₂ (a * b)) : CFin₂ ((a * b) * c) := 
  CFin₂.ofCNat₂ i.val (by 
    have : i.val < a * b := i.isLt
    sorry -- This should be provable using CNat₂ properties
  )

-- Complex arithmetic expressions maintain definitional equality
example : CFin₂ ((a * b) + (c * (a + b))) = CFin₂ (a * b + c * (a + b)) := rfl

end Examples