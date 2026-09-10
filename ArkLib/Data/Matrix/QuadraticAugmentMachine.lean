/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.AugmentedColumnMachine
public import ArkLib.Data.Matrix.QuadraticColumnMachine

/-!
# Coordinate augmented-column execution

Each row is packed as RHS followed by coefficients through explicit cell allocation. Reversal
restores row order, and the actual coordinate column child uses physical index j+1. Unpacking
allocates coefficient/RHS pairs and outer cells; final reversal and output are explicit. Extra
slot/root writes supplement the source ledger. Child work and wrapper costs are retained.
Input preparation, host fuel, reclamation and bit time are outside this primitive model.
-/

@[expose] public section

namespace Matrix.QuadraticAugmentMachine

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Row (F : Type*) := AugmentedColumnMachine.Row (Pair F)
abbrev administrative := QuadraticPivotMachine.administrative
abbrev wrapper := QuadraticPivotMachine.rowWrapper

/-- Extra slot/root writes supplement the source's bundled-cell allocation charges. -/
def allocation (n : ℕ) : Cost := ⟨{ data := n }, 0⟩

inductive Configuration (F : Type*) where
  | ready (state : AugmentedColumnMachine.Configuration (Pair F))
  | column (physical : ℕ) (state : QuadraticColumnMachine.Configuration F)

/-- Source delegated states enter the actual coordinate column child. -/
def enter {F : Type*} : AugmentedColumnMachine.Configuration (Pair F) → Configuration F
  | .column i s => .column i (QuadraticColumnMachine.enter s)
  | s => .ready s

variable {F : Type*} [Field F] [DecidableEq F]

/-- Local serialization transitions or one actual child instruction; no bulk list operation. -/
def step (a : F) (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .ready (.pack ((cs, b) :: rs) rev) =>
      some (.ready (.pack rs ((b :: cs) :: rev)),
        administrative AugmentedColumnMachine.packCost + allocation 2)
  | .ready (.pack [] rev) =>
      some (.ready (.reversePacked rev []), administrative AugmentedColumnMachine.endCost)
  | .ready (.reversePacked (r :: rs) out) =>
      some (.ready (.reversePacked rs (r :: out)),
        administrative AugmentedColumnMachine.reverseCost + allocation 1)
  | .ready (.reversePacked [] out) =>
      some (.column (j + 1) (.ready (.begin out)), administrative AugmentedColumnMachine.enterCost)
  | .ready (.column i s) => some (.column i (QuadraticColumnMachine.enter s), wrapper)
  | .ready (.unpack ((b :: cs) :: rs) rev) =>
      some (.ready (.unpack rs ((cs, b) :: rev)),
        administrative AugmentedColumnMachine.unpackCost + allocation 3)
  | .ready (.unpack ([] :: _) _) =>
      some (.ready .rejected, administrative AugmentedColumnMachine.rejectCost)
  | .ready (.unpack [] rev) =>
      some (.ready (.reverseRows rev []), administrative AugmentedColumnMachine.endCost)
  | .ready (.reverseRows (r :: rs) out) =>
      some (.ready (.reverseRows rs (r :: out)),
        administrative AugmentedColumnMachine.reverseCost + allocation 1)
  | .ready (.reverseRows [] out) =>
      some (.ready (.done out), administrative AugmentedColumnMachine.emitCost)
  | .ready (.done _) | .ready .rejected => none
  | .column i s => match QuadraticColumnMachine.step a i s with
      | some (t, c) => some (.column i t, c + wrapper)
      | none => match s with
          | .ready (.done out) =>
              some (.ready (.unpack out []), administrative AugmentedColumnMachine.returnCost)
          | .ready .rejected =>
              some (.ready .rejected, administrative AugmentedColumnMachine.rejectCost)
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a j 0 s 0 s
  | cons {n s u t c d} (head : step a j s = some (u, c)) (tail : Trace a j n u d t) :
      Trace a j (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a j s = some (t, c)) : Trace a j 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {j n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a j n s c u) (h' : Trace a j m u d t) : Trace a j (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a j s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a j n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {j n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a j n s c t) : runFuel a j n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticAugmentMachine
