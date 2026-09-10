/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.VandermondeMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine

/-!
# Vandermonde construction by quadratic coordinate instructions

Samples are materialized point/value coordinate pairs. Each row allocates the seed (1,0), then
executes the original coefficient, reversal, augmented-row and output-cell phases. Every next
power, including the final unused one, runs the actual base multiplication program. The input
record is constructed once at launch and retained throughout the call; unchanged frame registers
are shared. No bulk map, power, reversal or field-operation callback is executed.

The ledger preserves source administrative fields, charges seed slots/constants, call setup,
every base instruction and wrapper, and return. Outer save adds the root write beyond its two
reads and two cell-slot writes. Input preparation, host fuel and compiled/bit time are excluded.
-/

@[expose] public section

namespace Matrix.QuadraticVandermondeMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Row (F : Type*) := VandermondeMachine.Row (Pair F)
abbrev Sample (F : Type*) := Pair F × Pair F

/-- Preserve source natural, dispatch, access and output charges without abstract arithmetic. -/
def administrative (c : VandermondeMachine.Cost) : Cost :=
  ⟨{ control := c.row.control, data := c.row.data, output := c.row.output }, c.natural⟩
/-- Allocate the coordinate seed and write its two literal constants. -/
def seedCost : Cost := ⟨{ data := 2, constants := 2 }, 0⟩
/-- Read operands/parameter and write the three retained arithmetic-input registers. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Read the emitted pair and restore the suspended power-loop register. -/
def returned : Cost := ⟨{ control := 1, data := 3 }, 0⟩
/-- The outer list root write supplements its two reads and two cell-slot writes. -/
def saveRoot : Cost := ⟨{ data := 1 }, 0⟩

/-- Retained registers; coordinates and immutable lists are shared across the arithmetic call. -/
structure Frame (F : Type*) where
  point : Pair F
  value : Pair F
  samples : List (Sample F)
  rows : List (Row F)
  remaining : ℕ
  coefficients : List (Pair F)

inductive Configuration (F : Type*) where
  | ready (state : VandermondeMachine.Configuration (Pair F))
  | call (frame : Frame F) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)

/-- Install an already materialized power; all other registers retain their old values. -/
def resume {F : Type*} (frame : Frame F) (p : Pair F) : Configuration F :=
  .ready (.power frame.point frame.value frame.samples frame.rows frame.remaining p
    frame.coefficients)

variable {F : Type*} [Field F] [DecidableEq F]

/-- One base instruction or one explicit allocation/cursor transition. -/
def step (a : F) (L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .ready (.start ss) => some (.ready (.scan ss []), administrative VandermondeMachine.startCost)
  | .ready (.scan ((x, y) :: ss) rows) =>
      some (.ready (.power x y ss rows L (1, 0) []),
        administrative VandermondeMachine.takeCost + seedCost)
  | .ready (.scan [] rows) =>
      some (.ready (.reverseRows rows []), administrative VandermondeMachine.outerFinishCost)
  | .ready (.power x y ss rows (n + 1) p cs) =>
      some (.ready (.multiply x y ss rows n p (p :: cs)),
        administrative VandermondeMachine.coefficientCost)
  | .ready (.power _ y ss rows 0 _ cs) =>
      some (.ready (.reverseRow y ss rows cs []), administrative VandermondeMachine.powerFinishCost)
  | .ready (.multiply x y ss rows n p cs) =>
      some (.call ⟨x, y, ss, rows, n, cs⟩ ⟨a, p, x⟩ (.start .mul),
        administrative VandermondeMachine.multiplyCost + launch)
  | .ready (.reverseRow y ss rows (c :: cs) out) =>
      some (.ready (.reverseRow y ss rows cs (c :: out)),
        administrative VandermondeMachine.reverseCost)
  | .ready (.reverseRow y ss rows [] out) =>
      some (.ready (.pack y ss rows out), administrative VandermondeMachine.rowFinishCost)
  | .ready (.pack y ss rows cs) =>
      some (.ready (.save (cs, y) ss rows), administrative VandermondeMachine.packCost)
  | .ready (.save r ss rows) =>
      some (.ready (.scan ss (r :: rows)), administrative VandermondeMachine.saveCost + saveRoot)
  | .ready (.reverseRows (r :: rs) out) =>
      some (.ready (.reverseRows rs (r :: out)), administrative VandermondeMachine.reverseCost)
  | .ready (.reverseRows [] out) =>
      some (.ready (.emit out), administrative VandermondeMachine.finishCost)
  | .ready (.emit out) => some (.ready (.done out), administrative VandermondeMachine.emitCost)
  | .ready (.done _) => none
  | .call frame payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.call frame payload t, delegated c)
      | none => match s with
          | .done (.pair p) => some (resume frame p, returned)
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (L : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a L 0 s 0 s
  | cons {n s u t c d} (head : step a L s = some (u, c)) (tail : Trace a L n u d t) :
      Trace a L (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a L s = some (t, c)) : Trace a L 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {L n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a L n s c u) (h' : Trace a L m u d t) : Trace a L (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a L s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a L n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {L n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a L n s c t) : runFuel a L n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticVandermondeMachine
