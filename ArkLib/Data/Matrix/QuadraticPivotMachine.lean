/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotEliminationMachine
public import ArkLib.Data.Matrix.QuadraticRowMachine

/-!
# Coordinate pivot elimination

Lookup retains both original rows. Equality, inversion, negation and factor multiplication run
actual base instructions with inputs stored once. The resulting factor drives the actual
coordinate row machine, including reversal and rejection. Packed RHS entries are ordinary row
entries and receive the same arithmetic; their packing belongs to the augmented-column caller.

Every child step retains its ledger and pays a wrapper dispatch and two root accesses. The zero
comparison allocates its two-coordinate literal explicitly. Costs include returns and output;
input preparation, host fuel, reclamation and compiled/bit time remain outside this model.
-/

@[expose] public section

namespace Matrix.QuadraticPivotMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F

/-- Retain source administrative and natural operations without abstract scalar operations. -/
def administrative (c : PivotEliminationMachine.Cost) : Cost :=
  ⟨{ control := c.row.control, data := c.row.data, output := c.row.output }, c.natural⟩
/-- Read and store parameter and two operand handles once. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Write the coordinate zero's two slots and two constants. -/
def zeroSeed : Cost := ⟨{ data := 2, constants := 2 }, 0⟩
/-- Read a child result and restore the suspended scalar register. -/
def returned : Cost := ⟨{ control := 1, data := 3 }, 0⟩
/-- One parent dispatch and child-root read/write for a coordinate row instruction. -/
def rowWrapper : Cost := ⟨{ control := 1, data := 2 }, 0⟩

/-- Fixed return destinations share unchanged row lists and scalar registers. -/
inductive Continuation (F : Type*) where
  | check (pivot target : List (Pair F)) (entry value : Pair F)
  | inverse (pivot target : List (Pair F)) (value : Pair F)
  | negative (pivot target : List (Pair F)) (inverse : Pair F)
  | factor (pivot target : List (Pair F))

inductive Configuration (F : Type*) where
  | ready (state : PivotEliminationMachine.Configuration (Pair F))
  | arithmetic (cont : Continuation F) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | row (factor : Pair F) (state : QuadraticRowMachine.Configuration F)

/-- Source row states enter the actual coordinate row interpreter directly. -/
def enter {F : Type*} : PivotEliminationMachine.Configuration (Pair F) → Configuration F
  | .row factor s => .row factor (.ready s)
  | s => .ready s

/-- Consume an actual child output; no operation is recomputed on return. -/
def resume {F : Type*} : Continuation F → ArithmeticMachine.Result F →
    Option (Configuration F × Cost)
  | .check p t x e, .boolean b =>
      if b then some (.ready .rejected, administrative PivotEliminationMachine.zeroCost + returned)
      else some (.ready (.inverse p t x e),
        administrative PivotEliminationMachine.checkCost + returned)
  | .inverse p t e, .pair inv => some (.ready (.negate p t e inv), returned)
  | .negative p t inv, .pair neg => some (.ready (.factor p t neg inv), returned)
  | .factor p t, .pair factor => some (.row factor (.ready (.scan t p [])), returned)
  | _, _ => none

variable {F : Type*} [Field F] [DecidableEq F]

/-- Each dispatch performs one local transition or one actual child instruction. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.lookup _ _ [] _ _) | .ready (.lookup _ _ (_ :: _) [] _) =>
      some (.ready .rejected, administrative PivotEliminationMachine.missingCost)
  | .ready (.lookup p t (x :: _) (y :: _) 0) =>
      some (.ready (.check p t x y), administrative PivotEliminationMachine.hitCost)
  | .ready (.lookup p t (_ :: xs) (_ :: ys) (i + 1)) =>
      some (.ready (.lookup p t xs ys i), administrative PivotEliminationMachine.seekCost)
  | .ready (.check p t x e) =>
      some (.arithmetic (.check p t x e) ⟨a, x, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.inverse p t x e) =>
      some (.arithmetic (.inverse p t e) ⟨a, x, x⟩ (.start .inv),
        administrative PivotEliminationMachine.inverseCost + launch)
  | .ready (.negate p t e inv) =>
      some (.arithmetic (.negative p t inv) ⟨a, e, e⟩ (.start .neg),
        administrative PivotEliminationMachine.negateCost + launch)
  | .ready (.factor p t neg inv) =>
      some (.arithmetic (.factor p t) ⟨a, neg, inv⟩ (.start .mul),
        administrative PivotEliminationMachine.factorCost + launch)
  | .ready (.row factor s) => some (.row factor (.ready s), rowWrapper)
  | .ready (.done _) | .ready .rejected => none
  | .arithmetic cont payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.arithmetic cont payload t, delegated c)
      | none => match s with
          | .done r => resume cont r
          | _ => none
  | .row factor s => match QuadraticRowMachine.step a factor s with
      | some (t, c) => some (.row factor t, c + rowWrapper)
      | none => match s with
          | .ready (.done out) =>
              some (.ready (.done out), administrative PivotEliminationMachine.returnCost)
          | .ready .rejected =>
              some (.ready .rejected, administrative PivotEliminationMachine.returnCost)
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a 0 s 0 s
  | cons {n s u t c d} (head : step a s = some (u, c)) (tail : Trace a n u d t) :
      Trace a (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {s t : Configuration F} {c : Cost}
    (h : step a s = some (t, c)) : Trace a 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a n s c u) (h' : Trace a m u d t) :
    Trace a (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a n s c t) : runFuel a n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticPivotMachine
