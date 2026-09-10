/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotSolveMachine
public import ArkLib.Data.Matrix.QuadraticPivotMachine

/-!
# Coordinate correction of one pivot value

The complete row dot product includes the current pivot value. Retained arithmetic inputs
compute its product/sum, pivot test/inverse, RHS difference, scale and additive correction.
Indexed traversal and restoration preserve every other supplied coordinate. Scalar returns
and output-cell allocation are explicit. The caller supplies the initial dot accumulator;
its initialization, input materialization, host fuel and bit time are outside this ledger.
-/

@[expose] public section

namespace Matrix.QuadraticPivotSolveMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Row (F : Type*) := PivotSolveMachine.Row (Pair F)
abbrev administrative := QuadraticPivotMachine.administrative
abbrev launch := QuadraticPivotMachine.launch
abbrev zeroSeed := QuadraticPivotMachine.zeroSeed
abbrev returned := QuadraticPivotMachine.returned

/-- Immutable input handles retained for the entire pivot correction. -/
structure Input (F : Type*) where
  parameter : F
  row : Row F
  index : ℕ
  values : List (Pair F)

/-- One additional cell-slot/root write supplements source allocation. -/
def allocation : Cost := ⟨{ data := 1 }, 0⟩

inductive Continuation (F : Type*) where
  | dotProduct (coefficients values : List (Pair F)) (sum : Pair F)
  | dotSum (coefficients values : List (Pair F))
  | check (pivot sum : Pair F)
  | inverse (sum : Pair F)
  | negative (inverse : Pair F)
  | difference (inverse : Pair F)
  | scale
  | update (saved tail : List (Pair F))

inductive Configuration (F : Type*) where
  | ready (state : PivotSolveMachine.Configuration (Pair F))
  | arithmetic (cont : Continuation F) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | addDot (coefficients values : List (Pair F)) (sum product : Pair F)
  | saveUpdate (saved tail : List (Pair F)) (value : Pair F)

/-- Only actual child results are installed; no arithmetic is recomputed on return. -/
def resume {F : Type*} (input : Input F) : Continuation F → ArithmeticMachine.Result F →
    Option (Configuration F × Cost)
  | .dotProduct cs vs s, .pair p => some (.addDot cs vs s p, returned)
  | .dotSum cs vs, .pair s => some (.ready (.dot cs vs s), returned)
  | .check p s, .boolean b =>
      if b then some (.ready .rejected, administrative PivotSolveMachine.zeroCost + returned)
      else some (.ready (.inverse p s), administrative PivotSolveMachine.checkCost + returned)
  | .inverse s, .pair inv => some (.ready (.negate inv s), returned)
  | .negative inv, .pair neg => some (.ready (.difference inv neg), returned)
  | .difference inv, .pair d => some (.ready (.scale inv d), returned)
  | .scale, .pair d => some (.ready (.update input.values input.index [] d), returned)
  | .update rev xs, .pair x => some (.saveUpdate rev xs x, returned)
  | _, _ => none

variable {F : Type*} [Field F] [DecidableEq F]

/-- One retained base instruction or one explicit local traversal/allocation transition. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.dot (x :: xs) (y :: ys) s) =>
      some (.arithmetic (.dotProduct xs ys s) ⟨input.parameter, x, y⟩ (.start .mul),
        administrative PivotSolveMachine.dotCost + launch)
  | .addDot xs ys s p =>
      some (.arithmetic (.dotSum xs ys) ⟨input.parameter, s, p⟩ (.start .add), launch)
  | .ready (.dot [] [] s) =>
      some (.ready (.lookup input.row.1 input.index s),
        administrative PivotSolveMachine.lookupStartCost)
  | .ready (.dot [] (_ :: _) _) | .ready (.dot (_ :: _) [] _) =>
      some (.ready .rejected, administrative PivotSolveMachine.rejectCost)
  | .ready (.lookup (_ :: xs) (i + 1) s) =>
      some (.ready (.lookup xs i s), administrative PivotSolveMachine.seekCost)
  | .ready (.lookup (x :: _) 0 s) =>
      some (.ready (.check x s), administrative PivotSolveMachine.hitCost)
  | .ready (.lookup [] _ _) | .ready (.update [] _ _ _) =>
      some (.ready .rejected, administrative PivotSolveMachine.rejectCost)
  | .ready (.check p s) =>
      some (.arithmetic (.check p s) ⟨input.parameter, p, (0, 0)⟩ (.start .equal),
        launch + zeroSeed)
  | .ready (.inverse p s) =>
      some (.arithmetic (.inverse s) ⟨input.parameter, p, p⟩ (.start .inv),
        administrative PivotSolveMachine.inverseCost + launch)
  | .ready (.negate inv s) =>
      some (.arithmetic (.negative inv) ⟨input.parameter, s, s⟩ (.start .neg),
        administrative PivotSolveMachine.negateCost + launch)
  | .ready (.difference inv neg) =>
      some (.arithmetic (.difference inv) ⟨input.parameter, input.row.2, neg⟩ (.start .add),
        administrative PivotSolveMachine.addCost + launch)
  | .ready (.scale inv d) =>
      some (.arithmetic .scale ⟨input.parameter, d, inv⟩ (.start .mul),
        administrative PivotSolveMachine.scaleCost + launch)
  | .ready (.update (x :: xs) (i + 1) rev d) =>
      some (.ready (.update xs i (x :: rev) d),
        administrative PivotSolveMachine.updateSeekCost + allocation)
  | .ready (.update (x :: xs) 0 rev d) =>
      some (.arithmetic (.update rev xs) ⟨input.parameter, x, d⟩ (.start .add), launch)
  | .saveUpdate rev xs x => some (.ready (.restore rev (x :: xs)),
      administrative PivotSolveMachine.updateHitCost + allocation)
  | .ready (.restore (x :: xs) out) =>
      some (.ready (.restore xs (x :: out)),
        administrative PivotSolveMachine.reverseCost + allocation)
  | .ready (.restore [] out) =>
      some (.ready (.done out), administrative PivotSolveMachine.emitCost)
  | .ready (.done _) | .ready .rejected => none
  | .arithmetic cont payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.arithmetic cont payload t, delegated c)
      | none => match s with
          | .done r => resume input cont r
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (input : Input F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : step input s = some (u, c)) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Trace input 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace input n s c u) (h' : Trace input m u d t) :
    Trace input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel input n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {input : Input F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace input n s c t) : runFuel input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticPivotSolveMachine
