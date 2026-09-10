/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CandidateFilterSemantics
public import ArkLib.Data.QuadraticAlgebra.CoefficientDescentSemantics
/-!
# Raw-coordinate candidate descent and filtering

The descent cursor tests each imaginary coordinate and builds the base coefficient list one
cell at a time. The existing base-field filter then runs unchanged, with all child charges.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateCandidateMachine

namespace Descent

abbrev Cost := QuadraticAlgebra.ArithmeticMachine.Cost
abbrev charge := QuadraticAlgebra.CoefficientDescentMachine.charge

/-- Input coefficients remain shared; accepted scalar cells are allocated and reversed. -/
inductive Configuration (F : Type*)  where
  | start (coefficients : List (F × F))
  | scan (remaining : List (F × F)) (output : List F)
  | reverse (remaining output : List F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq

variable {F : Type*} [Zero F] [DecidableEq F]

/-- Each independent rule performs at most one base-field equality test. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | start {cs} : Step (.start cs) (charge 3 0 1 0) (.scan cs [])
  | accepted {x xs out} (h : x.2 = 0) :
      Step (.scan (x :: xs) out) (charge 6 1 0 0) (.scan xs (x.1 :: out))
  | rejected {x xs out} (h : x.2 ≠ 0) :
      Step (.scan (x :: xs) out) (charge 3 1 0 0) (.emit none)
  | finish {out} : Step (.scan [] out) (charge 3 0 0 0) (.reverse out [])
  | reverse {x xs out} : Step (.reverse (x :: xs) out) (charge 5 0 0 0)
      (.reverse xs (x :: out))
  | reversed {out} : Step (.reverse [] out) (charge 2 0 0 0) (.emit (some out))
  | emit {out} : Step (.emit out) (charge 2 0 0 1) (.done out)

/-- One cursor or output instruction; no full-list test or conversion is hidden. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .start cs => some (.scan cs [], charge 3 0 1 0)
  | .scan [] out => some (.reverse out [], charge 3 0 0 0)
  | .scan (x :: xs) out => if x.2 = 0 then
      some (.scan xs (x.1 :: out), charge 6 1 0 0)
      else some (.emit none, charge 3 1 0 0)
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), charge 5 0 0 0)
  | .reverse [] out => some (.emit (some out), charge 2 0 0 0)
  | .emit out => some (.done out, charge 2 0 0 1)
  | .done _ => none

end Descent

namespace Filter
export CandidateFilterMachine (Configuration step)
end Filter

/-- Each suspended callee retains its actual state. -/
inductive Configuration (F : Type*)  where
  | start (coefficients : List (F × F))
  | descent (inner : Descent.Configuration F)
  | filter (inner : Filter.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- One nested step or one local handoff, never an entire uncharged subroutine. -/
def step (w k A : ℕ) (rows : List (F × F)) :
    Configuration F → Option (Configuration F × ℕ)
  | .start cs => some (.descent (.start cs), 4)
  | .descent s => match Descent.step s with
      | some (t, c) => some (.descent t, c.total + 3)
      | none => match s with
          | .done none => some (.emit none, 3)
          | .done (some cs) => some (.filter (.start cs), 4)
          | _ => none
  | .filter s => match Filter.step w k A rows s with
      | some (t, c) => some (.filter t, c + 3)
      | none => match s with
          | .done out => some (.emit out, 3)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- Actual executable edges with their scalar-total ledger. -/
inductive Trace (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace w k A rows 0 s 0 s
  | cons {n s t u c d} (head : step w k A rows s = some (t, c))
      (tail : Trace w k A rows n t d u) : Trace w k A rows (n + 1) s (c + d) u

/-- Host fuel exposes the actual partial state and accumulated charges. -/
def runFuel (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step w k A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel w k A rows n t; (r.1, c + r.2)

/-- A trace determines the same execution, including its exact ledger. -/
theorem Trace.runFuel_eq {w k A n : ℕ} {rows : List (F × F)}
    {s t : Configuration F} {c : ℕ} (h : Trace w k A rows n s c t) :
    runFuel w k A rows n s = (t, c) := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.ListDecoding.CoordinateCandidateMachine
