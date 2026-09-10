/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetPreparationMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine
/-!
# Coordinate jet preparation

The cursor reverses the supplied jet and pads each missing entry with an explicitly materialized
pair of base zeros. Both zero literals and pair slots are charged. Capacity failure and tagged
output remain executable branches; no length, reversal or padding specification runs here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticJetPreparationMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Configuration (F : Type*) := JetPreparationMachine.Configuration (Pair F)

/-- Preserve all scalar-free source work; each source zero becomes two base literals. -/
def administrative (c : JetPreparationMachine.Cost) : Cost :=
  ⟨{ control := c.machine.control, data := c.machine.data + 2 * c.constants,
     constants := 2 * c.constants, output := c.machine.output }, c.machine.natural⟩
/-- The success option has its own materialized root. -/
def allocation : Cost := ⟨{ data := 1 }, 0⟩

variable {F : Type*} [Zero F]

/-- One cursor transition, including concrete base-zero construction. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .start D bs => some (.scan (D + 1) bs [], administrative JetPreparationMachine.startCost)
  | .scan n [] rev => some (.pad n rev, administrative JetPreparationMachine.padStartCost)
  | .scan 0 (_ :: _) _ => some (.emit none, administrative JetPreparationMachine.rejectCost)
  | .scan (n + 1) (b :: bs) rev =>
      some (.scan n bs (b :: rev), administrative JetPreparationMachine.takeCost)
  | .pad (n + 1) out =>
      some (.pad n ((0, 0) :: out), administrative JetPreparationMachine.padCost)
  | .pad 0 out =>
      some (.emit (some out), administrative JetPreparationMachine.padDoneCost + allocation)
  | .emit out => some (.done out, administrative JetPreparationMachine.emitCost)
  | .done _ => none

/-- Concrete edges with their complete charge. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : step s = some (u, c)) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

/-- Execute one concrete edge. -/
theorem single {s t : Configuration F} {c : Cost} (h : step s = some (t, c)) :
    Trace 1 s c t := by simpa using Trace.cons h (Trace.nil t)

/-- Concatenate executions, preserving the ledger. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace n s c u) (h' : Trace m u d t) : Trace (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exhaustion exposes the partial cursor and accumulated work. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel n t; (r.1, c + r.2)

/-- Exact trace fuel recovers its endpoint and cost. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace n s c t) : runFuel n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticJetPreparationMachine
