/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardMachine
/-!
# Execution and cost of the canonical guard

The bound sums the costs of the actual identity-check programs for the supplied equations and
one actual ordered-witness program. Failure may stop early. No chain correctness or assumed
cost of an evaluator is needed for this execution theorem; polynomial representation and
chain uniqueness are separate semantic obligations.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalGuardMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Proof-only final test; executable dispatch tests the returned scalar after witness search. -/
def witnessSpec (input : Input F) : Bool :=
  decide (ResidualWitnessMachine.result (residualInput input input.separant) input.samples =
    some input.center)

/-- Proof-only short-circuit specification of all previous identity checks and center selection. -/
def result (input : Input F) : List (Equation F) → Bool
  | [] => witnessSpec input
  | q :: ps => if ResidualZeroMachine.result (residualInput input q) input.samples
      then result input ps else false

/-- The actual residual-zero program's proved upper bound, without any evaluator-cost premise. -/
def zeroWork (input : Input F) (q : Equation F) : ℕ :=
  let i := residualInput input q
  (ResidualBatchMachine.cost i input.samples.length).total +
    3 * ResidualBatchMachine.fuel i input.samples.length + 6 * input.samples.length + 15

/-- Fuel for the final ordered witness and scalar equality, including its output. -/
def witnessFuel (input : Input F) : ℕ :=
  ResidualWitnessMachine.fuel (residualInput input input.separant) input.samples.length + 2

/-- All witness-program charges, its wrappers, the scalar equality and Boolean emission. -/
def witnessWork (input : Input F) : ℕ :=
  ResidualWitnessMachine.workBound (residualInput input input.separant) input.samples.length +
    3 * ResidualWitnessMachine.fuel (residualInput input input.separant) input.samples.length + 12

/-- Fuel for all supplied previous equations; exhaustion initializes the witness search. -/
def scanFuel (input : Input F) : List (Equation F) → ℕ
  | [] => witnessFuel input + 1
  | q :: ps => ResidualZeroMachine.fuel (residualInput input q) input.samples.length +
      scanFuel input ps + 2

/-- The work ledger includes every potential identity checker, wrapper and cursor transition. -/
def scanWork (input : Input F) : List (Equation F) → ℕ
  | [] => witnessWork input + 6
  | q :: ps => zeroWork input q +
      3 * ResidualZeroMachine.fuel (residualInput input q) input.samples.length +
        scanWork input ps + 9

/-- Uniform fuel for the closed guard, including initial input access. -/
def fuel (input : Input F) (ps : List (Equation F)) : ℕ := scanFuel input ps + 1
/-- Uniform same-execution work bound; the scan's exact subroutine sum remains explicit. -/
def workBound (input : Input F) (ps : List (Equation F)) : ℕ := scanWork input ps + 4

/-- Actual witness execution is followed by exactly the returned-scalar comparison. -/
theorem witness_trace (input : Input F) :
    ∃ n c, Trace input n (.witness (.start input.samples)) c (.done (witnessSpec input)) ∧
      n ≤ witnessFuel input ∧ c ≤ witnessWork input := by
  let i := residualInput input input.separant
  obtain ⟨c, hr, hc⟩ := ResidualWitnessMachine.witness_runFuel i input.samples
  obtain ⟨n, hn, ht⟩ := ResidualWitnessMachine.runFuel_refines i
    (ResidualWitnessMachine.fuel i input.samples.length) (.start input.samples)
  rw [hr] at ht
  cases ho : ResidualWitnessMachine.result i input.samples with
  | none =>
      dsimp only [i] at ho
      rw [ho] at ht
      have htrace := (lift_witness input ht).trans
        (Trace.cons Step.absent (Trace.cons Step.emit (Trace.nil _)))
      refine ⟨n + 2, c.total + 3 * n + 7, ?_, ?_, ?_⟩
      · simpa [witnessSpec, ho] using htrace
      · dsimp [witnessFuel, i] at *; omega
      · dsimp [witnessWork, i] at *; omega
  | some u =>
      dsimp only [i] at ho
      rw [ho] at ht
      have htrace := (lift_witness input ht).trans
        (Trace.cons Step.selected (Trace.cons Step.emit (Trace.nil _)))
      refine ⟨n + 2, c.total + 3 * n + 12, ?_, ?_, ?_⟩
      · simpa [witnessSpec, ho] using htrace
      · dsimp [witnessFuel, i] at *; omega
      · dsimp [witnessWork, i] at *; omega

omit [DecidableEq F] in
private theorem scanFuel_pos (input : Input F) (ps : List (Equation F)) :
    0 < scanFuel input ps := by
  cases ps <;> simp only [scanFuel] <;> omega

omit [DecidableEq F] in
private theorem scanWork_ge_four (input : Input F) (ps : List (Equation F)) :
    4 ≤ scanWork input ps := by
  cases ps <;> simp only [scanWork] <;> omega

/-- The closed scan executes all necessary earlier-identity tests before accepting a center. -/
theorem scan_trace (input : Input F) (ps : List (Equation F)) :
    ∃ n c, Trace input n (.scan ps) c (.done (result input ps)) ∧
      n ≤ scanFuel input ps ∧ c ≤ scanWork input ps := by
  induction ps with
  | nil =>
      obtain ⟨n, c, ht, hn, hc⟩ := witness_trace input
      exact ⟨n + 1, 6 + c, Trace.cons Step.empty ht,
        by dsimp [scanFuel]; omega, by dsimp [scanWork]; omega⟩
  | cons q ps ih =>
      let i := residualInput input q
      have hr := ResidualZeroMachine.zero_runFuel i input.samples
      have hc := ResidualZeroMachine.cost_total_le i input.samples
      change (ResidualZeroMachine.cost i input.samples).total ≤ zeroWork input q at hc
      obtain ⟨n, hn, ht⟩ := ResidualZeroMachine.runFuel_refines i
        (ResidualZeroMachine.fuel i input.samples.length) (.start input.samples)
      rw [hr] at ht
      cases ho : ResidualZeroMachine.result i input.samples with
      | false =>
          dsimp only [i] at ho
          rw [ho] at ht
          have htrace := Trace.cons Step.take ((lift_zero input q ps ht).trans
            (Trace.cons Step.failed (Trace.cons Step.emit (Trace.nil _))))
          refine ⟨n + 3, 6 + ((ResidualZeroMachine.cost i input.samples).total + 3 * n + 7),
            ?_, ?_, ?_⟩
          · simpa only [result, ho, Bool.false_eq_true, ↓reduceIte] using htrace
          · have hpos := scanFuel_pos input ps
            dsimp [scanFuel, i] at *
            omega
          · have hpos := scanWork_ge_four input ps
            dsimp only [scanWork]
            change 6 + ((ResidualZeroMachine.cost i input.samples).total + 3 * n +
              (3 + (4 + 0))) ≤ _
            dsimp only [i] at *
            omega
      | true =>
          dsimp only [i] at ho
          rw [ho] at ht
          obtain ⟨n', c', ht', hn', hc'⟩ := ih
          have htrace := Trace.cons Step.take ((lift_zero input q ps ht).trans
            (Trace.cons Step.passed ht'))
          refine ⟨n + (n' + 1) + 1,
            6 + ((ResidualZeroMachine.cost i input.samples).total + 3 * n + (3 + c')),
            ?_, ?_, ?_⟩
          · simpa only [result, ho, ↓reduceIte] using htrace
          · dsimp [scanFuel, i] at *
            omega
          · dsimp only [scanWork]
            dsimp only [i] at *
            omega

/-- A single closed execution returns the exact guard result with its accumulated work bound. -/
theorem evaluation_runFuel (input : Input F) (ps : List (Equation F)) :
    ∃ c, runFuel input (fuel input ps) (.start ps) = (.done (result input ps), c) ∧
      c ≤ workBound input ps := by
  obtain ⟨n, c, ht, hn, hc⟩ := scan_trace input ps
  have ht' := Trace.cons Step.start ht
  have hle : n + 1 ≤ fuel input ps := by dsimp [fuel]; omega
  have hr := ht'.runFuel_done (fuel input ps - (n + 1))
  rw [Nat.add_sub_of_le hle] at hr
  exact ⟨4 + c, hr, by dsimp [workBound]; omega⟩

end ReedSolomon.HiddenDerivative.CanonicalGuardMachine
