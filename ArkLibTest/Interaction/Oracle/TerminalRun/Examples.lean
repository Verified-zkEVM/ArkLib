/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.TerminalRun
import ArkLibTest.Interaction.Oracle.CoreRunExample

/-!
# Executing returned terminal outcomes

The same protocol queries its sent oracle before accepting, rejecting, or returning either of two
faults. Producer tests retain prior effects and source observations in every case, and close two
accepting executions with their own distinct input/message pairs.
-/

namespace Interaction.Oracle.TerminalRunExample

open OracleComp OracleSpec CoreRunExample

/-- The terminal action has effects before deciding its returned outcome. -/
def terminal (mode : Nat) :
    OracleComp (ambient + finalSpec) (Terminal (OpenClaim finalSpec Nat output) Nat) := do
  let _ ← liftM ((ambient + finalSpec).query (.inl 2))
  let sent : Nat ← liftM ((ambient + finalSpec).query (.inr (.inr ())))
  return match mode with
    | 0 => .reject
    | 1 => .fault 17
    | 2 => .fault 23
    | _ => .accept ⟨sent, outputOracle⟩

/-- Query access is still extended only after the oracle receive. -/
def verifier (mode : Nat) : Verifier.Strategy ambient protocol.tree protocol.roles
    protocol.oracles input.toPFunctor
    (TerminalOutcome protocol input.toPFunctor (fun _ => Nat) (fun _ => output) Nat) := by
  change OracleComp (ambient + finalSpec)
    (OracleComp (ambient + finalSpec) (Terminal (OpenClaim finalSpec Nat output) Nat))
  exact do
    let _ ← liftM ((ambient + finalSpec).query (.inl 1))
    return terminal mode

/-- Setup effects distinguish the wrapper from calling just its strategy runner. -/
def reduction (mode : Nat) : Reduction ambient protocol input.toPFunctor Unit (Nat × Nat)
    (fun _ => Nat)
    (TerminalOutcome protocol input.toPFunctor (fun _ => Nat) (fun _ => output) Nat) where
  prover := fun _ witness => do
    let _ ← liftM (ambient.query 9)
    return CoreRunExample.prover witness.1 witness.2
  verifier := fun _ => verifier mode

/-- Observe actual execution under the noncommutative ambient logger. -/
def observed (mode old message hidden : Nat) :=
  (simulateQ logger
    (executeTerminal (reduction mode) (fun _ => old) () (message, hidden))).run []

/-- Faults do not erase setup, send, receive, or terminal effects that already occurred. -/
example (hidden : Nat) : (observed 1 7 11 hidden).2 = [9, 0, 1, 2] := rfl

/-- A returned fault retains the terminal source observation and private output. -/
example (hidden : Nat) :
    ((observed 1 7 11 hidden).1.result.proverOut,
      (observed 1 7 11 hidden).1.result.sourceLog) =
      (hidden, [⟨Sum.inr (), (11 : Nat)⟩]) := rfl

/-- Fault labels survive closing separately. -/
example (hidden : Nat) : (observed 1 7 11 hidden).1.closed = .fault 17 := rfl

example (hidden : Nat) : (observed 2 7 11 hidden).1.closed = .fault 23 := rfl

/-- Verifier rejection remains a returned result and retains the already recorded query. -/
example (hidden : Nat) :
    ((observed 0 7 19 hidden).1.closed,
      (observed 0 7 19 hidden).1.verifierLocalView.2.1) =
      (.reject, [⟨Sum.inr (), (19 : Nat)⟩]) := rfl

/-- Accepted virtual output queries use this run's input and message. -/
example (hidden : Nat) :
    ((observed 3 7 11 hidden).1.closed.map fun claim => claim.oracles ⟨(), ()⟩) =
      .accept (18 : Nat) := rfl

/-- A second execution must not reuse either resource from the first. -/
example (hidden : Nat) :
    ((observed 3 13 19 hidden).1.closed.map fun claim => claim.oracles ⟨(), ()⟩) =
      .accept (32 : Nat) := rfl

#print axioms executeTerminal_erase
#print axioms TerminalRun.closed_of_ofOption

end Interaction.Oracle.TerminalRunExample
