/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.PhasedRun
import ArkLibTest.Interaction.Oracle.CoreRunExample

/-!
# Concrete phase and runtime correspondence

Both public ownership directions, a hidden oracle send, repeated setup queries, and a terminal
query have distinct action tags. Constant branches isolate scheduling from source arithmetic.
-/

namespace Interaction.Oracle.PhasedRunTest

open OracleComp OracleSpec

/-- World events carry tags and need no meaningful response. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Unit

/-- No input capabilities are needed by this scheduling producer. -/
abbrev initial : PFunctor := OracleSpec.toPFunctor (Empty →ₒ Unit)

/-- Both public sender directions precede one hidden send. -/
abbrev protocol : Oracle.Protocol :=
  .public .sender Bool fun _ => .public .receiver Bool fun _ =>
    .oracleWith Nat OracleInterface.instDefault .done

/-- Access after the one concrete send. -/
abbrev finalAccess := Access.extend initial (OracleInterface.instDefault (Message := Nat))

/-- Prover-local actions have tags 1, 4, and 5. -/
def prover : Prover.Strategy ambient protocol.tree protocol.roles (fun _ => Nat) := by
  change OracleComp ambient (Σ _ : Bool, Bool → OracleComp ambient
    (OracleComp ambient (Σ _ : Nat, Nat)))
  exact do
    let _ ← liftM (ambient.query 1)
    return ⟨true, fun (_ : Bool) => do
      let _ ← liftM (ambient.query 4)
      return (do
        let _ ← liftM (ambient.query 5)
        return ⟨17, 23⟩)⟩

/-- Verifier-local actions have tags 2, 3, 6, and terminal tag 7. -/
def verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
    (fun _ => Nat) := by
  change Bool → OracleComp (ambient + OracleSpec.ofPFunctor initial)
    (OracleComp (ambient + OracleSpec.ofPFunctor initial)
      (Σ _ : Bool, OracleComp (ambient + OracleSpec.ofPFunctor finalAccess)
        (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess) Nat)))
  exact fun _ => do
    let _ ← liftM ((ambient + OracleSpec.ofPFunctor initial).query (.inl 2))
    return (do
      let _ ← liftM ((ambient + OracleSpec.ofPFunctor initial).query (.inl 3))
      return ⟨false, do
        let _ ← liftM ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inl 6))
        return (do
          let _ ← liftM ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inl 7))
          return 31)⟩)

/-- Two equal setup queries precede all participant actions. -/
def reduction : Reduction ambient protocol initial Unit Unit (fun _ => Nat) (fun _ => Nat) where
  prover := fun _ _ => do
    let _ ← liftM (ambient.query 9)
    let _ ← liftM (ambient.query 9)
    return prover
  verifier := fun _ => verifier

/-- The persistent world state records chronological query digits. -/
private abbrev runtime : OracleRuntime (fun _ : Empty => Unit) ambient where
  State := Nat
  setup := pure 1
  handler := fun tag state => pure ((), state * 10 + tag + 1)

/-- Boundaries and owners are obtained from the produced run, not supplied by the observer. -/
def summary (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial
    (fun _ => Nat) (fun _ => Nat)) :=
  run.phases.map fun phase =>
    (phase.prefix.cursor.length, phase.party, phase.queries.map (·.1))

/-- A completed run cannot be relabeled by supplying a replacement role decoration. -/
example (_run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial
    (fun _ => Nat) (fun _ => Nat)) : True := by
  fail_if_success have := _run.phases protocol.roles
  trivial

/-- One shared state sees setup, both public roles, the oracle send, and terminal execution
in order. -/
example :
    (fun result => (summary result.output, result.state, result.trace.map (·.1))) <$>
      executePhasedWithRuntime runtime reduction Empty.elim () () =
    pure ([(0, .prover, [9, 9]), (0, .prover, [1]), (1, .verifier, [2]),
      (1, .verifier, [3]), (2, .prover, [4]), (2, .prover, [5]), (3, .verifier, [6]),
      (3, .verifier, [7])], 2102345678, [9, 9, 1, 2, 3, 4, 5, 6, 7]) := by
  rw [executePhasedWithRuntime, OracleRuntime.run_eq]
  simp only [runtime, pure_bind]
  have observation := runtime.runFrom_observe 1 (executePhased reduction Empty.elim () ())
  have projected := congrArg (fun program =>
    (fun result => (summary result.1, result.2.1, result.2.2.map (·.1))) <$> program) observation
  calc
    _ = (fun result => (summary result.1.1, result.2, result.1.2.map (·.1))) <$>
        runtime.handler.runState 1 (executePhased reduction Empty.elim () ()).withQueryLog := by
      simpa only [Functor.map_map] using projected
    _ = _ := by
      rfl

/-- A concrete observer answers each world query with its unique unit response. -/
def observed := simulateQ (fun _ => (pure () : Id Unit))
  (executePhased reduction Empty.elim () ())

/-- Repeated setup queries contribute twice under one fixed resource classification. -/
example : ((observed.phases[0]'(by decide)).queryProfile id).usage 9 = 2 := by
  classical
  change (ResourceProfile.single (ω := ℕ) 9 +
    (ResourceProfile.single (ω := ℕ) 9 + 0)).usage 9 = 2
  simp [ResourceProfile.single, ResourceProfile.ofUsage]

/-- The final prefix retains the concrete hidden payload. -/
example : (TypeTree.ExecutionPrefix.ofExecutionPath observed.execution.path).messages.1 = 17 := by
  rfl

namespace Closing

open CoreRunExample

/-- The terminal action queries the sent oracle before returning any explicit outcome. -/
def terminal (mode : Nat) :
    OracleComp (CoreRunExample.ambient + CoreRunExample.finalSpec)
      (Terminal (OpenClaim CoreRunExample.finalSpec Nat CoreRunExample.output) Nat) := do
  let _ ← liftM ((CoreRunExample.ambient + CoreRunExample.finalSpec).query (.inl 2))
  let sent : Nat ←
    liftM ((CoreRunExample.ambient + CoreRunExample.finalSpec).query (.inr (.inr ())))
  return match mode with
    | 0 => .reject
    | 1 => .fault 17
    | _ => .accept ⟨sent, CoreRunExample.outputOracle⟩

/-- Reception and the terminal action remain separate verifier phases. -/
def verifier (mode : Nat) : Verifier.Strategy CoreRunExample.ambient
    CoreRunExample.protocol.tree CoreRunExample.protocol.roles CoreRunExample.protocol.oracles
    CoreRunExample.input.toPFunctor
    (TerminalOutcome CoreRunExample.protocol CoreRunExample.input.toPFunctor
      (fun _ => Nat) (fun _ => CoreRunExample.output) Nat) := by
  change OracleComp (CoreRunExample.ambient + CoreRunExample.finalSpec)
    (OracleComp (CoreRunExample.ambient + CoreRunExample.finalSpec)
      (Terminal (OpenClaim CoreRunExample.finalSpec Nat CoreRunExample.output) Nat))
  exact do
    let _ ← liftM ((CoreRunExample.ambient + CoreRunExample.finalSpec).query (.inl 1))
    return terminal mode

/-- Setup, one oracle send, reception, and the terminal action all emit distinguishable events. -/
def reduction (mode : Nat) : Reduction CoreRunExample.ambient CoreRunExample.protocol
    CoreRunExample.input.toPFunctor Unit (Nat × Nat) (fun _ => Nat)
    (TerminalOutcome CoreRunExample.protocol CoreRunExample.input.toPFunctor
      (fun _ => Nat) (fun _ => CoreRunExample.output) Nat) where
  prover := fun _ witness => do
    let _ ← liftM (CoreRunExample.ambient.query 9)
    return CoreRunExample.prover witness.1 witness.2
  verifier := fun _ => verifier mode

/-- Run the phase producer under the noncommutative ambient logger. -/
def observed (mode old message hidden : Nat) :=
  (simulateQ CoreRunExample.logger
    (executePhased (reduction mode) (fun _ => old) () (message, hidden))).run []

/-- Read the ordered world regions directly from one completed phased artifact. -/
def worldTags (run : PhasedRun CoreRunExample.ambient CoreRunExample.protocol.tree
    CoreRunExample.protocol.roles CoreRunExample.protocol.oracles
    CoreRunExample.input.toPFunctor (fun _ => Nat)
    (TerminalOutcome CoreRunExample.protocol CoreRunExample.input.toPFunctor
      (fun _ => Nat) (fun _ => CoreRunExample.output) Nat)) :=
  run.phases.map fun phase => phase.queries.map (fun entry => entry.1)

/-- One artifact retains an input answer distinct from the sent answer, closes with both,
records the sent source observation, and keeps setup/send/receive/terminal world phases ordered. -/
example (hidden : Nat) :
    let result := observed 2 7 11 hidden
    let run := result.1
    (run.inputImpl (),
      run.terminalClosed.map fun claim => (claim.oracles ⟨(), ()⟩ : Nat),
      run.execution.sourceLog,
      worldTags run,
      result.2) =
    (7, .accept 18, [⟨Sum.inr (), (11 : Nat)⟩], [[9], [0], [1], [2]], [9, 0, 1, 2]) := by
  rfl

/-- Rejection remains explicit on a phased artifact. -/
example (hidden : Nat) : (observed 0 7 11 hidden).1.terminalClosed = .reject := by
  rfl

/-- A returned fault remains distinct from rejection on a phased artifact. -/
example (hidden : Nat) : (observed 1 7 11 hidden).1.terminalClosed = .fault 17 := by
  rfl

#print axioms executePhased_closed
#print axioms executePhased_terminalClosed

end Closing

end Interaction.Oracle.PhasedRunTest
