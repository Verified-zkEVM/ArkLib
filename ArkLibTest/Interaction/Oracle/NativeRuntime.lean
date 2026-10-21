/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.PhasedRun
import ArkLib.Interaction.Oracle.SourceRouting

/-!
# Native strategies share one persistent runtime

An ambient counter is queried by reduction setup, the prefix, and the suffix. The native prover
uses returned answers as its messages, and its private output depends on the first actual message.
-/

namespace Interaction.Oracle.NativeRuntimeTest

open OracleComp OracleSpec

/-- Tagged counter requests return the incremented count. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- No imported source is needed. -/
abbrev initial : PFunctor := OracleSpec.toPFunctor (Empty →ₒ Unit)

/-- Two sends provide a prefix and a suffix for one native strategy. -/
abbrev protocol : Oracle.Protocol :=
  .oracleWith Nat OracleInterface.instDefault <|
    .oracleWith Nat OracleInterface.instDefault .done

/-- Final source signature after both sends. -/
abbrev finalAccess := Access.extend
  (Access.extend initial (OracleInterface.instDefault (Message := Nat)))
  (OracleInterface.instDefault (Message := Nat))

/-- A private witness whose type depends on the concrete first message. -/
abbrev privateOutput (path : protocol.tree.ExecutionPath) := Fin (Nat.succ (show Nat from path.1))

/-- A terminal family with no output capabilities. -/
abbrev output : OracleFamily Empty (fun _ => Unit) := ⟨Empty.elim⟩

/-- A native prover asks the same counter in both fragments, without seeing its hidden state. -/
def prover : Prover.Strategy ambient protocol.tree protocol.roles privateOutput := do
  let first : Nat ← liftM (ambient.query 1)
  return ⟨first, do
    let second : Nat ← liftM (ambient.query 2)
    return ⟨second, ⟨0, Nat.zero_lt_succ first⟩⟩⟩

/-- The verifier queries both actual sends in order at the terminal leaf. -/
def verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
    (TerminalClaim protocol initial (fun _ => Nat × Nat) (fun _ => output)) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor
    (Access.extend initial (OracleInterface.instDefault (Message := Nat))))
    (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess)
      (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess)
        (Option (OpenClaim (OracleSpec.ofPFunctor finalAccess) (Nat × Nat) output))))
  exact pure (pure (do
    let first : Nat ← liftM
      ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inl (.inr ()))))
    let second : Nat ← liftM
      ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inr ())))
    return some ⟨(first, second), ⟨fun query => Empty.elim query.1⟩⟩))

/-- Setup makes one observable counter request before supplying the unchanged native strategy. -/
def reduction : Reduction ambient protocol initial Unit Unit privateOutput
    (TerminalClaim protocol initial (fun _ => Nat × Nat) (fun _ => output)) where
  prover := fun _ _ => do
    let _ : Nat ← liftM (ambient.query 0)
    return prover
  verifier := fun _ => verifier

/-- Both fragments and reduction setup share the same persistent counter. -/
private abbrev runtime : OracleRuntime (fun _ : Empty => Unit) ambient where
  State := Nat
  setup := pure 0
  handler := fun _ count => pure (count + 1, count + 1)

/-- Setup, prefix, and suffix run once in chronological order. Both source answers are retained. -/
example :
    (fun result =>
      (result.output.core.closed.map (·.stmt), result.output.core.proverOut.val,
        (result.output.sourceLog : QueryLog (OracleSpec.ofPFunctor finalAccess)),
        result.state, result.trace)) <$>
      executeWithRuntime runtime reduction Empty.elim () () =
    pure (some (2, 3), 0,
      [⟨Sum.inl (Sum.inr ()), (2 : Nat)⟩, ⟨Sum.inr (), (3 : Nat)⟩],
      3, [⟨0, (1 : Nat)⟩, ⟨1, (2 : Nat)⟩, ⟨2, (3 : Nat)⟩]) := by
  rw [executeWithRuntime_eq, OracleRuntime.run_eq]
  simp only [runtime, pure_bind]
  have observation := runtime.runFrom_observe 0 (executeLogged reduction Empty.elim () ())
  have projected := congrArg (fun program =>
    (fun result =>
      (result.1.core.closed.map (·.stmt), result.1.core.proverOut.val,
        (result.1.sourceLog : QueryLog (OracleSpec.ofPFunctor finalAccess)),
        result.2.1, result.2.2)) <$> program) observation
  calc
    _ = (fun result =>
        (result.1.1.core.closed.map (·.stmt), result.1.1.core.proverOut.val,
          (result.1.1.sourceLog : QueryLog (OracleSpec.ofPFunctor finalAccess)),
          result.2, result.1.2)) <$>
        runtime.handler.runState 0 (executeLogged reduction Empty.elim () ()).withQueryLog := by
      simpa only [Functor.map_map] using projected
    _ = _ := by rfl

/-- Direct native execution uses the same stateful runner and retains its actual final state. -/
example :
    (fun result => (result.output.core.closed.map (·.stmt), result.state, result.trace)) <$>
      executeStrategiesWithRuntime runtime Empty.elim prover verifier =
    pure (some (1, 2), 2, [⟨1, (1 : Nat)⟩, ⟨2, (2 : Nat)⟩]) := by
  rw [executeStrategiesWithRuntime_eq, OracleRuntime.run_eq]
  simp only [runtime, pure_bind]
  have observation := runtime.runFrom_observe 0
    (executeStrategiesLoggedRun Empty.elim prover verifier)
  have projected := congrArg (fun program =>
    (fun result => (result.1.core.closed.map (·.stmt), result.2.1, result.2.2)) <$> program)
    observation
  calc
    _ = (fun result => (result.1.1.core.closed.map (·.stmt), result.2, result.1.2)) <$>
        runtime.handler.runState 0
          (executeStrategiesLoggedRun Empty.elim prover verifier).withQueryLog := by
      simpa only [Functor.map_map] using projected
    _ = _ := by rfl

/-- The direct phased adapter shares all observations and final state with the direct logged run. -/
example :
    (fun result => ((result.output.execution.sourceLog : QueryLog (ofPFunctor finalAccess)),
        result.output.worldTrace, result.state)) <$>
      executeStrategiesPhasedWithRuntime runtime Empty.elim prover verifier =
    pure ([⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩, ⟨Sum.inr (), (2 : Nat)⟩],
      [⟨1, (1 : Nat)⟩, ⟨2, (2 : Nat)⟩], 2) := by
  unfold executeStrategiesPhasedWithRuntime
  rw [OracleRuntime.run_eq]
  simp only [runtime, pure_bind]
  have erased := runtime.runFrom_eraseTrace 0
    (executePhases ambient protocol.tree protocol.roles protocol.oracles initial Empty.elim
      (pure prover) verifier)
  have projected := congrArg (fun program =>
    (fun result => ((result.1.execution.sourceLog : QueryLog (ofPFunctor finalAccess)),
      result.1.worldTrace, result.2)) <$> program)
    erased
  calc
    _ = (fun result => ((result.1.execution.sourceLog : QueryLog (ofPFunctor finalAccess)),
      result.1.worldTrace, result.2)) <$>
        runtime.handler.runState 0
          (executePhases ambient protocol.tree protocol.roles protocol.oracles initial Empty.elim
            (pure prover) verifier) := by
      simpa only [Functor.map_map] using projected
    _ = _ := by rfl

namespace Expanded

open PFunctor.FreeM.Displayed (Decoration)

/-- One input answer and two observable sent messages form the raw source signature. -/
abbrev inputSpec : OracleSpec Unit := Unit →ₒ Nat

def inputImpl : QueryImpl (ofPFunctor inputSpec.toPFunctor) Id := fun _ => 7
abbrev firstProtocol : Protocol := .oracleWith Nat OracleInterface.instDefault .done
abbrev secondProtocol : Protocol := .oracleWith Nat OracleInterface.instDefault .done
abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => secondProtocol.tree),
    Decoration.append firstProtocol.roles (fun _ => secondProtocol.roles),
    Decoration.append firstProtocol.oracles (fun _ => secondProtocol.oracles)⟩
abbrev prefixAccess := Access.extend inputSpec.toPFunctor
  (OracleInterface.instDefault (Message := Nat))

/-- A single exported scalar capability. -/
@[reducible]
def family : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => OracleInterface.instDefault⟩

abbrev suffixAccess := Access.extend family.spec.toPFunctor
  (OracleInterface.instDefault (Message := Nat))
abbrev rawAccess := Access.extend prefixAccess (OracleInterface.instDefault (Message := Nat))

/-- Each exported request expands into the input answer followed by the prefix message. -/
def exportView : VirtualOracle (ofPFunctor prefixAccess) family := ⟨fun _ => do
  let input : Nat ← liftM ((ofPFunctor prefixAccess).query (.inl ()))
  let sent : Nat ← liftM ((ofPFunctor prefixAccess).query (.inr ()))
  return input + sent⟩

/-- The prefix returns a capability without executing its deferred query program. -/
def firstVerifier : Verifier.Fragment NativeRuntimeTest.ambient firstProtocol.tree
    firstProtocol.roles firstProtocol.oracles inputSpec.toPFunctor (fun _ =>
      OpenClaim (ofPFunctor prefixAccess) Unit family) := pure ⟨(), exportView⟩

/-- The suffix executes one exported request and one fresh-source request in that order. -/
def secondVerifier (_ : firstProtocol.tree.BranchPath) (_ : Unit) :
    Verifier.Strategy NativeRuntimeTest.ambient secondProtocol.tree secondProtocol.roles
      secondProtocol.oracles family.spec.toPFunctor
      (fun _ => Option (OpenClaim (ofPFunctor suffixAccess) Nat family)) := by
  change OracleComp (NativeRuntimeTest.ambient + ofPFunctor suffixAccess)
    (OracleComp (NativeRuntimeTest.ambient + ofPFunctor suffixAccess)
      (Option (OpenClaim (ofPFunctor suffixAccess) Nat family)))
  exact pure (do
    let _ : Nat ← liftM
      ((NativeRuntimeTest.ambient + ofPFunctor suffixAccess).query (.inl 3))
    let old : Nat ← liftM
      ((NativeRuntimeTest.ambient + ofPFunctor suffixAccess).query (.inr (.inl ⟨(), ()⟩)))
    let fresh : Nat ← liftM
      ((NativeRuntimeTest.ambient + ofPFunctor suffixAccess).query (.inr (.inr ())))
    return some ⟨old + fresh, ⟨fun _ => pure (old + fresh)⟩⟩)

/-- The suffix is authored against only the exported interface and its own new message. -/
def verifier : Verifier.Strategy NativeRuntimeTest.ambient combined.tree combined.roles
    combined.oracles inputSpec.toPFunctor
    (TerminalClaim combined inputSpec.toPFunctor (fun _ => Nat) (fun _ => family)) :=
  Verifier.appendExported NativeRuntimeTest.ambient firstProtocol.tree
    (fun _ => secondProtocol.tree) firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor
    (fun _ => Unit) (fun _ _ => Nat) (fun _ => family)
    (fun _ => Nat) (fun _ _ => Nat) (fun _ => family) firstVerifier secondVerifier

/-- The ordinary native continuation queries the same ambient counter in both fragments. -/
def prover (secret : Nat) : Prover.Strategy NativeRuntimeTest.ambient combined.tree combined.roles
    (fun _ => Nat) := do
  let first : Nat ← liftM (NativeRuntimeTest.ambient.query 1)
  return ⟨first, do
    let second : Nat ← liftM (NativeRuntimeTest.ambient.query 2)
    return ⟨second, secret⟩⟩

/-- A persistent counter also answers the suffix's terminal ambient request. -/
private abbrev runtime : OracleRuntime (fun _ : Empty => Unit) NativeRuntimeTest.ambient where
  State := Nat
  setup := pure 0
  handler := fun _ count => pure (count + 1, count + 1)

/-- Raw source observations remain paired with the final state and chronological world answers. -/
example (secret : Nat) :
    (fun result =>
      (result.output.core.proverOut, result.output.core.closed.map (·.stmt),
        (result.output.sourceLog : QueryLog (ofPFunctor rawAccess)),
        result.state, result.trace)) <$>
      executeStrategiesWithRuntime runtime inputImpl (prover secret) verifier =
    pure (secret, some 10,
      [⟨Sum.inl (Sum.inl ()), (7 : Nat)⟩,
        ⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩, ⟨Sum.inr (), (2 : Nat)⟩],
      3, [⟨1, (1 : Nat)⟩, ⟨2, (2 : Nat)⟩, ⟨3, (3 : Nat)⟩]) := by
  rw [executeStrategiesWithRuntime_eq, OracleRuntime.run_eq]
  simp only [runtime, pure_bind]
  have observation := runtime.runFrom_observe 0
    (executeStrategiesLoggedRun inputImpl (prover secret) verifier)
  have projected := congrArg (fun program =>
    (fun result =>
      (result.1.core.proverOut, result.1.core.closed.map (·.stmt),
        (result.1.sourceLog : QueryLog (ofPFunctor rawAccess)), result.2.1, result.2.2)) <$>
        program) observation
  calc
    _ = (fun result =>
        (result.1.1.core.proverOut, result.1.1.core.closed.map (·.stmt),
          (result.1.1.sourceLog : QueryLog (ofPFunctor rawAccess)), result.2, result.1.2)) <$>
        runtime.handler.runState 0
          (executeStrategiesLoggedRun inputImpl (prover secret) verifier).withQueryLog := by
      simpa only [Functor.map_map] using projected
    _ = _ := by rfl

/-- A simple exported query type separates the one authored request from its two raw calls. -/
abbrev exportSpec : OracleSpec Unit := Unit →ₒ Nat

def route : QueryImpl exportSpec (OracleComp (ofPFunctor prefixAccess)) :=
  fun _ => exportView.query ⟨(), ()⟩

/-- The handler-driven law logs two raw calls and their answers for one exported request. -/
example :
    simulateQ (Access.extendImpl inputSpec.toPFunctor
      (OracleInterface.instDefault (Message := Nat)) inputImpl 1)
      (simulateQ (QueryImpl.compose (ofPFunctor prefixAccess).loggingOracle route)
        (liftM (exportSpec.query ()) : OracleComp exportSpec Nat)).run =
      (8, [⟨Sum.inl (), (7 : Nat)⟩, ⟨Sum.inr (), (1 : Nat)⟩]) := by
  rw [← withQueryLog_simulateQ]
  change simulateQ (Access.extendImpl inputSpec.toPFunctor
    (OracleInterface.instDefault (Message := Nat)) inputImpl 1)
      (exportView.query ⟨(), ()⟩).withQueryLog = _
  rfl

/-- Phased execution retains the same expanded raw-source observations and final runtime state. -/
example (secret : Nat) :
    (fun result => (result.output.logView, result.state)) <$>
        executeStrategiesPhasedWithRuntime runtime inputImpl (prover secret) verifier =
      (fun result => ((result.output.observation, result.trace), result.state)) <$>
        executeStrategiesWithRuntime runtime inputImpl (prover secret) verifier := by
  exact executeStrategiesPhasedWithRuntime_logView runtime inputImpl (prover secret) verifier

end Expanded

#print axioms executeStrategiesLoggedRun_erase
#print axioms executeStrategiesWithRuntime_erase
#print axioms withQueryLog_simulateQ
#print axioms executeStrategiesPhasedWithRuntime_logView

end Interaction.Oracle.NativeRuntimeTest
