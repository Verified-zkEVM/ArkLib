/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Interaction.HonestSamplingResources
import ArkLibTest.ProofSystem.Logup.Prover.Completeness
import ArkLibTest.ProofSystem.Logup.Lookup.Completeness
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Completeness
import ArkLibTest.ProofSystem.Sumcheck.Interaction.SamplingResources
import Lean.Compiler.IR

/-! # Actual measured honest endpoints have empty private-party ambient logs -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction.HonestSamplingResources
open Lean Elab Command
namespace HonestSamplingResourcesTests

namespace Weighted
open LogupHonestTest.Cubic
abbrev Result := PhasedResult ambientSpec combined.tree combined.roles combined.oracles
  LogupStateTest.access (fun _ => Unit) (fun _ => Bool)
def prover := Logup.Prover.Honest.prover (RingHom.id F) LogupStateTest.cfg
  LogupStateTest.data ambientSpec
def verifier := Logup.Interaction.verifier (RingHom.id F) 1 2 1 LogupStateTest.cfg ambientSpec
  (event 0) jointDraw (event 4) LogupStateTest.access LogupStateTest.view
def run : OracleComp ambientSpec Result := executeStrategiesPhased ambientSpec combined.tree
  combined.roles combined.oracles LogupStateTest.access LogupStateTest.impl prover verifier
def summarize (result : Result × List Nat) : Bool × Nat × Nat × Nat × Array F × List Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .prover combined.roles result.1.world,
    WorldSegments.queryCount .verifier combined.roles result.1.world,
    result.1.sourceLog.length, (pathData result.1.path).1, result.2)
def summary (alpha : F) := summarize ((simulateQ (logger alpha) run).run [])
theorem contract : ∀ result ∈ support run,
    WorldSegments.queryCount .prover combined.roles result.world = 0 :=
  weighted_prover_queries_zero (RingHom.id F) LogupStateTest.cfg LogupStateTest.data ambientSpec
    LogupStateTest.access LogupStateTest.impl verifier
end Weighted

namespace Scalar
open LogupScalarHonestTest.Small
abbrev Result := PhasedResult ambient combined.tree combined.roles combined.oracles access
  (fun _ => Unit) (fun _ => Bool)
def prover (witness : Vector (Fin 4) 2) := Logup.Lookup.Honest.prover f cfg data witness ambient
def verifier := Logup.Lookup.verifier f 1 1 2 1 cfg ambient (event 0) joint (event 5) access view
def run (witness : Vector (Fin 4) 2) : OracleComp ambient Result :=
  executeStrategiesPhased ambient combined.tree combined.roles combined.oracles access impl
    (prover witness) verifier
def summarize (result : Result × List Nat) :
    Bool × Nat × Nat × Nat × Vector (CMlPolynomialEval F 1) 2 × List Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .prover combined.roles result.1.world,
    WorldSegments.queryCount .verifier combined.roles result.1.world,
    result.1.sourceLog.length, result.1.path.1, result.2)
def summary (alpha : F) (witness : Vector (Fin 4) 2 := indices) :=
  summarize ((simulateQ (logger alpha) (run witness)).run [])
theorem contract (witness : Vector (Fin 4) 2) : ∀ result ∈ support (run witness),
    WorldSegments.queryCount .prover combined.roles result.world = 0 :=
  scalar_prover_queries_zero f cfg data witness ambient access impl verifier
end Scalar

namespace Tuple
open LogupTupleHonestTest.Small
abbrev Result := PhasedResult ambient combined.tree combined.roles combined.oracles access
  (fun _ => Unit) (fun _ => Bool)
def prover (witness : Vector (Fin 6) 2) :=
  Logup.Lookup.Tuple.Honest.prover f cfg prepared witness ambient
def verifier := Logup.Lookup.Tuple.verifier f 1 1 3 2 1 cfg ambient
  (event 0) (event 1) joint (event 3) access view
def run (witness : Vector (Fin 6) 2) : OracleComp ambient Result :=
  executeStrategiesPhased ambient combined.tree combined.roles combined.oracles access impl
    (prover witness) verifier
def summarize (result : Result × List Nat) :
    Bool × Nat × Nat × Nat × Vector (CMlPolynomialEval F 1) 3 × F × List Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .prover combined.roles result.1.world,
    WorldSegments.queryCount .verifier combined.roles result.1.world,
    result.1.sourceLog.length, result.1.path.1, result.1.path.2.1, result.2)
def summary (beta alpha : F) (witness : Vector (Fin 6) 2 := indices) :=
  summarize ((simulateQ (logger beta alpha) (run witness)).run [])
theorem contract (witness : Vector (Fin 6) 2) : ∀ result ∈ support (run witness),
    WorldSegments.queryCount .prover combined.roles result.world = 0 :=
  tuple_prover_queries_zero f cfg prepared witness ambient access impl verifier
end Tuple

namespace Zero
open LogupHonestTest.ZeroRound
abbrev F := LogupHonestTest.F
abbrev ambient := LogupHonestTest.TwoRound.ambient
abbrev combined := Logup.Interaction.protocol F 0 2 1
abbrev Result := PhasedResult ambient combined.tree combined.roles combined.oracles access
  (fun _ => Unit) (fun _ => Bool)
def prover := Logup.Prover.Honest.prover (RingHom.id F) cfg data ambient
def verifier (alpha : F) := Logup.Interaction.verifier (RingHom.id F) 0 2 1 cfg ambient
  (pure alpha) (pure (Fin.elim0, (![4, 6] : Fin 2 → F))) LogupHonestTest.TwoRound.round access view
def run (alpha : F) : OracleComp ambient Result := executeStrategiesPhased ambient combined.tree
  combined.roles combined.oracles access impl prover (verifier alpha)
def summarize (result : Result × Nat) : Bool × Nat × Nat × Nat × Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .prover combined.roles result.1.world,
    WorldSegments.queryCount .verifier combined.roles result.1.world,
    result.1.sourceLog.length, result.2)
def summary (alpha : F) :=
  summarize ((simulateQ LogupHonestTest.TwoRound.logger (run alpha)).run 0)
theorem contract (alpha : F) : ∀ result ∈ support (run alpha),
    WorldSegments.queryCount .prover combined.roles result.world = 0 :=
  weighted_prover_queries_zero (RingHom.id F) cfg data ambient access impl (verifier alpha)
end Zero

namespace Native
abbrev F := LogupStateTest.F
abbrev ambient := LogupHonestTest.Cubic.ambientSpec
abbrev A := LogupStateTest.access
abbrev p := Sumcheck.Interaction.Computable.protocol F 3 1
abbrev Message := Sumcheck.Impl.Representation.Message F 3
abbrev source := Access.extend A (Sumcheck.Interaction.Native.Core.messageInterface F Message
  (Sumcheck.Impl.Representation.evaluate F 3))
def state := Logup.Prover.State.start
  (Logup.Prover.State.prepare (RingHom.id F) 2 LogupStateTest.cfg LogupStateTest.data)
  (fun _ => 3) (![4, 6] : Fin 2 → F)
def build := Logup.Prover.Honest.pureBuilder (E := F) LogupStateTest.cfg.groups
  LogupStateTest.cfg.length_group_le
def Out (path : p.tree.BranchPath) : Type :=
  if path.2.1.isSome then Vector F 2 else Vector F 1
def latest (x : F) := Sumcheck.Interaction.Native.Core.latest F Message
  (Sumcheck.Impl.Representation.evaluate F 3) ambient A x
/-- An arbitrary verifier queries after both the message and public abort, with dependent output. -/
def verifier (stop : Bool) : Verifier.Strategy ambient p.tree p.roles p.oracles A Out := do
  let _ ← (LogupHonestTest.Cubic.event 0).liftComp (ambient + ofPFunctor source)
  let a ← latest 5
  return do
    let _ ← (LogupHonestTest.Cubic.event 0).liftComp (ambient + ofPFunctor source)
    let b ← latest 5
    if stop then
      return ⟨none, do
        let _ ← (LogupHonestTest.Cubic.event 0).liftComp (ambient + ofPFunctor source)
        let _ ← latest 1
        return #v[a + b]⟩
    else
      return ⟨some 5, do
        let _ ← (LogupHonestTest.Cubic.event 0).liftComp (ambient + ofPFunctor source)
        let _ ← latest 1
        return #v[a, b]⟩
abbrev Result := PhasedResult ambient p.tree p.roles p.oracles A (fun _ => Unit) Out
def run (stop : Bool) : OracleComp ambient Result := executeStrategiesPhased ambient p.tree
  p.roles p.oracles A LogupStateTest.impl (Logup.Prover.Honest.nativeWith ambient build 1 state)
  (verifier stop)
def output (path : p.tree.BranchPath) (out : Out path) : List Nat := by
  rcases path with ⟨_, ⟨choice, _⟩⟩
  cases choice with
  | none => exact out.toList.map ZMod.val
  | some r => exact out.toList.map ZMod.val
def values (path : p.tree.BranchPath)
    (trace : QueryLog (ofPFunctor (TypeTree.accessAfter p.tree p.oracles A path))) : List F := by
  rcases path with ⟨_, ⟨choice, _⟩⟩
  cases choice <;>
    exact trace.map fun entry => match entry with
      | ⟨.inl _, answer⟩ => answer
      | ⟨.inr _, answer⟩ => answer

def summarize (result : Result × List Nat) : Nat × Nat × List Nat × List F × List Nat :=
  (WorldSegments.queryCount .prover p.roles result.1.world,
    WorldSegments.queryCount .verifier p.roles result.1.world,
    output result.1.path.toBranchPath result.1.verifierOut,
    values result.1.path.toBranchPath result.1.sourceLog, result.2)
def summary (stop : Bool) := summarize
  ((simulateQ (LogupHonestTest.Cubic.logger 2) (run stop)).run [])
theorem contract (stop : Bool) : ∀ result ∈ support (run stop),
    WorldSegments.queryCount .prover p.roles result.world = 0 :=
  nativeWith_prover_queries_zero ambient build 1 state A LogupStateTest.impl (verifier stop)
end Native

namespace Mixed
open Sumcheck.Interaction.TerminalCheckTest NativeSamplingResourcesTests
def summary (q : Sumcheck.Impl.Representation.Message F 1) : Nat × Nat × Nat × List Nat :=
  let result := ((simulateQ logger (oneRun q)).run []).1
  (WorldSegments.queryCount .prover (Sumcheck.Interaction.Computable.protocol F 1 1).roles
      result.world,
    WorldSegments.queryCount .verifier (Sumcheck.Interaction.Computable.protocol F 1 1).roles
      result.world,
    result.world.flatten.length, result.world.flatten.map fun entry => entry.1.val)
theorem partition (result : OneResult) :
    WorldSegments.queryCount .prover (Sumcheck.Interaction.Computable.protocol F 1 1).roles
        result.world +
      WorldSegments.queryCount .verifier (Sumcheck.Interaction.Computable.protocol F 1 1).roles
        result.world = result.world.flatten.length := by
  exact WorldSegments.queryCount_partition _ _
end Mixed

def check : IO Unit := do
  unless Native.summary true == (0, 3, [2], [1, 1, 0], [0, 0, 0]) &&
      Native.summary false == (0, 3, [1, 1], [1, 1, 0], [0, 0, 0]) do
    throw (IO.userError "native private0 changed arbitrary Some/None verifier effects")
  unless Weighted.summary 2 == (true, 0, 5, 9, #[0, 2, 10, 5], [0, 1, 2, 3, 4]) &&
      Weighted.summary 0 == (false, 0, 4, 2, #[13, 10, 4, 7], [0, 1, 2, 3]) do
    throw (IO.userError "weighted private0 changed the cubic, pole abort or source log")
  let mu : Vector (CMlPolynomialEval LogupScalarHonestTest.Small.F 1) 2 :=
    #v[#v[0, 0], #v[1, 1]]
  unless Scalar.summary 2 == (true, 0, 6, 11, mu, [0, 1, 2, 3, 4, 5]) &&
      Scalar.summary 5 == (false, 0, 5, 2, mu, [0, 1, 2, 3, 4]) do
    throw (IO.userError "measured scalar histogram/private0 changed source or pole effects")
  let invalid := Scalar.summary 2 #v[0, 1]
  unless !invalid.1 && invalid.2.1 == 0 do
    throw (IO.userError "private purity acquired an unjustified valid-lookup premise")
  let tupleMu : Vector (CMlPolynomialEval LogupTupleHonestTest.Small.F 1) 3 :=
    #v[#v[1, 0], #v[1, 0], #v[0, 0]]
  unless Tuple.summary 1 5 == (true, 0, 4, 22, tupleMu, 1, [0, 1, 2, 3]) &&
      Tuple.summary 0 5 == (true, 0, 4, 22, tupleMu, 0, [0, 1, 2, 3]) &&
      Tuple.summary 0 0 == (false, 0, 3, 2, tupleMu, 0, [0, 1, 2]) do
    throw (IO.userError "tuple private0 changed pre-beta mu, collision or pole effects")
  unless Zero.summary 2 == (true, 0, 0, 6, 0) &&
      Zero.summary 0 == (false, 0, 0, 6, 0) do
    throw (IO.userError "zero-round private0 skipped actual source authentication")
  unless Mixed.summary (Sumcheck.Interaction.TerminalCheckTest.affine 2 (-1)) ==
      (4, 3, 7, [1, 0, 1, 1, 1, 1, 2]) do
    throw (IO.userError "phase partition confused shared sampler indices or chronological queries")

run_cmd do
  match (← liftIO check.toBaseIO) with
  | .ok () => pure ()
  | .error e => throwError e.toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``WorldSegments.queryCount_partition, ``nativeWith_prover_queries_zero,
      ``honestWith_prover_queries_zero, ``scalarWith_prover_queries_zero,
      ``tupleWith_prover_queries_zero, ``weighted_prover_queries_zero,
      ``scalar_prover_queries_zero, ``tuple_prover_queries_zero,
      ``Weighted.contract, ``Scalar.contract, ``Tuple.contract, ``Native.contract,
      ``Zero.contract, ``Mixed.partition] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected honest ambient-log axiom: {name}"
  for name in #[``Weighted.prover, ``Weighted.verifier, ``Weighted.run, ``Weighted.summary,
      ``Scalar.prover, ``Scalar.run, ``Scalar.summary, ``Tuple.prover, ``Tuple.run, ``Tuple.summary,
      ``Native.verifier, ``Native.run, ``Native.output, ``Native.values, ``Native.summary,
      ``Zero.run, ``Zero.summary, ``Mixed.summary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable honest phased caller IR: {name}"
  logInfo "actual measured private0, arbitrary verifier effects and mixed phase partition passed"

end HonestSamplingResourcesTests
