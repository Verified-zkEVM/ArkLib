/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Resources
import ArkLibTest.ProofSystem.Sumcheck.Interaction.TerminalCheck
import Lean.Compiler.IR

/-! # Actual logged verifier counts, canonical arrays and unrestricted terminal fanout -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Sumcheck.Interaction
open Sumcheck.Interaction.Computable.Resources
namespace NativeResourcesTests
open TerminalCheckTest

/-- Private output depends on both the actual message length and the public branch. -/
def Private (path : (Computable.protocol F 1 1).tree.ExecutionPath) : Type :=
  Vector F (path.1.val.val.size + if path.2.1.isSome then 1 else 0)

def dependentProver (q : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec (Computable.protocol F 1 1).tree
      (Computable.protocol F 1 1).roles Private := do
  let secret ← event 0
  return ⟨q, fun
    | none => do
      let trailing ← event 2
      return Vector.replicate q.val.val.size (secret + trailing)
    | some r => do
      let trailing ← event 2
      return Vector.replicate (q.val.val.size + 1) (secret + trailing + r)⟩

def bare (q : Sumcheck.Impl.Representation.Message F 1) :=
  executeStrategiesLogged ambientSpec (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (Computable.protocol F 1 1).oracles
    inputSpec.toPFunctor inputImpl (dependentProver q)
    (Computable.verifier F 1 1 ambientSpec (event 1) [0, 1] 1 0 rfl
      inputSpec.toPFunctor originalView initial)

abbrev DependentResult := LoggedResult (Computable.protocol F 1 1).tree
  (Computable.protocol F 1 1).oracles inputSpec.toPFunctor Private (fun _ => Bool)

def completed (q : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec DependentResult :=
  executeStrategiesLogged ambientSpec (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (Computable.protocol F 1 1).oracles
    inputSpec.toPFunctor inputImpl (dependentProver q)
    (Computable.verifierWithFinalCheck F 1 1 ambientSpec (event 1) [0, 1] 1 0 rfl
      inputSpec.toPFunctor originalView initial)

def summarizeDependent (result : DependentResult × List Nat) :
    Bool × Usage × Nat × Nat × List Nat × List Nat :=
  let native := result.1.sourceLog.filter fun entry =>
    messageLabel 1 1 inputSpec.toPFunctor (fun _ => false) result.1.path entry.1
  (result.1.verifierOut, pathUsage 1 1 result.1.path, result.1.sourceLog.length,
    native.length, result.1.proverOut.toList.map ZMod.val, result.2)

def resourceSummary (q : Sumcheck.Impl.Representation.Message F 1) :
    Bool × Usage × Nat × Nat × List Nat × List Nat :=
  summarizeDependent ((simulateQ logger (completed q)).run [])

theorem actual_log_contract (q : Sumcheck.Impl.Representation.Message F 1) :
    ∀ result ∈ support (bare q),
      result.sourceLog.length = (pathUsage 1 1 result.path).messageQueries ∧
      result.verifierOut.isSome = decide ((pathUsage 1 1 result.path).terminalQueries = 1) :=
  logged_verifier_usage 1 1 ambientSpec (event 1) 1 0 rfl inputSpec.toPFunctor originalView
    initial inputImpl (dependentProver q)

def ordinary (q : Sumcheck.Impl.Representation.Message F 1) :=
  executeStrategies ambientSpec (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (Computable.protocol F 1 1).oracles
    inputSpec.toPFunctor inputImpl (dependentProver q)
    (Computable.verifierWithFinalCheck F 1 1 ambientSpec (event 1) [0, 1] 1 0 rfl
      inputSpec.toPFunctor originalView initial)

/-- Authentication cannot change the actual path census, even when its Bool rejects. -/
theorem actual_complete_contract (q : Sumcheck.Impl.Representation.Message F 1) :
    (fun result => pathUsage 1 1 result.1) <$> ordinary q =
      (fun result => pathUsage 1 1 result.path) <$> bare q :=
  complete_usage_eq_logged 1 1 ambientSpec (event 1) 1 0 rfl inputSpec.toPFunctor originalView
    initial inputImpl (dependentProver q)

def zeroRound (target : F) : Bool × Usage × Nat :=
  let result := (simulateQ logger (runFinal target)).run []
  (result.1.verifierOut, pathUsage 1 0 result.1.path, result.1.sourceLog.length)

def profileArray (q : Sumcheck.Impl.Representation.Message F 1) : List Nat :=
  let profile := profileArithmetic (Sumcheck.Impl.VerifierChecks.sumProgram
    (fun x => Arithmetic.evalHornerProgram q.val.val x) [0, 1])
  [ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
    .valueRead, .metadata].map profile.2

/-- A two-round arbitrary ordinary prover, including both private branch responses. -/
def twoProver (second : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec (Computable.protocol F 1 2).tree
      (Computable.protocol F 1 2).roles (fun _ => F) := do
  let secret ← event 0
  return ⟨affine 2 (-1), fun
    | none => do
      let trailing ← event 2
      return secret + trailing
    | some _ => do
      let middle ← event 2
      return do
        return ⟨second, fun
          | none => do
            let trailing ← event 0
            return secret + middle + trailing
          | some r => do
            let trailing ← event 0
            return secret + middle + trailing + r⟩⟩

def constantView : VirtualOracle (ofPFunctor inputSpec.toPFunctor)
    (MultivariateRound.polynomialFamily F 2 1) := ⟨fun _ => pure (11 : F)⟩

abbrev TwoResult := LoggedResult (Computable.protocol F 1 2).tree
  (Computable.protocol F 1 2).oracles inputSpec.toPFunctor (fun _ => F) (fun _ => Bool)

def twoRun (second : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec TwoResult :=
  executeStrategiesLogged ambientSpec
    (Computable.protocol F 1 2).tree (Computable.protocol F 1 2).roles
    (Computable.protocol F 1 2).oracles inputSpec.toPFunctor inputImpl (twoProver second)
    (Computable.verifierWithFinalCheck F 2 1 ambientSpec (event 1) [0, 1] 2 0 rfl
      inputSpec.toPFunctor constantView ⟨0, Fin.elim0⟩)

def summarizeTwo (result : TwoResult × List Nat) : Bool × Usage × Nat × List Nat :=
  (result.1.verifierOut, pathUsage 1 2 result.1.path, result.1.sourceLog.length, result.2)

def twoRound (second : Sumcheck.Impl.Representation.Message F 1) :
    Bool × Usage × Nat × List Nat := summarizeTwo ((simulateQ logger (twoRun second)).run [])

def check : IO Unit := do
  let full : Usage := ⟨3, 2, 1, 1, 1, 1, 6, 3, 3⟩
  let zero : Usage := ⟨3, 2, 1, 1, 1, 1, 0, 0, 0⟩
  let abort : Usage := ⟨2, 2, 1, 0, 0, 0, 2, 0, 0⟩
  unless resourceSummary (affine 2 (-1)) == (true, full, 5, 3, [15, 15, 15], [0, 1, 2]) do
    throw (IO.userError "actual full native path/length/private output census changed")
  unless resourceSummary (affine 0 0) == (false, zero, 5, 3, [15], [0, 1, 2]) do
    throw (IO.userError "terminal rejection was confused with public round abort or zero length")
  unless resourceSummary (affine 0 1) == (false, abort, 2, 2, [12], [0, 2]) do
    throw (IO.userError
      "failed round sampled a challenge or lost the actual private abort response")
  unless zeroRound 5 == (true, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 2) &&
      zeroRound 0 == (false, ⟨0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 2) do
    throw (IO.userError
      "zero rounds did not preserve actual two-query terminal fanout/authentication")
  unless twoRound (affine 0 11) == (true, ⟨6, 4, 2, 2, 1, 1, 9, 3, 3⟩, 6, [0, 1, 2, 1, 0]) do
    throw (IO.userError "two-round mixed canonical lengths or zero-query terminal view changed")
  unless twoRound (affine 0 1) == (false, ⟨5, 4, 2, 1, 0, 0, 8, 3, 3⟩, 5, [0, 1, 2, 0]) do
    throw (IO.userError "second-round rejection lost the first successful message or sampled again")
  unless profileArray (affine 2 (-1)) == [4, 0, 2, 0, 0, 4, 0, 0, 0] &&
      profileArray (affine 0 0) == [2, 0, 0, 0, 0, 0, 0, 0, 0] &&
      profileArray (affine 0 1) == [2, 0, 0, 0, 0, 2, 0, 0, 0] do
    throw (IO.userError "actual selected sum/Horner programs changed all-nine coordinate profiles")
  let kinds := [ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
    .valueRead, .metadata]
  unless (kinds.map full.arithmeticCost).sum == 16 do
    throw (IO.userError "native local total conflated additions, equality or coefficient reads")
  IO.println
    "actual native resources: dependent outputs, aborts, lengths and terminal fanout passed"

open Lean Elab Command in
run_cmd do
  liftIO check
  for name in #[``pathUsage, ``messageLabel, ``Usage.arithmeticCost,
      ``resourceSummary, ``twoRound] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing ordinary native resource caller IR"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``logged_verifier_usage, ``complete_usage_eq_logged, ``logged_checkFinalClaim,
      ``messageLabel_routeEntry, ``pathUsage_bounds, ``pathUsage_queries_eq,
      ``pathUsage_terminal_iff,
      ``profile_message, ``profile_messageSum, ``pathUsage_arithmeticCost_le,
      ``actual_log_contract, ``actual_complete_contract] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected actual native resource axiom: {name}"

end NativeResourcesTests
