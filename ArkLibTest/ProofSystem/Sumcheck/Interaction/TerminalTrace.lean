/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Resources
import ArkLibTest.ProofSystem.Sumcheck.Interaction.Resources
import Lean.Compiler.IR

/-! # Actual returned native queries retain their original source and ordered raw traces -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Sumcheck.Interaction
namespace NativeTerminalTraceTests
open TerminalCheckTest

namespace Prior
abbrev spec : OracleSpec Nat := Nat →ₒ Nat
abbrev access := spec.toPFunctor
@[reducible] def interface : OracleInterface Nat where
  Query := Nat
  toOC.spec := Nat →ₒ Nat
  toOC.impl q := do return (← read)+q

def impl : QueryImpl (ofPFunctor access) Id := fun q => q+1
def program (many : Bool) : OracleComp (ofPFunctor access) Nat := do
  let first : Nat ← liftM (spec.query 2)
  if many then
    let second : Nat ← liftM (spec.query (first+1))
    let third : Nat ← liftM (spec.query 2)
    return first+second+third
  else return first

def encode (result : Nat × QueryLog (ofPFunctor (Access.extend access interface))) :
    Nat × List (Nat × Nat × Nat) :=
  (result.1, result.2.map fun entry => match entry with
    | ⟨.inl q,answer⟩ => (0,q,answer)
    | ⟨.inr q,answer⟩ => (1,q,answer))
def run (many : Bool) := encode ((simulateQ (Access.extendImpl access interface impl 100)
  (simulateQ (Access.queryPrior access interface) (program many)).withQueryLog).run)

example {A : PFunctor.{1, 1}} {Msg : Type 1}
    (interface : OracleInterface.{1, 1} Msg)
    (impl : QueryImpl (ofPFunctor A) Id) (message : Msg) {α : Type 1}
    (program : OracleComp (ofPFunctor A) α) :
    simulateQ (Access.extendImpl A interface impl message)
        (simulateQ (Access.queryPrior A interface) program).withQueryLog =
      let result := simulateQ impl program.withQueryLog
      (result.1, result.2.map fun entry => ⟨Sum.inl entry.1, entry.2⟩) :=
  Access.simulateQ_queryPrior_withQueryLog interface impl message program
end Prior

namespace One
abbrev p := Computable.protocol F 1 1
abbrev Out := TerminalClaim p inputSpec.toPFunctor (fun _ => Native.Core.FinalStatement F 1)
  (fun _ => MultivariateRound.polynomialFamily F 1 1)
abbrev Result := LoggedResult p.tree p.oracles inputSpec.toPFunctor NativeResourcesTests.Private Out

def view (mode : Nat) : VirtualOracle (ofPFunctor inputSpec.toPFunctor)
    (MultivariateRound.polynomialFamily F 1 1) :=
  if mode = 0 then ⟨fun _ => pure (5 : F)⟩
  else if mode = 1 then ⟨fun q => liftM (inputSpec.query (0,q.2 0))⟩ else originalView

def run (mode : Nat) (q : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec Result := executeStrategiesLogged ambientSpec p.tree p.roles p.oracles
  inputSpec.toPFunctor inputImpl (NativeResourcesTests.dependentProver q)
  (Computable.verifier F 1 1 ambientSpec (event 1) [0,1] 1 0 rfl
    inputSpec.toPFunctor (view mode) initial)

def trace (mode : Nat) (result : Result) :
    Option (F × List (String × F) × F × List (String × F)) := do
  let claim ← result.verifierOut
  let actual : F × QueryLog (ofPFunctor (TypeTree.accessAfter p.tree p.oracles
      inputSpec.toPFunctor result.path.toBranchPath)) :=
    (simulateQ (result.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl)
      (claim.oracles.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
  let boundary : F × QueryLog (ofPFunctor inputSpec.toPFunctor) :=
    (simulateQ inputImpl ((view mode).query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
  return (actual.1, encodeSource result.path actual.2, boundary.1,
    encodeSource result.path (TypeTree.routeLog p.tree p.oracles inputSpec.toPFunctor
      result.path.toBranchPath boundary.2))

abbrev Summary := Option (F × List (String × F) × F × List (String × F)) ×
  Nat × List Nat × List Nat
def summarize (mode : Nat) (result : Result × List Nat) : Summary :=
  (trace mode result.1, result.1.sourceLog.length, result.1.proverOut.toList.map ZMod.val, result.2)
def summary (mode : Nat) (q : Sumcheck.Impl.Representation.Message F 1) : Summary :=
  summarize mode ((simulateQ logger (run mode q)).run [])

theorem contract (mode : Nat) (q : Sumcheck.Impl.Representation.Message F 1)
    (result : Result) (hresult : result ∈ support (run mode q))
    (claim : OpenClaim (ofPFunctor (TypeTree.accessAfter p.tree p.oracles
      inputSpec.toPFunctor result.path.toBranchPath)) (Native.Core.FinalStatement F 1)
      (MultivariateRound.polynomialFamily F 1 1)) (hclaim : result.verifierOut = some claim) :
    (simulateQ (result.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl)
      (claim.oracles.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run =
      let boundary : F × QueryLog (ofPFunctor inputSpec.toPFunctor) :=
        (simulateQ inputImpl ((view mode).query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
      (boundary.1, TypeTree.routeLog p.tree p.oracles inputSpec.toPFunctor
        result.path.toBranchPath boundary.2) :=
  Computable.Resources.logged_final_query_eq_boundary 1 1 ambientSpec (event 1) 1 0 rfl
    inputSpec.toPFunctor (view mode) initial inputImpl (NativeResourcesTests.dependentProver q)
    result hresult claim hclaim

end One

namespace Two
abbrev p := Computable.protocol F 1 2
abbrev Out := TerminalClaim p inputSpec.toPFunctor (fun _ => Native.Core.FinalStatement F 2)
  (fun _ => MultivariateRound.polynomialFamily F 2 1)
def Private (path : p.tree.ExecutionPath) : Type :=
  if (show Option F from path.2.1).isSome then Vector F 3 else Bool
abbrev Result := LoggedResult p.tree p.oracles inputSpec.toPFunctor Private Out

def view : VirtualOracle (ofPFunctor inputSpec.toPFunctor)
    (MultivariateRound.polynomialFamily F 2 1) := ⟨fun q => do
  let first : F ← liftM (inputSpec.query (0,q.2 0))
  let second : F ← liftM (inputSpec.query (1,q.2 1))
  return first+second⟩
def initial : Sumcheck.Spec.StatementRound F 2 0 := ⟨0,Fin.elim0⟩
def prover (first second : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec p.tree p.roles Private := do
  let secret ← event 0
  return ⟨first, fun
    | none => do
      let _ ← event 2
      return false
    | some r => do
      let _ ← event 2
      return do
        return ⟨second, fun
          | none => do
            let trailing ← event 2
            return #v[secret,r,trailing]
          | some s => do
            let trailing ← event 2
            return #v[secret,r+s,trailing]⟩⟩

def run (first second : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec Result := executeStrategiesLogged ambientSpec p.tree p.roles p.oracles
  inputSpec.toPFunctor inputImpl (prover first second)
  (Computable.verifier F 2 1 ambientSpec (event 1) [0,1] 2 0 rfl
    inputSpec.toPFunctor view initial)

def encode (path : p.tree.ExecutionPath)
    (log : QueryLog (ofPFunctor (TypeTree.accessAfter p.tree p.oracles
      inputSpec.toPFunctor path.toBranchPath))) : List (Nat × F × F) := by
  rcases path with ⟨first,⟨choice,rest⟩⟩
  cases choice with
  | none =>
    exact log.map fun entry => match entry with
      | ⟨.inl (i,x),answer⟩ => (i.val,x,answer)
      | ⟨.inr x,answer⟩ => (2,x,answer)
  | some r =>
    rcases rest with ⟨second,⟨choice,stop⟩⟩
    cases choice <;> exact log.map (fun entry => match entry with
      | ⟨.inl (.inl (i,x)),answer⟩ => (i.val,x,answer)
      | ⟨.inl (.inr x),answer⟩ => (2,x,answer)
      | ⟨.inr x,answer⟩ => (3,x,answer))

def privateValues (path : p.tree.ExecutionPath) (out : Private path) : List Nat := by
  rcases path with ⟨first,⟨choice,rest⟩⟩
  cases choice
  · change Bool at out
    exact if out then [1] else [0]
  · exact out.toList.map ZMod.val

def trace (result : Result) : Option (F × List (Nat × F × F) × F × List (Nat × F × F)) := do
  let claim ← result.verifierOut
  let actual : F × QueryLog (ofPFunctor (TypeTree.accessAfter p.tree p.oracles
      inputSpec.toPFunctor result.path.toBranchPath)) :=
    (simulateQ (result.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl)
      (claim.oracles.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
  let boundary : F × QueryLog (ofPFunctor inputSpec.toPFunctor) :=
    (simulateQ inputImpl (view.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
  return (actual.1, encode result.path actual.2, boundary.1,
    encode result.path (TypeTree.routeLog p.tree p.oracles inputSpec.toPFunctor
      result.path.toBranchPath boundary.2))
abbrev Summary := Option (F × List (Nat × F × F) × F × List (Nat × F × F)) ×
  Nat × List Nat × List Nat
def summarize (result : Result × List Nat) : Summary :=
  (trace result.1, result.1.sourceLog.length,
    privateValues result.1.path result.1.proverOut, result.2)
def summary (first second : Sumcheck.Impl.Representation.Message F 1) : Summary :=
  summarize ((simulateQ logger (run first second)).run [])

theorem contract (first second : Sumcheck.Impl.Representation.Message F 1)
    (result : Result) (hresult : result ∈ support (run first second))
    (claim : OpenClaim (ofPFunctor (TypeTree.accessAfter p.tree p.oracles
      inputSpec.toPFunctor result.path.toBranchPath)) (Native.Core.FinalStatement F 2)
      (MultivariateRound.polynomialFamily F 2 1)) (hclaim : result.verifierOut = some claim) :
    (simulateQ (result.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl)
      (claim.oracles.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run =
      let boundary : F × QueryLog (ofPFunctor inputSpec.toPFunctor) :=
        (simulateQ inputImpl (view.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
      (boundary.1, TypeTree.routeLog p.tree p.oracles inputSpec.toPFunctor
        result.path.toBranchPath boundary.2) :=
  Computable.Resources.logged_final_query_eq_boundary 2 1 ambientSpec (event 1) 2 0 rfl
    inputSpec.toPFunctor view initial inputImpl (prover first second)
    result hresult claim hclaim

end Two

namespace Zero
abbrev p := Computable.protocol F 1 0
abbrev Out := TerminalClaim p inputSpec.toPFunctor (fun _ => Native.Core.FinalStatement F 0)
  (fun _ => MultivariateRound.polynomialFamily F 0 1)
abbrev Result := LoggedResult p.tree p.oracles inputSpec.toPFunctor (fun _ => Vector Nat 2) Out

def view (many : Bool) : VirtualOracle (ofPFunctor inputSpec.toPFunctor)
    (MultivariateRound.polynomialFamily F 0 1) :=
  if many then ⟨fun _ => do
    let first : F ← liftM (inputSpec.query (0,3))
    let second : F ← liftM (inputSpec.query (1,3))
    return first+second⟩ else ⟨fun _ => pure (5 : F)⟩
def run (many : Bool) : OracleComp ambientSpec Result := executeStrategiesLogged ambientSpec
  p.tree p.roles p.oracles inputSpec.toPFunctor inputImpl #v[37,41]
  (Computable.verifier F 0 1 ambientSpec (event 1) [0,1] 0 0 rfl inputSpec.toPFunctor
    (view many) ⟨0,Fin.elim0⟩)
def trace (many : Bool) (result : Result) : Option (F × Nat × F × Nat) := do
  let claim ← result.verifierOut
  let actual : F × QueryLog (ofPFunctor inputSpec.toPFunctor) :=
    (simulateQ (result.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl)
      (claim.oracles.query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
  let boundary : F × QueryLog (ofPFunctor inputSpec.toPFunctor) :=
    (simulateQ inputImpl ((view many).query ⟨(),claim.stmt.challenges⟩).withQueryLog).run
  return (actual.1, actual.2.length, boundary.1, boundary.2.length)
def summarize (many : Bool) (result : Result × List Nat) :
    Option (F × Nat × F × Nat) × Nat × List Nat × List Nat :=
  (trace many result.1, result.1.sourceLog.length, result.1.proverOut.toList, result.2)
def summary (many : Bool) := summarize many ((simulateQ logger (run many)).run [])
end Zero

/-- Actual native source-trace fixtures, shared with the standalone compiled caller. -/
def check : IO Unit := do
  unless Prior.run false == (3,[(0,2,3)]) &&
      Prior.run true == (11,[(0,2,3),(0,4,5),(0,2,3)]) do
    throw (IO.userError
      "prior log transport changed actual responses, repeated order or old/new identity")
  let empty : OracleComp (ofPFunctor Prior.access) Nat := pure 17
  unless Prior.encode ((simulateQ
      (Access.extendImpl Prior.access Prior.interface Prior.impl 100)
      (simulateQ (Access.queryPrior Prior.access Prior.interface) empty).withQueryLog).run) ==
      (17,[]) do throw (IO.userError "empty prior program made a raw query")
  for mode in [0,1,2] do
    let entries : List (String × F) := if mode = 0 then []
      else if mode = 1 then [("input[0](3)",6)]
      else [("input[0](3)",6),("input[1](3)",-1)]
    let answer : F := if mode = 1 then 6 else 5
    unless One.summary mode (affine 2 (-1)) ==
        (some (answer,entries,answer,entries),3,[15,15,15],[0,1,2]) do
      throw (IO.userError
        "supported final view lost zero/one/many raw fanout or actual private effects")
    unless One.summary mode (affine 0 1) == (none,2,[12],[0,2]) do
      throw (IO.userError "aborted run manufactured a returned claim or queried an original source")
  let entries : List (Nat × F × F) := [(0,3,6),(1,3,-1)]
  unless Two.summary (affine 2 (-1)) (affine 0 11) ==
      (some (5,entries,5,entries),6,[7,6,5],[0,1,2,1,2]) do
    throw (IO.userError
      "two native extensions changed the retained original view/order/private responses")
  unless Two.summary (affine 0 1) (affine 0 11) == (none,2,[0],[0,2]) &&
      Two.summary (affine 2 (-1)) (affine 0 1) == (none,5,[7,3,5],[0,1,2,2]) do
    throw (IO.userError
      "first/second abort lost dependent private data or queried a nonexistent claim")
  unless Zero.summary false == (some (5,0,5,0),0,[37,41],[]) &&
      Zero.summary true == (some (5,2,5,2),0,[37,41],[]) do
    throw (IO.userError
      "n0 transport sampled a challenge or changed original empty/many-query view")
  IO.println "same original terminal view: zero/one/many fanout, n0/n2, aborts and effects passed"

open Lean Elab Command in
run_cmd do
  liftIO check
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Access.simulateQ_queryPrior_withQueryLog,
      ``Computable.Resources.logged_final_query_eq_boundary, ``One.contract, ``Two.contract] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected terminal-view transport axiom: {name}"
  for name in #[``Prior.run, ``One.run, ``One.trace, ``Two.run, ``Two.trace,
      ``Zero.run, ``Zero.trace] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable actual terminal-view caller IR: {name}"
end NativeTerminalTraceTests
