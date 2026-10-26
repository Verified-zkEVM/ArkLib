/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Interaction.Resources
import ArkLibTest.ProofSystem.Logup.Interaction.Fixture
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Fixture
import ArkLibTest.ProofSystem.Logup.Lookup.Source
import Lean.Compiler.IR

/-! # Actual complete packet and source provenance across LogUp prefixes -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction Logup.Interaction.Resources
namespace LoggedPrefixTests
namespace Weighted
open LogupRuntimeFixture

/-- Private output really has different types on public abort and native success. -/
def Output (path : combined.tree.ExecutionPath) : Type :=
  if path.2.2.2.2.1.isSome then Vector E 2 else Bool

def pack (path : combined.tree.ExecutionPath) (value : E) : Output path := by
  unfold Output
  split
  · exact #v[value, value + 1]
  · exact false

def dependentProver (h : E) (q : Message) :
    Prover.Strategy ambientSpec combined.tree combined.roles Output :=
  Interaction.StrategyOver.TwoParty.Focal.mapOutput
    (fun path value => pack (TypeTree.ExecutionPath.ofTypeTreePath path) value)
    (prover privateEffect h q)

theorem packet (h : E) (q : Message) :
    LoggedResult.observe <$> executeStrategiesLogged ambientSpec combined.tree combined.roles
      combined.oracles access impl (dependentProver h q)
      (verifier embedding 1 2 2 cfg ambientSpec (event 0) jointDraw (event 7) access view) = (do
        let alpha ← event 0
        let afterAlpha ← dependentProver h q alpha
        let sent ← afterAlpha
        let joint ← jointDraw
        let suffix ← sent.2 joint
        let result ← executeStrategiesLogged ambientSpec
          (Sumcheck.Interaction.Computable.protocol E 4 1).tree
          (Sumcheck.Interaction.Computable.protocol E 4 1).roles
          (Sumcheck.Interaction.Computable.protocol E 4 1).oracles
          (Access.extend access (helperInterface (E := E) 1 1))
          (Access.extendImpl access (helperInterface (E := E) 1 1) impl sent.1)
          (OutP := fun path => Output ⟨alpha, ⟨sent.1, ⟨joint, path⟩⟩⟩) suffix
          (Sumcheck.Interaction.Computable.verifierWithFinalCheck E 1 4 ambientSpec
            (event 7) [0, 1] 1 0 (by decide)
            (Access.extend access (helperInterface (E := E) 1 1))
            (qView embedding 1 2 1 cfg.groups alpha joint.1 joint.2 2 access view)
            (zeroStatement E 1))
        return ⟨⟨alpha, ⟨sent.1, ⟨joint, result.path⟩⟩⟩, result.proverOut,
          result.verifierOut, result.sourceLog⟩) :=
  executeStrategiesLogged_eq_prefix_bind embedding 1 2 2 cfg ambientSpec
    (event 0) jointDraw (event 7) access view impl (dependentProver h q)

/-- An original answer controls additional raw requests without changing the returned value. -/
def adaptiveView : VirtualOracle (ofPFunctor access) (inputFamily embedding 1 2) :=
  ⟨fun query => do
    let answer : E ← view.query query
    if answer = 0 then
      let _ ← view.query query
      return answer
    else return answer⟩

def run (input : VirtualOracle (ofPFunctor access) (inputFamily embedding 1 2))
    (h : E) (q : Message) : OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec combined.tree combined.roles combined.oracles access impl
    (prover privateEffect h q)
    (verifier embedding 1 2 2 cfg ambientSpec (event 0) jointDraw (event 7) access input)

def summary (input : VirtualOracle (ofPFunctor access) (inputFamily embedding 1 2))
    (h : E) (q : Message) :=
  summarize ((simulateQ logger (run input h q)).run [])

def raw (input : VirtualOracle (ofPFunctor access) (inputFamily embedding 1 2))
    (h : E) (q : Message) : List (Nat × E) :=
  let result := ((simulateQ logger (run input h q)).run []).1
  encodeSource result.path result.sourceLog

def pureView : VirtualOracle (ofPFunctor access) (inputFamily embedding 1 2) :=
  ⟨fun _ => pure (0 : E)⟩
end Weighted

namespace Tuple
open LogupTupleProtocolFixture

theorem packet :
    LoggedResult.observe <$> executeStrategiesLogged ambientSpec combined.tree combined.roles
      combined.oracles access impl (dependentProver correctMessage)
      (Logup.Lookup.Tuple.verifier f 1 1 2 2 1 cfg ambientSpec (event 1) (event 3)
        jointDraw (event 10) access view) = (do
      let sent ← dependentProver correctMessage
      let beta ← event 1
      let suffix ← sent.2 beta
      let result ← executeStrategiesLogged ambientSpec
        (protocol F 1 3 1).tree (protocol F 1 3 1).roles (protocol F 1 3 1).oracles
        (Access.extend access (Logup.Lookup.multiplicityInterface f 1 2))
        (Access.extendImpl access (Logup.Lookup.multiplicityInterface f 1 2) impl sent.1)
        (OutP := fun path => Output ⟨sent.1, ⟨beta, path⟩⟩) suffix
        (verifier f 1 3 1 cfg.weighted ambientSpec (event 3) jointDraw (event 10)
          (Access.extend access (Logup.Lookup.multiplicityInterface f 1 2))
          (Logup.Lookup.Tuple.weightedView f 1 1 2 2 beta access view))
      return ⟨⟨sent.1, ⟨beta, result.path⟩⟩, result.proverOut,
        result.verifierOut, result.sourceLog⟩) :=
  tuple_executeStrategiesLogged_eq_sender_beta_bind f 1 1 2 2 1 cfg ambientSpec
    (event 1) (event 3) jointDraw (event 10) access view impl
    (dependentProver correctMessage)
end Tuple

namespace Scalar
open LogupLookupSourceTest
abbrev ambient : OracleSpec Unit := Unit →ₒ F

def cfgLookup : Logup.Lookup.Config F 1 1 1 2 :=
  (Logup.Lookup.Config.create? F 1 1 1 2 17).get (by decide)

def privateEvent : OracleComp ambient F := liftM (ambient.query ())

def message : Sumcheck.Impl.Representation.Message F 4 :=
  LogupTupleProtocolFixture.SameShape.widen (LogupTupleProtocolFixture.affine 20 (-10))

def weighted (hs : Vector (CMlPolynomialEval F 1) 1) :
    Prover.Strategy ambient (protocol F 1 1 2).tree
      (protocol F 1 1 2).roles (fun _ => Nat) := fun _ => do
  let a ← privateEvent
  return do
    let b ← privateEvent
    return ⟨hs, fun _ => do
      let c ← privateEvent
      return pure ⟨message, fun choice => match choice with
        | none => pure (a.val + b.val + c.val)
        | some _ => pure (a.val + b.val + c.val + 1)⟩⟩

def wholeWith (msg hs : Vector (CMlPolynomialEval F 1) 1) :
    Prover.Strategy ambient (Logup.Lookup.protocol f 1 1 1 2).tree
      (Logup.Lookup.protocol f 1 1 1 2).roles (fun _ => Nat) := do
  let _ ← privateEvent
  return ⟨msg, weighted hs⟩

def whole := wholeWith mu helpers

abbrev combined := Logup.Lookup.protocol f 1 1 1 2
abbrev Result := LoggedResult combined.tree combined.oracles originalAccess
  (fun _ => Nat) (fun _ => Bool)

def observed (msg hs : Vector (CMlPolynomialEval F 1) 1) : Result × List Nat :=
  let record : QueryImpl ambient (StateM (List Nat)) := fun _ => do
    modify (· ++ [0])
    return (1 : F)
  (simulateQ record (executeStrategiesLogged ambient combined.tree combined.roles
    combined.oracles originalAccess originalHandler (wholeWith msg hs)
    (Logup.Lookup.verifier f 1 1 1 2 cfgLookup ambient (pure 5)
      (pure (fun _ => 3, fun _ => 3)) (pure 2) originalAccess originalView))).run []

def summarize (result : Result × List Nat) : Bool × Nat × List Nat :=
  (result.1.verifierOut, result.1.sourceLog.length, result.2)

def summary (msg hs : Vector (CMlPolynomialEval F 1) 1) : Bool × Nat × List Nat :=
  summarize (observed msg hs)

abbrev finalAccess := Access.extend retainedAccess
  (Sumcheck.Interaction.Native.Core.messageInterface F
    (Sumcheck.Impl.Representation.Message F 4) (Sumcheck.Impl.Representation.evaluate F 4))

def encodeEntry (entry : (query : finalAccess.A) × finalAccess.B query) : Nat × F :=
  match entry with
  | ⟨.inl (.inl (.inl q)), answer⟩ =>
    (match q.1 with | .inl _ => 0 | .inr _ => 1, answer)
  | ⟨.inl (.inl (.inr _)), answer⟩ => (2, answer)
  | ⟨.inl (.inr _), answer⟩ => (3, answer)
  | ⟨.inr _, answer⟩ => (4, answer)

def raw (msg hs : Vector (CMlPolynomialEval F 1) 1) : List (Nat × F) :=
  let result := (observed msg hs).1
  let encode (path : combined.tree.ExecutionPath) :
      QueryLog (ofPFunctor (TypeTree.accessAfter combined.tree combined.oracles originalAccess
        path.toBranchPath)) → List (Nat × F) := by
    rcases path with ⟨msg, alpha, hs, joint, message, choice, stop⟩
    cases choice <;> exact fun log => log.map encodeEntry
  encode result.path result.sourceLog

theorem packet :
    LoggedResult.observe <$> executeStrategiesLogged ambient
      (Logup.Lookup.protocol f 1 1 1 2).tree (Logup.Lookup.protocol f 1 1 1 2).roles
      (Logup.Lookup.protocol f 1 1 1 2).oracles originalAccess originalHandler whole
      (Logup.Lookup.verifier f 1 1 1 2 cfgLookup ambient (pure 5)
        (pure (fun _ => 3, fun _ => 3)) (pure 2) originalAccess originalView) = (do
      let sent ← whole
      let result ← executeStrategiesLogged ambient
        (protocol F 1 1 2).tree (protocol F 1 1 2).roles (protocol F 1 1 2).oracles
        muAccess (Access.extendImpl originalAccess
          (Logup.Lookup.multiplicityInterface f 1 1) originalHandler sent.1)
        (OutP := fun _ => Nat) sent.2
        (verifier f 1 2 2 cfgLookup.weighted ambient (pure 5)
          (pure (fun _ => 3, fun _ => 3)) (pure 2) muAccess
          (Logup.Lookup.weightedView f 1 1 1 originalAccess originalView))
      return ⟨⟨sent.1, result.path⟩, result.proverOut,
        result.verifierOut, result.sourceLog⟩) :=
  scalar_executeStrategiesLogged_eq_sender_bind f 1 1 1 2 cfgLookup
  ambient (pure 5) (pure (fun _ => 3, fun _ => 3)) (pure 2)
  originalAccess originalView originalHandler whole
abbrev native := Sumcheck.Interaction.Computable.protocol F 4 1

def nativeProver : Prover.Strategy ambient native.tree native.roles (fun _ => Nat) :=
  pure ⟨message, fun choice => match choice with
    | none => pure (0 : Nat)
    | some _ => pure (1 : Nat)⟩

def bare := executeStrategiesLogged ambient native.tree native.roles native.oracles
  retainedAccess (retainedHandler mu helpers) nativeProver
  (Sumcheck.Interaction.Computable.verifier F 1 4 ambient (pure 2) [0, 1] 1 0 (by decide)
    retainedAccess (qView f 1 2 1 cfg.groups 5 (fun _ => 3) (fun _ => 3) 2 muAccess
      (Logup.Lookup.weightedView f 1 1 1 originalAccess originalView)) (zeroStatement F 1))

/-- The new whole-suffix count law applies to the actual retained mu/helper source. -/
theorem reached_fanout (result : _) (hresult : result ∈ support bare)
    (claim : _) (hclaim : result.verifierOut = some claim) :
    (result.sourceLog ++ (simulateQ
      (result.path.closingImpl native.oracles retainedAccess (retainedHandler mu helpers))
      (claim.oracles.query ⟨(), claim.stmt.challenges⟩).withQueryLog).run.2).length =
      (Sumcheck.Interaction.Computable.Resources.pathUsage 4 1 result.path).messageQueries +
        (((List.finRange 2).map fun i =>
          (simulateQ (muHandler mu)
            ((Logup.Lookup.weightedView f 1 1 1 originalAccess originalView).query
              ⟨(0, i), claim.stmt.challenges⟩).withQueryLog).2.length).sum +
        ((List.finRange 2).map fun i =>
          (simulateQ (muHandler mu)
            ((Logup.Lookup.weightedView f 1 1 1 originalAccess originalView).query
              ⟨(1, i), claim.stmt.challenges⟩).withQueryLog).2.length).sum + 1) :=
  qView_final_log_length f 1 2 1 2 cfg.groups 5 (fun _ => 3) (fun _ => 3)
    ambient (pure 2) muAccess (Logup.Lookup.weightedView f 1 1 1 originalAccess originalView)
    (muHandler mu) helpers nativeProver result hresult claim hclaim

end Scalar

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Weighted.packet, ``Scalar.packet, ``Tuple.packet, ``Scalar.reached_fanout,
      ``Logup.Interaction.Resources.qView_complete_log_eq_boundary,
      ``Logup.Interaction.Resources.qView_final_log_length] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected complete packet axiom: {name}"
  for name in #[``Weighted.dependentProver, ``Weighted.run, ``Weighted.raw,
      ``Scalar.observed, ``Scalar.raw] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable endpoint caller IR: {name}"

/-- Final rejection still authenticates Q; round abort does not. -/
def checkWeighted : IO Unit := do
  let full := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  let zero := LogupRuntimeFixture.affine 0 0
  unless Weighted.summary Weighted.adaptiveView 0 zero == (true, 81, 10, full) &&
      Weighted.summary Weighted.adaptiveView 1 zero == (false, 81, 10, full) &&
      Weighted.summary Weighted.adaptiveView 0 (LogupRuntimeFixture.affine 2 (-1)) ==
        (false, 81, 10, full) do
    throw (IO.userError "actual terminal source fanout or helper authentication changed")
  unless Weighted.raw Weighted.adaptiveView 0 zero ==
      [(5, 0), (5, 0), (5, 0), (0, 0), (0, 0), (1, 0), (1, 0), (2, 1), (3, -1), (4, 0)] do
    throw (IO.userError "actual source request order or answers changed")
  unless Weighted.summary Weighted.adaptiveView 0 (LogupRuntimeFixture.affine 0 1) ==
      (false, 76, 2, [0, 1, 2, 3, 4, 5, 6, 8]) do
    throw (IO.userError "public abort performed an unreached terminal source query")
  unless Weighted.summary Weighted.pureView 0 zero == (true, 81, 4, full) &&
      Weighted.summary Weighted.pureView 1 zero == (false, 81, 4, full) do
    throw (IO.userError "zero original fanout removed retained helper authentication")

/-- Equal table shapes do not make multiplicity and helper slots interchangeable. -/
def checkScalar : IO Unit := do
  let scalar := Scalar.summary LogupLookupSourceTest.mu LogupLookupSourceTest.helpers
  unless scalar == (true, 7, [0, 0, 0, 0]) &&
      !(Scalar.summary LogupLookupSourceTest.mu #v[#v[1, 1]]).1 &&
      !(Scalar.summary #v[#v[0, 0]] LogupLookupSourceTest.helpers).1 do
    throw (IO.userError "same-shaped retained multiplicity and helper were confused")
  unless Scalar.raw LogupLookupSourceTest.mu LogupLookupSourceTest.helpers ==
      [(4, 7), (4, 10), (4, 13), (0, 9), (1, 9), (2, 6), (3, 0)] do
    throw (IO.userError "actual scalar complete packet lost source values or ordered slots")

/-- The tuple beta response retains a genuinely dependent private output. -/
def checkTuple : IO Unit := do
  unless LogupTupleProtocolFixture.dependentRun 0 LogupTupleProtocolFixture.correctMessage ==
      LogupTupleProtocolFixture.endpoint 0 LogupTupleProtocolFixture.correctMessage do
    throw (IO.userError "dependent tuple private output changed actual endpoint effects")

def check : IO Unit := do
  checkWeighted
  checkScalar
  checkTuple
  IO.println "complete packets: terminal accept/reject, source fanout and abort effects passed"

open Lean Elab Command in
run_cmd do
  liftIO check
end LoggedPrefixTests
