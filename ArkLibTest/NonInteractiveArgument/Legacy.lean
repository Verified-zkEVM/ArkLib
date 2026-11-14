/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
import ArkLib.NonInteractiveArgument.Legacy
import VCVio.OracleComp.RunIO

/-!
# Legacy NARG extractor permissions and shared oracle state
-/

open OracleComp OracleSpec ProtocolSpec

namespace LegacyNARGCoinsTest
namespace AdaptiveAccess

abbrev publicSpec := Unit →ₒ Fin 7

def publicImpl : QueryImpl publicSpec (StateT ℕ ProbComp) := fun _ => do
  modify (· + 1)
  return Fin.ofNat 7 (← get)

def prover : OracleComp (publicSpec + unifSpec) (Unit × Unit) := do
  let _ ← samplePrivateUniform (publicSpec := publicSpec) (Fin 7)
  let _ ← liftM ((publicSpec + unifSpec).query (.inl ()))
  return ((), ())

def verifier : NonInteractiveVerifier Unit publicSpec Unit Unit where
  verify _ _ := do
    let _ ← liftM (publicSpec.query ())
    return ()

-- The standalone extractor's type grants sampling only, independently of the prover's access.
def standalone : Unit → Unit → QueryLog publicSpec → QueryLog publicSpec →
    OptionT ProbComp (Fin 7) := fun _ _ trP trV =>
  if trP.length == 1 && trV.length == 1 then pure 1 else failure

-- Public query access is a separate, explicit choice of extractor interface and handler.
def shared : Unit → Unit → QueryLog publicSpec → QueryLog publicSpec →
    OptionT (OracleComp (publicSpec + unifSpec)) (Fin 7) := fun _ _ trP trV => do
  if trP.length == 1 && trV.length == 1 then
    liftM ((publicSpec + unifSpec).query (.inl ()))
  else failure

end AdaptiveAccess

/-- Execute the regression checks for observable oracle routing. -/
def checkRuntime : IO Unit := do
  let (_, witness, accepted) ← OracleComp.runIO <|
    adaptiveNARGKnowledgeSoundnessExp (pure 0) AdaptiveAccess.publicImpl
      (QueryImpl.id' unifSpec) ((QueryImpl.id' unifSpec).liftTarget (StateT ℕ ProbComp))
      AdaptiveAccess.verifier AdaptiveAccess.standalone AdaptiveAccess.prover
  unless witness == some 1 && accepted == some () do
    throw (IO.userError "adaptive KS exposed private draws in the extractor's public logs")
  let (_, witness, _) ← OracleComp.runIO <|
    adaptiveNARGKnowledgeSoundnessExp (pure 0) AdaptiveAccess.publicImpl
      (QueryImpl.id' unifSpec) (AdaptiveAccess.publicImpl.addLift (QueryImpl.id' unifSpec))
      AdaptiveAccess.verifier AdaptiveAccess.shared AdaptiveAccess.prover
  unless witness == some 3 do
    throw (IO.userError "explicit shared-oracle extraction did not continue the verifier state")

end LegacyNARGCoinsTest

/-- Run with `lake env lean --run ArkLibTest/NonInteractiveArgument/Legacy.lean`. -/
def main : IO Unit := LegacyNARGCoinsTest.checkRuntime
