/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.Logup.Interaction.Fixture
import VCVio.OracleComp.RunIO

/-!
# Native weighted LogUp execution checks

The classic acceptance caller and native executable share one fixture. The traced random handler
uses the same primitive as OracleComp.runIO, recording each inclusive uniform bound. The named
uniform endpoint must sample four extension elements through their existing six base-field limbs.
The balanced nonzero weights give Q=0 at every alpha, including poles, so these checks never rely
on a favorable random draw. No empirical soundness or cryptographic RNG claim is made here.
-/

open LogupRuntimeFixture OracleComp OracleSpec

namespace LogupRuntime

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError label

/-- Instrument the existing primitive IO sampler without changing the endpoint's sampling code. -/
def randomTrace : QueryImpl unifSpec (StateT (List Nat) IO) := fun n => do
  modify (· ++ [n])
  return Fin.ofNat (n + 1) (← (IO.rand 0 n).toIO)

def main : IO Unit := do
  let full := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  let abort := [0, 1, 2, 3, 4, 5, 6, 8]
  check "honest actual execution" (summary 0 (affine 0 0) == (true, 81, 8, full))
  check "forged final claim" (summary 0 (affine 2 (-1)) == (false, 81, 8, full))
  check "retained helper mutation" (summary 1 (affine 0 0) == (false, 81, 8, full))
  check "private effects after abort" (summary 0 (affine 0 1) == (false, 76, 2, abort))
  check "actual original/helper source query trace"
    (observations 0 (affine 0 0) ==
      [(5, 0), (5, 0), (5, 0), (0, 0), (1, 0), (2, 1), (3, -1), (4, 0)])
  check "forged polynomial actual answers"
    (observations 0 (affine 2 (-1)) ==
      [(5, -1), (5, 1), (5, 9), (0, 0), (1, 0), (2, 1), (3, -1), (4, 0)])
  check "abort source queries" (observations 0 (affine 0 1) == [(5, 1), (5, 1)])
  check "named execute honest endpoint" (endpoint 0 (affine 0 0) == (true, full))
  check "named execute rejects forged endpoint" (endpoint 0 (affine 2 (-1)) == (false, full))
  check "named execute binds actual helper" (endpoint 1 (affine 0 0) == (false, full))
  check "named execute preserves abort effects" (endpoint 0 (affine 0 1) == (false, abort))
  check "zero-round actual terminal authentication"
    (ZeroRound.summary 0 == (true, 37, 5, [0, 1, 2, 4, 5]))
  check "zero-round retained helper mutation"
    (ZeroRound.summary 1 == (false, 37, 5, [0, 1, 2, 4, 5]))
  let (accepted, bounds) ← (simulateQ randomTrace uniformEndpoint).run []
  check "named uniform endpoint rejected balanced data" accepted
  check "extension sampler did not use exactly24 base limbs" (bounds.length == 24)
  check "uniform endpoint enumerated an extension or function space"
    (bounds.all (· == KoalaBear.fieldSize - 1))
  IO.println "weighted LogUp native runtime: all16 checks passed"

end LogupRuntime

def main : IO Unit := LogupRuntime.main
