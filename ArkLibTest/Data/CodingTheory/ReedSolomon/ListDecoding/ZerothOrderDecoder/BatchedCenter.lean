/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.BatchedCenter
import Mathlib.Algebra.Field.ZMod

/-! Actual subproduct-tree obstruction search, one checked center, and quotient Newton. -/

namespace ZerothOrderBatchedCenterTests

open CPoly CompPoly ReedSolomon.ListDecoding.ZerothOrderDecoder

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def domain : Fin 3 ↪ ZMod 5 where
  toFun i := i.val
  inj' := by decide
private def equation : CMvPolynomial 2 (ZMod 5) :=
  CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 0 ^ 2

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Reject a zero obstruction value, select a later center, then decode only at that center. -/
def run : IO Unit := do
  let obstruction : CPolynomial (ZMod 5) := CPolynomial.X
  check "batched obstruction did not skip its zero" <|
    selectObstructionCenter obstruction [0, 1, 2] == some 1
  check "batched obstruction selected out of input order" <|
    selectObstructionCenter obstruction [0, 2, 1] == some 2
  check "zero obstruction exhaustion failed" <|
    selectObstructionCenter (0 : CPolynomial (ZMod 5)) [0, 1, 2] == none
  check "empty obstruction prefix failed" <|
    selectObstructionCenter obstruction [] == none
  check "batched selected-center decoder failed" <|
    runFromObstruction? 5 (RingHom.id (ZMod 5)) domain ![0, 1, 2] 2 3 equation
      obstruction [0, 1, 2] == some [[1, 0]]
  -- A false obstruction must not bypass the regular-fiber check at zero.
  check "invalid obstruction bypassed regularity check" <|
    runFromObstruction? 5 (RingHom.id (ZMod 5)) domain ![0, 1, 2] 2 3 equation
      1 [0, 1, 2] == none

#print axioms ReedSolomon.ListDecoding.ZerothOrderDecoder.runFromObstruction?_exact

end ZerothOrderBatchedCenterTests
