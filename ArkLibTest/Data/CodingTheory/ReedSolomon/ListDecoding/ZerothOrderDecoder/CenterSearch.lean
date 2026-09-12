/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.CenterSearch
import Mathlib.Algebra.Field.ZMod

/-! Single-center selection and actual quotient Newton followed by agreement recovery. -/

namespace ZerothOrderCenterSearchTests

open CPoly ReedSolomon.ListDecoding.ZerothOrderDecoder

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def domain : Fin 3 ↪ ZMod 5 where
  toFun i := i.val
  inj' := by decide

private def x : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 0
private def y : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 1
private def equation : CMvPolynomial 2 (ZMod 5) := y ^ 2 - x ^ 2

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Exercise rejection, first-success selection, recovery, and explicit search failure. -/
def run : IO Unit := do
  check "zeroth-order repeated fiber guard failed" <|
    goodCenter equation 0 == false && goodCenter equation 1 == true
  check "zeroth-order search did not select first regular center" <|
    selectCenter equation [0, 1, 2] == some 1
  check "zeroth-order exhausted search not reported" <|
    selectCenter equation [0] == none && selectCenter equation [] == none
  -- At x=0 this equation loses Y degree, despite its surviving linear factor being regular.
  check "zeroth-order leading-degree loss not rejected" <|
    goodCenter (x * y ^ 2 + y + 1) 0 == false
  check "zeroth-order degree-drop search failed to advance" <|
    selectCenter (x * y ^ 2 + y + 1) [0, 1] == some 1
  check "zeroth-order zero equation not rejected" <|
    selectCenter (0 : CMvPolynomial 2 (ZMod 5)) [0, 1] == none
  -- ExactOutput uses descending fixed-width vectors: X is [1, 0].
  let decoded := runNormalized? 5 (RingHom.id (ZMod 5)) domain ![0, 1, 2]
    2 3 equation [0, 1, 2]
  check "zeroth-order selected-center Newton/recovery failed" <|
    decoded == some [[1, 0]]
  check "zeroth-order failed search confused with empty output" <|
    runNormalized? 5 (RingHom.id (ZMod 5)) domain ![0, 1, 2]
      2 3 equation [0] == none
  check "zeroth-order successful empty output not retained" <|
    runNormalized? 5 (RingHom.id (ZMod 5)) domain ![1, 1, 1]
      2 3 equation [0, 1, 2] == some []

end ZerothOrderCenterSearchTests
