/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateDerivativeRefinement

/-! # Kernel replay of coordinate repeated scaling and characteristic cancellation -/

@[expose] public section

namespace MvPolynomial.QuadraticDerivativeMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev run := runFuel (2 : ZMod 5) 1
private def ts : List (Term (ZMod 5)) := [((1, 2), [(1, 5)]), ((0, 1), [(1, 2)])]
private def output : Configuration (ZMod 5) → Option (List (Term (ZMod 5)))
  | .ready (.done out) => some out
  | _ => none
private def state : Configuration (ZMod 5) →
    Option (PartialDerivativeMachine.Configuration (Pair (ZMod 5)))
  | .ready s => some s
  | _ => none

example : output (run 100 (.ready (.terms ts []))).1 = some [((0, 2), [(1, 1)])] := by
  decide +kernel
example : (run 100 (.ready (.terms ts []))).2 =
    ⟨{ additions := 14, equalities := 4, control := 174, data := 667,
       constants := 98, output := 11 }, 22⟩ := by
  decide +kernel
example : state (run 1 (.ready (.scan (1, 2) [(1, 2)] [] [] []))).1 =
    some (.scale (1, 2) 2 (0, 0) [(1, 1)] [] [] []) := by
  decide +kernel
theorem scan_charges_coordinate_constant :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    (runFuel (2 : ZMod 5) 1 1
      (.ready (.scan (1, 2) [(1, 2)] [] [] []))).2.base.constants = 2 := by
  decide +kernel
example : (run 1 (.ready (.scan (1, 2) [(1, 2)] [] [] []))).2.base.data = 9 := by
  decide +kernel
example : state (run 10 (.ready (.scale (1, 2) 3 (2, 2) [] [] [] []))).1 =
    some (.scale (1, 2) 2 (3, 4) [] [] [] []) := by
  decide +kernel
example : state (run 10 (.ready (.test (0, 0) [] [] [] []))).1 = some (.terms [] []) := by
  decide +kernel
example : state (run 10 (.ready (.test (0, 1) [] [] [] []))).1 =
    some (.restore (0, 1) [] [] [] []) := by
  decide +kernel
example : (run 1 (.ready (.test (0, 1) [] [] [] []))).2.base.constants = 2 := by
  decide +kernel
example : (run 1 (.call (.test (0, 1) [] [] [] []) ⟨2, (0, 1), (0, 0)⟩ (.start .equal))).2 =
    ⟨{ control := 2, data := 13, constants := 10 }, 0⟩ := by
  decide +kernel
example : (run 1 (.ready (.reverse [] []))).2.base.output = 1 := by
  decide +kernel

end MvPolynomial.QuadraticDerivativeMachine
