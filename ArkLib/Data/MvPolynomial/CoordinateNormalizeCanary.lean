/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.CoordinateNormalizeRefinement

/-! # Kernel checks for coordinate normalization, cancellation and charges -/

@[expose] public section

namespace MvPolynomial.QuadraticNormalizeMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev run := runFuel (2 : ZMod 5)
private def ts : List (Term (ZMod 5)) :=
  [((1, 2), [(1, 1)]), ((4, 3), [(1, 1)]), ((0, 1), [])]
private def output : Configuration (ZMod 5) → Option (List (Term (ZMod 5)))
  | .ready (.done out) => some out
  | _ => none
private def state : Configuration (ZMod 5) →
    Option (DenseNormalizeMachine.Configuration (Pair (ZMod 5)))
  | .ready s => some s
  | _ => none

example : output (run 58 (.ready (.terms ts []))).1 = some [((0, 1), [])] := by decide +kernel
example : (run 58 (.ready (.terms ts []))).2 =
    ⟨{ additions := 2, equalities := 8, control := 102, data := 381,
       constants := 58, output := 6 }, 2⟩ := by decide +kernel
example : state (run 10 (.ready (.terms [((0, 0), [])] []))).1 = some (.terms [] []) := by
  decide +kernel
example : state (run 10 (.ready (.terms [((0, 1), [])] []))).1 =
    some (.search (0, 1) [] [] [] []) := by decide +kernel
example : state (run 10 (.ready (.sum (0, 0) [] [((1, 0), [])] [] []))).1 =
    some (.restore [] [((1, 0), [])] []) := by decide +kernel
example : state (run 10 (.ready (.sum (0, 1) [] [((1, 0), [])] [] []))).1 =
    some (.restore [] [((0, 1), []), ((1, 0), [])] []) := by decide +kernel
example : state (run 10 (.ready (.compare (1, 2) [] ((3, 4), []) [] [] [] [] []))).1 =
    some (.sum (4, 1) [] [] [] []) := by decide +kernel
theorem nonzero_term_charges_coordinate_constant :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    (runFuel (2 : ZMod 5) 1
      (.ready (.terms [((0, 1), [])] []))).2.base.constants = 2 := by decide +kernel
example : (run 1 (.ready (.terms [((0, 1), [])] []))).2.base.data = 8 := by decide +kernel
example : (run 1 (.call (.term (0, 1) [] [] []) ⟨2, (0, 1), (0, 0)⟩ (.start .equal))).2 =
    ⟨{ control := 2, data := 13, constants := 10 }, 0⟩ := by decide +kernel
example : (run 1 (.ready (.terms [] []))).2.base.output = 1 := by decide +kernel

end MvPolynomial.QuadraticNormalizeMachine
