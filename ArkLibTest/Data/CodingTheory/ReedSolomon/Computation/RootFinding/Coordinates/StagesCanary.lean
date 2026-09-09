/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.StagesRefinement
/-! # Kernel replay of complete coordinate stage records and failure paths -/

namespace ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def ts : List (Term (ZMod 5)) := [((1, 0), [(1, 1)])]
private def sep : List (Term (ZMod 5)) := [((1, 0), [(1, 0)])]
private def input : Input (ZMod 5) := ⟨[(0, 0)], ts, 0⟩
private def stage : Stage (ZMod 5) := ⟨ts, some (1, 1)⟩
private def next : Stage (ZMod 5) := ⟨sep, none⟩
private def ctx : Context (ZMod 5) := ⟨stage, [], sep⟩
private def rec : Record (ZMod 5) := ⟨ctx, (0, 0), [(0, 0)]⟩
private abbrev run := runFuel (2 : ZMod 5) input 0 1
private def output : Configuration (ZMod 5) → Option (Option (List (Record (ZMod 5))))
  | .done out => some out
  | _ => none
private def payload : Configuration (ZMod 5) →
    Option (List (Pair (ZMod 5)) × List (Term (ZMod 5)) × ℕ)
  | .roots _ _ _ _ _ _ p _ => some (p.alphabet, p.terms, p.order)
  | _ => none
private def previous : Configuration (ZMod 5) → Option (List (List (Term (ZMod 5))))
  | .scan _ pre _ _ => some pre
  | _ => none

example : output (run 301 (.start [(0, 0)])).1 = some (some [rec]) := by decide +kernel
example : (run 301 (.start [(0, 0)])).2 =
    ⟨{ additions := 16, multiplications := 15, negations := 2, equalities := 8,
       control := 1640, data := 4065, constants := 146, output := 40 }, 52⟩ := by decide +kernel
example : payload (run 1 (.select ⟨ts, some (3, 1)⟩ [next] [] [ts] [] [])).1 =
    some ([(0, 0)], ts, 2) := by rfl
example : previous (run 1 (.select next [] [ts] [sep, ts] [] [])).1 =
    some [sep, ts] := by decide +kernel
example : output (run 2 (.select ⟨ts, some (0, 1)⟩ [next] [] [ts] [] [])).1 =
    some none := by decide +kernel
example : output (run 2 (.select stage [] [] [ts] [] [])).1 = some none := by decide +kernel
example : output (run 2 (.roots ctx 0 [] [] [] [] ⟨[], ts, 0⟩ (.done none))).1 =
    some none := by decide +kernel
example : output (run 10 (.collect ctx [((2, 3), [(4, 1)]), ((2, 3), [(4, 1)])]
    [] [] [] [])).1 = some (some [⟨ctx, (2, 3), [(4, 1)]⟩, ⟨ctx, (2, 3), [(4, 1)]⟩]) := by
  decide +kernel
example : output (run 4 (.reverse [rec, ⟨ctx, (2, 3), [(4, 1)]⟩] [])).1 =
    some (some [⟨ctx, (2, 3), [(4, 1)]⟩, rec]) := by decide +kernel
example : (run 1 (.start [])).2.base.data = 7 := by decide +kernel
example : (run 1 (.select stage [next] [] [ts] [] [])).2.base.data = 15 := by decide +kernel
example : (run 1 (.chain [] (MvPolynomial.QuadraticChainMachine.initial []))).2.base.control =
    4 := by
  decide +kernel
example : (run 1 (.roots ctx 0 [] [] [] [] ⟨[], ts, 0⟩ (.start []))).2.base.control = 2 := by
  decide +kernel
example : (run 1 (.reverse [] [])).2.base.data = 3 := by decide +kernel
example : (run 1 (.emit (some []))).2.base.output = 1 := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine
