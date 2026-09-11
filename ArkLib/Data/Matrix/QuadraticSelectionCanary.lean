/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticSelectionRefinement

/-!
# Kernel checks for coordinate first-pivot selection

Distinct zero rows precede an imaginary-only pivot. Duplicates and a malformed untouched tail
check first-pivot selection, row order and no speculative validation. Exact ledgers also cover
all-zero restoration, empty/zero-width/missing inputs, and retained partial child states.
-/

@[expose] public section

namespace Matrix.QuadraticSelectionMachine

private instance : DecidableEq (Row (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (Bool × List (Row (ZMod 3)))
  | .ready (.done b rows) => some (b, rows)
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def z₁ : Row (ZMod 3) := ([(1, 2), (0, 0)], (1, 0))
private def z₂ : Row (ZMod 3) := ([(2, 0), (0, 0)], (0, 2))
private def p : Row (ZMod 3) := ([(0, 0), (0, 1)], (2, 1))
private def bad : Row (ZMod 3) := ([], (1, 1))

private def first := runFuel (2 : ZMod 3) 1 43
  (.ready (.scan [z₁, z₂, p, z₁, p, bad] []))

example : (observe first.1, first.2) =
    (some (true, [p, z₁, z₂, z₁, p, bad]),
      ⟨⟨0, 0, 0, 0, 6, 73, 282, 36, 4⟩, 9⟩) := by decide +kernel

private def allZero := runFuel (2 : ZMod 3) 1 31 (.ready (.scan [z₁, z₂] []))

example : (observe allZero.1, allZero.2) =
    (some (false, [z₁, z₂]), ⟨⟨0, 0, 0, 0, 4, 51, 193, 24, 3⟩, 6⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) 0 3 (.ready (.scan [] []))

theorem empty_rows_return_no_pivot :
    let result := runFuel (2 : ZMod 3) 0 3 (.ready (.scan [] []))
    ((match result.1 with
      | .ready (.done b rows) => some (b, rows)
      | _ => none), result.2) =
    (some (false, []), ⟨⟨0, 0, 0, 0, 0, 3, 5, 0, 1⟩, 0⟩) := by decide +kernel

private def noColumns := runFuel (2 : ZMod 3) 0 2 (.ready (.scan [bad] []))

example : (rejected noColumns.1, noColumns.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 8, 0, 1⟩, 0⟩) := by decide +kernel

private def missing := runFuel (2 : ZMod 3) 2 3
  (.ready (.scan [([(0, 1)], (1, 0))] []))

example : (rejected missing.1, missing.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 3, 12, 0, 1⟩, 2⟩) := by decide +kernel

private def restoring : Configuration (ZMod 3) → Option (Row (ZMod 3))
  | .ready (.restore (some r) _ _) => some r
  | _ => none

private def stored := runFuel (2 : ZMod 3) 0 9
  (.checking ([(0, 0)], (1, 2)) [] [] ⟨2, (0, 1), (0, 0)⟩ (.start .equal))

example : (restoring stored.1, stored.2) =
    (some ([(0, 0)], (1, 2)), ⟨⟨0, 0, 0, 0, 2, 19, 65, 10, 1⟩, 0⟩) := by decide +kernel

private def pending : Configuration (ZMod 3) → Option (Pair (ZMod 3) × Pair (ZMod 3))
  | .checking _ _ _ payload (.start .equal) => some (payload.left, payload.right)
  | _ => none

private def launched := runFuel (2 : ZMod 3) 0 1 (.ready (.check z₁ [] [] (0, 1)))

example : (pending launched.1, launched.2) =
    (some ((0, 1), (0, 0)), ⟨⟨0, 0, 0, 0, 0, 1, 8, 2, 0⟩, 0⟩) := by decide +kernel

end Matrix.QuadraticSelectionMachine
