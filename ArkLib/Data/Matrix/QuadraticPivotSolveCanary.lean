/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticPivotSolveRefinement

/-!
# Kernel checks for coordinate pivot correction

The initial pivot value is nonzero, so replacement by the correction is observably wrong.
Nontrivial RHS and norm arithmetic preserve other coordinates through indexed restoration.
Zero/unequal/missing cases and partial dot/save phases carry literal ledgers. A deliberately
different retained inverse operand checks that arithmetic input is never reconstructed.
-/

@[expose] public section

namespace Matrix.QuadraticPivotSolveMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.done vs) => some vs
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def input : Input (ZMod 3) :=
  ⟨2, ([(1, 1), (0, 1), (2, 0)], (2, 1)), 1, [(1, 0), (2, 1), (0, 1)]⟩

private def corrected := runFuel input 155 (.ready (.dot input.row.1 input.values (0, 0)))

example : (observe corrected.1, corrected.2) =
    (some [(1, 0), (1, 2), (0, 1)],
      ⟨⟨19, 25, 4, 1, 2, 288, 1073, 122, 13⟩, 6⟩) := by decide +kernel

private def zeroPivot := runFuel input 10 (.ready (.check (0, 0) (1, 1)))

example : (rejected zeroPivot.1, zeroPivot.2) =
    (true, ⟨⟨0, 0, 0, 0, 2, 20, 69, 12, 2⟩, 0⟩) := by decide +kernel

private def unequal := runFuel input 27 (.ready (.dot [(1, 1), (0, 1)] [(1, 0)] (0, 0)))

example : (rejected unequal.1, unequal.2) =
    (true, ⟨⟨4, 5, 0, 0, 0, 50, 185, 20, 3⟩, 0⟩) := by decide +kernel

private def missingPivot := runFuel input 1 (.ready (.lookup [] 1 (0, 0)))

example : (rejected missingPivot.1, missingPivot.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 1, 2, 0, 1⟩, 0⟩) := by decide +kernel

private def missingUpdate := runFuel input 1 (.ready (.update [] 0 [] (1, 1)))

example : (rejected missingUpdate.1, missingUpdate.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 1, 2, 0, 1⟩, 0⟩) := by decide +kernel

private def inverse : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .ready (.negate inv _) => some inv
  | _ => none

theorem retained_inverse_operand_is_authoritative :
    let input : Input (ZMod 3) :=
      ⟨2, ([(1, 1), (0, 1), (2, 0)], (2, 1)), 1, [(1, 0), (2, 1), (0, 1)]⟩
    (match (runFuel input 15
      (.arithmetic (.inverse (0, 0)) ⟨2, (1, 1), (2, 0)⟩ (.start .inv))).1 with
    | .ready (.negate inv _) => some inv
    | _ => none) =
      some (2, 1) := by decide +kernel

private def pendingDot : Configuration (ZMod 3) → Option (Pair (ZMod 3) × Pair (ZMod 3))
  | .addDot _ _ s p => some (s, p)
  | _ => none

private def product := runFuel input 16 (.ready (.dot [(1, 1)] [(2, 1)] (1, 0)))

example : (pendingDot product.1, product.2) =
    (some ((1, 0), (1, 0)), ⟨⟨2, 5, 0, 0, 0, 31, 115, 10, 1⟩, 0⟩) := by decide +kernel

private def pendingSave : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.restore _ out) => some out
  | _ => none

private def saved := runFuel input 1 (.saveUpdate [(1, 0)] [(0, 1)] (1, 2))

example : (pendingSave saved.1, saved.2) =
    (some [(1, 2), (0, 1)], ⟨⟨0, 0, 0, 0, 0, 1, 6, 0, 0⟩, 1⟩) := by decide +kernel

end Matrix.QuadraticPivotSolveMachine
