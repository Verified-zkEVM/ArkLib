/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticPivotRefinement

/-!
# Kernel checks for coordinate pivot elimination

The first physical entry is a packed RHS; the pivot at index one must zero the second entry
and update that RHS. Literal ledgers include equality, norm inversion, factor and every row
instruction. Zero, imaginary-only and missing pivots test branch behavior. Mismatched rows
propagate the child rejection. Stored inverse payloads remain authoritative, including zero.
-/

@[expose] public section

namespace Matrix.QuadraticPivotMachine

private def observe : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.done row) => some row
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def packed :=
  let pivot : List (Pair (ZMod 3)) := [(2, 1), (1, 1)]
  let target := [(1, 2), (2, 1)]
  runFuel 2 113 (.ready (.lookup pivot target pivot target 1))

example : (observe packed.1, packed.2) =
    (some [(2, 0), (0, 0)], ⟨⟨11, 20, 4, 1, 2, 266, 879, 82, 10⟩, 3⟩) := by decide +kernel

private def zeroPivot := runFuel (2 : ZMod 3) 10 (.ready (.check [] [] (0, 0) (1, 1)))

example : (rejected zeroPivot.1, zeroPivot.2) =
    (true, ⟨⟨0, 0, 0, 0, 2, 20, 69, 12, 2⟩, 0⟩) := by decide +kernel

private def missing := runFuel (2 : ZMod 3) 1
  (.ready (.lookup [] [(1, 1)] [] [(1, 1)] 0))

example : (rejected missing.1, missing.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 1, 2, 0, 1⟩, 0⟩) := by decide +kernel

private def mismatch :=
  let pivot : List (Pair (ZMod 3)) := [(1, 1)]
  let target := [(2, 1), (1, 0)]
  runFuel 2 81 (.ready (.lookup pivot target pivot target 0))

example : (rejected mismatch.1, mismatch.2) =
    (true, ⟨⟨7, 15, 4, 1, 2, 180, 607, 62, 8⟩, 1⟩) := by decide +kernel

private def checked : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .ready (.inverse _ _ x _) => some x
  | _ => none

theorem imaginary_pivot_reaches_inverse_phase :
    (match (runFuel (2 : ZMod 3) 10
      (.ready (.check [] [] (0, 1) (1, 1)))).1 with
    | .ready (.inverse _ _ x _) => some x
    | _ => none) = some (0, 1) := by decide +kernel

private def inverse : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .ready (.negate _ _ _ inv) => some inv
  | _ => none

example : inverse (runFuel (0 : ZMod 3) 15
    (.arithmetic (.inverse [] [] (0, 0)) ⟨2, (1, 1), (2, 0)⟩ (.start .inv))).1 =
      some (2, 1) := by decide +kernel

private def zeroInverse := runFuel (2 : ZMod 3) 15
  (.arithmetic (.inverse [] [] (0, 0)) ⟨2, (0, 0), (1, 1)⟩ (.start .inv))

example : (inverse zeroInverse.1, zeroInverse.2.base.inversions) =
    (some (0, 0), 1) := by decide +kernel

end Matrix.QuadraticPivotMachine
