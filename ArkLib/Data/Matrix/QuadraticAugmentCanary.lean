/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticAugmentRefinement

/-!
# Kernel checks for augmented coordinate column execution

Distinct RHS values on repeated coefficient rows test pairing, physical column j+1 and order.
Literal ledgers include packing, all child work, unpacking and both outer reversals. Empty,
zero-width, zero-pivot and malformed partial states reject without dropping their charges.
-/

@[expose] public section

namespace Matrix.QuadraticAugmentMachine

private def observe : Configuration (ZMod 3) → Option (List (Row (ZMod 3)))
  | .ready (.done rows) => some rows
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def augmented := runFuel (2 : ZMod 3) 0 265
  (.ready (.pack [([(1, 1)], (2, 1)), ([(2, 1)], (1, 2)), ([(2, 1)], (0, 1))] []))

example : (observe augmented.1, augmented.2) =
    (some [([(1, 1)], (2, 1)), ([(0, 0)], (2, 0)), ([(0, 0)], (1, 2))],
      ⟨⟨22, 40, 8, 2, 6, 1055, 2950, 176, 23⟩, 10⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) 0 4 (.ready (.pack [] []))

example : (rejected empty.1, empty.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 5, 10, 0, 2⟩, 1⟩) := by decide +kernel

private def noColumns := runFuel (2 : ZMod 3) 0 8 (.ready (.pack [([], (1, 1))] []))

example : (rejected noColumns.1, noColumns.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 11, 40, 0, 2⟩, 3⟩) := by decide +kernel

private def zeroPivot := runFuel (2 : ZMod 3) 0 18 (.ready (.pack [([(0, 0)], (1, 1))] []))

example : (rejected zeroPivot.1, zeroPivot.2) =
    (true, ⟨⟨0, 0, 0, 0, 2, 41, 131, 12, 3⟩, 4⟩) := by decide +kernel

theorem malformed_unpack_is_rejected :
    (match (runFuel (2 : ZMod 3) 0 1 (.ready (.unpack [[]] []))).1 with
    | .ready .rejected => true
    | _ => false) = true := by
  decide +kernel

private def pendingRows : Configuration (ZMod 3) → Option (List (Row (ZMod 3)))
  | .ready (.unpack [] rev) => some rev
  | _ => none

private def suspended := runFuel (2 : ZMod 3) 0 1
  (.ready (.unpack [[(2, 1), (1, 1)]] []))

example : (pendingRows suspended.1, suspended.2) =
    (some [([(1, 1)], (2, 1))], ⟨⟨0, 0, 0, 0, 0, 1, 10, 0, 0⟩, 0⟩) := by decide +kernel

end Matrix.QuadraticAugmentMachine
