/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticRowRefinement

/-!
# Kernel checks for coordinate row-add-multiple

Nontrivial coordinate products, ordered entries and literal ledgers test both arithmetic calls
and explicit output allocation. Empty and mismatched rows test terminal paths. A deliberately
different saved payload checks that suspended calls do not reconstruct their inputs.
-/

@[expose] public section

namespace Matrix.QuadraticRowMachine

private def observe : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.done row) => some row
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def row := runFuel (2 : ZMod 3) (1, 1) 60
  (.ready (.scan [(1, 0), (2, 1)] [(1, 1), (2, 0)] []))

example : (observe row.1, row.2) =
    (some [(1, 2), (1, 0)], ⟨⟨8, 10, 0, 0, 0, 106, 397, 40, 5⟩, 0⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) (1, 1) 2 (.ready (.scan [] [] []))

example : (observe empty.1, empty.2) =
    (some [], ⟨⟨0, 0, 0, 0, 0, 2, 5, 0, 1⟩, 0⟩) := by decide +kernel

private def mismatch := runFuel (2 : ZMod 3) (1, 1) 29
  (.ready (.scan [(1, 0), (2, 1)] [(1, 1)] []))

example : (rejected mismatch.1, mismatch.2) =
    (true, ⟨⟨4, 5, 0, 0, 0, 52, 193, 20, 3⟩, 0⟩) := by decide +kernel

theorem mismatched_empty_row_is_rejected :
    (match (runFuel (2 : ZMod 3) (1, 1) 1
      (.ready (.scan [] [(1, 1)] []))).1 with
    | .ready .rejected => true
    | _ => false) = true := by decide +kernel

private def product : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .ready (.add _ _ _ _ p) => some p
  | _ => none

example : product (runFuel (0 : ZMod 3) (0, 0) 15
    (.call (.product [] [] [] (0, 0)) ⟨2, (1, 1), (2, 1)⟩ (.start .mul))).1 =
      some (1, 0) := by decide +kernel

end Matrix.QuadraticRowMachine
