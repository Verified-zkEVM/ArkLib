/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticColumnRefinement

/-!
# Kernel checks for coordinate column elimination

Repeated target rows remain in order after the unchanged pivot. Exact ledgers include every
pivot instruction and outer allocation. Empty/zero pivots reject; a saved equality payload
whose operand differs from the pivot head checks that child inputs remain authoritative.
-/

@[expose] public section

namespace Matrix.QuadraticColumnMachine

private def observe : Configuration (ZMod 3) → Option (List (List (Pair (ZMod 3))))
  | .ready (.done rows) => some rows
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def repeated :=
  let p : List (Pair (ZMod 3)) := [(2, 1), (1, 1)]
  let t := [(1, 2), (2, 1)]
  runFuel 2 1 248 (.ready (.begin [p, t, t]))

example : (observe repeated.1, repeated.2) =
    (some [[(2, 1), (1, 1)], [(2, 0), (0, 0)], [(2, 0), (0, 0)]],
      ⟨⟨22, 40, 8, 2, 6, 790, 2345, 176, 22⟩, 9⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) 1 1 (.ready (.begin []))

example : (rejected empty.1, empty.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0⟩) := by decide +kernel

private def zeroPivot := runFuel (2 : ZMod 3) 1 10 (.ready (.check [] [] (0, 0)))

example : (rejected zeroPivot.1, zeroPivot.2) =
    (true, ⟨⟨0, 0, 0, 0, 2, 20, 69, 12, 2⟩, 0⟩) := by decide +kernel

private def scanning : Configuration (ZMod 3) → Option (List (List (Pair (ZMod 3))))
  | .ready (.scan _ _ rev) => some rev
  | _ => none

theorem retained_equality_payload_resumes_scan :
    (match (runFuel (2 : ZMod 3) 0 9
      (.checking [(0, 0)] [] ⟨2, (0, 1), (0, 0)⟩ (.start .equal))).1 with
    | .ready (.scan _ _ rev) => some rev
    | _ => none) =
      some [[(0, 0)]] := by decide +kernel

private def pendingRejection : Configuration (ZMod 3) → Bool
  | .pivot _ _ _ (.ready .rejected) => true
  | _ => false

private def suspended := runFuel (2 : ZMod 3) 0 1
  (.pivot [] [] [] (.ready (.lookup [] [] [] [] 0)))

example : (pendingRejection suspended.1, suspended.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 1⟩, 0⟩) := by decide +kernel

end Matrix.QuadraticColumnMachine
