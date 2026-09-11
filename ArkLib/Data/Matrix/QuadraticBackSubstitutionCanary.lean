/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.QuadraticBackSubstitutionRefinement

/-!
# Kernel checks for coordinate back substitution

Two ordered pivots change nonzero initial pivot values while retaining a nonzero free coordinate.
Residual checks inspect both coordinates before solving. Literal ledgers expose caller input
and zero initialization, reversal allocation, child dispatch and retained suspended payloads.
-/

@[expose] public section

namespace Matrix.QuadraticBackSubstitutionMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance
private instance : DecidableEq (Row (ZMod 3)) := inferInstance
private instance : DecidableEq (Pivot (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.done v) => some v
  | _ => none

private def inconsistent : Configuration (ZMod 3) → Bool
  | .ready .inconsistent => true
  | _ => false

private def rejected : Configuration (ZMod 3) → Bool
  | .ready .rejected => true
  | _ => false

private def pivots : List (Pivot (ZMod 3)) :=
  [(0, ([(1, 1), (1, 0), (1, 2)], (2, 0))),
    (1, ([(0, 0), (0, 1), (2, 0)], (1, 1)))]

private def values : List (Pair (ZMod 3)) := [(1, 0), (2, 1), (0, 1)]

private def solved := runFuel (2 : ZMod 3) 326
  (.ready (.check [([(0, 0), (0, 0), (0, 0)], (0, 0))] pivots values))

private def contradiction := runFuel (2 : ZMod 3) 20
  (.ready (.check [([], (0, 0)), ([], (0, 1))] pivots values))

private def empty := runFuel (2 : ZMod 3) 3 (.ready (.check [] [] values))

private def malformed := runFuel (2 : ZMod 3) 4
  (.ready (.solve [(1, ([], (1, 2)))] []))

private def pendingCall : Configuration (ZMod 3) →
    Option (ℕ × Row (ZMod 3) × List (Pair (ZMod 3)) × Pair (ZMod 3))
  | .row input _ (.ready (.dot _ _ s)) => some (input.index, input.row, input.values, s)
  | _ => none

private def called := runFuel (2 : ZMod 3) 1
  (.ready (.solve [(1, ([(0, 0), (0, 1)], (1, 2)))] values))

private def reverseOrder : Configuration (ZMod 3) → Option (List ℕ)
  | .ready (.solve ps _) => some (ps.map Prod.fst)
  | _ => none

private def reversed := runFuel (2 : ZMod 3) 3 (.ready (.reverse pivots [] values))

private def pending : Configuration (ZMod 3) → Bool
  | .row _ _ (.ready .rejected) => true
  | _ => false

private def child := runFuel (2 : ZMod 3) 1
  (.row ⟨2, ([], (1, 2)), 1, values⟩ [] (.ready (.lookup [] 1 (0, 0))))

private def retained := runFuel (2 : ZMod 3) 9
  (.checking [] pivots values ⟨2, (0, 1), (0, 1)⟩ (.start .equal))

private def checkedZero : Configuration (ZMod 3) → Bool
  | .ready (.check [] _ _) => true
  | _ => false

private def returnedRow := runFuel (2 : ZMod 3) 10
  (.row ⟨2, ([], (2, 1)), 0, values⟩ []
    (.ready (.difference (1, 0) (0, 1))))

private def difference : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .row _ _ (.ready (.scale _ d)) => some d
  | _ => none


example : (observe solved.1, solved.2) =
    (some [(1, 2), (2, 2), (0, 1)],
      ⟨⟨38, 50, 8, 2, 6, 909, 2866, 260, 28⟩, 8⟩) := by decide +kernel

example : (inconsistent contradiction.1, contradiction.2) =
    (true, ⟨⟨0, 0, 0, 0, 4, 40, 142, 24, 3⟩, 0⟩) := by decide +kernel

theorem empty_pivot_list_preserves_values :
    let values : List (Pair (ZMod 3)) := [(1, 0), (2, 1), (0, 1)]
    let result := runFuel (2 : ZMod 3) 3 (.ready (.check [] [] values))
    ((match result.1 with
      | .ready (.done v) => some v
      | _ => none), result.2) =
      (some values, ⟨⟨0, 0, 0, 0, 0, 3, 7, 0, 1⟩, 0⟩) := by decide +kernel

example : (rejected malformed.1, malformed.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 6, 26, 2, 2⟩, 0⟩) := by decide +kernel

example : (pendingCall called.1, called.2) =
    (some (1, ([(0, 0), (0, 1)], (1, 2)), values, (0, 0)),
      ⟨⟨0, 0, 0, 0, 0, 1, 13, 2, 0⟩, 0⟩) := by decide +kernel

example : (reverseOrder reversed.1, reversed.2) =
    (some [1, 0], ⟨⟨0, 0, 0, 0, 0, 3, 14, 0, 0⟩, 0⟩) := by decide +kernel

example : (pending child.1, child.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 1⟩, 0⟩) := by decide +kernel

example : (checkedZero retained.1, retained.2) =
    (true, ⟨⟨0, 0, 0, 0, 2, 19, 63, 10, 1⟩, 0⟩) := by decide +kernel

example : (difference returnedRow.1, returnedRow.2) =
    (some (2, 2), ⟨⟨2, 0, 0, 0, 0, 29, 91, 10, 1⟩, 0⟩) := by decide +kernel

private def started := runFuel (2 : ZMod 3) 4 (.ready (.check [] pivots values))

example : (reverseOrder started.1, started.2) =
    (some [1, 0], ⟨⟨0, 0, 0, 0, 0, 4, 18, 0, 0⟩, 0⟩) := by decide +kernel

end Matrix.QuadraticBackSubstitutionMachine
