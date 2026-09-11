/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.QuadraticUpdateRefinement

/-!
# Kernel checks for coordinate indexed updates

Middle and final updates preserve ordered prefixes and untouched suffixes. Empty input rejects;
a retained operand different from the supplied increment exposes accidental reconstruction.
The separate save carries an exact allocation ledger.
-/

@[expose] public section

namespace Polynomial.QuadraticUpdateMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (Option (List (Pair (ZMod 3))))
  | .ready (.done out) => some out
  | _ => none

private def cs : List (Pair (ZMod 3)) := [(1, 1), (2, 1), (0, 1)]
private def middle := runFuel (2 : ZMod 3) (2, 1) 17 (.ready (.start cs 1))
private def lastCell := runFuel (2 : ZMod 3) (2, 1) 19 (.ready (.start cs 2))
private def empty := runFuel (2 : ZMod 3) (2, 1) 3 (.ready (.start [] 20))

example : (observe middle.1, middle.2) =
    (some (some [(1, 1), (1, 2), (0, 1)]),
      ⟨⟨2, 0, 0, 0, 0, 25, 103, 10, 2⟩, 3⟩) := by decide +kernel

example : (observe lastCell.1, lastCell.2) =
    (some (some [(1, 1), (2, 1), (2, 2)]),
      ⟨⟨2, 0, 0, 0, 0, 27, 117, 10, 2⟩, 5⟩) := by decide +kernel

theorem empty_coefficients_return_none :
    let result := runFuel (2 : ZMod 3) (2, 1) 3 (.ready (.start [] 20))
    ((match result.1 with
      | .ready (.done out) => some out
      | _ => none), result.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 3, 9, 0, 1⟩, 0⟩) := by decide +kernel

private def pending : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .save v _ _ => some v
  | _ => none

private def retained := runFuel (2 : ZMod 3) (1, 0) 9
  (.call [] [] ⟨2, (1, 1), (2, 2)⟩ (.start .add))

example : (pending retained.1, retained.2) =
    (some (0, 0), ⟨⟨2, 0, 0, 0, 0, 17, 62, 10, 1⟩, 0⟩) := by decide +kernel

private def restored : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.restore _ out) => some out
  | _ => none

private def saved := runFuel (2 : ZMod 3) (1, 0) 1 (.save (1, 2) [(0, 1)] [(1, 1)])

example : (restored saved.1, saved.2) =
    (some [(1, 2), (0, 1)], ⟨⟨0, 0, 0, 0, 0, 1, 6, 0, 0⟩, 0⟩) := by decide +kernel

end Polynomial.QuadraticUpdateMachine
