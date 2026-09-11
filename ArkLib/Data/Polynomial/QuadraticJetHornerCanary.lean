/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.QuadraticJetHornerRefinement

/-!
# Kernel checks for quadratic jet Horner lowering

The linear polynomial checks coordinate arithmetic, old-predecessor carry and output order.
The empty polynomial checks explicit zero initialization; zero requested entries exercise the
control-only path. Literal ledgers retain every base program, wrapper, allocation and output.
-/

@[expose] public section

namespace Polynomial.QuadraticJetHornerMachine

private def observe : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .ready (.done js) => some js
  | _ => none

private def linear := runFuel (2 : ZMod 3) (2, 1) 121
  (.ready (.initialize [(1, 1), (1, 1)] 2 []))

example : (observe linear.1, linear.2) =
    (some [(2, 1), (1, 1)], ⟨⟨16, 20, 0, 0, 0, 217, 823, 84, 10⟩, 5⟩) := by decide +kernel

private def empty := runFuel (2 : ZMod 3) (1, 2) 9 (.ready (.initialize [] 3 []))

example : (observe empty.1, empty.2) =
    (some [(0, 0), (0, 0), (0, 0)], ⟨⟨0, 0, 0, 0, 0, 9, 31, 6, 3⟩, 7⟩) := by decide +kernel

private def noJet := runFuel (2 : ZMod 3) (1, 2) 6 (.ready (.initialize [(1, 1)] 0 []))

theorem zero_requested_jets_emit_empty_output :
    let result := runFuel (2 : ZMod 3) (1, 2) 6
      (.ready (.initialize [(1, 1)] 0 []))
    ((match result.1 with
      | .ready (.done js) => some js
      | _ => none), result.2) =
    (some [], ⟨⟨0, 0, 0, 0, 0, 6, 17, 0, 0⟩, 1⟩) := by decide +kernel

end Polynomial.QuadraticJetHornerMachine
