/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement

/-!
# Kernel checks for actual quadratic evaluation lowering

A nontrivial quadratic power exercises two multiplication calls and an addition. Missing lookup
checks explicit zero allocation. The short run must suspend before executing the selected child.
The literal ledgers include initialization, base instructions, wrappers and final emission.
-/

@[expose] public section

namespace MvPolynomial.QuadraticEvaluationMachine

private def observe (s : Configuration (ZMod 3)) : Option (Pair (ZMod 3)) :=
  match s with
  | .ready (.done x) => some x
  | _ => none

private def powerRun := runFuel (2 : ZMod 3) [(1, 2)] 47
  (.ready (.terms [((1, 1), [(0, 2)])] (0, 0)))

example : (observe powerRun.1, powerRun.2) =
    (some (2, 1), ⟨⟨6, 10, 0, 0, 0, 86, 316, 30, 4⟩, 6⟩) := by decide +kernel

private def missingRun := runFuel (2 : ZMod 3) [] 31
  (.ready (.terms [((1, 1), [(2, 1)])] (0, 0)))

example : (observe missingRun.1, missingRun.2) =
    (some (0, 0), ⟨⟨4, 5, 0, 0, 0, 55, 203, 22, 3⟩, 3⟩) := by decide +kernel

private def shortRun := runFuel (2 : ZMod 3) [(1, 2)] 4
  (.ready (.terms [((1, 1), [(0, 2)])] (0, 0)))

private def waitingMultiply : Configuration (ZMod 3) → Bool
  | .call (.multiply _ _ _ _ _) _ (.start .mul) => true
  | _ => false

theorem short_run_suspends_before_multiplication :
    let result := runFuel (2 : ZMod 3) [(1, 2)] 4
      (.ready (.terms [((1, 1), [(0, 2)])] (0, 0)))
    ((match result.1 with
      | .call (.multiply _ _ _ _ _) _ (.start .mul) => true
      | _ => false), result.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 5, 24, 0, 0⟩, 3⟩) := by decide +kernel

end MvPolynomial.QuadraticEvaluationMachine
