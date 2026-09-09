/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.LiftRefinement
/-!
# Kernel checks for coordinate lifting loops

A complete nonzero-center linear lift recovers the expected descending vector. Partial stages
expose decreasing stage counts, increasing residual order, retained input/gamma, descending
update indices, both failure returns and exact initialization/wrapper/option charges.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticRegularLiftMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (Option (List (Pair (ZMod 3))))
  | .done out => some out
  | _ => none

private def input : Input (ZMod 3) :=
  ⟨[(0, 0), (1, 1)], [((1, 0), [(1, 1)]), ((2, 0), [(0, 1)])], (1, 1), 0⟩

private def completed := runFuel (2 : ZMod 3) input 1 2 1904 (.start [(0, 0), (0, 1)])
private def noStages := runFuel (2 : ZMod 3) input 0 2 3 (.start [(0, 1)])

private def counters : Configuration (ZMod 3) → Option (ℕ × ℕ × List (Pair (ZMod 3)))
  | .loop k n cs _ => some (k, n, cs)
  | _ => none

private def started := runFuel (2 : ZMod 3) input 3 4 1 (.start [(0, 1)])

private def stagedInput : Configuration (ZMod 3) →
    Option (ℕ × ℕ × List (Pair (ZMod 3)) × Pair (ZMod 3))
  | .direct k n _ p _ => some (k, n, p.coefficients, p.center)
  | _ => none

private def staged := runFuel (2 : ZMod 3) input 3 4 1 (.loop 2 2 [(2, 1)] [(0, 1)])

private def childCenter : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .direct _ _ _ _ (.recover _ _ p _) => some p.center
  | _ => none

private def retained := runFuel (2 : ZMod 3) input 3 4 1
  (.direct 2 1 [] ⟨[(2, 1)], [], (2, 2), 0⟩ (.start []))

private def updatedInput : Configuration (ZMod 3) →
    Option (Pair (ZMod 3) × ℕ × List (Pair (ZMod 3)))
  | .update _ _ _ gamma (.ready (.start cs j)) => some (gamma, j, cs)
  | _ => none

private def returned := runFuel (2 : ZMod 3) input 3 4 1
  (.direct 2 1 [] ⟨[(2, 1)], [], (2, 2), 0⟩ (.done (some (0, 1))))

private def pending : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .update _ _ _ _ (.save v _ _) => some v
  | _ => none

private def increment := runFuel (2 : ZMod 3) input 3 4 10
  (.update 2 1 [] (0, 1) (.ready (.add (1, 1) [] [])))

private def next := runFuel (2 : ZMod 3) input 3 4 1
  (.update 2 1 [] (0, 1) (.ready (.done (some [(1, 2)]))))
private def failedDirect := runFuel (2 : ZMod 3) input 3 4 2
  (.direct 2 1 [] input (.done none))
private def failedUpdate := runFuel (2 : ZMod 3) input 3 4 2
  (.update 2 1 [] (0, 1) (.ready (.done none)))
private def finished := runFuel (2 : ZMod 3) input 3 4 2 (.loop 4 0 [(1, 2)] [])


example : (observe completed.1, completed.2) =
    (some (some [(1, 0), (1, 1)]),
      ⟨⟨187, 260, 28, 7, 30, 12931, 31748, 1262, 167⟩, 169⟩) := by decide +kernel

example : (observe noStages.1, noStages.2) =
    (some (some [(0, 0), (1, 1)]), ⟨⟨0, 0, 0, 0, 0, 3, 10, 0, 1⟩, 3⟩) := by decide +kernel

example : (counters started.1, started.2) =
    (some (1, 3, [(0, 0), (1, 1)]), ⟨⟨0, 0, 0, 0, 0, 1, 5, 0, 0⟩, 2⟩) := by decide +kernel

example : (stagedInput staged.1, staged.2) =
    (some (2, 1, [(2, 1)], (1, 1)), ⟨⟨0, 0, 0, 0, 0, 1, 10, 0, 0⟩, 2⟩) := by decide +kernel

example : (childCenter retained.1, retained.2) =
    (some (2, 2), ⟨⟨0, 0, 0, 0, 0, 2, 11, 0, 0⟩, 0⟩) := by decide +kernel

example : (updatedInput returned.1, returned.2) =
    (some ((0, 1), 1, [(2, 1)]), ⟨⟨0, 0, 0, 0, 0, 1, 6, 0, 0⟩, 2⟩) := by decide +kernel

example : (pending increment.1, increment.2) =
    (some (1, 2), ⟨⟨2, 0, 0, 0, 0, 28, 88, 10, 1⟩, 0⟩) := by decide +kernel

example : (counters next.1, next.2) =
    (some (3, 1, [(1, 2)]), ⟨⟨0, 0, 0, 0, 0, 1, 5, 0, 0⟩, 1⟩) := by decide +kernel

example : (observe failedDirect.1, failedDirect.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe failedUpdate.1, failedUpdate.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe finished.1, finished.2) =
    (some (some [(1, 2)]), ⟨⟨0, 0, 0, 0, 0, 2, 5, 0, 1⟩, 1⟩) := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticRegularLiftMachine
