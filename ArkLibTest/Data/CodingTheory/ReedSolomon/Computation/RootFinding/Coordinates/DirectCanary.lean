/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.DirectRefinement
/-!
# Kernel checks for coordinate direct coefficients

Two residual recoveries around an actual candidate increment produce a nonreal coefficient.
Singular slopes and child failures reject. Focused ledgers expose retained recovery/increment
payloads, one-pair construction, lookup traversal, second-call initialization and final emission.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticDirectCoefficientMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (Option (Pair (ZMod 3)))
  | .done out => some out
  | _ => none

private def input : Input (ZMod 3) :=
  ⟨[(1, 2)], [((1, 1), [(1, 1)]), ((0, 1), [])], (2, 1), 0⟩

private def completed := runFuel (2 : ZMod 3) input 1 1 0 663 (.start [(0, 1)])
private def singular := runFuel (2 : ZMod 3) input 1 1 0 30
  (.arithmetic (.ready (.negate (1, 2) (1, 2))))
private def missing := runFuel (2 : ZMod 3) input 1 1 0 3 (.lookup none [] 7 [])

private def recoveredPayload : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .recover _ _ _ (.system p _) => some p.center
  | _ => none

private def retained := runFuel (2 : ZMod 3) input 1 1 0 1
  (.recover none [] ⟨[], [], (2, 2), 1⟩ (.start []))

private def updatePending : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .update _ _ _ (.save v _ _) => some v
  | _ => none

private def increment := runFuel (2 : ZMod 3) input 1 1 0 10
  (.update (1, 0) [] (0, 1) (.ready (.add (1, 1) [] [])))

private def selectedUpdate : Configuration (ZMod 3) → Option (Pair (ZMod 3) × ℕ)
  | .update _ _ gamma (.ready (.start _ j)) => some (gamma, j)
  | _ => none

private def selected := runFuel (2 : ZMod 3) input 4 2 1 1 (.lookup none [] 0 [(2, 1)])

private def restarted : Configuration (ZMod 3) →
    Option (Option (Pair (ZMod 3)) × List (Pair (ZMod 3)) × List (Pair (ZMod 3)))
  | .recover b xs p (.start _) => some (b, xs, p.coefficients)
  | _ => none

private def second := runFuel (2 : ZMod 3) input 1 1 0 1
  (.update (2, 1) [(0, 1)] (1, 0) (.ready (.done (some [(2, 2)]))))

private def lookedUp : Configuration (ZMod 3) → Option (ℕ × List (Pair (ZMod 3)))
  | .lookup _ _ j vs => some (j, vs)
  | _ => none

private def lookupStart := runFuel (2 : ZMod 3) input 1 2 1 1
  (.recover (some (1, 1)) [] input (.done (some [(2, 1), (1, 2)])))
private def lookupNext := runFuel (2 : ZMod 3) input 1 2 1 1
  (.lookup (some (1, 1)) [] 1 [(2, 1), (1, 2)])

private def failedRecovery := runFuel (2 : ZMod 3) input 1 1 0 3
  (.recover none [] input (.done none))
private def failedUpdate := runFuel (2 : ZMod 3) input 1 1 0 3
  (.update (1, 1) [] (1, 0) (.ready (.done none)))
private def emitted := runFuel (2 : ZMod 3) input 1 1 0 2
  (.arithmetic (.ready (.emit (some (0, 2)))))


example : (observe completed.1, completed.2) =
    (some (some (0, 2)), ⟨⟨57, 70, 12, 3, 14, 3326, 8648, 436, 68⟩, 60⟩) := by decide +kernel

example : (observe singular.1, singular.2) =
    (some none, ⟨⟨2, 0, 2, 0, 2, 86, 271, 32, 4⟩, 0⟩) := by decide +kernel

example : (observe missing.1, missing.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 4, 8, 0, 1⟩, 0⟩) := by decide +kernel

example : (recoveredPayload retained.1, retained.2) =
    (some (2, 2), ⟨⟨0, 0, 0, 0, 0, 2, 9, 0, 0⟩, 0⟩) := by decide +kernel

example : (updatePending increment.1, increment.2) =
    (some (1, 2), ⟨⟨2, 0, 0, 0, 0, 28, 88, 10, 1⟩, 0⟩) := by decide +kernel

example : (selectedUpdate selected.1, selected.2) =
    (some ((1, 0), 2), ⟨⟨0, 0, 0, 0, 0, 1, 10, 2, 0⟩, 4⟩) := by decide +kernel

example : (restarted second.1, second.2) =
    (some (some (2, 1), [(0, 1)], [(2, 2)]),
      ⟨⟨0, 0, 0, 0, 0, 1, 11, 0, 0⟩, 0⟩) := by decide +kernel

example : (lookedUp lookupStart.1, lookupStart.2) =
    (some (1, [(2, 1), (1, 2)]), ⟨⟨0, 0, 0, 0, 0, 1, 4, 0, 0⟩, 0⟩) := by decide +kernel

example : (lookedUp lookupNext.1, lookupNext.2) =
    (some (0, [(1, 2)]), ⟨⟨0, 0, 0, 0, 0, 1, 4, 0, 0⟩, 2⟩) := by decide +kernel

example : (observe failedRecovery.1, failedRecovery.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 4, 8, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe failedUpdate.1, failedUpdate.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 4, 8, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe emitted.1, emitted.2) =
    (some (some (0, 2)), ⟨⟨0, 0, 0, 0, 0, 3, 6, 0, 1⟩, 0⟩) := by decide +kernel

private def entered := runFuel (2 : ZMod 3) input 1 1 0 1 (.start [(0, 1)])

example : (restarted entered.1, entered.2) =
    (some (none, [(0, 1)], [(1, 2)]),
      ⟨⟨0, 0, 0, 0, 0, 1, 9, 0, 0⟩, 0⟩) := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticDirectCoefficientMachine
