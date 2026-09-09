/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Refinement
/-!
# Kernel checks for coordinate coefficient recovery

A nonzero-center linear residual recovers both coefficients through actual system and solve
children. Zero-width contradiction, both failure returns, partial seed allocation, retained
payloads and exact handoff ledgers distinguish success from uncharged or fabricated output.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticResidualCoefficientMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance
private instance : DecidableEq (Row (ZMod 3)) := inferInstance
private instance : DecidableEq (Pivot (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (Option (List (Pair (ZMod 3))))
  | .done out => some out
  | _ => none

private def input : Input (ZMod 3) := ⟨[], [((1, 0), [(0, 1)])], (1, 1), 0⟩

private def completed := runFuel (2 : ZMod 3) input 2 717 (.start [(0, 1), (1, 0)])
private def empty := runFuel (2 : ZMod 3) input 0 100 (.start [])
private def inconsistent := runFuel (2 : ZMod 3) input 0 1000 (.start [(0, 1)])

private def initialized : Configuration (ZMod 3) → Option (ℕ × List (Pair (ZMod 3)))
  | .initialize _ _ n zs => some (n, zs)
  | _ => none

private def seeded := runFuel (2 : ZMod 3) input 2 1 (.initialize [] [] 2 [(1, 2)])

private def payload : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .system p _ => some p.center
  | _ => none

private def entered := runFuel (2 : ZMod 3) input 2 1 (.start [(0, 1)])

private def nestedPayload : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .system _ (.sample p _) => some p.center
  | _ => none

private def retained := runFuel (2 : ZMod 3) input 2 1
  (.system ⟨[(2, 1)], [], (2, 2), 1⟩ (.start [(0, 1)]))

private def systemPending : Configuration (ZMod 3) → Bool
  | .system _ (.matrix (.ready (.scan [] []))) => true
  | _ => false

private def systemChild := runFuel (2 : ZMod 3) input 2 1
  (.system input (.matrix (.ready (.start []))))

private def backsubPending : Configuration (ZMod 3) → Bool
  | .backsub (.ready (.reverse [] [] [])) => true
  | _ => false

private def backsubChild := runFuel (2 : ZMod 3) input 2 1 (.backsub (.ready (.check [] [] [])))

private def initializedSystem : Configuration (ZMod 3) →
    Option (List (Pivot (ZMod 3)) × List (Row (ZMod 3)) × ℕ)
  | .initialize ps rs n [] => some (ps, rs, n)
  | _ => none

private def handed := runFuel (2 : ZMod 3) input 2 1
  (.system input (.done [(1, ([(0, 0), (1, 2)], (2, 1)))] [([], (1, 2))]))

private def seedOutput : Configuration (ZMod 3) → Option (List (Pair (ZMod 3)))
  | .backsub (.ready (.check _ _ zs)) => some zs
  | _ => none

private def seedDone := runFuel (2 : ZMod 3) input 2 1 (.initialize [] [] 0 [(1, 2)])

private def returned := runFuel (2 : ZMod 3) input 2 2 (.backsub (.ready (.done [(1, 2)])))
private def failedSystem := runFuel (2 : ZMod 3) input 2 2 (.system input .rejected)
private def failedBacksub := runFuel (2 : ZMod 3) input 2 2 (.backsub (.ready .rejected))


example : (observe completed.1, completed.2) =
    (some (some [(1, 1), (1, 0)]),
      ⟨⟨65, 95, 12, 3, 14, 3436, 9068, 474, 66⟩, 63⟩) := by decide +kernel

example : (observe empty.1, empty.2) =
    (some (some []), ⟨⟨0, 0, 0, 0, 0, 46, 119, 0, 6⟩, 2⟩) := by decide +kernel

example : (observe inconsistent.1, inconsistent.2) =
    (some none, ⟨⟨6, 5, 0, 0, 2, 375, 982, 48, 13⟩, 11⟩) := by decide +kernel

example : (initialized seeded.1, seeded.2) =
    (some (1, [(0, 0), (1, 2)]), ⟨⟨0, 0, 0, 0, 0, 1, 7, 2, 0⟩, 2⟩) := by decide +kernel

example : (payload entered.1, entered.2) =
    (some (1, 1), ⟨⟨0, 0, 0, 0, 0, 1, 7, 0, 0⟩, 0⟩) := by decide +kernel

example : (nestedPayload retained.1, retained.2) =
    (some (2, 2), ⟨⟨0, 0, 0, 0, 0, 2, 9, 0, 0⟩, 0⟩) := by decide +kernel

example : (systemPending systemChild.1, systemChild.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 3, 8, 0, 0⟩, 0⟩) := by decide +kernel

example : (backsubPending backsubChild.1, backsubChild.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 6, 0, 0⟩, 0⟩) := by decide +kernel

example : (initializedSystem handed.1, handed.2) =
    (some ([(1, ([(0, 0), (1, 2)], (2, 1)))], [([], (1, 2))], 2),
      ⟨⟨0, 0, 0, 0, 0, 1, 5, 0, 0⟩, 0⟩) := by decide +kernel

example : (seedOutput seedDone.1, seedDone.2) =
    (some [(1, 2)], ⟨⟨0, 0, 0, 0, 0, 1, 4, 0, 0⟩, 1⟩) := by decide +kernel

example : (observe returned.1, returned.2) =
    (some (some [(1, 2)]), ⟨⟨0, 0, 0, 0, 0, 2, 5, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe failedSystem.1, failedSystem.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe failedBacksub.1, failedBacksub.2) =
    (some none, ⟨⟨0, 0, 0, 0, 0, 2, 4, 0, 1⟩, 0⟩) := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticResidualCoefficientMachine
