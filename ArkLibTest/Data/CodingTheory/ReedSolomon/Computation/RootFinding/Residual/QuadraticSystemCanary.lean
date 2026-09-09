/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticSystemRefinement
/-!
# Kernel checks for coordinate residual systems

Nonzero-center sampling feeds actual matrix construction and elimination. Boundary checks retain
ordered sample pairs, full RHS rows, width, pivot indices and contradictory zero-width residuals.
Literal ledgers and deliberately different retained input distinguish every child wrapper,
payload initialization and final emission from uncharged or reconstructed handoffs.
-/

namespace ReedSolomon.HiddenDerivative.QuadraticResidualSystemMachine

private instance : DecidableEq (Pair (ZMod 3)) := inferInstance
private instance : DecidableEq (MvPolynomial.EvaluationMachine.Term (Pair (ZMod 3))) :=
  inferInstance
private instance : DecidableEq (Row (ZMod 3)) := inferInstance
private instance : DecidableEq (Pivot (ZMod 3)) := inferInstance

private def observe : Configuration (ZMod 3) → Option (List (Pivot (ZMod 3)) × List (Row (ZMod 3)))
  | .done ps rs => some (ps, rs)
  | _ => none

private def rejected : Configuration (ZMod 3) → Bool
  | .rejected => true
  | _ => false

private def input : Input (ZMod 3) := ⟨[], [((1, 0), [(0, 1)])], (1, 1), 0⟩

private def completed := runFuel (2 : ZMod 3) input 2 446 (.start [(0, 1), (1, 0)])
private def empty := runFuel (2 : ZMod 3) input 0 13 (.start [])
private def zeroColumns := runFuel (2 : ZMod 3) input 0 1000 (.start [(0, 1)])

private def payload : Configuration (ZMod 3) →
    Option (List (Pair (ZMod 3)) × List (MvPolynomial.EvaluationMachine.Term (Pair (ZMod 3))) ×
      Pair (ZMod 3) × ℕ)
  | .sample p _ => some (p.coefficients, p.terms, p.center, p.order)
  | _ => none

private def started := runFuel (2 : ZMod 3) input 2 1 (.start [(0, 1)])

private def retainedCenter : Configuration (ZMod 3) → Option (Pair (ZMod 3))
  | .sample _ (.call _ _ _ p .start) => some p.center
  | _ => none

private def retained := runFuel (2 : ZMod 3) input 2 1
  (.sample ⟨[(2, 1)], [], (2, 2), 1⟩ (.enter (0, 1) [] []))

private def samplePending : Configuration (ZMod 3) → Bool
  | .sample _ (.scan [] []) => true
  | _ => false

private def sampleChild := runFuel (2 : ZMod 3) input 2 1 (.sample input (.start []))

private def matrixPending : Configuration (ZMod 3) → Bool
  | .matrix (.ready (.scan [] [])) => true
  | _ => false

private def matrixChild := runFuel (2 : ZMod 3) input 2 1 (.matrix (.ready (.start [])))

private def echelonPending : Configuration (ZMod 3) → Bool
  | .echelon (.ready (.reverse [] [] [])) => true
  | _ => false

private def echelonChild := runFuel (2 : ZMod 3) input 0 1 (.echelon (.ready (.loop 0 0 [] [])))

private def samples : Configuration (ZMod 3) → Option (List (Pair (ZMod 3) × Pair (ZMod 3)))
  | .matrix (.ready (.start ps)) => some ps
  | _ => none

private def sampled := runFuel (2 : ZMod 3) input 2 1
  (.sample input (.done [((0, 1), (2, 1)), ((1, 0), (1, 2))]))

private def rows : Configuration (ZMod 3) → Option (ℕ × List (Row (ZMod 3)))
  | .echelon (.ready (.loop 0 L rs [])) => some (L, rs)
  | _ => none

private def constructed := runFuel (2 : ZMod 3) input 2 1
  (.matrix (.ready (.done [([(1, 0), (0, 1)], (2, 1)), ([(1, 0), (1, 0)], (1, 2))])))

private def failed := runFuel (2 : ZMod 3) input 2 1 (.echelon (.ready .rejected))

private def finished := runFuel (2 : ZMod 3) input 2 1
  (.echelon (.ready (.done [(1, ([(0, 0), (1, 0)], (1, 2)))] [([], (2, 1))])))


example : (observe completed.1, completed.2) =
    (some ([(0, ([(1, 0), (0, 1)], (1, 2))), (1, ([(0, 0), (1, 2)], (1, 2)))], []),
      ⟨⟨35, 55, 4, 1, 10, 1980, 5288, 262, 42⟩, 50⟩) := by decide +kernel

example : (observe empty.1, empty.2) =
    (some ([], []), ⟨⟨0, 0, 0, 0, 0, 22, 59, 0, 4⟩, 1⟩) := by decide +kernel

example : (observe zeroColumns.1, zeroColumns.2) =
    (some ([], [([], (1, 2))]), ⟨⟨6, 5, 0, 0, 0, 265, 721, 36, 10⟩, 10⟩) := by decide +kernel

example : (payload started.1, started.2) =
    (some ([], [((1, 0), [(0, 1)])], (1, 1), 0),
      ⟨⟨0, 0, 0, 0, 0, 1, 7, 0, 0⟩, 0⟩) := by decide +kernel

example : (retainedCenter retained.1, retained.2) =
    (some (2, 2), ⟨⟨0, 0, 0, 0, 0, 2, 13, 0, 0⟩, 0⟩) := by decide +kernel

example : (samplePending sampleChild.1, sampleChild.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 5, 0, 0⟩, 0⟩) := by decide +kernel

example : (matrixPending matrixChild.1, matrixChild.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 6, 0, 0⟩, 0⟩) := by decide +kernel

example : (echelonPending echelonChild.1, echelonChild.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 2, 6, 0, 0⟩, 1⟩) := by decide +kernel

example : (samples sampled.1, sampled.2) =
    (some [((0, 1), (2, 1)), ((1, 0), (1, 2))],
      ⟨⟨0, 0, 0, 0, 0, 1, 3, 0, 0⟩, 0⟩) := by decide +kernel

example : (rows constructed.1, constructed.2) =
    (some (2, [([(1, 0), (0, 1)], (2, 1)), ([(1, 0), (1, 0)], (1, 2))]),
      ⟨⟨0, 0, 0, 0, 0, 1, 5, 0, 0⟩, 0⟩) := by decide +kernel

example : (rejected failed.1, failed.2) =
    (true, ⟨⟨0, 0, 0, 0, 0, 1, 3, 0, 1⟩, 0⟩) := by decide +kernel

example : (observe finished.1, finished.2) =
    (some ([(1, ([(0, 0), (1, 0)], (1, 2)))], [([], (2, 1))]),
      ⟨⟨0, 0, 0, 0, 0, 1, 3, 0, 1⟩, 0⟩) := by decide +kernel

end ReedSolomon.HiddenDerivative.QuadraticResidualSystemMachine
