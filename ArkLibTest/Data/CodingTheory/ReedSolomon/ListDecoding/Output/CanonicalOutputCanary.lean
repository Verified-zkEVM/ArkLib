/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputSemantics
/-!
# Ordered output collection boundaries

Synthetic context-tagged inputs test this collector independently of chain generation. Accepted
base polynomials retain their order while center and prefix failures are removed. Repeating an
identical input record repeats its output: the collector does not secretly implement a set or
claim duplicate freedom without the stage enumerator's uniqueness contract.
-/

namespace ReedSolomon.ListDecoding.CanonicalOutputMachine

private abbrev E := QuadraticAlgebra ℕ 2 0

private def record (v c : ℕ) (previous : List (List (MvPolynomial.EvaluationMachine.Term E))) :
    Record E := ⟨⟨⟨[], none⟩, previous, [(1, [])]⟩, ⟨c, 0⟩, [⟨0, 0⟩, ⟨v, 0⟩]⟩

private def samples : List E := [⟨0, 0⟩, ⟨1, 0⟩]

private def records : List (Record E) :=
  [record 1 0 [], record 2 1 [], record 3 0 [], record 1 0 [[(1, [])]]]

-- Two different accepted outputs retain order through rejection and explicit reversal.
example : runFuel 0 samples 2 1 0 [] 348 (.start records) =
    (.done [[1], [3]], 6307) := by decide +kernel

-- One missing step leaves the ordered output ready for separately charged emission.
example : runFuel 0 samples 2 1 0 [] 347 (.start records) =
    (.emit [[1], [3]], 6304) := by decide +kernel

-- Uniqueness must come from valid generated records, not an implicit set conversion.
example : runFuel 0 samples 2 1 0 [] 200 (.start [record 1 0 [], record 1 0 []]) =
    (.done [[1], [1]], 3471) := by decide +kernel

-- Empty input still pays initial dispatch, scan termination, reversal and emission.
example : runFuel 0 samples 2 1 0 [] 4 (.start []) = (.done [], 13) := by decide +kernel

end ReedSolomon.ListDecoding.CanonicalOutputMachine
