/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Machine
/-!
# Descending integer ambient search

The runtime receives integer parameters and materialized received points. It counts those
points, then tries descending ambient degrees, stopping at the first
actual interpolation success. Each failed attempt is charged in full. The constant control
charge covers the natural-number tests, arithmetic, branch and output allocation; underlying
interpolation costs are retained verbatim. No real parameter or witness enters execution.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.AmbientSearchMachine

/-- A successful search records its actual ambient degree and sparse interpolant. -/
structure Output (F : Type*) where
  degree : ℕ
  interpolant : NonzeroInterpolationMachine.Output F
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Visit descending candidates at strict jet cutoff `J`, charging every failed attempt. -/
def searchWithBudget (d m J A : ℕ) (received : List (F × F)) :
    ℕ → ℕ → Option (Output F) × ℕ
  | 0, _ => (none, 32)
  | count + 1, D =>
      let attempt := NonzeroInterpolationMachine.runWithBudget D d m J A received
      match attempt.1 with
      | some out => (some ⟨D, out⟩, 32 + attempt.2)
      | none =>
          let rest := searchWithBudget d m J A received count (D - 1)
          (rest.1, 32 + attempt.2 + rest.2)

/-- Legacy descending search specializes the strict jet cutoff to `2 * m`. -/
def search (d m A : ℕ) (received : List (F × F)) (count D : ℕ) :
    Option (Output F) × ℕ :=
  searchWithBudget d m (2 * m) A received count D

/-- Count the input and search the ambient interval at strict jet cutoff `J`. -/
def runWithBudget (k d m J A : ℕ) (received : List (F × F)) : Option (Output F) × ℕ :=
  let counted := ReceivedInterpolationMatrixMachine.countCells received
  let lower := max (k - 1) d
  let result := searchWithBudget d m J A received (counted.1 - lower) (counted.1 - 1)
  (result.1, 32 + counted.2 + result.2)

/-- Legacy search retains its original interval `max(k-1,d+1),...,n-1`. -/
def run (k d m A : ℕ) (received : List (F × F)) : Option (Output F) × ℕ :=
  let counted := ReceivedInterpolationMatrixMachine.countCells received
  let lower := max (k - 1) (d + 1)
  let result := search d m A received (counted.1 - lower) (counted.1 - 1)
  (result.1, 32 + counted.2 + result.2)

end ReedSolomon.HiddenDerivative.AmbientSearchMachine
