/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.EvaluationMachine

/-!
# Concrete sparse-evaluation machine checks

The mixed case independently fixes the scalar result and every cost component. It includes repeated
indices, a constant term, and missing variables with positive and zero exponents. The remaining
checks distinguish exhausted fuel from emission and exercise both empty input lists.
-/

@[expose] public section

namespace MvPolynomial.EvaluationMachine

/-- `5*3²*2*3⁰ + 7 + 4*0¹ + 3*0⁰ = 100`; every supplied factor is executed. -/
example : runFuel [2, 3] 34
    (.terms ([(5, [(1, 2), (0, 1), (1, 0)]), (7, []), (4, [(9, 1)]), (3, [(9, 0)])] :
      List (Term ℕ)) 0) =
      (.done 100, ⟨4, 4, 34, 126, 28, 1⟩) := by decide

/-- One fewer transition leaves the computed accumulator un-emitted. -/
example : runFuel [2, 3] 33
    (.terms ([(5, [(1, 2), (0, 1), (1, 0)]), (7, []), (4, [(9, 1)]), (3, [(9, 0)])] :
      List (Term ℕ)) 0) =
      (.terms [] 100, ⟨4, 4, 33, 124, 28, 0⟩) := by decide

/-- An empty term list emits zero without looking up any values. -/
example : runFuel ([] : List ℕ) 1 (.terms [] 0) =
    (.done 0, ⟨0, 0, 1, 2, 0, 1⟩) := by decide

/-- Even a zero exponent performs a missing lookup; it then multiplies zero times. -/
example : runFuel ([] : List ℕ) 6 (.terms [(3, [(9, 0)])] 0) =
    (.done 3, ⟨1, 0, 6, 19, 1, 1⟩) := by decide

end MvPolynomial.EvaluationMachine
