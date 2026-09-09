/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.TotalDegreeExtension
/-!
# Zero-fiber boundaries for total-degree root counting

The equation `X*Y₀` is not primitive in X. At the zero center its fiber is zero, and hence
it has no chain witness there, even though it has polynomial solutions. Total jet degree
counts the jet exponent only, regardless of the degree in X.
-/

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

noncomputable section

open MvPolynomial

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def vanishingFiberEquation : DifferentialPolynomial (ZMod 5) 0 :=
  X none * X (some 0)

/-- A nonprimitive equation can have an identically zero fiber. -/
example : jetFiberHom (0 : ZMod 5) vanishingFiberEquation = 0 := by
  simp [vanishingFiberEquation, jetFiberHom]

/-- Such a center contributes no witnesses, rather than a full grid of spurious witnesses. -/
example (P : Polynomial (ZMod 5)) : ¬ ChainWitness vanishingFiberEquation P 0 := by
  intro h
  exact h.jetFiber_ne_zero (by simp [vanishingFiberEquation, jetFiberHom])

/-- The X factor does not increase the total jet-degree budget. -/
example : jetTotalDegree vanishingFiberEquation ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  simp [vanishingFiberEquation, X, monomial_mul, support_monomial]

end
end ReedSolomon.HiddenDerivative
