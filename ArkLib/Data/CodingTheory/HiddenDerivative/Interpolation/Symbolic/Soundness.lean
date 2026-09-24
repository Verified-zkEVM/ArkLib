/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport

/-!
# Weighted support under coefficient specialization

Applying a coefficient homomorphism to a linear combination of eligible source monomials
preserves its weighted support over the target coefficient field.

## Main statements

* `map_interpolant_mem_weightedSupportSpace`: challenge specialization preserves weighted support.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential
open Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open MvPolynomial
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E]
variable {d D m W : ℕ} {L : ℝ}

/-- Specializing a symbolic interpolant preserves the weighted-support bound on its monomials. -/
theorem map_interpolant_mem_weightedSupportSpace (hD : 0 < D)
    {N : ℕ} (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X]) (ι : F →+* E) (z : E) :
    MvPolynomial.map (Polynomial.eval₂RingHom ι z)
      (SourceColumn.interpolant columns v) ∈
      weightedSupportSpace E D d W L hD := by
  rw [SourceColumn.interpolant, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [MvPolynomial.map_monomial]
  rw [mem_weightedSupportSpace_iff]
  intro u hu
  have hueq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  subst u
  exact hband j

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
