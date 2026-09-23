/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport

/-!
# Coefficient specialization of symbolic interpolation

Coefficient homomorphisms preserve local constraints and weighted support. In particular, every
specialization of a symbolic weighted-support interpolant remains in the same support space.

## Main statements

* `map_projectLowContact` and `SatisfiesLocalConstraints.map`: local constraints commute with
  coefficient homomorphisms.
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

variable {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}

/-- Low-contact projection commutes with changing the coefficient ring. -/
theorem map_projectLowContact (φ : R →+* S) (m : ℕ) (P : LocalPolynomial R d) :
    MvPolynomial.map φ (projectLowContact m P) =
      projectLowContact m (MvPolynomial.map φ P) := by
  ext e
  simp only [MvPolynomial.coeff_map, coeff_projectLowContact]
  split_ifs <;> simp

/-- Local constraints are preserved by every coefficient-ring homomorphism. -/
theorem SatisfiesLocalConstraints.map (φ : R →+* S) (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] at hQ ⊢
  rw [← ReedSolomon.HiddenDerivative.map_unscaledLocalSubstitution,
    ← map_projectLowContact]
  simpa using congrArg (MvPolynomial.map φ) hQ

variable {F E : Type*} [Field F] [Field E]
variable {D A m W : ℕ} {L : ℝ}

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
