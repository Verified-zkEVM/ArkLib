/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport

/-!
# Weighted support and agreement soundness under specialization

Applying a coefficient homomorphism to an interpolant of eligible source monomials preserves its
weighted support over the target field. If the interpolant also satisfies the local constraints,
then every sufficiently agreeing bounded-degree polynomial has zero differential specialization.

## Main statements

* `map_interpolant_mem_weightedSupportSpace`: challenge specialization preserves weighted support.
* `differentialSpecialization_curve_interpolant_eq_zero_of_agreements`: the general agreement
  soundness theorem for polynomial received data.
* `differentialSpecialization_map_interpolant_eq_zero_of_agreements` and
  `differentialSpecialization_map_interpolant_eq_zero_of_degree_lt`: the received-line statements,
  including the degree-`< k` form.

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
variable {d D m A W : ℕ} {L : ℝ}

/-- Specializing a symbolic interpolant preserves the weighted-support bound on its monomials. -/
theorem map_interpolant_mem_weightedSupportSpace (hD : 0 < D)
    {κ : Type*} [Fintype κ] (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : κ → F[X]) (ι : F →+* E) (z : E) :
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

/-- Every specialization of a weighted-support interpolant satisfying polynomial local
constraints vanishes at sufficiently many agreements with a bounded-degree polynomial. -/
theorem differentialSpecialization_curve_interpolant_eq_zero_of_agreements
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    {ι κ : Type*} [Fintype κ]
    (centers : ι → F) (received : ι → F[X]) (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : κ → F[X])
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
      (received i) (SourceColumn.interpolant columns v))
    (ι' : F →+* E) (z : E) (indices : Finset ι) (P : E[X])
    (hPdegree : P.natDegree ≤ D)
    (hcenters : Set.InjOn centers (indices : Set ι))
    (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices,
      P.eval (ι' (centers i)) = (received i).eval₂ ι' z) :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom ι' z)
        (SourceColumn.interpolant columns v)) P = 0 := by
  let φ := Polynomial.eval₂RingHom ι' z
  have hQband : MvPolynomial.map φ (SourceColumn.interpolant columns v) ∈
      weightedSupportSpace E D d W L hD :=
    map_interpolant_mem_weightedSupportSpace hD columns hband v ι' z
  have hconstraintsE : ∀ i, SatisfiesLocalConstraints m (ι' (centers i))
      ((received i).eval₂ ι' z) (MvPolynomial.map φ (SourceColumn.interpolant columns v)) := by
    intro i
    have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
      (received i) (SourceColumn.interpolant columns v) (hconstraints i)
    change SatisfiesLocalConstraints m
      (Polynomial.eval₂ ι' z (Polynomial.C (centers i)))
      (Polynomial.eval₂ ι' z (received i))
      (MvPolynomial.map φ (SourceColumn.interpolant columns v)) at hi
    simpa only [Polynomial.eval₂_C] using hi
  have hcentersE : Set.InjOn (fun i ↦ ι' (centers i)) (indices : Set ι) := by
    intro i hi j hj hij
    exact hcenters hi hj (ι'.injective hij)
  exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i ↦ ι' (centers i)) (fun i ↦ (received i).eval₂ ι' z) indices
    (differentialWeightedDegree_lt_of_mem_weightedSupportSpace hbudget hL hQband)
    (fun i _ ↦ hconstraintsE i) P hPdegree hcentersE hcard hagreements

/-- The received-line case of weighted-support interpolation soundness. -/
theorem differentialSpecialization_map_interpolant_eq_zero_of_agreements
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    {n N : ℕ} (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X])
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) (SourceColumn.interpolant columns v))
    (ι' : F →+* E) (z : E) (indices : Finset (Fin n)) (P : E[X])
    (hPdegree : P.natDegree ≤ D)
    (hcenters : Set.InjOn centers (indices : Set (Fin n)))
    (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices,
      P.eval (ι' (centers i)) = ι' (f i) + z * ι' (g i)) :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom ι' z)
        (SourceColumn.interpolant columns v)) P = 0 := by
  apply differentialSpecialization_curve_interpolant_eq_zero_of_agreements
    hD hL hbudget centers (fun i ↦ receivedLine (f i) (g i)) columns hband v
    hconstraints ι' z indices P hPdegree hcenters hcard
  simpa only [receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X] using hagreements

/-- A degree-`< k` polynomial satisfies the degree premise of received-line soundness when
`k ≤ D + 1`. -/
theorem differentialSpecialization_map_interpolant_eq_zero_of_degree_lt
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    {n N k : ℕ} (hkD : k ≤ D + 1)
    (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X])
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) (SourceColumn.interpolant columns v))
    (ι' : F →+* E) (z : E) (indices : Finset (Fin n)) (P : E[X])
    (hPdegree : P.degree < k)
    (hcenters : Set.InjOn centers (indices : Set (Fin n)))
    (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices,
      P.eval (ι' (centers i)) = ι' (f i) + z * ι' (g i)) :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom ι' z)
        (SourceColumn.interpolant columns v)) P = 0 := by
  have hPnat : P.natDegree ≤ D := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
      omega
  exact differentialSpecialization_map_interpolant_eq_zero_of_agreements
    hD hL hbudget centers f g columns hband v hconstraints ι' z indices P hPnat
      hcenters hcard hagreements

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
