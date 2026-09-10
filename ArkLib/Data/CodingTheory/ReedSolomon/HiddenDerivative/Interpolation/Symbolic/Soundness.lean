/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedLine
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Basic
/-!
# Soundness of symbolic received-curve interpolation

Changing coefficients preserves the actual local constraints and weighted support support.
Consequently each challenge specialization of a symbolic interpolant vanishes identically
on every sufficiently close low-degree polynomial over an arbitrary extension field.
Received lines are the degree-one specialization of the general curve statement.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open MvPolynomial
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}

/-- The unscaled local substitution commutes with changing the coefficient ring. -/
theorem map_unscaledLocalSubstitution (φ : R →+* S) (center received : R)
    (Q : DifferentialPolynomial R d) :
    MvPolynomial.map φ (unscaledLocalSubstitution d center received Q) =
      unscaledLocalSubstitution d (φ center) (φ received) (MvPolynomial.map φ Q) := by
  simp only [unscaledLocalSubstitution, MvPolynomial.map_bind₁]
  have hhom :
      MvPolynomial.bind₁ (fun i ↦ MvPolynomial.map φ (unscaledLocalImage d center received i)) =
        MvPolynomial.bind₁ (unscaledLocalImage d (φ center) (φ received)) := by
    apply MvPolynomial.algHom_ext
    intro v
    rcases v with _ | j
    · simp [unscaledLocalImage]
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp [unscaledLocalImage, localCorrection]
      · simp [unscaledLocalImage]
  rw [hhom]

/-- Low-contact projection commutes with changing the coefficient ring. -/
theorem map_projectLowContact (φ : R →+* S) (m : ℕ) (P : LocalPolynomial R d) :
    MvPolynomial.map φ (projectLowContact m P) =
      projectLowContact m (MvPolynomial.map φ P) := by
  ext e
  by_cases he : localContactOrder d e < m <;>
    simp [projectLowContact, coeff_filterLocalMonomials, MvPolynomial.coeff_map, he]

/-- Local constraints are preserved by every coefficient-ring homomorphism. -/
theorem SatisfiesLocalConstraints.map (φ : R →+* S) (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] at hQ ⊢
  rw [← map_unscaledLocalSubstitution, ← map_projectLowContact]
  simpa using congrArg (MvPolynomial.map φ) hQ

variable {F E : Type*} [Field F] [Field E]
variable {D A m W : ℕ} {L : ℝ}

/-- Specializing the challenge in a linear combination of eligible source monomials remains in
the weighted-support space over the extension field. -/
theorem map_interpolant_mem_weightedSupportSpace (hD : 0 < D)
    {N : ℕ} (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X]) (ι : F →+* E) (z : E) :
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ∈
      weightedSupportSpace E D d W L hD := by
  rw [interpolant, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [MvPolynomial.map_monomial]
  rw [mem_weightedSupportSpace_iff]
  intro u hu
  have hueq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  subst u
  exact hband j

/-- Every specialization of a symbolic weighted-support interpolant satisfying the polynomial local
constraints solves the differential identity at each sufficiently agreeing bounded-degree
polynomial over every extension field. -/
theorem differentialSpecialization_curve_interpolant_eq_zero_of_agreements
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    {n N : ℕ} (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X])
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
      (w i) (interpolant columns v))
    (ι : F →+* E) (z : E) (indices : Finset (Fin n)) (P : E[X])
    (hPdegree : P.natDegree ≤ D)
    (hcenters : Set.InjOn centers (indices : Set (Fin n)))
    (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices,
      P.eval (ι (centers i)) = (w i).eval₂ ι z) :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v)) P = 0 := by
  let φ := Polynomial.eval₂RingHom ι z
  have hQband : MvPolynomial.map φ (interpolant columns v) ∈
      weightedSupportSpace E D d W L hD :=
    map_interpolant_mem_weightedSupportSpace hD columns hband v ι z
  have hconstraintsE : ∀ i, SatisfiesLocalConstraints m (ι (centers i))
      ((w i).eval₂ ι z) (MvPolynomial.map φ (interpolant columns v)) := by
    intro i
    have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
      (w i) (interpolant columns v) (hconstraints i)
    change SatisfiesLocalConstraints m
      (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
      (Polynomial.eval₂ ι z (w i))
      (MvPolynomial.map φ (interpolant columns v)) at hi
    simpa only [Polynomial.eval₂_C] using hi
  have hcentersE : Set.InjOn (fun i ↦ ι (centers i)) (indices : Set (Fin n)) := by
    intro i hi j hj hij
    exact hcenters hi hj (ι.injective hij)
  apply differentialSpecialization_eq_zero_of_global_multiplicity
    (fun i ↦ ι (centers i)) indices m A _ P hcentersE hcard
  · intro i hi
    exact X_sub_C_pow_dvd_differentialSpecialization_of_contact
      _ P (ι (centers i)) ((w i).eval₂ ι z) (hagreements i hi) (hconstraintsE i)
  · exact (natDegree_differentialSpecialization_le _ P hPdegree).trans_lt
      (differentialWeightedDegree_lt_of_mem_weightedSupportSpace hbudget hL hQband)


/-- Received-line soundness is the degree-one case of symbolic curve soundness. -/
theorem differentialSpecialization_map_interpolant_eq_zero_of_agreements
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    {n N : ℕ} (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X])
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) (interpolant columns v))
    (ι : F →+* E) (z : E) (indices : Finset (Fin n)) (P : E[X])
    (hPdegree : P.natDegree ≤ D)
    (hcenters : Set.InjOn centers (indices : Set (Fin n)))
    (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices,
      P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v)) P = 0 := by
  apply differentialSpecialization_curve_interpolant_eq_zero_of_agreements
    hD hL hbudget centers (fun i ↦ receivedLine (f i) (g i)) columns hband v
    hconstraints ι z indices P hPdegree hcenters hcard
  simpa only [receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X] using hagreements

/-- Degree-`< k` form of symbolic interpolation soundness. The ambient specialization parameter
only needs to satisfy `k ≤ D + 1`; in the weighted-support construction it is `D = K - 1`. -/
theorem differentialSpecialization_map_interpolant_eq_zero_of_degree_lt
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    {n N k : ℕ} (hkD : k ≤ D + 1)
    (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : Fin N → F[X])
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) (interpolant columns v))
    (ι : F →+* E) (z : E) (indices : Finset (Fin n)) (P : E[X])
    (hPdegree : P.degree < k)
    (hcenters : Set.InjOn centers (indices : Set (Fin n)))
    (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices,
      P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v)) P = 0 := by
  have hPnat : P.natDegree ≤ D := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
      omega
  exact differentialSpecialization_map_interpolant_eq_zero_of_agreements
    hD hL hbudget centers f g columns hband v hconstraints ι z indices P hPnat
      hcenters hcard hagreements

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
