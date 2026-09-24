/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity

/-!
# First-order curve certificates

This module packages primitive first-order differential equations supported in the finite
first-order space, with local constraints and specialization soundness along received polynomial
curves. A strict surplus of shifted coefficient slots over the numerical row bound constructs
such a certificate for the canonical enumeration of the support.

## Main statements

* `FirstOrderCurveCertificate`: a primitive interpolant with bounded support and uniform
  specialization soundness along a received polynomial curve.
* `exists_finite_firstOrder_curve_certificate_of_heightSlotCount`: a strict shifted-slot surplus
  constructs a certificate with bounded coefficient degree.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

/-- A primitive first-order interpolant with support and specialization soundness along a
received polynomial curve. -/
structure FirstOrderCurveCertificate {n N : ℕ} (D A m M μ k h : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1) where
  coefficients : Fin N → F[X]
  Q : DifferentialPolynomial F[X] 1
  eq_interpolant : Q = SourceColumn.interpolant columns coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (Q.coeff u).natDegree ≤ h
  support : Q ∈ firstOrderSpace F[X] D A m M μ
  firstJetDegree_le : ∀ u ∈ Q.support, firstJetExponent u ≤ M
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = (w i).eval₂ ι z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- A strict shifted-slot surplus constructs a primitive first-order curve certificate whose
coefficients have challenge degree at most `h`. -/
theorem exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    {D A m M μ k h n : ℕ} (ℓ : ℕ)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) :
    Nonempty (FirstOrderCurveCertificate (F := F) D A m M μ k h centers w
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  classical
  obtain ⟨v, hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_firstOrderCurve_interpolant_of_shifted_height_bound
      D A m M μ n ℓ h hD (fun i ↦ centers i) w hw hheight
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)
  let Q : DifferentialPolynomial F[X] 1 := SourceColumn.interpolant columns v
  have hvheight : ∀ j, (v j).natDegree ≤ h := by
    intro j
    by_cases hz : v j = 0
    · simp [hz]
    · have hlt : (v j).natDegree <
          h + 1 - ℓ * totalJetDegree (columns j).exponent :=
        (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
          (Polynomial.mem_degreeLT.mp (hvdegree j))
      omega
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M μ :=
    interpolant_mem_firstOrderSpace columns firstOrderColumns_eligible v
  have hfirstJet : ∀ u ∈ Q.support, firstJetExponent u ≤ M := by
    intro u hu
    exact (mem_firstOrderSpace_iff.mp hQsupport u hu).1
  have htotalJet : ∀ u ∈ Q.support, totalJetDegree u ≤ μ := by
    intro u hu
    exact (mem_firstOrderSpace_iff.mp hQsupport u hu).2.1
  refine ⟨⟨v, Q, rfl, hprimitive,
    SourceColumn.coeff_interpolant_natDegree_le columns firstOrderColumns_injective v hvheight,
    hQsupport, hfirstJet, htotalJet, hconstraints, ?_⟩⟩
  intro E _ ι z
  refine ⟨hnonzero ι z, ?_⟩
  intro indices P hPdegree hcard hagreements
  let φ := Polynomial.eval₂RingHom ι z
  have hQmapped : MvPolynomial.map φ Q ∈ firstOrderSpace E D A m M μ := by
    rw [mem_firstOrderSpace_iff]
    intro u hu
    have huQ : u ∈ Q.support := MvPolynomial.support_map_subset φ Q hu
    exact mem_firstOrderSpace_iff.mp hQsupport u huQ
  have hconstraintsE : ∀ i, SatisfiesLocalConstraints m (ι (centers i))
      ((w i).eval₂ ι z) (MvPolynomial.map φ Q) := by
    intro i
    have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
      (w i) Q (hconstraints i)
    change SatisfiesLocalConstraints m
      (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
      ((w i).eval₂ ι z) (MvPolynomial.map φ Q) at hi
    simpa only [Polynomial.eval₂_C] using hi
  have hPnat : P.natDegree ≤ D := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
      omega
  have hcenters : Set.InjOn (fun i ↦ ι (centers i)) (indices : Set (Fin n)) := by
    intro i _ j _ hij
    exact centers.injective (ι.injective hij)
  have hweight : differentialWeightedDegree D (MvPolynomial.map φ Q) < m * A :=
    (differentialWeightedDegree_lt_of_mem_firstOrderSpace hbudget hQmapped)
  exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i ↦ ι (centers i)) (fun i ↦ (w i).eval₂ ι z) indices hweight
    (fun i _ ↦ hconstraintsE i) P hPnat hcenters hcard hagreements

end

end ReedSolomon.HiddenDerivative
