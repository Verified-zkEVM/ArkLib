/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveSymbolic

/-!
# Executable finite curve certificates

The complete first-order support has a canonical enumeration. Grading by total jet degree gives
an executable truncated source-slot sum and a compressed row-slot bound. Combining their strict
surplus with the translated polynomial-curve matrix and primitive-kernel construction leaves only
an integer inequality for the caller to check.

The received curve has coordinate degree at most `ℓ`; the resulting single equation
has height at most `h`. It remains nonzero and sound at every challenge over every
extension field. In particular this proves the interpolation step at the exact heights
selected by the concrete powers-batching search, without a caller-supplied matrix or
geometric hypothesis.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-- The shifted graded-row inequality constructs the complete finite first-order curve
certificate. All matrix, rank, and kernel facts are discharged internally. -/
theorem exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    {D A m M μ k h n : ℕ} (ℓ : ℕ)
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) :
    Nonempty (FirstOrderCurveCertificate (F := F) D A m M μ k h centers w
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_firstOrderCurve_interpolant_of_shifted_height_bound
      D A m M μ n ℓ h (by omega) (fun i ↦ centers i) w hw hheight
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)
  let Q : DifferentialPolynomial F[X] 1 := interpolant columns v
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
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).1
  have htotalJet : ∀ u ∈ Q.support, totalJetDegree u ≤ μ := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).2.1
  refine ⟨⟨v, Q, rfl, hprimitive, coeff_interpolant_natDegree_le columns
    firstOrderColumns_injective v hvheight, hQsupport, hfirstJet, htotalJet,
    hconstraints, ?_⟩⟩
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
  apply differentialSpecialization_eq_zero_of_global_multiplicity
    (fun i ↦ ι (centers i)) indices m A (MvPolynomial.map φ Q) P hcenters hcard
  · intro i hi
    exact X_sub_C_pow_dvd_differentialSpecialization_of_contact
      _ P (ι (centers i)) ((w i).eval₂ ι z) (hagreements i hi) (hconstraintsE i)
  · exact (natDegree_differentialSpecialization_le _ P hPnat).trans_lt
      (differentialWeightedDegree_lt_of_mem_firstOrderSpace hbudget hQmapped)


end

end ReedSolomon.HiddenDerivative
