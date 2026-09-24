/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageSum
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity

/-!
# First-order curve certificates

This module packages primitive first-order differential equations supported in the finite
first-order space, with local constraints and specialization soundness along received polynomial
curves. A strict surplus of shifted coefficient slots over the numerical row bound constructs
such a certificate for the canonical enumeration of the support. Received lines also give
symbolic certificates whose specialization soundness is stated directly for affine combinations
of two received words. The shared specialization theorem derives vanishing from support and local
constraint hypotheses.

## Main statements

* `FirstOrderCurveCertificate`: a primitive interpolant with bounded support and uniform
  specialization soundness along a received polynomial curve.
* `differentialSpecialization_eq_zero_of_firstOrderSpace`: support and local constraints imply
  vanishing after specialization at sufficiently many agreeing points.
* `FirstOrderSymbolicCertificate.toCurve`: views a line certificate as a degree-one curve
  certificate.
* `FirstOrderCurveCertificate.exists_exceptional_of_regular_stage_bounds_of_factors`: combines
  per-stage regularity bounds into one exceptional set bounded by the curve envelope.
* `exists_finite_firstOrder_curve_certificate_of_heightSlotCount`: a strict shifted-slot surplus
  constructs a certificate with bounded coefficient degree.
* `exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount`: a strict shifted-slot
  surplus for a received line constructs a symbolic certificate.

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

/-- A supported first-order polynomial satisfying the local constraints vanishes after
specialization at any sufficiently large set of points where the polynomial agrees. -/
theorem differentialSpecialization_eq_zero_of_firstOrderSpace
    {D A m M μ k n : ℕ} (hkD : k ≤ D + 1) (hbudget : 0 < m * A)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (Q : DifferentialPolynomial F[X] 1)
    (hQsupport : Q ∈ firstOrderSpace F[X] D A m M μ)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i) Q)
    {E : Type*} [Field E] (ι : F →+* E) (z : E) (indices : Finset (Fin n)) (P : E[X])
    (hPdegree : P.degree < k) (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices, P.eval (ι (centers i)) = (w i).eval₂ ι z) :
    differentialSpecialization (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0 := by
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
    differentialWeightedDegree_lt_of_mem_firstOrderSpace hbudget hQmapped
  exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i ↦ ι (centers i)) (fun i ↦ (w i).eval₂ ι z) indices hweight
    (fun i _ ↦ hconstraintsE i) P hPnat hcenters hcard hagreements

/-- A symbolic line certificate is a degree-one received-curve certificate with the same
equation. -/
def FirstOrderSymbolicCertificate.toCurve
    {D A m M μ k h n N : ℕ}
    {centers : Fin n ↪ F} {f g : Fin n → F} {columns : Fin N → SourceColumn 1}
    (cert : FirstOrderSymbolicCertificate (F := F) D A m M μ k h centers f g columns) :
    FirstOrderCurveCertificate (F := F) D A m M μ k h centers
      (fun i ↦ receivedLine (f i) (g i)) columns := {
  coefficients := cert.coefficients
  Q := cert.Q
  eq_interpolant := cert.eq_interpolant
  primitiveCoefficients := cert.primitiveCoefficients
  challengeDegree_le := cert.challengeDegree_le
  support := cert.support
  firstJetDegree_le := cert.firstJetDegree_le
  totalJetDegree_le := cert.totalJetDegree_le
  localConstraints := cert.localConstraints
  specialization_sound := by
    intro E _ ι z
    obtain ⟨hne, hsound⟩ := cert.specialization_sound ι z
    refine ⟨hne, ?_⟩
    intro indices P hP hcard hagree
    apply hsound indices P hP hcard
    intro i hi
    have h := hagree i hi
    simp only [receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Polynomial.eval₂_mul, Polynomial.eval₂_X] at h
    exact h
}

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
  exact differentialSpecialization_eq_zero_of_firstOrderSpace
    hkD hbudget centers w Q hQsupport hconstraints ι z indices P hPdegree hcard hagreements

/-- A strict shifted-slot surplus for a received line gives a symbolic first-order certificate. -/
theorem exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    {D A m M μ k h n : ℕ}
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n 1 h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ 1 h) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) D A m M μ k h centers f g
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    1 (Nat.zero_lt_of_lt hD) hbudget hkD centers w
      (fun i ↦ natDegree_receivedLine_le (f i) (g i)) hheight
  refine ⟨{
    coefficients := cert.coefficients
    Q := cert.Q
    eq_interpolant := cert.eq_interpolant
    primitiveCoefficients := cert.primitiveCoefficients
    challengeDegree_le := cert.challengeDegree_le
    support := cert.support
    firstJetDegree_le := cert.firstJetDegree_le
    totalJetDegree_le := cert.totalJetDegree_le
    localConstraints := cert.localConstraints
    specialization_sound := ?_ }⟩
  intro E _ ι z
  obtain ⟨hnonzero, hsound⟩ := cert.specialization_sound ι z
  refine ⟨hnonzero, ?_⟩
  intro indices P hPdegree hcard hagreements
  apply hsound indices P hPdegree hcard
  intro i hi
  rw [hagreements i hi]
  change ι (f i) + z * ι (g i) =
    Polynomial.eval₂ ι z (receivedLine (f i) (g i))
  simp only [receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_mul, Polynomial.eval₂_X]

namespace FirstOrderCurveCertificate

open PolynomialDifferential.SeparantChain

universe u

variable {F E : Type u} [Field F] [Field E] {D A m M μ k h n N : ℕ}
  {domain : Fin n ↪ F} {w : Fin n → F[X]} {columns : Fin N → SourceColumn 1}

/-- Uniform exceptional sets for regular stages combine into a single set bounded by the
first-order curve envelope. -/
theorem exists_exceptional_of_regular_stage_bounds_of_factors
    (cert : FirstOrderCurveCertificate.{u, u} D A m M μ k h domain w columns)
    {stages : List (SeparantStage F[X] 1)} {terminal : DifferentialPolynomial F[X] 1}
    (hc : SeparantChain cert.Q stages terminal) (ι : F →+* E)
    (K L ell τ : ℕ) (η : ℚ) (hη : 1 ≤ η)
    (hK : 2 ≤ K) (hLA : L ≤ A) (hAn : A ≤ n)
    (conclusion : E → E[X] → Prop)
    (hregular : ∀ stage ∈ stages, ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
          firstOrderCurveStageCharge n K k L A ell h stage (τ := τ) (η := η) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 →
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1)
              stage.2) P ≠ 0 → conclusion z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
          firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) → conclusion z P := by
  classical
  obtain ⟨base, hbase, hcover⟩ :=
    hc.exists_finset_regular_stage cert.challengeDegree_le ι ι.injective
  let ex : SeparantStage F[X] 1 → Finset E := fun stage ↦
    if hs : stage ∈ stages then (hregular stage hs).choose else ∅
  have hex (stage : SeparantStage F[X] 1) (hs : stage ∈ stages) :=
    (hregular stage hs).choose_spec
  have hex_eq (stage : SeparantStage F[X] 1) (hs : stage ∈ stages) :
      ex stage = (hregular stage hs).choose := by simp [ex, hs]
  have hμ : jetTotalDegree cert.Q ≤ μ := by
    rw [jetTotalDegree_le_iff]
    exact cert.totalJetDegree_le
  have hM : jetDegree cert.Q 1 ≤ M := by
    rw [jetDegree, MvPolynomial.degreeOf_le_iff]
    intro u hu
    have hfirst : u (some (⟨1, by omega⟩ : Fin 2)) ≤ M := by
      simpa only [firstJetExponent_eq_coordinates Nat.one_pos,
        jetExponentCoordinatesEquiv_apply] using cert.firstJetDegree_le u hu
    have hcoord : (⟨1, by omega⟩ : Fin 2) = 1 := Fin.ext rfl
    simpa only [hcoord] using hfirst
  have hnodup : stages.Nodup := by
    exact hc.pairwise_stages.imp (fun hab heq ↦ by
      cases heq
      exact (lt_irrefl _ hab.1))
  refine ⟨base ∪ stages.toFinset.biUnion ex, ?_, ?_⟩
  · calc
      ((base ∪ stages.toFinset.biUnion ex).card : ℚ) ≤
          (base.card : ℚ) + ((stages.toFinset.biUnion ex).card : ℚ) := by
        exact_mod_cast Finset.card_union_le base (stages.toFinset.biUnion ex)
      _ ≤ (h : ℚ) + ∑ stage ∈ stages.toFinset, ((ex stage).card : ℚ) := by
        apply add_le_add
        · exact_mod_cast hbase
        · exact_mod_cast Finset.card_biUnion_le
      _ ≤ (h : ℚ) + ∑ stage ∈ stages.toFinset,
          firstOrderCurveStageCharge n K k L A ell h stage (τ := τ) (η := η) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro stage hs
        rw [hex_eq stage (List.mem_toFinset.mp hs)]
        exact (hex stage (List.mem_toFinset.mp hs)).1
      _ = (h : ℚ) + (stages.map (fun stage ↦
          firstOrderCurveStageCharge n K k L A ell h stage
            (τ := τ) (η := η))).sum := by
        rw [List.sum_toFinset _ hnodup]
      _ ≤ _ := hc.sum_firstOrderCurveStageCharge_add_height_le_of_factors τ η hη hμ hM
        hK hLA hAn
  · intro z hz indices P hdegree hagree hvalues
    have hzbase : z ∉ base := fun hm ↦ hz (Finset.mem_union_left _ hm)
    have hroot := (cert.specialization_sound (E := E) ι z).2 indices P hdegree hagree hvalues
    obtain ⟨stage, hs, hsol, hsep⟩ := hcover z hzbase P hroot
    apply (hex stage hs).2 z ?_ indices P hdegree hagree hvalues hsol hsep
    intro hm
    apply hz (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨stage, List.mem_toFinset.mpr hs, ?_⟩))
    rwa [hex_eq stage hs]

end FirstOrderCurveCertificate

end

end ReedSolomon.HiddenDerivative
