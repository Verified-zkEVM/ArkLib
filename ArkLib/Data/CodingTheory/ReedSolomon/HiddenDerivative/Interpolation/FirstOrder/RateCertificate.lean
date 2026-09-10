/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateRounding
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveWeightedSupport

/-!
# First-order rate certificate adapter

A checked finite rate choice supplies a first-order symbolic equation uniformly for every block
length, ambient degree, agreement threshold, field, evaluation set, and received line satisfying
the advertised rate inequalities.  The source lower bound is transferred to the exact finite
support count, while the paper's all-`M` rank sum is identified with the existing local-rank
engine.  The primitive polynomial-kernel theorem then gives the challenge height selected before
the block length.

This field-generic certificate has no prime-field execution guards.  The executable decoder
adapter adds those guards separately when it instantiates its interpolation search.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

noncomputable section

universe u

variable {R a : ℝ} (p : FirstOrderFiniteRateParameters R a)

/-- A line certificate is a degree-one received-curve certificate with the same equation. -/
def FirstOrderSymbolicCertificate.toCurve
    {F : Type*} [Field F] {D A m M μ k h n N : ℕ}
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

/-- A positive multiplicity embeds every capped first-order support into a degree-two
ambient support with a larger agreement budget. The local rank does not depend on that budget. -/
theorem firstOrderExponents_subset_degree_two {D A m M μ : ℕ} (hm : 0 < m) :
    firstOrderExponents D A m M μ ⊆ firstOrderExponents 2 (A + 2 * μ) m M μ := by
  intro u hu
  obtain ⟨hM, hμ, hw⟩ := mem_firstOrderExponents_iff_coordinates.mp hu
  apply mem_firstOrderExponents_iff_coordinates.mpr
  refine ⟨hM, hμ, ?_⟩
  have hx : (exactExponentCoordinatesEquiv (by omega : 0 < 1) u).1 < m * A := by omega
  have hmμ := Nat.le_mul_of_pos_left (2 * μ) hm
  norm_num only at ⊢
  nlinarith

/-- The sharp first-order matrix rank bound includes ambient degree one. -/
theorem firstOrder_rate_curve_matrix_rank_le
    {F : Type*} [Field F] {D A m M μ n N : ℕ} (hm : 0 < m)
    (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((SymbolicReceivedCurve.constraintMatrix m centers w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * certifiedEnlargedRankBound 1 m M 0 :=
  firstOrder_curve_matrix_rank_le (D := 2) (A := A + 2 * μ) (by omega)
    centers w columns (fun j ↦ firstOrderExponents_subset_degree_two hm (heligible j))

/-- The checked finite rate surplus remains strict after scaling by every positive block length. -/
theorem FirstOrderFiniteRateParameters.rankCount_mul_lt_dimensionCount
    {n D A : ℕ} (hn : 0 < n)
    (hD : (D : ℝ) ≤ R * n) (hA : a * n ≤ A) :
    n * p.rankCount <
      firstOrderDimensionCount D A p.multiplicity p.derivativeCap p.jetDegree := by
  have hlower := firstOrderRateSourceCount_le_dimensionCount
    (m := p.multiplicity) (M := p.derivativeCap) (mu := p.jetDegree) hD hA
  have hstrict : ((n * p.rankCount : ℕ) : ℝ) <
      n * p.sourceCount := by
    push_cast
    exact mul_lt_mul_of_pos_left p.sourceCount_gt_rankCount (Nat.cast_pos.mpr hn)
  exact_mod_cast hstrict.trans_le hlower

/-- The block-dependent polynomial-kernel height is bounded by the fixed challenge degree in the
finite rate recipe. -/
theorem FirstOrderFiniteRateParameters.kernelHeight_le_challengeDegree
    {n D A : ℕ} (hn : 0 < n)
    (hD : (D : ℝ) ≤ R * n) (hA : a * n ≤ A) :
    let N := firstOrderDimensionCount D A p.multiplicity p.derivativeCap p.jetDegree
    n * p.rankCount * p.jetDegree / (N - n * p.rankCount) ≤ p.challengeDegree := by
  dsimp only
  have hlower := firstOrderRateSourceCount_le_dimensionCount
    (m := p.multiplicity) (M := p.derivativeCap) (mu := p.jetDegree) hD hA
  have h := scaledKernelHeight_le_rateChallengeDegree (n := n)
    (N := firstOrderDimensionCount D A p.multiplicity p.derivativeCap p.jetDegree)
    (r := p.rankCount) (mu := p.jetDegree) (N₀ := p.sourceCount)
    hn p.sourceCount_gt_rankCount hlower
  simpa [FirstOrderFiniteRateParameters.challengeDegree,
    firstOrderRateChallengeDegree, FirstOrderFiniteRateParameters.rankCount,
    FirstOrderFiniteRateParameters.sourceCount, FirstOrderFiniteRateParameters.derivativeCap,
    FirstOrderFiniteRateParameters.jetDegree] using h

/-- A checked first-order rate choice constructs the complete symbolic certificate over every
field, including ambient degree one. -/
theorem exists_firstOrderRate_symbolicCertificate
    {F : Type*} [Field F] {n D A k : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hbudget : 0 < p.multiplicity * A)
    (hkD : k ≤ D + 1) (hDrate : (D : ℝ) ≤ R * n) (hArate : a * n ≤ A)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (FirstOrderSymbolicCertificate (F := F)
      D A p.multiplicity p.derivativeCap p.jetDegree k p.challengeDegree centers f g
      (firstOrderColumns (D := D) (A := A) (m := p.multiplicity)
        (M := p.derivativeCap) (μ := p.jetDegree))) := by
  let m := p.multiplicity
  let M := p.derivativeCap
  let mu := p.jetDegree
  let h := p.challengeDegree
  let N := (firstOrderExponents D A m M mu).card
  let r := n * p.rankCount
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := mu)
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  have hN : N = firstOrderDimensionCount D A m M mu :=
    card_firstOrderExponents_eq_dimensionCount (by omega)
  have hrN : r < N := by
    rw [hN]
    exact p.rankCount_mul_lt_dimensionCount hn hDrate hArate
  have hy₀ : ∀ j, (columns j).y₀ ≤ mu := by
    intro j
    rw [← SourceColumn.exponent_zero]
    exact firstOrder_y₀_le_μ (firstOrderColumns_eligible
      (D := D) (A := A) (m := m) (M := M) (μ := mu) j)
  have hw : ∀ i, (w i).natDegree ≤ 1 := fun i ↦ receivedLine_natDegree_le (f i) (g i)
  have hrank : ((SymbolicReceivedCurve.finiteConstraintMatrix m
      (fun i ↦ centers i) w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ r := by
    calc
      _ ≤ ((SymbolicReceivedCurve.constraintMatrix m
          (fun i ↦ centers i) w columns).map
          (algebraMap F[X] (RatFunc F))).rank :=
        SymbolicReceivedCurve.finiteConstraintMatrix_rank_le m
          (fun i ↦ centers i) w columns
      _ ≤ n * certifiedEnlargedRankBound 1 m M 0 :=
        firstOrder_rate_curve_matrix_rank_le p.multiplicity_pos
          (fun i ↦ centers i) w columns
          (fun j ↦ firstOrderColumns_eligible
            (D := D) (A := A) (m := m) (M := M) (μ := mu) j)
      _ = r := by
        rw [certifiedEnlargedRankBound_one_eq_firstOrderRateRankCount]
        rfl
  have hrN' : r < Fintype.card ↑(firstOrderExponents D A m M mu) := by
    simpa [N] using hrN
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    SymbolicReceivedCurve.exists_primitive_interpolant_of_rank_le
      m 1 mu r (fun i ↦ centers i) w hw columns firstOrderColumns_injective hy₀ hrank hrN'
  let Q : DifferentialPolynomial F[X] 1 := interpolant columns v
  have hheight : r * mu / (N - r) ≤ h := by
    rw [hN]
    exact p.kernelHeight_le_challengeDegree hn hDrate hArate
  have hvheight : ∀ j, (v j).natDegree ≤ h := by
    intro j
    apply (hvdegree j).trans
    simpa [N] using hheight
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M mu :=
    interpolant_mem_firstOrderSpace columns firstOrderColumns_eligible v
  have hfirstJet : ∀ u ∈ Q.support, firstJetExponent u ≤ M := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).1
  have htotalJet : ∀ u ∈ Q.support, totalJetDegree u ≤ mu := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).2.1
  refine ⟨⟨v, Q, rfl, hprimitive, coeff_interpolant_natDegree_le columns
    firstOrderColumns_injective v hvheight, hQsupport, hfirstJet, htotalJet,
    hconstraints, ?_⟩⟩
  intro E _ ι z
  refine ⟨hnonzero ι z, ?_⟩
  intro indices P hPdegree hcard hagreements
  let φ := Polynomial.eval₂RingHom ι z
  have hQmapped : MvPolynomial.map φ Q ∈ firstOrderSpace E D A m M mu := by
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
    apply X_sub_C_pow_dvd_differentialSpecialization_of_contact
      _ P (ι (centers i)) ((w i).eval₂ ι z) _ (hconstraintsE i)
    rw [hagreements i hi]
    simp only [w, receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Polynomial.eval₂_mul, Polynomial.eval₂_X]
  · exact (natDegree_differentialSpecialization_le _ P hPnat).trans_lt
      (differentialWeightedDegree_lt_of_mem_firstOrderSpace hbudget hQmapped)

end

end ReedSolomon.HiddenDerivative
