/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.LowRateFiniteLengthBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthMCA
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-! # Semantic low-rate finite-length first-order bounds -/

@[expose] public section

open PolynomialDifferential Polynomial
open CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

namespace ReedSolomon.FirstOrder

open HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicWeightedSupportInterpolation
open MvPolynomial

noncomputable section

universe u

open Classical in
/-- The exact low-rate finite-length selectors construct their symbolic line certificate internally.
Unlike the fixed-rate constructor, the source rate here is `rho - 1/n`, while the derivative
ratio remains selected at `rho`; the proof therefore uses the literal finite source and rank
counts rather than coercing them into `FirstOrderFiniteRateParameters`. -/
theorem exists_lowRateFiniteLengthFirstOrder_symbolicCertificate
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hlow : rho < firstOrderRateSwitch)
    (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) (k - 1) A
      (lowRateFiniteLengthMultiplicity rho eta n)
      (lowRateFiniteLengthDerivativeCap rho eta n)
      (lowRateFiniteLengthJetDegree rho eta n) k
      (lowRateFiniteLengthChallengeHeight rho eta n) centers f g
      (firstOrderColumns (D := k - 1) (A := A)
        (m := lowRateFiniteLengthMultiplicity rho eta n)
        (M := lowRateFiniteLengthDerivativeCap rho eta n)
        (μ := lowRateFiniteLengthJetDegree rho eta n))) := by
  let R := finiteLengthRate rho n
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let D := k - 1
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let M := lowRateFiniteLengthDerivativeCap rho eta n
  let mu := lowRateFiniteLengthJetDegree rho eta n
  let h := lowRateFiniteLengthChallengeHeight rho eta n
  let rlocal := lowRateFiniteLengthRankCount rho eta n
  let Nzero := lowRateFiniteLengthSourceCount rho eta n
  let N := (firstOrderExponents D A m M mu).card
  let r := n * rlocal
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := mu)
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hmPos : 0 < m := lowRateFiniteLengthMultiplicity_pos
    hrho hrhoOne hlow heta haOne hn
  have hDPos : 0 < D := by dsimp only [D]; omega
  have hN : N = firstOrderDimensionCount D A m M mu :=
    card_firstOrderExponents_eq_dimensionCount hDPos
  have hDrate : (D : ℝ) ≤ R * n := by
    have hshift : (k : ℝ) - 1 ≤ rho * n - 1 := sub_le_sub_right hkRate 1
    rw [finiteLengthRate_eq hnPos]
    dsimp only [D]
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    exact hshift
  have hArate : a * n ≤ A := by
    apply (mul_le_mul_of_nonneg_right
      (min_le_left (firstOrderLowRateThreshold rho + eta)
        ((1 + firstOrderLowRateThreshold rho) / 2))
      (Nat.cast_nonneg n)).trans
    exact hA
  have hsourceLower : (n : ℝ) * Nzero ≤
      firstOrderDimensionCount D A m M mu := by
    have hlower := firstOrderRateSourceCount_le_dimensionCount
      (R := R) (a := a) (n := n) (D := D) (A := A) (m := m) (M := M) (mu := mu)
      hDrate hArate
    simpa only [R, a, m, M, mu, Nzero, lowRateFiniteLengthSourceCount] using hlower
  have hsurplus : (rlocal : ℝ) < Nzero := by
    have hdelta := lowRateFiniteLengthDensityMargin_pos
      hrho hrhoOne hlow heta haOne hn
    have hgap := lowRateFiniteLength_count_gap hrho hrhoOne hlow heta haOne hn
    have hpositive : 0 < 3 * (m : ℝ) ^ 3 * lowRateFiniteLengthDensityMargin rho eta n / 4 := by
      positivity
    dsimp only [m, rlocal, Nzero]
    linarith
  have hrN : r < N := by
    rw [hN]
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    exact_mod_cast (calc
      (r : ℝ) = (n : ℝ) * rlocal := by simp [r]
      _ < (n : ℝ) * Nzero := mul_lt_mul_of_pos_left hsurplus hnReal
      _ ≤ firstOrderDimensionCount D A m M mu := hsourceLower)
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
        HiddenDerivative.firstOrder_rate_curve_matrix_rank_le hmPos
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
    have hkernel := scaledKernelHeight_le_rateChallengeDegree
      (n := n) (N := firstOrderDimensionCount D A m M mu)
      (r := rlocal) (mu := mu) (N₀ := Nzero) hnPos hsurplus hsourceLower
    simpa only [r, h, mu, rlocal, Nzero, lowRateFiniteLengthChallengeHeight] using hkernel
  have hvheight : ∀ j, (v j).natDegree ≤ h := by
    intro j
    apply (hvdegree j).trans
    simpa [N] using hheight
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M mu :=
    interpolant_mem_firstOrderSpace columns firstOrderColumns_eligible v
  have hfirstJet : ∀ exponent ∈ Q.support, firstJetExponent exponent ≤ M := by
    intro exponent hexponent
    exact (mem_firstOrderExponents.mp
      (mem_firstOrderSpace_iff.mp hQsupport exponent hexponent)).1
  have htotalJet : ∀ exponent ∈ Q.support, totalJetDegree exponent ≤ mu := by
    intro exponent hexponent
    exact (mem_firstOrderExponents.mp
      (mem_firstOrderSpace_iff.mp hQsupport exponent hexponent)).2.1
  refine ⟨⟨v, Q, rfl, hprimitive, coeff_interpolant_natDegree_le columns
    firstOrderColumns_injective v hvheight, hQsupport, hfirstJet, htotalJet,
    hconstraints, ?_⟩⟩
  intro E _ iota z
  refine ⟨hnonzero iota z, ?_⟩
  intro indices P hPdegree hcard hagreements
  let phi := Polynomial.eval₂RingHom iota z
  have hQmapped : MvPolynomial.map phi Q ∈ firstOrderSpace E D A m M mu := by
    rw [mem_firstOrderSpace_iff]
    intro exponent hexponent
    have hexponentQ : exponent ∈ Q.support :=
      MvPolynomial.support_map_subset phi Q hexponent
    exact mem_firstOrderSpace_iff.mp hQsupport exponent hexponentQ
  have hconstraintsE : ∀ i, SatisfiesLocalConstraints m (iota (centers i))
      ((w i).eval₂ iota z) (MvPolynomial.map phi Q) := by
    intro i
    have hi := SatisfiesLocalConstraints.map phi m (Polynomial.C (centers i))
      (w i) Q (hconstraints i)
    change SatisfiesLocalConstraints m
      (Polynomial.eval₂ iota z (Polynomial.C (centers i)))
      ((w i).eval₂ iota z) (MvPolynomial.map phi Q) at hi
    simpa only [Polynomial.eval₂_C] using hi
  have hPnat : P.natDegree ≤ D := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
      dsimp only [D]
      omega
  have hcenters : Set.InjOn (fun i ↦ iota (centers i)) (indices : Set (Fin n)) := by
    intro i _ j _ hij
    exact centers.injective (iota.injective hij)
  apply differentialSpecialization_eq_zero_of_global_multiplicity
    (fun i ↦ iota (centers i)) indices m A (MvPolynomial.map phi Q) P hcenters hcard
  · intro i hi
    apply X_sub_C_pow_dvd_differentialSpecialization_of_contact
      _ P (iota (centers i)) ((w i).eval₂ iota z) _ (hconstraintsE i)
    rw [hagreements i hi]
    simp only [w, receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Polynomial.eval₂_mul, Polynomial.eval₂_X]
  · exact (natDegree_differentialSpecialization_le _ P hPnat).trans_lt
      (differentialWeightedDegree_lt_of_mem_firstOrderSpace
        (Nat.mul_pos hmPos (by
          have hregime :=
            (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
          have haPos : 0 < firstOrderLowRateThreshold rho + eta :=
            (hrho.trans
              (rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime)).trans
              (lt_add_of_pos_right _ heta)
          exact_mod_cast (mul_pos haPos (by exact_mod_cast hnPos) |>.trans_le hA)))
        hQmapped)

private theorem lowRate_specialized_weightedTotalDegree_map_le
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (phi : R →+* S) (weight : sigma → ℕ) (Q : MvPolynomial sigma R) :
    (MvPolynomial.map phi Q).weightedTotalDegree weight ≤ Q.weightedTotalDegree weight := by
  rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  rw [MvPolynomial.mem_restrictWeightedDegree]
  intro exponent hexponent
  exact MvPolynomial.le_weightedTotalDegree weight
    (MvPolynomial.support_map_subset phi Q hexponent)

private theorem lowRate_specialized_degreeOf_map_le
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (phi : R →+* S) (i : sigma) (Q : MvPolynomial sigma R) :
    MvPolynomial.degreeOf i (MvPolynomial.map phi Q) ≤ Q.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro exponent hexponent
  exact MvPolynomial.monomial_le_degreeOf i
    (MvPolynomial.support_map_subset phi Q hexponent)

open Classical in
/-- A generic certificate-to-complete-list bridge with explicit finite-length support bounds.
It handles the exact `M = 0` ordinary endpoint as well as the positive squarefree branch. -/
theorem closePolynomialSet_finite_and_card_le_finiteLength_of_bounded_certificate
    {F : Type u} [Field F] {C eta : ℝ}
    {Dcert A m M B k H n N : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F)
      Dcert A m M B k H domain received (fun _ ↦ 0) columns)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (hkA : k ≤ A) (hAn : A ≤ n)
    (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (hC : 1 ≤ C) (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1)
    (hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * C ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  by_cases hMzero : M = 0
  · let T := closePolynomialSet domain received k A
    have hfinite : T.Finite := closePolynomialSet_finite domain received hkA
    let phi := Polynomial.eval₂RingHom (RingHom.id F) 0
    let Q : DifferentialPolynomial F 1 := MvPolynomial.map phi cert.Q
    obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
    have hweight : jetWeight Q ≤ B := by
      exact (lowRate_specialized_weightedTotalDegree_map_le phi _ cert.Q).trans
        cert.toCurve.jetWeight_le
    have hdegree : jetDegree Q (1 : Fin 2) ≤ M := by
      exact (lowRate_specialized_degreeOf_map_le phi (some (1 : Fin 2)) cert.Q).trans
        cert.toCurve.jetDegree_one_le
    have hsem (S : Finset F[X])
        (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
        (S.card : ℝ) ≤ B := by
      have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
        intro P hP
        let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
        apply hsound indices P (hS P hP).1 (hS P hP).2
        intro i hi
        simpa using (Finset.mem_filter.mp hi).2
      have hraw := HiddenDerivative.finite_firstOrder_field_hybrid_agreement_solutions_card_le
        domain received Q hQ hweight hdegree (by omega) (by omega) hAn hMB hchar S hsol
          (fun P hP ↦ by simpa only [show k - 1 + 1 = k by omega] using hS P hP)
      simpa only [hMzero, hybridLambdaClosed, hybridT, Nat.cast_zero,
        mul_zero, zero_mul, zero_div, zero_add, add_zero, Nat.sub_zero] using hraw.2.2
    refine ⟨hfinite, ?_⟩
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    apply (hsem hfinite.toFinset (fun P hP ↦
      (show IsAgreementSolution domain received k A P by
        simpa [T, closePolynomialSet, IsAgreementSolution, polynomialAgreementSet] using
          (hfinite.mem_toFinset.mp hP)))).trans
    let s := finiteLengthSlack eta n
    have hs : 0 < s := finiteLengthSlack_pos heta (by omega)
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    calc
      (B : ℝ) ≤ C / s := hB
      _ ≤ 7 * C ^ 3 * n / s ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hs)]
        have hCs : C / s * s ^ 2 = C * s := by
          field_simp [ne_of_gt hs]
        rw [hCs]
        have hCs : C ≤ C ^ 3 := by
          nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hC),
            mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)]
        calc
          C * s ≤ C := mul_le_of_le_one_right hC0 hsOne
          _ ≤ C ^ 3 := hCs
          _ ≤ 7 * C ^ 3 * n := by
            have hC3 : 0 ≤ C ^ 3 := by positivity
            nlinarith [mul_nonneg hC3 (zero_le_one.trans hnOne)]
  · exact closePolynomialSet_finite_and_card_le_finiteLength_of_certificate
      domain received columns cert hn hk hkn hkA hAn
        (Nat.one_le_iff_ne_zero.mpr hMzero) hMB hchar hC heta hsOne hlambda hB

/-- Rate-only control of the retained line ratio on the low-rate stationary branch. -/
def lowRateHybridEnvelopeConstant (rho : ℝ) : ℝ :=
  max 1 (1 / (firstOrderLowRateThreshold rho - rho))

/-- One low-rate constant controlling both the exact selectors and the retained line ratio. -/
def lowRateFiniteLengthMCAParameterConstant (rho : ℝ) : ℝ :=
  max (lowRateParameterBoundConstant rho) (lowRateHybridEnvelopeConstant rho)

theorem one_le_lowRateFiniteLengthMCAParameterConstant (rho : ℝ) :
    1 ≤ lowRateFiniteLengthMCAParameterConstant rho := by
  exact (one_le_lowRateParameterBoundConstant rho).trans (le_max_left _ _)

theorem lowRate_hybridTheta_le_parameterConstant
    {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (hDn : D ≤ n) (hDA : D < A)
    (hDrate : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) :
    hybridTheta n D A ≤ lowRateFiniteLengthMCAParameterConstant rho := by
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
  have hthetaRate := hybridTheta_le_rate_gap hDn hDA hDrate hA
    (hthreshold.trans (lt_add_of_pos_right _ heta))
  calc
    hybridTheta n D A ≤ 1 / (firstOrderLowRateThreshold rho + eta - rho) := hthetaRate
    _ ≤ 1 / (firstOrderLowRateThreshold rho - rho) := by
      exact div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr hthreshold) (by linarith)
    _ ≤ lowRateHybridEnvelopeConstant rho := le_max_right _ _
    _ ≤ lowRateFiniteLengthMCAParameterConstant rho := le_max_right _ _

open Classical in
/-- Assumption-free complete-list semantics for the exact low-rate selectors in dimension at
least two.  The symbolic certificate is constructed internally from the literal count gap. -/
theorem lowRate_closePolynomialSet_finite_and_card_le_finiteLength
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * lowRateFiniteLengthMCAParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2 := by
  let C := lowRateFiniteLengthMCAParameterConstant rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let M := lowRateFiniteLengthDerivativeCap rho eta n
  let B := lowRateFiniteLengthJetDegree rho eta n
  let H := lowRateFiniteLengthChallengeHeight rho eta n
  have hnPos := length_pos_of_two_le_rate_mul_length hn
  have hkA : k ≤ A := by
    have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
    have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hkAlt : k < A := by
      exact_mod_cast (hkRate.trans_lt <| (mul_lt_mul_of_pos_right
        (hthreshold.trans (lt_add_of_pos_right _ heta)) hnReal).trans_le hA)
    exact hkAlt.le
  have hkn : k ≤ n := hkA.trans hAn
  have hnTwo : 2 ≤ n := hk.trans hkn
  have hDrate : ((k - 1 : ℕ) : ℝ) ≤ rho * n := by
    exact (show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast (Nat.sub_le k 1)).trans hkRate
  obtain ⟨cert⟩ := exists_lowRateFiniteLengthFirstOrder_symbolicCertificate
    hrho hrhoOne heta haOne hn hlow hk hkRate hA domain received (fun _ ↦ 0)
  have hMB : M ≤ B := by
    dsimp only [M, B]
    exact lowRateFiniteLengthDerivativeCap_le_jetDegree hrho hrhoOne hlow heta haOne hn
  have hsOne := (lowRateFiniteLengthSlack_lt_one hrho hrhoOne hlow haOne hn).le
  have hC : 1 ≤ C := one_le_lowRateFiniteLengthMCAParameterConstant rho
  have hs := finiteLengthSlack_pos heta hnPos
  obtain ⟨_hm, _hM, hBsel, _hH⟩ :=
    lowRateFiniteLength_parameter_bounds hrho hrhoOne hlow heta haOne hn
  have hB : (B : ℝ) ≤ C / finiteLengthSlack eta n := by
    exact hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  have htheta := lowRate_hybridTheta_le_parameterConstant hrho hrhoOne hlow heta
    (show k - 1 ≤ n by omega) (show k - 1 < A by omega) hDrate hA
  have hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C := by
    simpa only [C, hybridTheta, show n - k + 1 = n - (k - 1) by omega,
      show A - k + 1 = A - (k - 1) by omega] using htheta
  exact closePolynomialSet_finite_and_card_le_finiteLength_of_bounded_certificate
    domain received
      (firstOrderColumns (D := k - 1) (A := A) (m := m) (M := M) (μ := B))
      cert hnTwo hk hkn hkA hAn hMB hchar hC heta hsOne hlambda hB

open Classical in
/-- The simpler inverse-`eta` complete-list consequence on the low-rate branch. -/
theorem lowRate_closePolynomialSet_finite_and_card_le_inv_eta
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * lowRateFiniteLengthMCAParameterConstant rho ^ 3 * n / eta ^ 2 := by
  obtain ⟨hfinite, hcard⟩ := lowRate_closePolynomialSet_finite_and_card_le_finiteLength
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain received hchar
  refine ⟨hfinite, hcard.trans ?_⟩
  exact div_finiteLengthSlack_sq_le_div_eta_sq
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (zero_le_one.trans (one_le_lowRateFiniteLengthMCAParameterConstant rho)) _))
      (Nat.cast_nonneg n))
      heta (length_pos_of_two_le_rate_mul_length hn)

private theorem lowRate_line_degreeOf_extendSymbolicCoefficients_le
    {F E : Type*} [Field F] [Field E]
    (iota : F →+* E) (Q : DifferentialPolynomial F[X] 1) (j : Fin 2) :
    (extendSymbolicCoefficients iota Q).degreeOf (some j) ≤ Q.degreeOf (some j) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact MvPolynomial.monomial_le_degreeOf _
    (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota) Q hmon)

open Classical in
/-- Generic ordinary-endpoint descent for an actual first-order certificate with exact
derivative cap zero.  The exceptional set is selected before the challenge and candidate. -/
theorem exists_exceptional_firstOrderMCA_zero_derivative_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert k A m B H : ℕ}
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hB : 1 ≤ B)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A m 0 B k H
      domain f g columns)
    (hchar : ringChar F = 0 ∨ max (k - 1) 0 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        hybridEClosed (hybridTheta n (k - 1) A) n (k - 1) H B 0 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  let Q := extendSymbolicCoefficients iota cert.Q
  let curve := cert.toCurve
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans curve.jetWeight_le
  have hderiv : jetDegree Q (1 : Fin 2) ≤ 0 := by
    exact (lowRate_line_degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans
      curve.jetDegree_one_le
  have hheight : ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  obtain ⟨extensionExceptional, _hraw, _hceil, hcard, hgood⟩ :=
    ReedSolomon.exists_exceptional_firstOrder_hybrid domain f g iota Q hQ hjet hderiv hheight
      (by omega) (by omega) hAn hB (by omega) hchar
  have hgoodPower : ∀ z ∉ extensionExceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
      HasExactPowerAgreement domain ![f, g] iota k z P := by
    intro z hz P hdegree hagree
    have hdegree' : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
      have hkEq : ((k - 1 : ℕ) : WithBot ℕ) + 1 = (k : WithBot ℕ) := by
        change WithBot.some (k - 1) + WithBot.some 1 = WithBot.some k
        rw [← WithBot.coe_add, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      rwa [hkEq]
    have hline : powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
        (fun i ↦ iota (f i) + z * iota (g i)) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    let indices := polynomialAgreementSet (mappedDomain domain iota)
      (fun i ↦ iota (f i) + z * iota (g i)) P
    have hagreeLine : A ≤ indices.card := by
      dsimp only [indices]
      rwa [hline] at hagree
    have hroot := (cert.specialization_sound iota z).2 indices P hdegree hagreeLine
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    have hroot' : differentialSpecialization (challengeSpecialization Q z) P = 0 := by
      change differentialSpecialization
        (MvPolynomial.map (Polynomial.aeval z).toRingHom Q) P = 0
      have heval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
        ext <;> simp
      rw [heval]
      change differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom z)
          (extendSymbolicCoefficients iota cert.Q)) P = 0
      rw [specialize_extendSymbolicCoefficients]
      exact hroot
    have hpower := hgood z hz P hdegree' (by rwa [hline]) hroot'
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hpower
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend
      domain ![f, g] iota k A extensionExceptional hgoodPower
  refine ⟨exceptional, ?_, ?_⟩
  · exact (show (exceptional.card : ℝ) ≤ (extensionExceptional.card : ℝ) by
      exact_mod_cast hcardBase).trans hcard
  · intro z hz P hdegree hagree
    have hline : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hpower := hgoodBase z hz P hdegree (by rwa [hline])
    exact exactCorrelatedPair_of_powerAgreement_one
      domain ![f, g] (RingHom.id F) z P hpower

open Classical in
/-- A generic certificate-to-MCA bridge with explicit finite-length arithmetic and support
premises.  It preserves the ordinary `M = 0` endpoint and exact full agreement sets. -/
theorem exists_exceptional_firstOrderMCA_of_bounded_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {C eta : ℝ} {n N Dcert k A m M B H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A m M B k H
      domain f g columns)
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hBpos : 1 ≤ B) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (hC : 1 ≤ C) (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1)
    (hDn : k - 1 ≤ n)
    (htheta : hybridTheta n (k - 1) A ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n)
    (hM : (M : ℝ) ≤ C / finiteLengthSlack eta n)
    (hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 140 * C ^ 6 * n ^ 2 /
        finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have htheta0 : 0 ≤ hybridTheta n (k - 1) A := by
    unfold hybridTheta
    positivity
  have hEnvelope := finiteLengthMCAEnvelope_le hC heta hn hsOne hDn htheta0 htheta hB hM hH
  by_cases hMzero : M = 0
  · subst M
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_firstOrderMCA_zero_derivative_of_certificate
        hk hkA hAn hBpos domain f g iota columns cert hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [hybridEClosed_zero_eq_finiteLengthMCAEnvelope _ _ _ _ _ hBpos]
    exact hEnvelope
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      Squarefree.exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate
        domain f g iota columns cert hk hkA hAn
          (Nat.one_le_iff_ne_zero.mpr hMzero) hMB hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [Squarefree.retainedSquarefreeLineMCAEnvelope_eq_finiteLengthMCAEnvelope]
    exact hEnvelope

theorem lowRateFiniteLengthJetDegree_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    0 < lowRateFiniteLengthJetDegree rho eta n := by
  unfold lowRateFiniteLengthJetDegree
  apply Nat.ceil_pos.mpr
  have hm := lowRateFiniteLengthMultiplicity_pos hrho hrhoOne hlow heta haOne hn
  have ha := lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le
  have hrate := finiteLengthRate_pos hrho hn
  positivity

open Classical in
/-- Assumption-free retained squarefree line MCA for the exact low-rate selectors in dimension
at least two.  The exceptional set precedes both challenge and candidate quantifiers. -/
theorem exists_exceptional_lowRateFiniteLengthMCA
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  let C := lowRateFiniteLengthMCAParameterConstant rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let M := lowRateFiniteLengthDerivativeCap rho eta n
  let B := lowRateFiniteLengthJetDegree rho eta n
  let H := lowRateFiniteLengthChallengeHeight rho eta n
  have hnPos := length_pos_of_two_le_rate_mul_length hn
  have hkA : k ≤ A := by
    have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
    have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hkAlt : k < A := by
      exact_mod_cast (hkRate.trans_lt <| (mul_lt_mul_of_pos_right
        (hthreshold.trans (lt_add_of_pos_right _ heta)) hnReal).trans_le hA)
    exact hkAlt.le
  have hkn : k ≤ n := hkA.trans hAn
  have hDrate : ((k - 1 : ℕ) : ℝ) ≤ rho * n := by
    exact (show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast (Nat.sub_le k 1)).trans hkRate
  obtain ⟨cert⟩ := exists_lowRateFiniteLengthFirstOrder_symbolicCertificate
    hrho hrhoOne heta haOne hn hlow hk hkRate hA domain f g
  have hMB : M ≤ B := by
    dsimp only [M, B]
    exact lowRateFiniteLengthDerivativeCap_le_jetDegree hrho hrhoOne hlow heta haOne hn
  have hBpos : 1 ≤ B := by
    dsimp only [B]
    exact lowRateFiniteLengthJetDegree_pos hrho hrhoOne hlow heta haOne hn
  have hsOne := (lowRateFiniteLengthSlack_lt_one hrho hrhoOne hlow haOne hn).le
  have hC : 1 ≤ C := one_le_lowRateFiniteLengthMCAParameterConstant rho
  have hs := finiteLengthSlack_pos heta hnPos
  obtain ⟨_hm, hMsel, hBsel, hHsel⟩ :=
    lowRateFiniteLength_parameter_bounds hrho hrhoOne hlow heta haOne hn
  have hM : (M : ℝ) ≤ C / finiteLengthSlack eta n :=
    hMsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  have hB : (B : ℝ) ≤ C / finiteLengthSlack eta n :=
    hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  have hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2 :=
    hHsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have htheta := lowRate_hybridTheta_le_parameterConstant hrho hrhoOne hlow heta
    (show k - 1 ≤ n by omega) (show k - 1 < A by omega) hDrate hA
  exact exists_exceptional_firstOrderMCA_of_bounded_certificate
    domain f g iota
      (firstOrderColumns (D := k - 1) (A := A) (m := m) (M := M) (μ := B)) cert
      (by omega) hk hkA hAn hBpos hMB hchar hC heta hsOne
      (by omega) htheta hB hM hH

open Classical in
/-- The inverse-`eta` low-rate MCA consequence. -/
theorem exists_exceptional_lowRateFiniteLengthMCA_inv_eta
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_lowRateFiniteLengthMCA
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f g iota hchar
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  exact div_finiteLengthSlack_four_le_div_eta_four
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (zero_le_one.trans (one_le_lowRateFiniteLengthMCAParameterConstant rho)) _))
      (sq_nonneg (n : ℝ))) heta (length_pos_of_two_le_rate_mul_length hn)

open Classical in
/-- Complete-list endpoint for dimensions zero and one, with the same low-rate constant but no
large-length or rate-product premise. -/
theorem lowRate_closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 1 ≤ n) (hk : k ≤ 1) (hkA : k ≤ A)
    (heta : 0 < eta) (hsOne : finiteLengthSlack eta n ≤ 1) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * lowRateFiniteLengthMCAParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2 := by
  exact closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
    domain received hn hk hkA (one_le_lowRateFiniteLengthMCAParameterConstant rho)
      heta hsOne

open Classical in
/-- Constant-code line endpoint with the low-rate fourth-power envelope.  It requires neither
the selector count gap nor the characteristic guard. -/
theorem exists_exceptional_lowRateFiniteLengthMCA_one
    {F : Type u} [Field F] {rho eta : ℝ} {n A : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 1 ≤ n) (hA : 0 < A) (heta : 0 < eta)
    (hsOne : finiteLengthSlack eta n ≤ 1) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 1 z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactLineMCA_one n A domain f g hA
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  let C := lowRateFiniteLengthMCAParameterConstant rho
  let s := finiteLengthSlack eta n
  have hC : 1 ≤ C := one_le_lowRateFiniteLengthMCAParameterConstant rho
  have hs : 0 < s := finiteLengthSlack_pos heta (by omega)
  rw [le_div_iff₀ (pow_pos hs 4)]
  have hsFour : s ^ 4 ≤ 1 := pow_le_one₀ hs.le hsOne
  have hCpow : 1 ≤ C ^ 6 := one_le_pow₀ hC
  have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  calc
    (n : ℝ) ^ 2 * s ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    _ ≤ 140 * C ^ 6 * (n : ℝ) ^ 2 := by nlinarith

open Classical in
/-- One assumption-free low-rate semantic family: an independently constructed complete-list
certificate gives the inverse-square bound and an independently constructed line certificate
gives one inverse-fourth exceptional set with exact full agreement sets. -/
theorem lowRate_finiteLength_completeList_and_exceptionalMCA
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    ((closePolynomialSet domain f k A).Finite ∧
      ((closePolynomialSet domain f k A).ncard : ℝ) ≤
        7 * lowRateFiniteLengthMCAParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
            finiteLengthSlack eta n ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  refine ⟨lowRate_closePolynomialSet_finite_and_card_le_finiteLength
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f hchar, ?_⟩
  exact exists_exceptional_lowRateFiniteLengthMCA
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f g iota hchar

open Classical in
/-- Eta-only consequence of the low-rate semantic family, derived after the exact
`eta + 1/n` bounds. -/
theorem lowRate_finiteLength_completeList_and_exceptionalMCA_inv_eta
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    ((closePolynomialSet domain f k A).Finite ∧
      ((closePolynomialSet domain f k A).ncard : ℝ) ≤
        7 * lowRateFiniteLengthMCAParameterConstant rho ^ 3 * n / eta ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  refine ⟨lowRate_closePolynomialSet_finite_and_card_le_inv_eta
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f hchar, ?_⟩
  exact exists_exceptional_lowRateFiniteLengthMCA_inv_eta
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f g iota hchar

theorem lowRateFiniteLengthSlack_lt_one_of_one_le_rate_mul_length
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : 1 ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hnPos : (0 : ℝ) < n := by
    have hprod : 0 < rho * (n : ℝ) := lt_of_lt_of_le zero_lt_one hn
    nlinarith [hrho]
  have hinv : 1 / (n : ℝ) ≤ rho := by
    rw [div_le_iff₀ hnPos]
    simpa [mul_comm] using hn
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
  unfold finiteLengthSlack
  linarith

open Classical in
/-- Unified low-rate finite-length rate facade for every positive code dimension.  The `k = 1`
branch needs only `1 ≤ rho*n`; the selector/count-gap branch is entered only when `2 ≤ k`. -/
theorem lowRate_finiteLength_rate_bounds
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (iota : F →+* E)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * lowRateFiniteLengthMCAParameterConstant rho ^ 3 * n /
            finiteLengthSlack eta n ^ 2) ∧
      ∀ f g : Fin n → F,
        ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤
            140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
              finiteLengthSlack eta n ^ 4 ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hnPos : 0 < n := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hprod : 0 < rho * (n : ℝ) := hkReal.trans_le hkRate
    have hnReal : (0 : ℝ) < n := by nlinarith [hrho]
    exact_mod_cast hnReal
  by_cases hkTwo : 2 ≤ k
  · have hnRate : (2 : ℝ) ≤ rho * n := by
      exact (show (2 : ℝ) ≤ k by exact_mod_cast hkTwo).trans hkRate
    have hcharTwo : ringChar F = 0 ∨
        max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F :=
      hchar.resolve_left (by omega)
    constructor
    · intro received
      exact lowRate_closePolynomialSet_finite_and_card_le_finiteLength
        hrho hrhoOne hlow heta haOne hnRate hkTwo hkRate hA hAn domain received hcharTwo
    · intro f g
      exact exists_exceptional_lowRateFiniteLengthMCA
        hrho hrhoOne hlow heta haOne hnRate hkTwo hkRate hA hAn domain f g iota hcharTwo
  · have hkOne : k = 1 := by omega
    subst k
    have hkRateOne : (1 : ℝ) ≤ rho * (n : ℝ) := by simpa using hkRate
    have hsOne : finiteLengthSlack eta n ≤ 1 :=
      (lowRateFiniteLengthSlack_lt_one_of_one_le_rate_mul_length
        (rho := rho) (eta := eta) (n := n) hrho hrhoOne hlow haOne hkRateOne).le
    have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
    have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
    have hAPos : 0 < A := by
      have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
      exact_mod_cast (mul_pos
        ((hrho.trans hthreshold).trans (lt_add_of_pos_right _ heta)) hnReal |>.trans_le hA)
    constructor
    · intro received
      exact lowRate_closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
        domain received (by omega) (by omega) (by omega) heta hsOne
    · intro f g
      exact exists_exceptional_lowRateFiniteLengthMCA_one
        domain f g (by omega) hAPos heta hsOne

open Classical in
/-- Finite-field probability is derived separately from the arbitrary-field low-rate semantic
exceptional-set theorem by division by `|F|` and capping at one. -/
theorem lowRate_finiteLength_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (firstOrderLowRateThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) /
          (Fintype.card F : ℝ))) := by
  let a := firstOrderLowRateThreshold rho + eta
  let A := Nat.ceil (a * n)
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hAn : A ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      a * (n : ℝ) ≤ 1 * n :=
        mul_le_mul_of_nonneg_right haOne.le (Nat.cast_nonneg n)
      _ = n := one_mul _
  let E := AlgebraicClosure F
  have hline : LineExactAgreementBound domain k A
      (140 * lowRateFiniteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      (lowRate_finiteLength_rate_bounds
        (F := F) (E := E) hrho hrhoOne hlow heta haOne hk hkRate hA hAn
          domain (algebraMap F E) hchar).2 f g
    refine ⟨exceptional, hcard.trans ?_, ?_⟩
    · exact div_finiteLengthSlack_four_le_div_eta_four
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (pow_nonneg
              (zero_le_one.trans (one_le_lowRateFiniteLengthMCAParameterConstant rho)) _))
          (sq_nonneg (n : ℝ))) heta (by
            have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
            have hprod : 0 < rho * (n : ℝ) := hkReal.trans_le hkRate
            have hnReal : (0 : ℝ) < n := by nlinarith [hrho]
            exact_mod_cast hnReal)
    · intro z hz P hP hagree
      obtain ⟨pair, hPzero, hPone, heq, hset⟩ := hgood z hz P hP hagree
      refine ⟨pair.1, pair.2, hPzero, hPone, ?_, ?_⟩
      · simpa [correlatedPairSpecialization] using heq
      · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - (firstOrderLowRateThreshold rho + eta))) = a * n := by
    dsimp only [a]
    ring
  rw [heq]


end

end ReedSolomon.FirstOrder
