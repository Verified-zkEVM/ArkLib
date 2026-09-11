/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthSelectors
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthList
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.LineCertificate

/-!
# Finite-length first-order mutual correlated agreement

This file composes the literal finite-length interpolation selectors with the retained squarefree
line theorem.  The interpolation degree `Dcert` stays independent of the recovery degree `k - 1`.
For each received line, the certificate determines one exceptional set before either the challenge
or the candidate polynomial is chosen, and the conclusion retains equality of the complete
agreement sets.

The semantic theorem is stated over an arbitrary field.  No finite-field probability interpretation
is folded into it.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder

open HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicWeightedSupportInterpolation
open MvPolynomial

noncomputable section

universe u

open Classical in
private theorem mem_closePolynomialSet_iff_isAgreementSolution
    {F : Type*} [Field F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (P : F[X]) :
    P ∈ closePolynomialSet domain received k A ↔
      IsAgreementSolution domain received k A P := by
  unfold closePolynomialSet IsAgreementSolution
  constructor
  · intro hP
    refine ⟨hP.1, ?_⟩
    convert hP.2 using 1
    congr 1
  · intro hP
    refine ⟨hP.1, ?_⟩
    convert hP.2 using 1
    congr 1

private theorem specialized_weightedTotalDegree_map_le
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (phi : R →+* S) (weight : sigma → ℕ) (Q : MvPolynomial sigma R) :
    (MvPolynomial.map phi Q).weightedTotalDegree weight ≤ Q.weightedTotalDegree weight := by
  rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  rw [MvPolynomial.mem_restrictWeightedDegree]
  intro exponent hexponent
  exact MvPolynomial.le_weightedTotalDegree weight
    (MvPolynomial.support_map_subset phi Q hexponent)

private theorem specialized_degreeOf_map_le
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (phi : R →+* S) (i : sigma) (Q : MvPolynomial sigma R) :
    MvPolynomial.degreeOf i (MvPolynomial.map phi Q) ≤ MvPolynomial.degreeOf i Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro exponent hexponent
  exact MvPolynomial.monomial_le_degreeOf i
    (MvPolynomial.support_map_subset phi Q hexponent)

/-- One rate-only constant simultaneously controlling the literal interpolation selectors and the
retained-line agreement ratio. -/
def finiteLengthMCAParameterConstant (rho : ℝ) : ℝ :=
  max (finiteLengthParameterBoundConstant rho) (automaticHybridEnvelopeConstant rho)

theorem one_le_finiteLengthMCAParameterConstant (rho : ℝ) :
    1 ≤ finiteLengthMCAParameterConstant rho := by
  exact (one_le_finiteLengthParameterBoundConstant rho).trans (le_max_left _ _)

/-- The retained squarefree line expression is exactly the finite-length envelope.  In particular,
the natural subtractions occurring at small length and at full code rate are unchanged. -/
theorem Squarefree.retainedSquarefreeLineMCAEnvelope_eq_finiteLengthMCAEnvelope
    (lambda : ℝ) (n D B M H : ℕ) :
    Squarefree.retainedSquarefreeLineMCAEnvelope lambda n D B M H =
      finiteLengthMCAEnvelope lambda n D B M H := by
  unfold Squarefree.retainedSquarefreeLineMCAEnvelope Squarefree.retainedOrdinaryMCARaw
    finiteLengthMCAEnvelope
  push_cast
  ring

/-- At derivative cap zero, the retained hybrid expression is the same ordinary endpoint as the
finite-length envelope.  Positivity of `B` selects the nonzero ordinary-tail formula. -/
theorem hybridEClosed_zero_eq_finiteLengthMCAEnvelope
    (lambda : ℝ) (n D B H : ℕ) (hB : 1 ≤ B) :
    hybridEClosed lambda n D H B 0 =
      finiteLengthMCAEnvelope lambda n D B 0 H := by
  unfold hybridEClosed hybridT hybridOrdinaryRaw finiteLengthMCAEnvelope
  rw [if_neg (by omega : B ≠ 0)]
  push_cast
  ring_nf

private theorem line_degreeOf_extendSymbolicCoefficients_le
    {F E : Type*} [Field F] [Field E]
    (iota : F →+* E) (Q : DifferentialPolynomial F[X] 1) (j : Fin 2) :
    (extendSymbolicCoefficients iota Q).degreeOf (some j) ≤ Q.degreeOf (some j) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact MvPolynomial.monomial_le_degreeOf _
    (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota) Q hmon)

private theorem finiteLengthJetDegree_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    0 < finiteLengthJetDegree rho eta n := by
  unfold finiteLengthJetDegree
  apply Nat.ceil_pos.mpr
  have hm := finiteLengthMultiplicity_pos hrho hrhoOne heta haOne hn hbetaHalf
  have ha : 0 < finiteLengthCertifiedAgreement rho eta :=
    hrho.trans (rho_lt_automaticAgreement hrho hrhoOne (by linarith))
  have hrate := finiteLengthRate_pos hrho hn
  positivity

open Classical in
/-- The exact finite-length selectors construct their symbolic line certificate internally.
Unlike the fixed-rate constructor, the source rate here is `rho - 1/n`, while the derivative
ratio remains selected at `rho`; the proof therefore uses the literal finite source and rank
counts rather than coercing them into `FirstOrderFiniteRateParameters`. -/
theorem exists_finiteLengthFirstOrder_symbolicCertificate
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) (k - 1) A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) centers f g
      (firstOrderColumns (D := k - 1) (A := A)
        (m := finiteLengthMultiplicity rho eta n)
        (M := finiteLengthDerivativeCap rho eta n)
        (μ := finiteLengthJetDegree rho eta n))) := by
  let R := finiteLengthRate rho n
  let a := finiteLengthCertifiedAgreement rho eta
  let D := k - 1
  let m := finiteLengthMultiplicity rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  let mu := finiteLengthJetDegree rho eta n
  let h := finiteLengthChallengeHeight rho eta n
  let rlocal := finiteLengthRankCount rho eta n
  let Nzero := finiteLengthSourceCount rho eta n
  let N := (firstOrderExponents D A m M mu).card
  let r := n * rlocal
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := mu)
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hmPos : 0 < m := finiteLengthMultiplicity_pos
    hrho hrhoOne heta haOne hn hbetaHalf
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
      (automaticAgreement_le (rho := rho) (a := automaticFirstOrderThreshold rho + eta))
      (Nat.cast_nonneg n)).trans
    exact hA
  have hsourceLower : (n : ℝ) * Nzero ≤
      firstOrderDimensionCount D A m M mu := by
    have hlower := firstOrderRateSourceCount_le_dimensionCount
      (R := R) (a := a) (n := n) (D := D) (A := A) (m := m) (M := M) (mu := mu)
      hDrate hArate
    simpa only [R, a, m, M, mu, Nzero, finiteLengthSourceCount] using hlower
  have hsurplus : (rlocal : ℝ) < Nzero := by
    have hdelta := finiteLengthDensityMargin_pos
      hrho hrhoOne heta haOne hn hbetaHalf
    have hgap := finiteLength_count_gap hrho hrhoOne heta haOne hn hbetaHalf
    have hpositive : 0 < 3 * (m : ℝ) ^ 3 * finiteLengthDensityMargin rho eta n / 4 := by
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
    simpa only [r, h, mu, rlocal, Nzero, finiteLengthChallengeHeight] using hkernel
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
          have haPos : 0 < automaticFirstOrderThreshold rho + eta :=
            (hrho.trans (rho_lt_automaticFirstOrderThreshold hrho hrhoOne)).trans
              (lt_add_of_pos_right _ heta)
          exact_mod_cast (mul_pos haPos (by exact_mod_cast hnPos) |>.trans_le hA)))
        hQmapped)

open Classical in
/-- The ordinary endpoint adapter for a literal selector certificate whose derivative cap is zero.
It keeps the extension field internal and descends both the exceptional set and exact power
agreement to the base field. -/
private theorem exists_exceptional_finiteLengthMCA_zero_derivative
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f g columns)
    (_hMzero : finiteLengthDerivativeCap rho eta n = 0)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ hybridEClosed (hybridTheta n (k - 1) A)
        n (k - 1) (finiteLengthChallengeHeight rho eta n)
        (finiteLengthJetDegree rho eta n) (finiteLengthDerivativeCap rho eta n) ∧
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
  have hjet : jetWeight Q ≤ finiteLengthJetDegree rho eta n :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans curve.jetWeight_le
  have hderiv : jetDegree Q (1 : Fin 2) ≤ finiteLengthDerivativeCap rho eta n := by
    exact (line_degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans
      curve.jetDegree_one_le
  have hheight : ChallengeHeightLE Q (finiteLengthChallengeHeight rho eta n) :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  have hB : 1 ≤ finiteLengthJetDegree rho eta n :=
    finiteLengthJetDegree_pos hrho hrhoOne heta haOne hn hbetaHalf
  obtain ⟨extensionExceptional, _hraw, _hceil, hcard, hgood⟩ :=
    ReedSolomon.exists_exceptional_firstOrder_hybrid domain f g iota Q hQ hjet hderiv hheight
      (by omega) (by omega) hAn hB
      (finiteLengthDerivativeCap_le_jetDegree hrho hrhoOne heta haOne hn) hchar
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

/-- The constant-polynomial endpoint needs no interpolation equation.  Pairwise collisions of
received coordinates are the only exceptional challenges. -/
theorem exists_exceptional_exactLineMCA_one
    {F : Type u} [Field F] [DecidableEq F]
    (n A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hA : 0 < A) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 1 z P := by
  classical
  let collision : Fin n × Fin n → F := fun ij ↦
    if g ij.1 = g ij.2 then 0 else -(f ij.1 - f ij.2) / (g ij.1 - g ij.2)
  let exceptional := (Finset.univ : Finset (Fin n × Fin n)).image collision
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : exceptional.card ≤ n * n := by
      calc
        exceptional.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_image_le
        _ = n * n := by simp
    exact_mod_cast (by simpa [pow_two] using hcard)
  · intro z hz P hdegree hagree
    let agreement := polynomialAgreementSet domain (fun i ↦ f i + z * g i) P
    have hagreementPos : 0 < agreement.card := hA.trans_le hagree
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hagreementPos
    have hiEq : P.eval (domain i) = f i + z * g i :=
      (Finset.mem_filter.mp hi).2
    have hconstant : P = Polynomial.C (P.eval (domain i)) := by
      have hpdeg : P.degree ≤ 0 := Order.lt_succ_iff.mp hdegree
      rw [Polynomial.eq_C_of_degree_le_zero hpdeg]
      simp
    have hpair : ∀ j, j ∈ agreement → f j = f i ∧ g j = g i := by
      intro j hj
      have hjEq : P.eval (domain j) = f j + z * g j :=
        (Finset.mem_filter.mp hj).2
      have heq : f j + z * g j = f i + z * g i := by
        rw [← hjEq, ← hiEq, hconstant]
        simp only [Polynomial.eval_C]
      by_cases hg : g j = g i
      · refine ⟨?_, hg⟩
        rw [hg] at heq
        simpa using heq
      · exfalso
        apply hz
        apply Finset.mem_image.mpr
        refine ⟨(j, i), Finset.mem_univ _, ?_⟩
        rw [show collision (j, i) = -(f j - f i) / (g j - g i) by
          simp [collision, hg]]
        apply (div_eq_iff (sub_ne_zero.mpr hg)).2
        linear_combination -heq
    let P₀ : F[X] := Polynomial.C (f i)
    let P₁ : F[X] := Polynomial.C (g i)
    refine ⟨⟨P₀, P₁⟩,
      Polynomial.degree_C_le.trans_lt (by norm_num),
      Polynomial.degree_C_le.trans_lt (by norm_num), ?_, ?_⟩
    · rw [hconstant, hiEq]
      simp [P₀, P₁, correlatedPairSpecialization]
    · ext j
      simp only [polynomialAgreementSet, commonPolynomialAgreementSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        have hjmem : j ∈ agreement := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa [mappedDomain] using hj
        obtain ⟨hfj, hgj⟩ := hpair j hjmem
        simp [P₀, P₁, hfj, hgj]
      · rintro ⟨hfj, hgj⟩
        have hfj' : f i = f j := by
          simpa only [P₀, Polynomial.eval_C] using hfj
        have hgj' : g i = g j := by
          simpa only [P₁, Polynomial.eval_C] using hgj
        rw [hconstant, Polynomial.eval_C, hiEq, hfj', hgj']
        simp

/-- The literal selectors and the retained agreement ratio satisfy the fourth-power
inverse-finite-length-slack line-MCA envelope. -/
theorem finiteLengthSelectorMCAEnvelope_le
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (_hk : 2 ≤ k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n) :
    let C := finiteLengthMCAParameterConstant rho
    let B := finiteLengthJetDegree rho eta n
    let M := finiteLengthDerivativeCap rho eta n
    let H := finiteLengthChallengeHeight rho eta n
    let theta := hybridTheta n (k - 1) A
    finiteLengthMCAEnvelope theta n (k - 1) B M H ≤
      140 * C ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 := by
  dsimp only
  let C := finiteLengthMCAParameterConstant rho
  let Csel := finiteLengthParameterBoundConstant rho
  let Chybrid := automaticHybridEnvelopeConstant rho
  let s := finiteLengthSlack eta n
  let B := finiteLengthJetDegree rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  let H := finiteLengthChallengeHeight rho eta n
  let theta := hybridTheta n (k - 1) A
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hnOne : 1 ≤ n := hnPos
  have hDA : k - 1 < A := by
    have hnCast : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hrhoNltA : rho * n < (A : ℝ) := by
      have hthreshold : rho < automaticFirstOrderThreshold rho :=
        rho_lt_automaticFirstOrderThreshold hrho hrhoOne
      have : rho * n < (automaticFirstOrderThreshold rho + eta) * n := by
        nlinarith
      exact this.trans_le hA
    exact_mod_cast hDrate.trans_lt hrhoNltA
  have hDn : k - 1 ≤ n := hDA.le.trans hAn
  have hC : 1 ≤ C := one_le_finiteLengthMCAParameterConstant rho
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta]
    unfold hybridTheta
    positivity
  have hthetaRate := hybridTheta_le_rate_gap hDn hDA
    hDrate
    hA (show rho < automaticFirstOrderThreshold rho + eta by
      exact (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans
        (lt_add_of_pos_right _ heta))
  have hthresholdGap : 0 < automaticFirstOrderThreshold rho - rho :=
    sub_pos.mpr (rho_lt_automaticFirstOrderThreshold hrho hrhoOne)
  have hthetaHybrid : theta ≤ Chybrid := by
    calc
      theta ≤ 1 / (automaticFirstOrderThreshold rho + eta - rho) := hthetaRate
      _ ≤ 1 / (automaticFirstOrderThreshold rho - rho) := by
        exact div_le_div_of_nonneg_left zero_le_one hthresholdGap (by linarith)
      _ ≤ Chybrid := rateGapInv_le_automaticHybridEnvelopeConstant rho
  have htheta : theta ≤ C := hthetaHybrid.trans (le_max_right _ _)
  obtain ⟨_hm, hMsel, hBsel⟩ :=
    finiteLength_multiplicity_derivativeCap_jetDegree_bounds
      hrho hrhoOne heta haOne hn hbetaHalf
  have hCsel : Csel ≤ C := le_max_left _ _
  have hs : 0 < s := finiteLengthSlack_pos heta hnPos
  have hB : (B : ℝ) ≤ C / s := by
    exact hBsel.trans (div_le_div_of_nonneg_right hCsel hs.le)
  have hM : (M : ℝ) ≤ C / s := by
    exact hMsel.trans (div_le_div_of_nonneg_right hCsel hs.le)
  have hHsel := finiteLengthChallengeHeight_le_common_inv_slack_sq
    hrho hrhoOne heta haOne hn hbetaHalf
  have hH : (H : ℝ) ≤ C / s ^ 2 := by
    exact hHsel.trans (div_le_div_of_nonneg_right hCsel (sq_nonneg s))
  exact finiteLengthMCAEnvelope_le hC heta hnOne hsOne hDn htheta0 htheta hB hM hH

/-- Simpler inverse-`eta` consequence of the literal-selector line-MCA envelope. -/
theorem finiteLengthSelectorMCAEnvelope_le_inv_eta
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 2 ≤ k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n) :
    let C := finiteLengthMCAParameterConstant rho
    let B := finiteLengthJetDegree rho eta n
    let M := finiteLengthDerivativeCap rho eta n
    let H := finiteLengthChallengeHeight rho eta n
    let theta := hybridTheta n (k - 1) A
    finiteLengthMCAEnvelope theta n (k - 1) B M H ≤
      140 * C ^ 6 * n ^ 2 / eta ^ 4 := by
  dsimp only
  apply (finiteLengthSelectorMCAEnvelope_le hrho hrhoOne heta haOne hn hbetaHalf
    hk hDrate hA hAn).trans
  exact div_finiteLengthSlack_four_le_div_eta_four
    (by positivity : 0 ≤ 140 * finiteLengthMCAParameterConstant rho ^ 6 * (n : ℝ) ^ 2)
      heta (length_pos_of_two_le_rate_mul_length hn)

/-- The literal jet-degree selector fits the inverse-square complete-list envelope, including
the zero derivative-cap endpoint. -/
theorem finiteLengthSelectorJetDegree_le_listEnvelope
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthJetDegree rho eta n : ℝ) ≤
      7 * finiteLengthMCAParameterConstant rho ^ 3 * n /
        finiteLengthSlack eta n ^ 2 := by
  let C := finiteLengthMCAParameterConstant rho
  let Csel := finiteLengthParameterBoundConstant rho
  let s := finiteLengthSlack eta n
  let B := finiteLengthJetDegree rho eta n
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
  have hs : 0 < s := finiteLengthSlack_pos heta hnPos
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have hC : 1 ≤ C := one_le_finiteLengthMCAParameterConstant rho
  obtain ⟨_hm, _hM, hBsel⟩ :=
    finiteLength_multiplicity_derivativeCap_jetDegree_bounds
      hrho hrhoOne heta haOne hn hbetaHalf
  have hB : (B : ℝ) ≤ C / s := by
    exact hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  apply hB.trans
  rw [le_div_iff₀ (sq_pos_of_pos hs)]
  have hCs : C / s * s ^ 2 = C * s := by
    field_simp [ne_of_gt hs]
  rw [hCs]
  calc
    C * s ≤ C := mul_le_of_le_one_right (zero_le_one.trans hC) hsOne
    _ ≤ C ^ 3 := by
      nlinarith [mul_nonneg (zero_le_one.trans hC) (sub_nonneg.mpr hC),
        mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)]
    _ = 1 * C ^ 3 * 1 := by ring
    _ ≤ 7 * C ^ 3 * n := by gcongr; norm_num

open Classical in
/-- Complete-list semantics for the literal finite-length selectors.  The positive-cap branch
uses squarefree descent; when the exact floor gives derivative cap zero, the specialized
ordinary equation gives the same inverse-square envelope.  Dimensions zero and one use the
elementary incidence endpoint and require no characteristic reasoning. -/
theorem closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate
    {F : Type u} [Field F]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain received (fun _ ↦ 0) columns)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * finiteLengthMCAParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2 := by
  let C := finiteLengthMCAParameterConstant rho
  let s := finiteLengthSlack eta n
  let B := finiteLengthJetDegree rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hnOne : 1 ≤ n := hnPos
  have hs : 0 < s := finiteLengthSlack_pos heta hnPos
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have hC : 1 ≤ C := one_le_finiteLengthMCAParameterConstant rho
  have hkA : k ≤ A := by
    have hnCast : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hrhoNltA : rho * n < (A : ℝ) := by
      have hthreshold := rho_lt_automaticFirstOrderThreshold hrho hrhoOne
      have : rho * n < (automaticFirstOrderThreshold rho + eta) * n := by
        nlinarith
      exact this.trans_le hA
    have hDA : k - 1 < A := by exact_mod_cast hDrate.trans_lt hrhoNltA
    omega
  by_cases hkTwo : 2 ≤ k
  · have hkn : k ≤ n := hkA.trans hAn
    have hnTwo : 2 ≤ n := hkTwo.trans hkn
    have hMB : M ≤ B := finiteLengthDerivativeCap_le_jetDegree
      hrho hrhoOne heta haOne hn
    by_cases hMzero : M = 0
    · let T := closePolynomialSet domain received k A
      have hfinite : T.Finite := closePolynomialSet_finite domain received hkA
      let phi := Polynomial.eval₂RingHom (RingHom.id F) 0
      let Q : DifferentialPolynomial F 1 := MvPolynomial.map phi cert.Q
      obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
      have hweight : jetWeight Q ≤ B := by
        exact (specialized_weightedTotalDegree_map_le phi _ cert.Q).trans
          cert.toCurve.jetWeight_le
      have hdegree : jetDegree Q (1 : Fin 2) ≤ M := by
        exact (specialized_degreeOf_map_le phi (some (1 : Fin 2)) cert.Q).trans
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
        simpa only [M, B, hMzero, hybridLambdaClosed, hybridT, Nat.cast_zero,
          mul_zero, zero_mul, zero_div, zero_add, add_zero, Nat.sub_zero] using hraw.2.2
      refine ⟨hfinite, ?_⟩
      rw [Set.ncard_eq_toFinset_card _ hfinite]
      apply (hsem hfinite.toFinset (fun P hP ↦
        (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
          (hfinite.mem_toFinset.mp hP))).trans
      exact finiteLengthSelectorJetDegree_le_listEnvelope
        hrho hrhoOne heta haOne hn hbetaHalf
    · have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hMzero
      have htheta : hybridTheta n (k - 1) A ≤ C := by
        have hDn : k - 1 ≤ n := by omega
        have hDA : k - 1 < A := by omega
        have hthetaRate := hybridTheta_le_rate_gap hDn hDA hDrate hA
          (show rho < automaticFirstOrderThreshold rho + eta by
            exact (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans
              (lt_add_of_pos_right _ heta))
        calc
          hybridTheta n (k - 1) A ≤
              1 / (automaticFirstOrderThreshold rho + eta - rho) := hthetaRate
          _ ≤ 1 / (automaticFirstOrderThreshold rho - rho) := by
            exact div_le_div_of_nonneg_left zero_le_one
              (sub_pos.mpr (rho_lt_automaticFirstOrderThreshold hrho hrhoOne)) (by linarith)
          _ ≤ automaticHybridEnvelopeConstant rho :=
            rateGapInv_le_automaticHybridEnvelopeConstant rho
          _ ≤ C := le_max_right _ _
      have hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C := by
        simpa only [C, hybridTheta, show n - k + 1 = n - (k - 1) by omega,
          show A - k + 1 = A - (k - 1) by omega] using htheta
      obtain ⟨_hm, _hMsel, hBsel⟩ :=
        finiteLength_multiplicity_derivativeCap_jetDegree_bounds
          hrho hrhoOne heta haOne hn hbetaHalf
      have hB : (B : ℝ) ≤ C / s := by
        exact hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
      exact closePolynomialSet_finite_and_card_le_finiteLength_of_certificate
        domain received columns cert hnTwo hkTwo hkn hkA hAn hM hMB hchar hC heta hsOne
          hlambda hB
  · have hkOne : k ≤ 1 := by omega
    exact closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
      domain received hnOne hkOne hkA hC heta hsOne

open Classical in
/-- Finite-length retained squarefree MCA from a literal selector certificate.  The exceptional
set is fixed before the challenge `z` and candidate `P`, and the recovered pair has equality of
the full agreement sets. -/
private theorem exists_exceptional_finiteLengthMCA_of_selector_certificate_of_two_le
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 2 ≤ k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f g columns)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hkA : k ≤ A := by
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast length_pos_of_two_le_rate_mul_length hn
    have hrhoNltA : rho * n < (A : ℝ) := by
      have hthreshold := rho_lt_automaticFirstOrderThreshold hrho hrhoOne
      have : rho * n < (automaticFirstOrderThreshold rho + eta) * n := by
        nlinarith
      exact this.trans_le hA
    have hDA : k - 1 < A := by
      exact_mod_cast hDrate.trans_lt hrhoNltA
    omega
  have hMB := finiteLengthDerivativeCap_le_jetDegree
    hrho hrhoOne heta haOne hn
  have hEnvelope :
      finiteLengthMCAEnvelope (hybridTheta n (k - 1) A) n (k - 1)
          (finiteLengthJetDegree rho eta n) (finiteLengthDerivativeCap rho eta n)
          (finiteLengthChallengeHeight rho eta n) ≤
        140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 :=
    finiteLengthSelectorMCAEnvelope_le
      hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
  by_cases hMzero : finiteLengthDerivativeCap rho eta n = 0
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_finiteLengthMCA_zero_derivative
        hrho hrhoOne heta haOne hn hbetaHalf hk hkA hAn
        domain f g iota columns cert hMzero hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [hMzero, hybridEClosed_zero_eq_finiteLengthMCAEnvelope]
    · simpa [hMzero] using hEnvelope
    · exact finiteLengthJetDegree_pos hrho hrhoOne heta haOne hn hbetaHalf
  · have hM : 1 ≤ finiteLengthDerivativeCap rho eta n :=
      Nat.one_le_iff_ne_zero.mpr hMzero
    obtain ⟨exceptional, hcard, hgood⟩ :=
      Squarefree.exists_baseExceptional_retainedSquarefreeLineMCA_of_certificate
        domain f g iota columns cert hk hkA hAn hM hMB hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [Squarefree.retainedSquarefreeLineMCAEnvelope_eq_finiteLengthMCAEnvelope]
    exact hEnvelope

open Classical in
/-- Selector-to-semantics finite-length MCA, including the constant-code endpoint `k = 1`.
The certificate is used for `k ≥ 2`; at `k = 1`, the elementary collision set gives the same
quadratic finite-length envelope. -/
theorem exists_exceptional_finiteLengthMCA_of_selector_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f g columns)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  by_cases hkTwo : 2 ≤ k
  · exact exists_exceptional_finiteLengthMCA_of_selector_certificate_of_two_le
      hrho hrhoOne heta haOne hn hbetaHalf hkTwo hDrate hA hAn
      domain f g iota columns cert hchar
  · have hkOne : k = 1 := by omega
    subst k
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast length_pos_of_two_le_rate_mul_length hn
    have hthresholdPos : 0 < automaticFirstOrderThreshold rho + eta :=
      (hrho.trans (rho_lt_automaticFirstOrderThreshold hrho hrhoOne)).trans
        (lt_add_of_pos_right _ heta)
    have hAPos : 0 < A := by
      exact_mod_cast (mul_pos hthresholdPos hnPos |>.trans_le hA)
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_exactLineMCA_one n A domain f g hAPos
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    let C := finiteLengthMCAParameterConstant rho
    let s := finiteLengthSlack eta n
    have hC : 1 ≤ C := one_le_finiteLengthMCAParameterConstant rho
    have hs : 0 < s := finiteLengthSlack_pos heta
      (length_pos_of_two_le_rate_mul_length hn)
    have hsOne : s ≤ 1 :=
      (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
    rw [le_div_iff₀ (pow_pos hs 4)]
    have hsFour : s ^ 4 ≤ 1 := pow_le_one₀ hs.le hsOne
    have hCpow : 1 ≤ C ^ 6 := one_le_pow₀ hC
    have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    calc
      (n : ℝ) ^ 2 * s ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
      _ ≤ 140 * C ^ 6 * (n : ℝ) ^ 2 := by nlinarith

open Classical in
/-- The same selector-to-semantics theorem with the simpler inverse-`eta` exception budget. -/
theorem exists_exceptional_finiteLengthMCA_of_selector_certificate_inv_eta
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f g columns)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_finiteLengthMCA_of_selector_certificate
      hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
      domain f g iota columns cert hchar
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  exact div_finiteLengthSlack_four_le_div_eta_four
    (by positivity : 0 ≤ 140 * finiteLengthMCAParameterConstant rho ^ 6 * (n : ℝ) ^ 2)
      heta (length_pos_of_two_le_rate_mul_length hn)

open Classical in
/-- One semantic finite-length family: the complete list around `f` has the inverse-square
finite-length-slack bound, while one exceptional challenge set for the line `f + z g` has the
inverse-fourth bound and is chosen before both `z` and `P`.  The two literal certificates may
use different interpolation degrees and column index types; neither is identified with the
recovery degree `k - 1`. -/
theorem finiteLength_completeList_and_exceptionalMCA_of_selector_certificates
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n Nlist Nline Dlist Dline k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (listColumns : Fin Nlist → SourceColumn 1)
    (lineColumns : Fin Nline → SourceColumn 1)
    (listCert : FirstOrderSymbolicCertificate.{u, u} Dlist A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f (fun _ ↦ 0) listColumns)
    (lineCert : FirstOrderSymbolicCertificate.{u, u} Dline A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f g lineColumns)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    ((closePolynomialSet domain f k A).Finite ∧
        ((closePolynomialSet domain f k A).ncard : ℝ) ≤
          7 * finiteLengthMCAParameterConstant rho ^ 3 * n /
            finiteLengthSlack eta n ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 /
            finiteLengthSlack eta n ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  refine ⟨closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate
    hrho hrhoOne heta haOne hn hbetaHalf hDrate hA hAn
      domain f listColumns listCert hchar, ?_⟩
  exact exists_exceptional_finiteLengthMCA_of_selector_certificate
    hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
      domain f g iota lineColumns lineCert hchar

open Classical in
/-- Eta-only consequence of the semantic finite-length family.  It is derived only after the
exact `eta + 1/n` list and exceptional-set bounds, using `eta ≤ eta + 1/n`. -/
theorem finiteLength_completeList_and_exceptionalMCA_of_selector_certificates_inv_eta
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n Nlist Nline Dlist Dline k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (listColumns : Fin Nlist → SourceColumn 1)
    (lineColumns : Fin Nline → SourceColumn 1)
    (listCert : FirstOrderSymbolicCertificate.{u, u} Dlist A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f (fun _ ↦ 0) listColumns)
    (lineCert : FirstOrderSymbolicCertificate.{u, u} Dline A
      (finiteLengthMultiplicity rho eta n)
      (finiteLengthDerivativeCap rho eta n)
      (finiteLengthJetDegree rho eta n) k
      (finiteLengthChallengeHeight rho eta n) domain f g lineColumns)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    ((closePolynomialSet domain f k A).Finite ∧
        ((closePolynomialSet domain f k A).ncard : ℝ) ≤
          7 * finiteLengthMCAParameterConstant rho ^ 3 * n / eta ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨⟨hfinite, hlist⟩, exceptional, hcard, hgood⟩ :=
    finiteLength_completeList_and_exceptionalMCA_of_selector_certificates
      hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
        domain f g iota listColumns lineColumns listCert lineCert hchar
  have hC0 : 0 ≤ finiteLengthMCAParameterConstant rho :=
    zero_le_one.trans (one_le_finiteLengthMCAParameterConstant rho)
  refine ⟨⟨hfinite, hlist.trans ?_⟩, exceptional, hcard.trans ?_, hgood⟩
  · exact div_finiteLengthSlack_sq_le_div_eta_sq
      (by positivity : 0 ≤ 7 * finiteLengthMCAParameterConstant rho ^ 3 * (n : ℝ))
        heta (length_pos_of_two_le_rate_mul_length hn)
  · exact div_finiteLengthSlack_four_le_div_eta_four
      (by positivity : 0 ≤ 140 * finiteLengthMCAParameterConstant rho ^ 6 * (n : ℝ) ^ 2)
        heta (length_pos_of_two_le_rate_mul_length hn)

end

end ReedSolomon.FirstOrder
