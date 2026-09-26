/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthSelectors
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Bounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveMCA

/-!
# Finite-length first-order correlated agreement

Literal finite-length selectors yield a symbolic line certificate and an exact correlated-pair
recovery theorem. The same selectors bound the complete polynomial list by an inverse-square
finite-length slack and the exceptional challenge set by an inverse-fourth slack.

## Main statements

* `exists_finiteLengthFirstOrder_symbolicCertificate` constructs the line certificate.
* `closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate` bounds the list.
* `exists_exceptional_finiteLengthMca_of_selector_certificate` gives exact line agreement.
* `exists_exceptional_firstOrderMca_of_bounded_certificate` bounds both certificate endpoints.
* `finiteLength_completeList_and_exceptionalMca_of_selector_certificates` combines both bounds.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder

open HiddenDerivative
open MvPolynomial

noncomputable section

universe u

/-- One rate-only constant simultaneously controlling the literal interpolation selectors and the
retained-line agreement ratio. -/
def finiteLengthMcaParameterConstant (rho : ℝ) : ℝ :=
  max (finiteLengthParameterBoundConstant rho) (automaticRateEnvelopeConstant rho)

/-- The common finite-length parameter constant is at least one. -/
theorem one_le_finiteLengthMcaParameterConstant (rho : ℝ) :
    1 ≤ finiteLengthMcaParameterConstant rho := by
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- A quadratic collision count fits the finite-length exception budget whenever the slack is
at most one and the envelope constant is at least one. -/
theorem square_le_finiteLengthMcaExceptionBudget
    {C eta : ℝ} {n : ℕ} (hC : 1 ≤ C) (heta : 0 < eta)
    (hsOne : finiteLengthSlack eta n ≤ 1) :
    (n : ℝ) ^ 2 ≤ 140 * C ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 := by
  have hsPos := finiteLengthSlack_pos (n := n) heta
  have hCpow : 1 ≤ C ^ 6 := one_le_pow₀ hC
  rw [le_div_iff₀ (pow_pos hsPos 4)]
  have hsFour : finiteLengthSlack eta n ^ 4 ≤ 1 := pow_le_one₀ hsPos.le hsOne
  have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  calc
    (n : ℝ) ^ 2 * finiteLengthSlack eta n ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    _ ≤ 140 * C ^ 6 * (n : ℝ) ^ 2 := by nlinarith

/-- The retained squarefree line expression equals the finite-length envelope at every length
and code rate, including boundary cases with truncated natural subtraction. -/
theorem Squarefree.retainedSquarefreeLineAgreementEnvelope_eq_finiteLengthMcaEnvelope
    (lambda : ℝ) (n D B M H : ℕ) :
    Squarefree.retainedSquarefreeLineAgreementEnvelope lambda n D B M H =
      finiteLengthMcaEnvelope lambda n D B M H := by
  unfold Squarefree.retainedSquarefreeLineAgreementEnvelope
    Squarefree.retainedOrdinaryCurveAgreementCharge finiteLengthMcaEnvelope
  push_cast
  ring

/-- At derivative cap zero, the retained hybrid expression is the same ordinary endpoint as the
finite-length envelope.  Positivity of `B` selects the nonzero ordinary-tail formula. -/
theorem firstOrderExceptionConstant_zero_eq_finiteLengthMcaEnvelope
    (lambda : ℝ) (n D B H : ℕ) (hB : 1 ≤ B) :
    firstOrderExceptionConstant lambda n D H B 0 =
      finiteLengthMcaEnvelope lambda n D B 0 H := by
  unfold firstOrderExceptionConstant stageStaircase ordinaryTailCharge finiteLengthMcaEnvelope
  rw [ite_eq_right (by omega : B ≠ 0)]
  push_cast
  ring_nf

private theorem finiteLengthJetDegree_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
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
/-- The finite-length selectors construct a symbolic line certificate at interpolation rate
`rho - 1/n` and derivative ratio selected at `rho`. -/
theorem exists_finiteLengthFirstOrder_symbolicCertificate
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
    card_firstOrderExponents hDPos
  have hDrate : (D : ℝ) ≤ R * n := by
    have hshift : (k : ℝ) - 1 ≤ rho * n - 1 := sub_le_sub_right hkRate 1
    rw [finiteLengthRate_eq hnPos]
    dsimp only [D]
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    exact hshift
  have hArate : a * n ≤ A := by
    apply (mul_le_mul_of_nonneg_right
      (automaticAgreement_le (rho := rho) (a := firstOrderRateThreshold rho + eta))
      (Nat.cast_nonneg n)).trans
    exact hA
  have hsourceLower : (n : ℝ) * Nzero ≤
      firstOrderDimensionCount D A m M mu := by
    have hlower := firstOrderSourceCount_mul_le_firstOrderDimensionCount
      (rate := R) (agreement := a) (n := n) (D := D) (A := A) (m := m) (M := M) (mu := mu)
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
  have hw : ∀ i, (w i).natDegree ≤ 1 := fun i ↦ natDegree_receivedLine_le (f i) (g i)
  have hrank :
      ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ r := by
    calc
      _ ≤ n * certifiedEnlargedRankBound 1 m M 0 := by
        simpa only [Fintype.card_fin] using
          rank_firstOrderLocalConstraintMatrix_le (D := D) (A := A) (m := m) (M := M)
            (μ := mu) (fun i ↦ centers i) w columns
            (fun j ↦ firstOrderColumns_eligible
              (D := D) (A := A) (m := m) (M := M) (μ := mu) j)
      _ = r := by
        rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount]
        rfl
  have hrN' : r < Fintype.card (Fin (Fintype.card ↑(firstOrderExponents D A m M mu))) := by
    simpa [N, Fintype.card_coe] using hrN
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le m 1 mu (fun i ↦ centers i) w hw columns
      firstOrderColumns_injective hy₀ (algebraMap F[X] (RatFunc F))
      (IsFractionRing.injective F[X] (RatFunc F)) hrank hrN'
  let Q : DifferentialPolynomial F[X] 1 := SourceColumn.interpolant columns v
  have hheight : r * mu / (N - r) ≤ h := by
    rw [hN]
    have hkernel := scaledKernelHeight_le_floor
      (n := n) (N := firstOrderDimensionCount D A m M mu)
      (r := rlocal) (mu := mu) (N₀ := Nzero) hsurplus hsourceLower
    exact hkernel.trans (by
      simpa only [h, mu, rlocal, Nzero, finiteLengthChallengeHeight] using
        (Nat.le_max_right 1 ⌊(rlocal : ℝ) * mu / (Nzero - rlocal)⌋₊))
  have hvheight : ∀ j, (v j).natDegree ≤ h := by
    intro j
    apply (hvdegree j).trans
    simpa [N] using hheight
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M mu :=
    interpolant_mem_firstOrderSpace columns firstOrderColumns_eligible v
  have hfirstJet : ∀ exponent ∈ Q.support, firstJetExponent exponent ≤ M := by
    intro exponent hexponent
    exact (mem_firstOrderSpace_iff.mp hQsupport exponent hexponent).1
  have htotalJet : ∀ exponent ∈ Q.support, totalJetDegree exponent ≤ mu := by
    intro exponent hexponent
    exact (mem_firstOrderSpace_iff.mp hQsupport exponent hexponent).2.1
  refine ⟨⟨v, Q, rfl, hprimitive,
    SourceColumn.coeff_interpolant_natDegree_le columns firstOrderColumns_injective v hvheight,
    hQsupport, hfirstJet, htotalJet, hconstraints, ?_⟩⟩
  intro E _ iota z
  refine ⟨hnonzero (Polynomial.eval₂RingHom iota z), ?_⟩
  intro indices P hPdegree hcard hagreements
  have hagreeCurve : ∀ i ∈ indices,
      P.eval (iota (centers i)) = (w i).eval₂ iota z := by
    intro i hi
    rw [hagreements i hi]
    simp [w, receivedLine]
    ring
  exact differentialSpecialization_eq_zero_of_firstOrderSpace
    (by omega : k ≤ D + 1)
    (Nat.mul_pos hmPos (by
      have haPos : 0 < firstOrderRateThreshold rho + eta :=
        (hrho.trans (rate_lt_firstOrderRateThreshold hrho hrhoOne)).trans
          (lt_add_of_pos_right _ heta)
      exact_mod_cast (mul_pos haPos (by exact_mod_cast hnPos) |>.trans_le hA)))
    centers w Q hQsupport hconstraints iota z indices P hPdegree hcard hagreeCurve

open Classical in
/-- Generic ordinary-endpoint descent for an actual first-order certificate with exact
derivative cap zero.  The exceptional set is selected before the challenge and candidate. -/
theorem exists_exceptional_firstOrderMca_zero_derivative_of_certificate
    {F : Type u} [Field F]
    {n N Dcert k A m B H : ℕ}
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} Dcert A m 0 B k H
      domain f g columns)
    (hchar : ringChar F = 0 ∨ max (k - 1) 0 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        firstOrderExceptionConstant (agreementIncidenceRatio n (k - 1) A) n (k - 1) H B 0 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨exceptional, _, _, hcard, hgood⟩ :=
    cert.exists_exceptional_hybrid (D := k - 1) (by omega) (by omega)
      (by omega) hAn (by simp) hchar
  exact ⟨exceptional, hcard, hgood⟩

open Classical in
/-- A generic certificate-to-MCA bridge with explicit finite-length arithmetic and support
premises.  It preserves the ordinary `M = 0` endpoint and exact full agreement sets. -/
theorem exists_exceptional_firstOrderMca_of_bounded_certificate
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
    (htheta : agreementIncidenceRatio n (k - 1) A ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n)
    (hM : (M : ℝ) ≤ C / finiteLengthSlack eta n)
    (hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 140 * C ^ 6 * n ^ 2 /
        finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have htheta0 : 0 ≤ agreementIncidenceRatio n (k - 1) A := by
    unfold agreementIncidenceRatio
    positivity
  have hEnvelope := finiteLengthMcaEnvelope_le hC heta hn hsOne hDn htheta0 htheta hB hM hH
  by_cases hMzero : M = 0
  · subst M
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_firstOrderMca_zero_derivative_of_certificate
        hk hkA hAn domain f g columns cert hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [firstOrderExceptionConstant_zero_eq_finiteLengthMcaEnvelope _ _ _ _ _ hBpos]
    exact hEnvelope
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      Squarefree.exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
        domain f g iota columns cert hk hkA hAn
          (Nat.one_le_iff_ne_zero.mpr hMzero) hMB hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [Squarefree.retainedSquarefreeLineAgreementEnvelope_eq_finiteLengthMcaEnvelope]
    exact hEnvelope

/-- The constant-polynomial endpoint needs no interpolation equation.  Pairwise collisions of
received coordinates are the only exceptional challenges. -/
theorem exists_exceptional_exactLineMca_one
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
          simpa using hj
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
theorem finiteLengthSelectorMcaEnvelope_le
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n) :
    let C := finiteLengthMcaParameterConstant rho
    let B := finiteLengthJetDegree rho eta n
    let M := finiteLengthDerivativeCap rho eta n
    let H := finiteLengthChallengeHeight rho eta n
    let theta := agreementIncidenceRatio n (k - 1) A
    finiteLengthMcaEnvelope theta n (k - 1) B M H ≤
      140 * C ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 := by
  dsimp only
  let C := finiteLengthMcaParameterConstant rho
  let Csel := finiteLengthParameterBoundConstant rho
  let Chybrid := automaticRateEnvelopeConstant rho
  let s := finiteLengthSlack eta n
  let B := finiteLengthJetDegree rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  let H := finiteLengthChallengeHeight rho eta n
  let theta := agreementIncidenceRatio n (k - 1) A
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hnOne : 1 ≤ n := hnPos
  have hDA : k - 1 < A := by
    have hnCast : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hrhoNltA : rho * n < (A : ℝ) := by
      have hthreshold : rho < firstOrderRateThreshold rho :=
        rate_lt_firstOrderRateThreshold hrho hrhoOne
      have : rho * n < (firstOrderRateThreshold rho + eta) * n := by
        nlinarith
      exact this.trans_le hA
    exact_mod_cast hDrate.trans_lt hrhoNltA
  have hDn : k - 1 ≤ n := hDA.le.trans hAn
  have hC : 1 ≤ C := one_le_finiteLengthMcaParameterConstant rho
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta]
    unfold agreementIncidenceRatio
    positivity
  have hthetaRate := agreementIncidenceRatio_le_one_div_sub hDn hDA
    hDrate
    hA (show rho < firstOrderRateThreshold rho + eta by
      exact (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans
        (lt_add_of_pos_right _ heta))
  have hthresholdGap : 0 < firstOrderRateThreshold rho - rho :=
    sub_pos.mpr (rate_lt_firstOrderRateThreshold hrho hrhoOne)
  have hthetaHybrid : theta ≤ Chybrid := by
    calc
      theta ≤ 1 / (firstOrderRateThreshold rho + eta - rho) := hthetaRate
      _ ≤ 1 / (firstOrderRateThreshold rho - rho) := by
        exact div_le_div_of_nonneg_left zero_le_one hthresholdGap (by linarith)
      _ ≤ Chybrid := automaticRateGapInv_le_rateEnvelopeConstant rho
  have htheta : theta ≤ C := hthetaHybrid.trans (le_max_right _ _)
  obtain ⟨_hm, hMsel, hBsel⟩ :=
    finiteLength_multiplicity_derivativeCap_jetDegree_bounds
      hrho hrhoOne heta haOne hn hbetaHalf
  have hCsel : Csel ≤ C := le_max_left _ _
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hB : (B : ℝ) ≤ C / s := by
    exact hBsel.trans (div_le_div_of_nonneg_right hCsel hs.le)
  have hM : (M : ℝ) ≤ C / s := by
    exact hMsel.trans (div_le_div_of_nonneg_right hCsel hs.le)
  have hHsel := finiteLengthChallengeHeight_le_common_inv_slack_sq
    hrho hrhoOne heta haOne hn hbetaHalf
  have hH : (H : ℝ) ≤ C / s ^ 2 := by
    exact hHsel.trans (div_le_div_of_nonneg_right hCsel (sq_nonneg s))
  exact finiteLengthMcaEnvelope_le hC heta hnOne hsOne hDn htheta0 htheta hB hM hH

/-- Simpler inverse-`eta` consequence of the literal-selector line-MCA envelope. -/
theorem finiteLengthSelectorMcaEnvelope_le_inv_eta
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n) :
    let C := finiteLengthMcaParameterConstant rho
    let B := finiteLengthJetDegree rho eta n
    let M := finiteLengthDerivativeCap rho eta n
    let H := finiteLengthChallengeHeight rho eta n
    let theta := agreementIncidenceRatio n (k - 1) A
    finiteLengthMcaEnvelope theta n (k - 1) B M H ≤
      140 * C ^ 6 * n ^ 2 / eta ^ 4 := by
  dsimp only
  apply (finiteLengthSelectorMcaEnvelope_le hrho hrhoOne heta haOne hn hbetaHalf
    hDrate hA hAn).trans
  exact div_finiteLengthSlack_four_le_div_eta_four
    (by positivity : 0 ≤ 140 * finiteLengthMcaParameterConstant rho ^ 6 * (n : ℝ) ^ 2)
      heta

/-- The literal jet-degree selector fits the inverse-square complete-list envelope, including
the zero derivative-cap endpoint. -/
theorem finiteLengthSelectorJetDegree_le_listEnvelope
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthJetDegree rho eta n : ℝ) ≤
      7 * finiteLengthMcaParameterConstant rho ^ 3 * n /
        finiteLengthSlack eta n ^ 2 := by
  let C := finiteLengthMcaParameterConstant rho
  let Csel := finiteLengthParameterBoundConstant rho
  let s := finiteLengthSlack eta n
  let B := finiteLengthJetDegree rho eta n
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have hC : 1 ≤ C := one_le_finiteLengthMcaParameterConstant rho
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
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
        7 * finiteLengthMcaParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2 := by
  let C := finiteLengthMcaParameterConstant rho
  let s := finiteLengthSlack eta n
  let B := finiteLengthJetDegree rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  have hnPos : 0 < n := length_pos_of_two_le_rate_mul_length hn
  have hnOne : 1 ≤ n := hnPos
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have hC : 1 ≤ C := one_le_finiteLengthMcaParameterConstant rho
  have hkA : k ≤ A := by
    have hnCast : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hrhoNltA : rho * n < (A : ℝ) := by
      have hthreshold := rate_lt_firstOrderRateThreshold hrho hrhoOne
      have : rho * n < (firstOrderRateThreshold rho + eta) * n := by
        nlinarith
      exact this.trans_le hA
    have hDA : k - 1 < A := by exact_mod_cast hDrate.trans_lt hrhoNltA
    omega
  by_cases hkTwo : 2 ≤ k
  · have hkn : k ≤ n := hkA.trans hAn
    have hnTwo : 2 ≤ n := hkTwo.trans hkn
    have hMB : M ≤ B := finiteLengthDerivativeCap_le_jetDegree
      hrho hrhoOne heta hn
    have htheta : agreementIncidenceRatio n (k - 1) A ≤ C := by
      have hDn : k - 1 ≤ n := by omega
      have hDA : k - 1 < A := by omega
      have hthetaRate := agreementIncidenceRatio_le_one_div_sub hDn hDA hDrate hA
        (show rho < firstOrderRateThreshold rho + eta by
          exact (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans
            (lt_add_of_pos_right _ heta))
      calc
        agreementIncidenceRatio n (k - 1) A ≤
            1 / (firstOrderRateThreshold rho + eta - rho) := hthetaRate
        _ ≤ 1 / (firstOrderRateThreshold rho - rho) := by
          exact div_le_div_of_nonneg_left zero_le_one
            (sub_pos.mpr (rate_lt_firstOrderRateThreshold hrho hrhoOne)) (by linarith)
        _ ≤ automaticRateEnvelopeConstant rho :=
          automaticRateGapInv_le_rateEnvelopeConstant rho
        _ ≤ C := le_max_right _ _
    have hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C := by
      simpa only [C, agreementIncidenceRatio, show n - k + 1 = n - (k - 1) by omega,
        show A - k + 1 = A - (k - 1) by omega] using htheta
    obtain ⟨_hm, _hMsel, hBsel⟩ :=
      finiteLength_multiplicity_derivativeCap_jetDegree_bounds
        hrho hrhoOne heta haOne hn hbetaHalf
    have hB : (B : ℝ) ≤ C / s := by
      exact hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
    exact closePolynomialSet_finite_and_card_le_finiteLength_of_bounded_certificate
      domain received columns cert hnTwo hkTwo hkA hAn hMB hchar hC heta hsOne hlambda hB
  · have hkOne : k ≤ 1 := by omega
    exact closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
      domain received hnOne hkOne hkA hC heta hsOne

open Classical in
/-- Finite-length retained squarefree MCA from a literal selector certificate.  The exceptional
set is fixed before the challenge `z` and candidate `P`, and the recovered pair has equality of
the full agreement sets. -/
private theorem exists_exceptional_finiteLengthMca_of_selector_certificate_of_two_le
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 2 ≤ k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
        140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hkA : k ≤ A := by
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast length_pos_of_two_le_rate_mul_length hn
    have hrhoNltA : rho * n < (A : ℝ) := by
      have hthreshold := rate_lt_firstOrderRateThreshold hrho hrhoOne
      have : rho * n < (firstOrderRateThreshold rho + eta) * n := by
        nlinarith
      exact this.trans_le hA
    have hDA : k - 1 < A := by
      exact_mod_cast hDrate.trans_lt hrhoNltA
    omega
  have hMB := finiteLengthDerivativeCap_le_jetDegree
    hrho hrhoOne heta hn
  have hEnvelope :
      finiteLengthMcaEnvelope (agreementIncidenceRatio n (k - 1) A) n (k - 1)
          (finiteLengthJetDegree rho eta n) (finiteLengthDerivativeCap rho eta n)
          (finiteLengthChallengeHeight rho eta n) ≤
        140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 :=
    finiteLengthSelectorMcaEnvelope_le
      hrho hrhoOne heta haOne hn hbetaHalf hDrate hA hAn
  by_cases hMzero : finiteLengthDerivativeCap rho eta n = 0
  · simp only [hMzero] at cert hchar
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_firstOrderMca_zero_derivative_of_certificate
        hk hkA hAn domain f g columns cert hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [firstOrderExceptionConstant_zero_eq_finiteLengthMcaEnvelope]
    · simpa [hMzero] using hEnvelope
    · exact finiteLengthJetDegree_pos hrho hrhoOne heta haOne hn hbetaHalf
  · have hM : 1 ≤ finiteLengthDerivativeCap rho eta n :=
      Nat.one_le_iff_ne_zero.mpr hMzero
    obtain ⟨exceptional, hcard, hgood⟩ :=
      Squarefree.exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
        domain f g iota columns cert hk hkA hAn hM hMB hchar
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [Squarefree.retainedSquarefreeLineAgreementEnvelope_eq_finiteLengthMcaEnvelope]
    exact hEnvelope

open Classical in
/-- Selector-to-semantics finite-length MCA, including the constant-code endpoint `k = 1`.
The certificate is used for `k ≥ 2`; at `k = 1`, the elementary collision set gives the same
quadratic finite-length envelope. -/
theorem exists_exceptional_finiteLengthMca_of_selector_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
        140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  by_cases hkTwo : 2 ≤ k
  · exact exists_exceptional_finiteLengthMca_of_selector_certificate_of_two_le
      hrho hrhoOne heta haOne hn hbetaHalf hkTwo hDrate hA hAn
      domain f g iota columns cert hchar
  · have hkOne : k = 1 := by omega
    subst k
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast length_pos_of_two_le_rate_mul_length hn
    have hthresholdPos : 0 < firstOrderRateThreshold rho + eta :=
      (hrho.trans (rate_lt_firstOrderRateThreshold hrho hrhoOne)).trans
        (lt_add_of_pos_right _ heta)
    have hAPos : 0 < A := by
      exact_mod_cast (mul_pos hthresholdPos hnPos |>.trans_le hA)
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_exactLineMca_one n A domain f g hAPos
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    have hsOne : finiteLengthSlack eta n ≤ 1 :=
      (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
    exact square_le_finiteLengthMcaExceptionBudget
      (one_le_finiteLengthMcaParameterConstant rho) heta hsOne

open Classical in
/-- The same selector-to-semantics theorem with the simpler inverse-`eta` exception budget. -/
theorem exists_exceptional_finiteLengthMca_of_selector_certificate_inv_eta
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n N Dcert k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
        140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_finiteLengthMca_of_selector_certificate
      hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
      domain f g iota columns cert hchar
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  exact div_finiteLengthSlack_four_le_div_eta_four
    (by positivity : 0 ≤ 140 * finiteLengthMcaParameterConstant rho ^ 6 * (n : ℝ) ^ 2)
      heta

open Classical in
/-- One semantic finite-length family: the complete list around `f` has the inverse-square
finite-length-slack bound, while one exceptional challenge set for the line `f + z g` has the
inverse-fourth bound and is chosen before both `z` and `P`.  The two literal certificates may
use different interpolation degrees and column index types; neither is identified with the
recovery degree `k - 1`. -/
theorem finiteLength_completeList_and_exceptionalMca_of_selector_certificates
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n Nlist Nline Dlist Dline k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
          7 * finiteLengthMcaParameterConstant rho ^ 3 * n /
            finiteLengthSlack eta n ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
            finiteLengthSlack eta n ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  refine ⟨closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate
    hrho hrhoOne heta haOne hn hbetaHalf hDrate hA hAn
      domain f listColumns listCert hchar, ?_⟩
  exact exists_exceptional_finiteLengthMca_of_selector_certificate
    hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
      domain f g iota lineColumns lineCert hchar

open Classical in
/-- Eta-only consequence of the semantic finite-length family.  It is derived only after the
exact `eta + 1/n` list and exceptional-set bounds, using `eta ≤ eta + 1/n`. -/
theorem finiteLength_completeList_and_exceptionalMca_of_selector_certificates_inv_eta
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n Nlist Nline Dlist Dline k A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
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
          7 * finiteLengthMcaParameterConstant rho ^ 3 * n / eta ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨⟨hfinite, hlist⟩, exceptional, hcard, hgood⟩ :=
    finiteLength_completeList_and_exceptionalMca_of_selector_certificates
      hrho hrhoOne heta haOne hn hbetaHalf hk hDrate hA hAn
        domain f g iota listColumns lineColumns listCert lineCert hchar
  have hC0 : 0 ≤ finiteLengthMcaParameterConstant rho :=
    zero_le_one.trans (one_le_finiteLengthMcaParameterConstant rho)
  refine ⟨⟨hfinite, hlist.trans ?_⟩, exceptional, hcard.trans ?_, hgood⟩
  · exact div_finiteLengthSlack_sq_le_div_eta_sq
      (by positivity : 0 ≤ 7 * finiteLengthMcaParameterConstant rho ^ 3 * (n : ℝ))
        heta
  · exact div_finiteLengthSlack_four_le_div_eta_four
      (by positivity : 0 ≤ 140 * finiteLengthMcaParameterConstant rho ^ 6 * (n : ℝ) ^ 2)
        heta

end

end ReedSolomon.FirstOrder
