/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.LowRateFiniteLengthBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthMca
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Low-rate finite-length first-order agreement

Low-rate selectors produce symbolic line certificates, bounded complete lists, and exact
correlated agreement outside a bounded set of challenges. The results include the constant-code
endpoint and a finite-field sampling-error bound.

## Main statements

* `exists_lowRateFiniteLengthFirstOrder_symbolicCertificate` constructs the certificate.
* `lowRate_finiteLength_rate_bounds` gives complete-list and exceptional-set bounds.
* `lowRate_finiteLength_mcaError_le` bounds finite-field sampling error.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial
open CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

namespace ReedSolomon.FirstOrder

open HiddenDerivative
open MvPolynomial

noncomputable section

universe u

open Classical in
/-- The low-rate selectors construct a symbolic line certificate with interpolation rate
`rho - 1/n` and derivative ratio selected at `rho`. -/
theorem exists_lowRateFiniteLengthFirstOrder_symbolicCertificate
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (heta : 0 < eta)
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
    hrho hlow heta haOne hn
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
      (min_le_left (firstOrderLowRateThreshold rho + eta)
        ((1 + firstOrderLowRateThreshold rho) / 2))
      (Nat.cast_nonneg n)).trans
    exact hA
  have hsourceLower : (n : ℝ) * Nzero ≤
      firstOrderDimensionCount D A m M mu := by
    have hlower := firstOrderSourceCount_mul_le_firstOrderDimensionCount
      (rate := R) (agreement := a) (n := n) (D := D) (A := A) (m := m) (M := M) (mu := mu)
      hDrate hArate
    simpa only [R, a, m, M, mu, Nzero, lowRateFiniteLengthSourceCount] using hlower
  have hsurplus : (rlocal : ℝ) < Nzero := by
    have hdelta := lowRateFiniteLengthDensityMargin_pos
      hrho hlow heta haOne hn
    have hgap := lowRateFiniteLength_count_gap hrho hlow heta haOne hn
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
      simpa only [h, mu, rlocal, Nzero, lowRateFiniteLengthChallengeHeight] using
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
      have haPos : 0 < firstOrderLowRateThreshold rho + eta :=
        (hrho.trans (rate_lt_firstOrderLowRateThreshold hrho
          ((firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow))).trans
          (lt_add_of_pos_right _ heta)
      exact_mod_cast (mul_pos haPos (by exact_mod_cast hnPos) |>.trans_le hA)))
    centers w Q hQsupport hconstraints iota z indices P hPdegree hcard hagreeCurve

/-- Rate-only control of the retained line ratio on the low-rate stationary branch. -/
def lowRateHybridEnvelopeConstant (rho : ℝ) : ℝ :=
  max 1 (1 / (firstOrderLowRateThreshold rho - rho))

/-- One low-rate constant controlling both the exact selectors and the retained line ratio. -/
def lowRateFiniteLengthMcaParameterConstant (rho : ℝ) : ℝ :=
  max (lowRateParameterBoundConstant rho) (lowRateHybridEnvelopeConstant rho)

/-- The low-rate parameter constant is at least one. -/
theorem one_le_lowRateFiniteLengthMcaParameterConstant (rho : ℝ) :
    1 ≤ lowRateFiniteLengthMcaParameterConstant rho := by
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- The agreement incidence ratio is bounded by the low-rate parameter constant. -/
theorem lowRate_agreementIncidenceRatio_le_parameterConstant
    {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (hDn : D ≤ n) (hDA : D < A)
    (hDrate : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) :
    agreementIncidenceRatio n D A ≤ lowRateFiniteLengthMcaParameterConstant rho := by
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
  have hthetaRate := agreementIncidenceRatio_le_one_div_sub hDn hDA hDrate hA
    (hthreshold.trans (lt_add_of_pos_right _ heta))
  calc
    agreementIncidenceRatio n D A ≤ 1 / (firstOrderLowRateThreshold rho + eta - rho) := hthetaRate
    _ ≤ 1 / (firstOrderLowRateThreshold rho - rho) := by
      exact div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr hthreshold) (by linarith)
    _ ≤ lowRateHybridEnvelopeConstant rho := le_max_right _ _
    _ ≤ lowRateFiniteLengthMcaParameterConstant rho := le_max_right _ _

open Classical in
/-- Assumption-free complete-list semantics for the exact low-rate selectors in dimension at
least two.  The symbolic certificate is constructed internally from the literal count gap. -/
theorem lowRate_closePolynomialSet_finite_and_card_le_finiteLength
    {F : Type u} [Field F] {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (_hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        7 * lowRateFiniteLengthMcaParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2 := by
  let C := lowRateFiniteLengthMcaParameterConstant rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let M := lowRateFiniteLengthDerivativeCap rho eta n
  let B := lowRateFiniteLengthJetDegree rho eta n
  let H := lowRateFiniteLengthChallengeHeight rho eta n
  have hnPos := length_pos_of_two_le_rate_mul_length hn
  have hkA : k ≤ A := by
    have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
    have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
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
    hrho heta haOne hn hlow hk hkRate hA domain received (fun _ ↦ 0)
  have hMB : M ≤ B := by
    dsimp only [M, B]
    exact lowRateFiniteLengthDerivativeCap_le_jetDegree hrho heta haOne hn
  have hsOne := (lowRateFiniteLengthSlack_lt_one hrho hlow haOne hn).le
  have hC : 1 ≤ C := one_le_lowRateFiniteLengthMcaParameterConstant rho
  have hs := finiteLengthSlack_pos (n := n) heta
  obtain ⟨_hm, _hM, hBsel, _hH⟩ :=
    lowRateFiniteLength_parameter_bounds hrho hlow heta haOne hn
  have hB : (B : ℝ) ≤ C / finiteLengthSlack eta n := by
    exact hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  have htheta := lowRate_agreementIncidenceRatio_le_parameterConstant hrho hlow heta
    (show k - 1 ≤ n by omega) (show k - 1 < A by omega) hDrate hA
  have hlambda : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ C := by
    simpa only [C, agreementIncidenceRatio, show n - k + 1 = n - (k - 1) by omega,
      show A - k + 1 = A - (k - 1) by omega] using htheta
  exact closePolynomialSet_finite_and_card_le_finiteLength_of_bounded_certificate
    domain received
      (firstOrderColumns (D := k - 1) (A := A) (m := m) (M := M) (μ := B))
      cert hnTwo hk hkA hAn hMB hchar hC heta hsOne hlambda hB

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
        7 * lowRateFiniteLengthMcaParameterConstant rho ^ 3 * n / eta ^ 2 := by
  obtain ⟨hfinite, hcard⟩ := lowRate_closePolynomialSet_finite_and_card_le_finiteLength
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain received hchar
  refine ⟨hfinite, hcard.trans ?_⟩
  exact div_finiteLengthSlack_sq_le_div_eta_sq
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (zero_le_one.trans (one_le_lowRateFiniteLengthMcaParameterConstant rho)) _))
      (Nat.cast_nonneg n))
      heta

/-- The selected low-rate total jet degree is positive. -/
theorem lowRateFiniteLengthJetDegree_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    0 < lowRateFiniteLengthJetDegree rho eta n := by
  unfold lowRateFiniteLengthJetDegree
  apply Nat.ceil_pos.mpr
  have hm := lowRateFiniteLengthMultiplicity_pos hrho hlow heta haOne hn
  have ha := lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le
  have hrate := finiteLengthRate_pos hrho hn
  positivity

open Classical in
/-- Assumption-free retained squarefree line MCA for the exact low-rate selectors in dimension
at least two.  The exceptional set precedes both challenge and candidate quantifiers. -/
theorem exists_exceptional_lowRateFiniteLengthMca
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {rho eta : ℝ} {n k A : ℕ}
    (hrho : 0 < rho) (_hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderLowRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  let C := lowRateFiniteLengthMcaParameterConstant rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let M := lowRateFiniteLengthDerivativeCap rho eta n
  let B := lowRateFiniteLengthJetDegree rho eta n
  let H := lowRateFiniteLengthChallengeHeight rho eta n
  have hnPos := length_pos_of_two_le_rate_mul_length hn
  have hkA : k ≤ A := by
    have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
    have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hkAlt : k < A := by
      exact_mod_cast (hkRate.trans_lt <| (mul_lt_mul_of_pos_right
        (hthreshold.trans (lt_add_of_pos_right _ heta)) hnReal).trans_le hA)
    exact hkAlt.le
  have hkn : k ≤ n := hkA.trans hAn
  have hDrate : ((k - 1 : ℕ) : ℝ) ≤ rho * n := by
    exact (show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast (Nat.sub_le k 1)).trans hkRate
  obtain ⟨cert⟩ := exists_lowRateFiniteLengthFirstOrder_symbolicCertificate
    hrho heta haOne hn hlow hk hkRate hA domain f g
  have hMB : M ≤ B := by
    dsimp only [M, B]
    exact lowRateFiniteLengthDerivativeCap_le_jetDegree hrho heta haOne hn
  have hBpos : 1 ≤ B := by
    dsimp only [B]
    exact lowRateFiniteLengthJetDegree_pos hrho hlow heta haOne hn
  have hsOne := (lowRateFiniteLengthSlack_lt_one hrho hlow haOne hn).le
  have hC : 1 ≤ C := one_le_lowRateFiniteLengthMcaParameterConstant rho
  have hs := finiteLengthSlack_pos (n := n) heta
  obtain ⟨_hm, hMsel, hBsel, hHsel⟩ :=
    lowRateFiniteLength_parameter_bounds hrho hlow heta haOne hn
  have hM : (M : ℝ) ≤ C / finiteLengthSlack eta n :=
    hMsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  have hB : (B : ℝ) ≤ C / finiteLengthSlack eta n :=
    hBsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  have hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2 :=
    hHsel.trans (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have htheta := lowRate_agreementIncidenceRatio_le_parameterConstant hrho hlow heta
    (show k - 1 ≤ n by omega) (show k - 1 < A by omega) hDrate hA
  exact exists_exceptional_firstOrderMca_of_bounded_certificate
    domain f g iota
      (firstOrderColumns (D := k - 1) (A := A) (m := m) (M := M) (μ := B)) cert
      (by omega) hk hkA hAn hBpos hMB hchar hC heta hsOne
      (by omega) htheta hB hM hH

open Classical in
/-- The inverse-`eta` low-rate MCA consequence. -/
theorem exists_exceptional_lowRateFiniteLengthMca_inv_eta
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
        140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_lowRateFiniteLengthMca
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f g iota hchar
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  exact div_finiteLengthSlack_four_le_div_eta_four
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (zero_le_one.trans (one_le_lowRateFiniteLengthMcaParameterConstant rho)) _))
      (sq_nonneg (n : ℝ))) heta

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
        7 * lowRateFiniteLengthMcaParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2 := by
  exact closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
    domain received hn hk hkA (one_le_lowRateFiniteLengthMcaParameterConstant rho)
      heta hsOne

open Classical in
/-- Constant-code line endpoint with the low-rate fourth-power envelope.  It requires neither
the selector count gap nor the characteristic guard. -/
theorem exists_exceptional_lowRateFiniteLengthMca_one
    {F : Type u} [Field F] {rho eta : ℝ} {n A : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hA : 0 < A) (heta : 0 < eta)
    (hsOne : finiteLengthSlack eta n ≤ 1) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
          finiteLengthSlack eta n ^ 4 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 1 z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactLineMca_one n A domain f g hA
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  let C := lowRateFiniteLengthMcaParameterConstant rho
  let s := finiteLengthSlack eta n
  have hC : 1 ≤ C := one_le_lowRateFiniteLengthMcaParameterConstant rho
  have hs : 0 < s := finiteLengthSlack_pos (n := n) heta
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
theorem lowRate_finiteLength_completeList_and_exceptionalMca
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
        7 * lowRateFiniteLengthMcaParameterConstant rho ^ 3 * n /
          finiteLengthSlack eta n ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
            finiteLengthSlack eta n ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  refine ⟨lowRate_closePolynomialSet_finite_and_card_le_finiteLength
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f hchar, ?_⟩
  exact exists_exceptional_lowRateFiniteLengthMca
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f g iota hchar

open Classical in
/-- Eta-only consequence of the low-rate semantic family, derived after the exact
`eta + 1/n` bounds. -/
theorem lowRate_finiteLength_completeList_and_exceptionalMca_inv_eta
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
        7 * lowRateFiniteLengthMcaParameterConstant rho ^ 3 * n / eta ^ 2) ∧
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  refine ⟨lowRate_closePolynomialSet_finite_and_card_le_inv_eta
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f hchar, ?_⟩
  exact exists_exceptional_lowRateFiniteLengthMca_inv_eta
    hrho hrhoOne hlow heta haOne hn hk hkRate hA hAn domain f g iota hchar

/-- The finite-length slack is below one when the rate times length is at least one. -/
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
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
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
          7 * lowRateFiniteLengthMcaParameterConstant rho ^ 3 * n /
            finiteLengthSlack eta n ^ 2) ∧
      ∀ f g : Fin n → F,
        ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤
            140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 /
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
      exact exists_exceptional_lowRateFiniteLengthMca
        hrho hrhoOne hlow heta haOne hnRate hkTwo hkRate hA hAn domain f g iota hcharTwo
  · have hkOne : k = 1 := by omega
    subst k
    have hkRateOne : (1 : ℝ) ≤ rho * (n : ℝ) := by simpa using hkRate
    have hsOne : finiteLengthSlack eta n ≤ 1 :=
      (lowRateFiniteLengthSlack_lt_one_of_one_le_rate_mul_length
        (rho := rho) (eta := eta) (n := n) hrho hrhoOne hlow haOne hkRateOne).le
    have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
    have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
    have hAPos : 0 < A := by
      have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
      exact_mod_cast (mul_pos
        ((hrho.trans hthreshold).trans (lt_add_of_pos_right _ heta)) hnReal |>.trans_le hA)
    constructor
    · intro received
      exact lowRate_closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
        domain received (by omega) (by omega) (by omega) heta hsOne
    · intro f g
      exact exists_exceptional_lowRateFiniteLengthMca_one
        domain f g hAPos heta hsOne

open Classical in
/-- Finite-field probability is derived separately from the arbitrary-field low-rate semantic
exceptional-set theorem by division by `|F|` and capping at one. -/
theorem lowRate_finiteLength_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] [SampleableType F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (firstOrderLowRateThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) /
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
      (140 * lowRateFiniteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) := by
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
              (zero_le_one.trans (one_le_lowRateFiniteLengthMcaParameterConstant rho)) _))
          (sq_nonneg (n : ℝ))) heta
    · intro z hz P hP hagree
      obtain ⟨pair, hPzero, hPone, heq, hset⟩ := hgood z hz P hP hagree
      refine ⟨pair.1, pair.2, hPzero, hPone, ?_, ?_⟩
      · simpa [correlatedPairSpecialization] using heq
      · simpa using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - (firstOrderLowRateThreshold rho + eta))) = a * n := by
    dsimp only [a]
    ring
  simp only [Fintype.card_fin]
  rw [heq]


end

end ReedSolomon.FirstOrder
