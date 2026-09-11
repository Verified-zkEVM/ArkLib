/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.LowRateSemantics
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthRateBounds

/-! # Branchwise finite-length first-order rate bounds -/

@[expose] public section

namespace ReedSolomon.FirstOrder

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

noncomputable section

set_option autoImplicit false

/-- Above the stationary cutoff, the clean threshold puts the tuned derivative ratio in the
`beta ≤ 1/2` rank branch. -/
theorem finiteLengthDerivativeRatio_le_half_of_rateSwitch_le
    {rho eta : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hswitch : firstOrderRateSwitch ≤ rho) (heta : 0 < eta) :
    finiteLengthDerivativeRatio rho eta ≤ 1 / 2 := by
  let q := rho * (5 - rho) * (2 - rho)
  let s := Real.sqrt q
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg (mul_nonneg hrho.le (by linarith)) (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = q := by
    dsimp only [s]
    exact Real.sq_sqrt hq
  have hs13 : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg _
  have hs13Sq : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hswitchPoly : firstOrderRateSwitch ^ 2 - 22 * firstOrderRateSwitch + 4 = 0 := by
    unfold firstOrderRateSwitch
    nlinarith
  have hswitchLtOne : firstOrderRateSwitch < 1 := by
    unfold firstOrderRateSwitch
    nlinarith
  have hfactorOne : rho ^ 2 - 22 * rho + 4 ≤ 0 := by
    have hdiff :
        (rho ^ 2 - 22 * rho + 4) -
            (firstOrderRateSwitch ^ 2 - 22 * firstOrderRateSwitch + 4) =
          (rho - firstOrderRateSwitch) * (rho + firstOrderRateSwitch - 22) := by ring
    have hleft : 0 ≤ rho - firstOrderRateSwitch := sub_nonneg.mpr hswitch
    have hright : rho + firstOrderRateSwitch - 22 ≤ 0 := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hleft hright]
  have hfactorTwo : -rho ^ 2 + 10 * rho - 16 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrho.le) (sub_nonneg.mpr hrho.le),
      mul_nonneg (sub_nonneg.mpr (show rho ≤ 2 by linarith))
        (sub_nonneg.mpr (show rho ≤ 8 by linarith))]
  have hpoly : 0 ≤ 36 * q - (8 - 2 * rho - rho ^ 2) ^ 2 := by
    have hprod : 0 ≤
        (rho ^ 2 - 22 * rho + 4) * (-rho ^ 2 + 10 * rho - 16) :=
      mul_nonneg_of_nonpos_of_nonpos hfactorOne hfactorTwo
    dsimp only [q]
    nlinarith
  have hrhs : 0 ≤ 8 - 2 * rho - rho ^ 2 := by
    nlinarith [sq_nonneg (rho - 1)]
  have hsBound : 8 - 2 * rho - rho ^ 2 ≤ 6 * s := by
    nlinarith [sq_nonneg (6 * s - (8 - 2 * rho - rho ^ 2))]
  have hthreshold : (1 + rho) / 3 ≤ automaticFirstOrderThreshold rho := by
    rw [automaticFirstOrderThreshold]
    apply (le_div_iff₀ (by linarith : 0 < 8 - rho)).2
    dsimp only [s, q] at hsBound ⊢
    nlinarith
  have hagreement : (1 + rho) / 3 ≤
      automaticAgreement rho (automaticFirstOrderThreshold rho + eta) := by
    exact hthreshold.trans (automatic_threshold_lt_agreement hrho hrhoOne
      (lt_add_of_pos_right _ heta)).le
  unfold finiteLengthDerivativeRatio automaticBeta
  rw [div_le_iff₀ (by nlinarith : 0 < 2 * (2 - rho))]
  nlinarith

/-- Exact branchwise derivative cap used by the characteristic guard. -/
def firstOrderBranchFiniteLengthDerivativeCap (rho eta : ℝ) (n : ℕ) : ℕ :=
  if rho < firstOrderRateSwitch then lowRateFiniteLengthDerivativeCap rho eta n
  else finiteLengthDerivativeCap rho eta n

/-- Rate-only constant selected on the same branch as the finite-length interpolation recipe. -/
def firstOrderBranchFiniteLengthMCAConstant (rho : ℝ) : ℝ :=
  if rho < firstOrderRateSwitch then lowRateFiniteLengthMCAParameterConstant rho
  else finiteLengthMCAParameterConstant rho

theorem one_le_firstOrderBranchFiniteLengthMCAConstant (rho : ℝ) :
    1 ≤ firstOrderBranchFiniteLengthMCAConstant rho := by
  by_cases hlow : rho < firstOrderRateSwitch
  · simp only [firstOrderBranchFiniteLengthMCAConstant, if_pos hlow]
    exact one_le_lowRateFiniteLengthMCAParameterConstant rho
  · simp only [firstOrderBranchFiniteLengthMCAConstant, if_neg hlow]
    exact one_le_finiteLengthMCAParameterConstant rho

open Classical in
/-- All-rate finite-length first-order list/MCA semantics.  The selector branch, its agreement
threshold, its rate-only constant, and its exact derivative cap are chosen together. -/
theorem firstOrderBranch_finiteLength_finiteSlack_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderBranchThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * firstOrderBranchFiniteLengthMCAConstant rho ^ 3 * n /
            finiteLengthSlack eta n ^ 2) ∧
      ∀ f g : Fin n → F,
        ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤
            140 * firstOrderBranchFiniteLengthMCAConstant rho ^ 6 * n ^ 2 /
              finiteLengthSlack eta n ^ 4 ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  by_cases hlow : rho < firstOrderRateSwitch
  · have haOneLow : firstOrderLowRateThreshold rho + eta < 1 := by
      simpa only [firstOrderBranchThreshold_eq_low hlow] using haOne
    have hALow : (firstOrderLowRateThreshold rho + eta) * (n : ℝ) ≤ A := by
      simpa only [firstOrderBranchThreshold_eq_low hlow] using hA
    have hcharLow : k = 1 ∨ ringChar F = 0 ∨
        max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F := by
      simpa only [firstOrderBranchFiniteLengthDerivativeCap, if_pos hlow] using hchar
    let E := AlgebraicClosure F
    simpa only [firstOrderBranchFiniteLengthMCAConstant, if_pos hlow] using
      (lowRate_finiteLength_rate_bounds (F := F) (E := E)
        hrho hrhoOne hlow heta haOneLow hk hkRate hALow hAn
          domain (algebraMap F E) hcharLow)
  · have hclean : firstOrderRateSwitch ≤ rho := not_lt.mp hlow
    have haOneClean : automaticFirstOrderThreshold rho + eta < 1 := by
      simpa only [firstOrderBranchThreshold_eq_clean hclean,
        firstOrderRateThreshold, automaticFirstOrderThreshold] using haOne
    have hAClean : (automaticFirstOrderThreshold rho + eta) * (n : ℝ) ≤ A := by
      simpa only [firstOrderBranchThreshold_eq_clean hclean,
        firstOrderRateThreshold, automaticFirstOrderThreshold] using hA
    have hbetaHalf := finiteLengthDerivativeRatio_le_half_of_rateSwitch_le
      hrho hrhoOne hclean heta
    have hcharClean : k = 1 ∨ ringChar F = 0 ∨
        max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F := by
      simpa only [firstOrderBranchFiniteLengthDerivativeCap, if_neg hlow] using hchar
    simpa only [firstOrderBranchFiniteLengthMCAConstant, if_neg hlow] using
      (automaticFirstOrder_finiteLength_finiteSlack_bounds
        rho eta n k A hrho hrhoOne heta haOneClean hbetaHalf hk hkRate
          hAClean hAn domain hcharClean)

open Classical in
/-- Eta-only consequence of the all-rate semantic family, derived from the exact
`eta + 1/n` bounds. -/
theorem firstOrderBranch_finiteLength_rate_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderBranchThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * firstOrderBranchFiniteLengthMCAConstant rho ^ 3 * n / eta ^ 2) ∧
      ∀ f g : Fin n → F,
        ∃ exceptional : Finset F,
          (exceptional.card : ℝ) ≤
            140 * firstOrderBranchFiniteLengthMCAConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨hlist, hmca⟩ := firstOrderBranch_finiteLength_finiteSlack_bounds
    rho eta n k A hrho hrhoOne heta haOne hk hkRate hA hAn domain hchar
  have hnPos : 0 < n := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hprod : 0 < rho * (n : ℝ) := hkReal.trans_le hkRate
    have hnReal : (0 : ℝ) < n := by nlinarith [hrho]
    exact_mod_cast hnReal
  constructor
  · intro received
    obtain ⟨hfinite, hcard⟩ := hlist received
    refine ⟨hfinite, hcard.trans ?_⟩
    exact div_finiteLengthSlack_sq_le_div_eta_sq
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (pow_nonneg
            (zero_le_one.trans (one_le_firstOrderBranchFiniteLengthMCAConstant rho)) _))
        (Nat.cast_nonneg n)) heta hnPos
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hmca f g
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    exact div_finiteLengthSlack_four_le_div_eta_four
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (pow_nonneg
            (zero_le_one.trans (one_le_firstOrderBranchFiniteLengthMCAConstant rho)) _))
        (sq_nonneg (n : ℝ))) heta hnPos

open Classical in
/-- Separate finite-field probability consequence of the all-rate semantic facade. -/
theorem firstOrderBranch_finiteLength_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (firstOrderBranchThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((140 * firstOrderBranchFiniteLengthMCAConstant rho ^ 6 * n ^ 2 / eta ^ 4) /
          (Fintype.card F : ℝ))) := by
  let a := firstOrderBranchThreshold rho + eta
  let A := Nat.ceil (a * n)
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hAn : A ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      a * (n : ℝ) ≤ 1 * n :=
        mul_le_mul_of_nonneg_right haOne.le (Nat.cast_nonneg n)
      _ = n := one_mul _
  have hline : LineExactAgreementBound domain k A
      (140 * firstOrderBranchFiniteLengthMCAConstant rho ^ 6 * n ^ 2 / eta ^ 4) := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      (firstOrderBranch_finiteLength_rate_bounds
        rho eta n k A hrho hrhoOne heta haOne hk hkRate hA hAn domain hchar).2 f g
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hPzero, hPone, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hPzero, hPone, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - (firstOrderBranchThreshold rho + eta))) = a * n := by
    dsimp only [a]
    ring
  rw [heq]

end

end ReedSolomon.FirstOrder
