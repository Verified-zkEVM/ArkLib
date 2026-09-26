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
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.BranchwiseRate

/-!
# Branchwise finite-length first-order bounds

The first-order threshold selects the low-rate interpolation construction below
`firstOrderRateSwitch` and the automatic construction above it. The selected derivative cap
controls the characteristic guard. The resulting list and line-agreement bounds use either
finite-length slack or the simpler gap parameter; over a finite field, the latter also bounds
mutual correlated agreement error.

## Main statements

* `firstOrderBranch_finiteLength_finiteSlack_bounds` bounds complete lists and exceptional
  challenges using `eta + 1/n`.
* `firstOrderBranch_finiteLength_rate_bounds` gives the corresponding bounds using `eta`.
* `firstOrderBranch_finiteLength_mcaError_le` bounds affine-line MCA error over finite fields.

## References

* [DKTZ26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

noncomputable section

set_option autoImplicit false

/-- Above the rate switch, the finite-length derivative ratio is at most one half. -/
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
  have hthreshold : (1 + rho) / 3 ≤ firstOrderRateThreshold rho := by
    rw [firstOrderRateThreshold]
    apply (le_div_iff₀ (by linarith : 0 < 8 - rho)).2
    dsimp only [s, q] at hsBound ⊢
    nlinarith
  have hagreement : (1 + rho) / 3 ≤
      automaticAgreement rho (firstOrderRateThreshold rho + eta) := by
    exact hthreshold.trans (automatic_threshold_lt_agreement hrho hrhoOne
      (lt_add_of_pos_right _ heta)).le
  unfold finiteLengthDerivativeRatio automaticDerivativeRatio firstOrderRateBeta
  rw [div_le_iff₀ (by nlinarith : 0 < 2 * (2 - rho))]
  nlinarith

/-- The derivative cap selected by the first-order rate branch. -/
def firstOrderBranchFiniteLengthDerivativeCap (rho eta : ℝ) (n : ℕ) : ℕ :=
  if rho < firstOrderRateSwitch then lowRateFiniteLengthDerivativeCap rho eta n
  else finiteLengthDerivativeCap rho eta n

/-- The MCA envelope constant selected by the first-order rate branch. -/
def firstOrderBranchFiniteLengthMcaConstant (rho : ℝ) : ℝ :=
  if rho < firstOrderRateSwitch then lowRateFiniteLengthMcaParameterConstant rho
  else finiteLengthMcaParameterConstant rho

/-- The branchwise MCA envelope constant is at least one. -/
theorem one_le_firstOrderBranchFiniteLengthMcaConstant (rho : ℝ) :
    1 ≤ firstOrderBranchFiniteLengthMcaConstant rho := by
  by_cases hlow : rho < firstOrderRateSwitch
  · simp only [firstOrderBranchFiniteLengthMcaConstant, ite_eq_left hlow]
    exact one_le_lowRateFiniteLengthMcaParameterConstant rho
  · simp only [firstOrderBranchFiniteLengthMcaConstant, ite_eq_right hlow]
    exact one_le_finiteLengthMcaParameterConstant rho

open Classical in
/-- Complete lists and exact correlated pairs obey the branchwise finite-slack bounds. The list
size is at most `7 C³ n / (eta + 1/n)²`, and each received line has at most
`140 C⁶ n² / (eta + 1/n)⁴` exceptional challenges, where `C` is the branchwise MCA constant. -/
theorem firstOrderBranch_finiteLength_finiteSlack_bounds
    -- Fix the rate envelope, curve gap, block length, message dimension, and threshold.
    (rho eta : ℝ) (n k A : ℕ)
    -- The rate and gap are positive and the rate is strictly below one.
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    -- The actual agreement fraction `a = firstOrderBranchThreshold rho + eta` is feasible.
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    -- Messages have positive dimension and realized rate at most `rho`.
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    -- The integral threshold realizes agreement fraction `a` and cannot exceed the block length.
    (hA : (firstOrderBranchThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    -- The evaluation embedding supplies `n` distinct points over an arbitrary field `F`.
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    -- Constant codes are unrestricted; otherwise reconstruction and separation clear their caps.
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    -- First, every received word has a finite complete agreement list.
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        -- Its exact finite-gap bound is `7*C^3*n/s^2` in the notation above.
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * firstOrderBranchFiniteLengthMcaConstant rho ^ 3 * n /
            finiteLengthSlack eta n ^ 2) ∧
      -- Second, the same branch parameters control every affine line of received words.
      ∀ f g : Fin n → F,
        -- One exceptional set is chosen from `(f,g)` before challenge and candidate.
        ∃ exceptional : Finset F,
          -- Its exact finite-gap bound is `140*C^6*n^2/s^4`.
          (exceptional.card : ℝ) ≤
            140 * firstOrderBranchFiniteLengthMcaConstant rho ^ 6 * n ^ 2 /
              finiteLengthSlack eta n ^ 4 ∧
          -- Every nonexceptional challenge works simultaneously for every candidate.
          ∀ z ∉ exceptional,
            -- Candidate messages have ordinary polynomial degree below `k`.
            ∀ P : F[X], P.degree < k →
            -- At least `A` agreements trigger the exact-witness conclusion.
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            -- Witnesses reproduce `P` and exactly its entire agreement set.
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  by_cases hlow : rho < firstOrderRateSwitch
  · have haOneLow : firstOrderLowRateThreshold rho + eta < 1 := by
      simpa only [firstOrderBranchThreshold_eq_low hlow] using haOne
    have hALow : (firstOrderLowRateThreshold rho + eta) * (n : ℝ) ≤ A := by
      simpa only [firstOrderBranchThreshold_eq_low hlow] using hA
    have hcharLow : k = 1 ∨ ringChar F = 0 ∨
        max (k - 1) (lowRateFiniteLengthDerivativeCap rho eta n) < ringChar F := by
      simpa [firstOrderBranchFiniteLengthDerivativeCap, hlow] using hchar
    let E := AlgebraicClosure F
    simpa [firstOrderBranchFiniteLengthMcaConstant, hlow] using
      (lowRate_finiteLength_rate_bounds (F := F) (E := E)
        hrho hrhoOne hlow heta haOneLow hk hkRate hALow hAn
          domain (algebraMap F E) hcharLow)
  · have hclean : firstOrderRateSwitch ≤ rho := not_lt.mp hlow
    have haOneClean : firstOrderRateThreshold rho + eta < 1 := by
      simpa only [firstOrderBranchThreshold_eq_clean hclean,
        firstOrderRateThreshold] using haOne
    have hAClean : (firstOrderRateThreshold rho + eta) * (n : ℝ) ≤ A := by
      simpa only [firstOrderBranchThreshold_eq_clean hclean,
        firstOrderRateThreshold] using hA
    have hbetaHalf := finiteLengthDerivativeRatio_le_half_of_rateSwitch_le
      hrho hrhoOne hclean heta
    have hcharClean : k = 1 ∨ ringChar F = 0 ∨
        max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F := by
      simpa [firstOrderBranchFiniteLengthDerivativeCap, hlow] using hchar
    simpa [firstOrderBranchFiniteLengthMcaConstant, hlow] using
      (automaticFirstOrder_finiteLength_finiteSlack_bounds
        rho eta n k A hrho hrhoOne heta haOneClean hbetaHalf hk hkRate
          hAClean hAn domain hcharClean)

open Classical in
/-- Complete lists and exact correlated pairs obey the branchwise gap bounds. The list size is at
most `7 C³ n / eta²`, and each received line has at most `140 C⁶ n² / eta⁴` exceptional
challenges, where `C` is the branchwise MCA constant. -/
theorem firstOrderBranch_finiteLength_rate_bounds
    -- Fix the rate envelope, curve gap, block length, message dimension, and threshold.
    (rho eta : ℝ) (n k A : ℕ)
    -- Work at positive rate and gap, with rate strictly below one.
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    -- Agreement is above the selected first-order threshold by `eta` and remains below one.
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    -- Messages have positive dimension and rate at most `rho`.
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    -- The integer agreement threshold realizes that fraction and lies within the block.
    (hA : (firstOrderBranchThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    -- The theorem is uniform over arbitrary fields and `n` distinct evaluation points.
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    -- Constant codes need no restriction; other codes clear the reconstruction/derivative caps.
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    -- Every received word has a finite complete agreement list.
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        -- The coarser eta-only cardinality bound is exactly `7*C^3*n/eta^2`.
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * firstOrderBranchFiniteLengthMcaConstant rho ^ 3 * n / eta ^ 2) ∧
      -- For every affine received line, one common exceptional set exists.
      ∀ f g : Fin n → F,
        -- This set is fixed before both the challenge and the candidate.
        ∃ exceptional : Finset F,
          -- Its eta-only size bound is exactly `140*C^6*n^2/eta^4`.
          (exceptional.card : ℝ) ≤
            140 * firstOrderBranchFiniteLengthMcaConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
          -- Every challenge outside the set works for every later candidate.
          ∀ z ∉ exceptional,
            -- Candidate polynomials use ordinary degree strictly below `k`.
            ∀ P : F[X], P.degree < k →
            -- A candidate with at least `A` agreements enters exact recovery.
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            -- The witnesses reproduce the candidate and its complete agreement set.
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨hlist, hmca⟩ := firstOrderBranch_finiteLength_finiteSlack_bounds
    rho eta n k A hrho hrhoOne heta haOne hk hkRate hA hAn domain hchar
  constructor
  · intro received
    obtain ⟨hfinite, hcard⟩ := hlist received
    refine ⟨hfinite, hcard.trans ?_⟩
    exact div_finiteLengthSlack_sq_le_div_eta_sq
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (pow_nonneg
            (zero_le_one.trans (one_le_firstOrderBranchFiniteLengthMcaConstant rho)) _))
        (Nat.cast_nonneg n)) heta
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hmca f g
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    exact div_finiteLengthSlack_four_le_div_eta_four
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (pow_nonneg
            (zero_le_one.trans (one_le_firstOrderBranchFiniteLengthMcaConstant rho)) _))
        (sq_nonneg (n : ℝ))) heta

open Classical in
/-- Over a finite field, the affine-line MCA error is at most one and at most the branchwise
exceptional-set budget divided by the field size. -/
theorem firstOrderBranch_finiteLength_mcaError_le
    -- Fix rate, first-order gap, block length, and message dimension.
    (rho eta : ℝ) (n k : ℕ)
    -- The rate and gap are positive and the rate is strictly below one.
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    -- The induced agreement fraction `a` is feasible.
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    -- The message space is nonempty and has rate at most `rho`.
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    -- Probability enters through the finite field; `domain` gives `n` distinct evaluations.
    {F : Type} [Field F] [Fintype F] [SampleableType F] (domain : Fin n ↪ F)
    -- The same constant-code escape and branch-selected characteristic cap remain in force.
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F) :
    -- The left side is MCA error for radius `1-a` under a uniformly sampled line challenge.
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (firstOrderBranchThreshold rho + eta)) ≤
      -- The right side is the exceptional count divided by `|F|`, capped by probability one.
      min 1 (ENNReal.ofReal
        ((140 * firstOrderBranchFiniteLengthMcaConstant rho ^ 6 * n ^ 2 / eta ^ 4) /
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
      (140 * firstOrderBranchFiniteLengthMcaConstant rho ^ 6 * n ^ 2 / eta ^ 4) := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      (firstOrderBranch_finiteLength_rate_bounds
        rho eta n k A hrho hrhoOne heta haOne hk hkRate hA hAn domain hchar).2 f g
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hPzero, hPone, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hPzero, hPone, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - (firstOrderBranchThreshold rho + eta))) = a * n := by
    dsimp only [a]
    ring
  simp only [Fintype.card_fin]
  rw [heq]

end

end ReedSolomon.FirstOrder
