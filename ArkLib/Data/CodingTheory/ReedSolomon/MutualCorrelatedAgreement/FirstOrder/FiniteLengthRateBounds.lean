/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthMca
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Finite-length first-order rate bounds

The literal finite-length selectors bound every complete polynomial list and recover exact
correlated pairs outside a fixed exceptional set for each received line. For finite fields, the
exception count also bounds the affine-line mutual correlated agreement error.

## Main statements

* `automaticFirstOrder_finiteLength_finiteSlack_bounds` gives the inverse-square list and
  inverse-fourth line bounds using `eta + 1/n`.
* `automaticFirstOrder_finiteLength_rate_bounds` gives the corresponding bounds using `eta`.
* `automaticFirstOrder_finiteLength_mcaError_le` bounds finite-field line sampling error.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

noncomputable section

set_option autoImplicit false

private theorem finiteLengthSlack_lt_one_of_one_le_rate_mul_length
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (1 : ℝ) ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hnPos : (0 : ℝ) < n := by
    by_contra hnNot
    have hnZero : (n : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hnNot) (Nat.cast_nonneg n)
    rw [hnZero, mul_zero] at hn
    norm_num at hn
  have hinv : 1 / (n : ℝ) ≤ rho := by
    rw [div_le_iff₀ hnPos]
    simpa [mul_comm] using hn
  have hthreshold := rate_lt_firstOrderRateThreshold hrho hrhoOne
  unfold finiteLengthSlack
  linarith

open Classical in
/-- Automatic semantic finite-length bounds on the clean first-order selector branch.

For every received word the complete list is finite and has size at most `7 C³ n / (eta + 1/n)²`.
Independently, for every received line, a separately constructed line certificate gives one
exceptional set of size at most `140 C⁶ n² / (eta + 1/n)⁴`, fixed before the challenge
and candidate.
The `k = 1` endpoint is dispatched before the nontrivial selector feasibility argument. -/
theorem automaticFirstOrder_finiteLength_finiteSlack_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * finiteLengthMcaParameterConstant rho ^ 3 * n / finiteLengthSlack eta n ^ 2) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hrho : 0 < rho :=
    pos_of_mul_pos_left ((Nat.cast_pos.mpr hk).trans_le hkRate) (Nat.cast_nonneg n)
  have hnPos : 0 < n := by
    have hnReal : (0 : ℝ) < n := by
      by_contra hnNot
      have hnZero : (n : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hnNot) (Nat.cast_nonneg n)
      rw [hnZero, mul_zero] at hkRate
      have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
      linarith
    exact_mod_cast hnReal
  have hDrate : (((k - 1 : ℕ) : ℝ)) ≤ rho * n :=
    (Nat.cast_le.mpr (Nat.sub_le k 1)).trans hkRate
  by_cases hkTwo : 2 ≤ k
  · have hchar := hchar.resolve_left (by omega)
    have hnSelector : (2 : ℝ) ≤ rho * n :=
      (by exact_mod_cast hkTwo : (2 : ℝ) ≤ k).trans hkRate
    constructor
    · intro received
      obtain ⟨listCert⟩ := exists_finiteLengthFirstOrder_symbolicCertificate
        hrhoOne heta haOne hnSelector hbetaHalf hkTwo hkRate hA
          domain received (fun _ ↦ 0)
      exact closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate
        hrho hrhoOne heta haOne hnSelector hbetaHalf hDrate hA
          domain received _ listCert hchar
    · intro f g
      obtain ⟨lineCert⟩ := exists_finiteLengthFirstOrder_symbolicCertificate
        hrhoOne heta haOne hnSelector hbetaHalf hkTwo hkRate hA domain f g
      exact exists_exceptional_finiteLengthMca_of_selector_certificate
        hrho hrhoOne heta haOne hnSelector hbetaHalf hk hDrate hA hAn
          domain f g _ lineCert hchar
  · have hkOne : k = 1 := by omega
    subst k
    have hkRateOne : (1 : ℝ) ≤ rho * (n : ℝ) := by simpa using hkRate
    have hsOne : finiteLengthSlack eta n ≤ 1 :=
      (finiteLengthSlack_lt_one_of_one_le_rate_mul_length
        (n := n) hrho hrhoOne haOne hkRateOne).le
    have hC : 1 ≤ finiteLengthMcaParameterConstant rho :=
      one_le_finiteLengthMcaParameterConstant rho
    have hAPos : 0 < A := by
      have hthresholdPos : 0 < firstOrderRateThreshold rho + eta :=
        (hrho.trans (rate_lt_firstOrderRateThreshold hrho hrhoOne)).trans
          (lt_add_of_pos_right _ heta)
      exact_mod_cast (mul_pos hthresholdPos (by exact_mod_cast hnPos) |>.trans_le hA)
    constructor
    · intro received
      exact closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
        domain received (by omega) (by omega) (by omega) hC heta hsOne
    · intro f g
      obtain ⟨exceptional, hcard, hgood⟩ :=
        exists_exceptional_exactLineMca_one n A domain f g
      refine ⟨exceptional, hcard.trans ?_, hgood⟩
      exact square_le_finiteLengthMcaExceptionBudget hC heta hsOne

open Classical in
/-- Automatic semantic finite-length bounds on the clean first-order selector branch.

For every received word the complete list is finite and has size at most `7 C³ n / eta²`.
Independently, for every received line, a separately constructed line certificate gives one
exceptional set of size at most `140 C⁶ n² / eta⁴`, fixed before the challenge and candidate.
The `k = 1` endpoint is dispatched before the nontrivial selector feasibility argument. -/
theorem automaticFirstOrder_finiteLength_rate_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * finiteLengthMcaParameterConstant rho ^ 3 * n / eta ^ 2) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  by_cases hAn : A ≤ n
  swap
  · have hsmall (received : Fin n → F) (P : F[X]) :
        ¬ A ≤ (polynomialAgreementSet domain received P).card := by
      intro h
      exact hAn (h.trans (by
        simpa using (polynomialAgreementSet domain received P).card_le_univ))
    have hC0 := zero_le_one.trans (one_le_finiteLengthMcaParameterConstant rho)
    constructor
    · intro received
      have hempty : closePolynomialSet domain received k A = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun P hP ↦ hsmall received P hP.2
      rw [hempty]
      refine ⟨Set.finite_empty, ?_⟩
      simp only [Set.ncard_empty, Nat.cast_zero]
      positivity
    · intro f g
      refine ⟨∅, ?_, ?_⟩
      · simp only [Finset.card_empty, Nat.cast_zero]
        positivity
      · intro z hz P hP hagree
        exact (hsmall _ P hagree).elim
  have hnPos : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    subst n
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Nat.cast_zero, mul_zero] at hkRate
    linarith
  have hC0 : 0 ≤ finiteLengthMcaParameterConstant rho :=
    zero_le_one.trans (one_le_finiteLengthMcaParameterConstant rho)
  obtain ⟨hlist, hmca⟩ := automaticFirstOrder_finiteLength_finiteSlack_bounds
    rho eta n k A hrhoOne heta haOne hbetaHalf hk hkRate hA hAn domain hchar
  constructor
  · intro received
    exact (hlist received).imp id fun hbound ↦
      hbound.trans (div_finiteLengthSlack_sq_le_div_eta_sq (by positivity) heta)
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hmca f g
    exact ⟨exceptional, hcard.trans
      (div_finiteLengthSlack_four_le_div_eta_four (by positivity) heta), hgood⟩

open Classical in
/-- Finite-field probability consequence of the inverse-fourth semantic exceptional-set theorem.
Finiteness appears only here: uniform affine-line sampling divides the exceptional count by
`|F|` and caps the result by one. -/
theorem automaticFirstOrder_finiteLength_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] [SampleableType F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (firstOrderRateThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) /
          (Fintype.card F : ℝ))) := by
  let a := firstOrderRateThreshold rho + eta
  let A := Nat.ceil (a * n)
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hline : LineExactAgreementBound domain k A
      (140 * finiteLengthMcaParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      (automaticFirstOrder_finiteLength_rate_bounds rho eta n k A
        hrhoOne heta haOne hbetaHalf hk hkRate hA domain hchar).2 f g
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hPzero, hPone, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hPzero, hPone, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) *
      (1 - (1 - (firstOrderRateThreshold rho + eta))) = a * n := by
    dsimp only [a]
    ring
  simp only [Fintype.card_fin]
  rw [heq]

end

end ReedSolomon.FirstOrder
