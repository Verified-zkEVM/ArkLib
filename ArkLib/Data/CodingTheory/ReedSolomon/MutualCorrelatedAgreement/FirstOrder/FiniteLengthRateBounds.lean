/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthMCA
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Public finite-length first-order rate bounds

This module constructs the literal length-dependent interpolation certificates internally and
exposes the inverse-square complete-list and inverse-fourth line-MCA theorems.  The semantic
statements remain field-generic.  Only the last theorem assumes a finite field and divides the
exceptional-set count by its cardinality.

The present selector arithmetic covers the clean branch
`finiteLengthDerivativeRatio rho eta ≤ 1 / 2`.  No claim about the separate low-rate stationary
branch is folded into these declarations.
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
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
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
  have hthreshold := rho_lt_automaticFirstOrderThreshold hrho hrhoOne
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
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * finiteLengthMCAParameterConstant rho ^ 3 * n / finiteLengthSlack eta n ^ 2) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
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
        hrho hrhoOne heta haOne hnSelector hbetaHalf hkTwo hkRate hA
          domain received (fun _ ↦ 0)
      exact closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate
        hrho hrhoOne heta haOne hnSelector hbetaHalf hDrate hA hAn
          domain received _ listCert hchar
    · intro f g
      obtain ⟨lineCert⟩ := exists_finiteLengthFirstOrder_symbolicCertificate
        hrho hrhoOne heta haOne hnSelector hbetaHalf hkTwo hkRate hA domain f g
      let E := AlgebraicClosure F
      exact exists_exceptional_finiteLengthMCA_of_selector_certificate
        hrho hrhoOne heta haOne hnSelector hbetaHalf hk hDrate hA hAn
          domain f g (algebraMap F E) _ lineCert hchar
  · have hkOne : k = 1 := by omega
    subst k
    have hkRateOne : (1 : ℝ) ≤ rho * (n : ℝ) := by simpa using hkRate
    have hsOne : finiteLengthSlack eta n ≤ 1 :=
      (finiteLengthSlack_lt_one_of_one_le_rate_mul_length
        (n := n) hrho hrhoOne haOne hkRateOne).le
    have hC : 1 ≤ finiteLengthMCAParameterConstant rho :=
      one_le_finiteLengthMCAParameterConstant rho
    have hAPos : 0 < A := by
      have hthresholdPos : 0 < automaticFirstOrderThreshold rho + eta :=
        (hrho.trans (rho_lt_automaticFirstOrderThreshold hrho hrhoOne)).trans
          (lt_add_of_pos_right _ heta)
      exact_mod_cast (mul_pos hthresholdPos (by exact_mod_cast hnPos) |>.trans_le hA)
    constructor
    · intro received
      exact closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
        domain received (by omega) (by omega) (by omega) hC heta hsOne
    · intro f g
      obtain ⟨exceptional, hcard, hgood⟩ :=
        exists_exceptional_exactLineMCA_one n A domain f g hAPos
      refine ⟨exceptional, hcard.trans ?_, hgood⟩
      have hsPos := finiteLengthSlack_pos heta hnPos
      have hCpow : 1 ≤ finiteLengthMCAParameterConstant rho ^ 6 := one_le_pow₀ hC
      rw [le_div_iff₀ (pow_pos hsPos 4)]
      have hsFour : finiteLengthSlack eta n ^ 4 ≤ 1 := pow_le_one₀ hsPos.le hsOne
      have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
      calc
        (n : ℝ) ^ 2 * finiteLengthSlack eta n ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
        _ ≤ 140 * finiteLengthMCAParameterConstant rho ^ 6 * (n : ℝ) ^ 2 := by
          nlinarith

open Classical in
/-- Automatic semantic finite-length bounds on the clean first-order selector branch.

For every received word the complete list is finite and has size at most `7 C³ n / eta²`.
Independently, for every received line, a separately constructed line certificate gives one
exceptional set of size at most `140 C⁶ n² / eta⁴`, fixed before the challenge and candidate.
The `k = 1` endpoint is dispatched before the nontrivial selector feasibility argument. -/
theorem automaticFirstOrder_finiteLength_rate_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          7 * finiteLengthMCAParameterConstant rho ^ 3 * n / eta ^ 2) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤
          140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hnPos : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    subst n
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Nat.cast_zero, mul_zero] at hkRate
    linarith
  have hC0 : 0 ≤ finiteLengthMCAParameterConstant rho :=
    zero_le_one.trans (one_le_finiteLengthMCAParameterConstant rho)
  obtain ⟨hlist, hmca⟩ := automaticFirstOrder_finiteLength_finiteSlack_bounds
    rho eta n k A hrho hrhoOne heta haOne hbetaHalf hk hkRate hA hAn domain hchar
  constructor
  · intro received
    exact (hlist received).imp id fun hbound ↦
      hbound.trans (div_finiteLengthSlack_sq_le_div_eta_sq (by positivity) heta hnPos)
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hmca f g
    exact ⟨exceptional, hcard.trans
      (div_finiteLengthSlack_four_le_div_eta_four (by positivity) heta hnPos), hgood⟩

open Classical in
/-- Finite-field probability consequence of the inverse-fourth semantic exceptional-set theorem.
Finiteness appears only here: uniform affine-line sampling divides the exceptional count by
`|F|` and caps the result by one. -/
theorem automaticFirstOrder_finiteLength_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (automaticFirstOrderThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) /
          (Fintype.card F : ℝ))) := by
  let a := automaticFirstOrderThreshold rho + eta
  let A := Nat.ceil (a * n)
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hAn : A ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      a * (n : ℝ) ≤ 1 * n :=
        mul_le_mul_of_nonneg_right haOne.le (Nat.cast_nonneg n)
      _ = n := one_mul _
  have hline : LineExactAgreementBound domain k A
      (140 * finiteLengthMCAParameterConstant rho ^ 6 * n ^ 2 / eta ^ 4) := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      (automaticFirstOrder_finiteLength_rate_bounds rho eta n k A
        hrho hrhoOne heta haOne hbetaHalf hk hkRate hA hAn domain hchar).2 f g
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hPzero, hPone, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hPzero, hPone, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) *
      (1 - (1 - (automaticFirstOrderThreshold rho + eta))) = a * n := by
    dsimp only [a]
    ring
  rw [heq]

end

end ReedSolomon.FirstOrder
