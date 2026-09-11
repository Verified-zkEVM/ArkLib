/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CapacityOutputBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.WeightedCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthRateBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Branchwise

/-!
# Improved list bounds for any retained exact output

Only the existing ExactOutput contract is used. These transfers apply to both complete
inefficient decoders without changing their algorithms, correctness proofs, or execution recipe.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityOutputBounds

open Polynomial JetHornerMachine SeparateSampleFieldExecution ReedSolomon
open ReedSolomon.FirstOrder ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

open Classical in
/-- Duplicate-free exact output identifies physical length with the full polynomial list. -/
theorem length_eq_closePolynomialSet_ncard
    {F : Type*} [Field F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (he : ExactOutput domain received k A out) :
    out.length = (closePolynomialSet domain received k A).ncard := by
  classical
  have hset : closePolynomialSet domain received k A =
      ((out.map coefficientPolynomial).toFinset : Set F[X]) := by
    ext P
    simp only [Finset.mem_coe, List.mem_toFinset, he.2.2.1]
    simp [closePolynomialSet, polynomialAgreementSet, Code.agree, evalOnPoints]
    tauto
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup he.1, List.length_map]

open Classical in
/-- The sharp integral pairwise Johnson estimate bounds the already-computed exact output. -/
theorem johnsonPairwise_length_le
    {F : Type*} [Field F] {n D A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (hDA : D + 1 ≤ A) (hpositive : n * D < A * A)
    (he : ExactOutput domain received (D + 1) A out) :
    out.length ≤ johnsonPairwiseListFloor n D A := by
  rw [length_eq_closePolynomialSet_ncard domain received out he]
  exact (closePolynomialSet_finite_and_ncard_le_johnsonPairwise
    domain received hDA hpositive).2

open Classical in
/-- Automatic finite-length list bounds transfer unchanged to exact physical coefficient lists.
The constant-code endpoint does not impose a characteristic restriction. -/
theorem automaticFirstOrder_finiteSlack_length_le
    {F : Type*} [Field F] (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (finiteLengthDerivativeCap rho eta n) < ringChar F)
    (he : ExactOutput domain received k A out) :
    (out.length : ℝ) ≤
      7 * finiteLengthMCAParameterConstant rho ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  rw [length_eq_closePolynomialSet_ncard domain received out he]
  exact ((automaticFirstOrder_finiteLength_finiteSlack_bounds rho eta n k A
    hrho hrhoOne heta haOne hbetaHalf hk hkRate hA hAn domain hchar).1 received).2

open Classical in
/-- The all-rate branchwise finite-slack bound applies to the same exact physical output.
The branch condition and its derivative cap are selected internally. -/
theorem firstOrderBranch_finiteSlack_length_le
    {F : Type*} [Field F] (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderBranchThreshold rho + eta < 1)
    (hk : 0 < k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderBranchThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (firstOrderBranchFiniteLengthDerivativeCap rho eta n) < ringChar F)
    (he : ExactOutput domain received k A out) :
    (out.length : ℝ) ≤
      7 * firstOrderBranchFiniteLengthMCAConstant rho ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  rw [length_eq_closePolynomialSet_ncard domain received out he]
  exact ((firstOrderBranch_finiteLength_finiteSlack_bounds rho eta n k A
    hrho hrhoOne heta haOne hk hkRate hA hAn domain hchar).1 received).2

end

end ReedSolomon.ListDecoding.CapacityOutputBounds
