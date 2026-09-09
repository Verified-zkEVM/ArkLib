/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FirstOrder.FirstOrderHybridList
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
import ArkLib.ToMathlib.Set.Finite
/-!
# Complete automatic first-order hybrid list bound

This file passes from the uniform finite-family Lambda estimate to the complete set of close
Reed--Solomon message polynomials. Finiteness is derived from that same estimate, and the final
theorems retain the optimized raw, optimized natural ceiling, and printed closed raw bounds.
-/

open Polynomial

namespace ReedSolomon

open HiddenDerivative

noncomputable section

set_option autoImplicit false

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

open Classical in
/-- The complete close-polynomial set is finite and obeys all three automatic Lambda bounds.
Finiteness follows from the natural bound on every finite subset, rather than from a finite-field
assumption. -/
theorem automaticFirstOrder_closePolynomialSet_finite_and_card_le
    {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max D (automaticDerivativeCap rho a) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        hybridListOptimizedRaw (hybridTheta n D A) D
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      (closePolynomialSet domain received k A).ncard ≤
        hybridListOptimizedCeil (hybridTheta n D A) D
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        hybridLambdaClosed (hybridTheta n D A) D
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) := by
  let T := closePolynomialSet domain received k A
  let B := hybridListOptimizedCeil (hybridTheta n D A) D
    (automaticJetDegree rho a) (automaticDerivativeCap rho a)
  have hfinite : T.Finite := by
    refine Set.finite_of_forall_finset_card_le (R := ℕ) (ℓ := B) ?_
    intro S hST
    have hbound := finite_automaticFirstOrder_hybrid_agreement_solutions_card_le
      hrho hrhoOne ha haOne hn hD hk hkRate hA hAn domain received hchar S
      (fun P hP ↦ (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
        (hST hP))
    exact hbound.2.1
  have hwhole := finite_automaticFirstOrder_hybrid_agreement_solutions_card_le
    hrho hrhoOne ha haOne hn hD hk hkRate hA hAn domain received hchar hfinite.toFinset
    (fun P hP ↦ (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
      (hfinite.mem_toFinset.mp hP))
  have hncard : T.ncard = hfinite.toFinset.card := Set.ncard_eq_toFinset_card T hfinite
  refine ⟨hfinite, ?_, ?_, ?_⟩
  · simpa only [T, hncard] using hwhole.1
  · simpa only [T, B, hncard] using hwhole.2.1
  · simpa only [T, hncard] using hwhole.2.2

open Classical in
/-- Physical-parameter form with the exact integer threshold `A = ceil (a*n)`. -/
theorem automaticFirstOrder_closePolynomialSet_at_ceil_finite_and_card_le
    {rho a : ℝ} {n k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap rho a) < ringChar F) :
    (closePolynomialSet domain received k (Nat.ceil (a * n))).Finite ∧
      ((closePolynomialSet domain received k (Nat.ceil (a * n))).ncard : ℝ) ≤
        hybridListOptimizedRaw (hybridTheta n (k - 1) (Nat.ceil (a * n))) (k - 1)
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      (closePolynomialSet domain received k (Nat.ceil (a * n))).ncard ≤
        hybridListOptimizedCeil (hybridTheta n (k - 1) (Nat.ceil (a * n))) (k - 1)
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      ((closePolynomialSet domain received k (Nat.ceil (a * n))).ncard : ℝ) ≤
        hybridLambdaClosed (hybridTheta n (k - 1) (Nat.ceil (a * n))) (k - 1)
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) := by
  have hA : a * (n : ℝ) ≤ (Nat.ceil (a * n) : ℕ) := Nat.le_ceil _
  have hAn : Nat.ceil (a * n) ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      a * (n : ℝ) ≤ 1 * n := mul_le_mul_of_nonneg_right haOne.le (Nat.cast_nonneg n)
      _ = n := one_mul _
  exact automaticFirstOrder_closePolynomialSet_finite_and_card_le
    hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn domain received hchar

end

end ReedSolomon
