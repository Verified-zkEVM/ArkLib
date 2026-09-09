/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FirstOrder.AutomaticHybridProbability
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.AutomaticHybrid

/-!
# Automatic first-order list decoding and full agreement-set MCA

The public theorem uses one literal automatic recipe for both conclusions. It displays the
optimized real, optimized natural ceiling, and closed constants separately, with numerical
parameters fixed before choosing any field.
-/

namespace ReedSolomon
open Polynomial HiddenDerivative

open Classical in
/-- The optimized finite bounds and the closed Lambda and E from the automatic first-order
recipe, over arbitrary fields with the hybrid characteristic guard. -/
theorem automaticFirstOrder_list_and_lineMCA
    (rho a : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : a * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap rho a) < ringChar F) :
    let D := k - 1
    let theta := hybridTheta n D A
    let h := automaticChallengeHeight rho a
    let mu := automaticJetDegree rho a
    let M := automaticDerivativeCap rho a
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          hybridListOptimizedRaw theta D mu M ∧
        (closePolynomialSet domain received k A).ncard ≤
          hybridListOptimizedCeil theta D mu M ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          hybridLambdaClosed theta D mu M) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ hybridEOptimizedRaw theta n D A h mu M ∧
        exceptional.card ≤ hybridEOptimizedCeil theta n D A h mu M ∧
        (exceptional.card : ℝ) ≤ hybridEClosed theta n D h mu M ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  constructor
  · intro received
    exact automaticFirstOrder_closePolynomialSet_finite_and_card_le
      hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn domain received hchar
  · intro f g
    obtain ⟨Q, hQ, hweight, hdegree, hheight, hsound, exceptional,
        hraw, hceil, hclosed, hgood⟩ :=
      exists_automaticFirstOrder_hybridEquation_base
        hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn hchar domain f g
    refine ⟨exceptional, hraw, hceil, hclosed, ?_⟩
    intro z hz P hP hagree
    have hdegreeCast : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
      have heq : ((k : WithBot ℕ)) = ((k - 1 : ℕ) : WithBot ℕ) + 1 :=
        congrArg (fun x : ℕ ↦ (x : WithBot ℕ))
          (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
      rwa [← heq]
    simpa only [show k - 1 + 1 = k by omega, Matrix.cons_val_zero,
      Matrix.cons_val_one] using
      (exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
        (hgood z hz P hdegreeCast (by
          have hword : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
            funext i
            simp [powerBatchedWord, Fin.sum_univ_two]
          rwa [hword])))
end ReedSolomon
