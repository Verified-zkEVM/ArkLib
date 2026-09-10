/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
/-!
# Finite-field probability for the automatic first-order hybrid transfer

The physical agreement threshold is rounded once as `ceil (a*n)`.  The automatic equation and
its algebraic closure remain internal.  Uniform challenge sampling turns each exceptional-set
bound into the canonical probability bound `min 1 (E / |F|)`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

set_option autoImplicit false

open Classical in
/-- The automatic first-order construction controls finite-field affine-line MCA error by each
of its optimized real, optimized ceiling, and closed-form exceptional-set bounds.  All numerical
parameters and physical hypotheses precede the field and code data. -/
theorem automaticFirstOrder_hybrid_mcaError_le
    {rho a : ℝ} {n k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    {F : Type} [Field F] [Fintype F]
    (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap rho a) < ringChar F) :
    let A := Nat.ceil (a * n)
    let theta := hybridTheta n (k - 1) A
    let h := automaticChallengeHeight rho a
    let mu := automaticJetDegree rho a
    let M := automaticDerivativeCap rho a
    mcaError (AffineLineGenerator F) (code domain k) (1 - a) ≤
        min 1 (ENNReal.ofReal
          (hybridEOptimizedRaw theta n (k - 1) A h mu M /
            (Fintype.card F : ℝ))) ∧
      mcaError (AffineLineGenerator F) (code domain k) (1 - a) ≤
        min 1 (ENNReal.ofReal
          ((hybridEOptimizedCeil theta n (k - 1) A h mu M : ℕ) /
            (Fintype.card F : ℝ))) ∧
      mcaError (AffineLineGenerator F) (code domain k) (1 - a) ≤
        min 1 (ENNReal.ofReal
          (hybridEClosed theta n (k - 1) h mu M /
            (Fintype.card F : ℝ))) := by
  classical
  dsimp only
  let A := Nat.ceil (a * n)
  let theta := hybridTheta n (k - 1) A
  let h := automaticChallengeHeight rho a
  let mu := automaticJetDegree rho a
  let M := automaticDerivativeCap rho a
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hAn : A ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      a * (n : ℝ) ≤ 1 * n :=
        mul_le_mul_of_nonneg_right haOne.le (Nat.cast_nonneg n)
      _ = n := one_mul _
  have hdegreeCast (P : F[X]) (hP : P.degree < k) :
      P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
    have heq : ((k : WithBot ℕ)) = ((k - 1 : ℕ) : WithBot ℕ) + 1 :=
      congrArg (fun x : ℕ ↦ (x : WithBot ℕ))
        (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
    rwa [← heq]
  have toLineConclusion {f g : Fin n → F} {z : F} {P : F[X]}
      (hexact : HasExactCorrelatedPair domain f g (RingHom.id F) k z P) :
      ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
        P = P₀ + Polynomial.C z * P₁ ∧
        polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
          commonPolynomialAgreementSet domain f g P₀ P₁ := by
    obtain ⟨pair, hP₀, hP₁, heq, hset⟩ := hexact
    refine ⟨pair.1, pair.2, hP₀, hP₁, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  have hlineRaw : LineExactAgreementBound domain k A
      (hybridEOptimizedRaw theta n (k - 1) A h mu M) := by
    intro f g
    obtain ⟨Q, hQ, hweight, hdegree, hheight, hsound, exceptional,
        hraw, hceil, hclosed, hgood⟩ :=
      exists_automaticFirstOrder_hybridEquation_base
        hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn hchar domain f g
    refine ⟨exceptional, hraw, ?_⟩
    intro z hz P hP hagree
    apply toLineConclusion
    simpa only [show k - 1 + 1 = k by omega, Matrix.cons_val_zero,
      Matrix.cons_val_one] using
      (exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
      (hgood z hz P (hdegreeCast P hP) (by
        have hword : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
          funext i
          simp [powerBatchedWord, Fin.sum_univ_two]
        rwa [hword])))
  have hlineCeil : LineExactAgreementBound domain k A
      (hybridEOptimizedCeil theta n (k - 1) A h mu M : ℕ) := by
    intro f g
    obtain ⟨Q, hQ, hweight, hdegree, hheight, hsound, exceptional,
        hraw, hceil, hclosed, hgood⟩ :=
      exists_automaticFirstOrder_hybridEquation_base
        hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn hchar domain f g
    refine ⟨exceptional, ?_, ?_⟩
    · exact_mod_cast hceil
    · intro z hz P hP hagree
      apply toLineConclusion
      simpa only [show k - 1 + 1 = k by omega, Matrix.cons_val_zero,
        Matrix.cons_val_one] using
        (exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
        (hgood z hz P (hdegreeCast P hP) (by
          have hword : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
            funext i
            simp [powerBatchedWord, Fin.sum_univ_two]
          rwa [hword])))
  have hlineClosed : LineExactAgreementBound domain k A
      (hybridEClosed theta n (k - 1) h mu M) := by
    intro f g
    obtain ⟨Q, hQ, hweight, hdegree, hheight, hsound, exceptional,
        hraw, hceil, hclosed, hgood⟩ :=
      exists_automaticFirstOrder_hybridEquation_base
        hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn hchar domain f g
    refine ⟨exceptional, hclosed, ?_⟩
    intro z hz P hP hagree
    apply toLineConclusion
    simpa only [show k - 1 + 1 = k by omega, Matrix.cons_val_zero,
      Matrix.cons_val_one] using
      (exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
      (hgood z hz P (hdegreeCast P hP) (by
        have hword : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
          funext i
          simp [powerBatchedWord, Fin.sum_univ_two]
        rwa [hword])))
  have hthreshold : A ≤ ⌈(n : ℝ) * (1 - (1 - a))⌉₊ := by
    have heq : (n : ℝ) * (1 - (1 - a)) = a * n := by ring
    rw [heq]
  exact ⟨
    mcaError_affineLine_le_min_one_of_exactAgreement domain _ hlineRaw _ hthreshold,
    mcaError_affineLine_le_min_one_of_exactAgreement domain _ hlineCeil _ hthreshold,
    mcaError_affineLine_le_min_one_of_exactAgreement domain _ hlineClosed _ hthreshold⟩

end ReedSolomon
