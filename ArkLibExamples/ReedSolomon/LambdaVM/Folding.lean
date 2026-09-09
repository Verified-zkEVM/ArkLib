/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.LambdaVM.Certificates
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.BinaryFoldAgreement
/-!
# Backward reconstruction through CPU folds

Each certificate describes the child domain. Exact agreement there recovers the even
and odd parent parts, giving twice as many parent agreements. The checked ceiling
schedule makes this sufficient at every preceding stage. The last child has length
256; its parent has length 512. No child commitment is required in the transfer lemma.
-/
open Polynomial ReedSolomon
namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU
open ConcreteFields
noncomputable section
local instance foldingDecidableEq : DecidableEq GoldilocksCubic := Classical.decEq _
local instance : NeZero (2 : GoldilocksCubic) := ⟨Ring.two_ne_zero (by
  rw [goldilocksCubic_ringChar]
  decide)⟩

/-- Each child profile has half the length/dimension and enough doubled agreement for its parent. -/
theorem fold_parameters (i : Fin 8) :
    2 * (profiles (foldIndex i)).n = (profiles ⟨i.val, by omega⟩).n ∧
    2 * (profiles (foldIndex i)).k = (profiles ⟨i.val, by omega⟩).k ∧
    (profiles ⟨i.val, by omega⟩).agreement ≤ 2 * (profiles (foldIndex i)).agreement := by
  fin_cases i <;> decide


/-- Each of the eight finite curve certificates reconstructs a parent outside its actual
exceptional set. The parent points are the two square roots of each child point. -/
theorem exists_fold_reconstruction (i : Fin 8)
    (domain : SquarePairedDomain GoldilocksCubic (profiles (foldIndex i)).n)
    (word : Fin (profiles (foldIndex i)).n × Fin 2 → GoldilocksCubic) :
    ∃ bad : Finset GoldilocksCubic,
      bad.card ≤ exceptionalCounts (foldIndex i) ∧
      ∀ γ ∉ bad, ∀ Q : GoldilocksCubic[X],
        Q.degree < (profiles (foldIndex i)).k →
        (profiles (foldIndex i)).agreement ≤
          (polynomialAgreementSet domain.child (binaryFoldedWord domain word γ) Q).card →
        ∃ P : GoldilocksCubic[X],
          P.natDegree < (profiles ⟨i.val, by omega⟩).k ∧
          Q = FoldingPolynomial.polyFold P 2 γ ∧
          (profiles ⟨i.val, by omega⟩).agreement ≤
            (pairedPolynomialAgreementSet domain word P).card := by
  have hDegree : (profiles (foldIndex i)).batchingDegree = 1 := by
    fin_cases i <;> decide
  have hExists := exists_exceptional (foldIndex i) domain.child
  rw [hDegree] at hExists
  obtain ⟨bad, hCard, hGood⟩ := hExists (binarySplitWord domain word)
  refine ⟨bad, hCard, ?_⟩
  intro γ hγ Q hQ hClose
  have hk : 0 < (profiles (foldIndex i)).k := by fin_cases i <;> decide
  have hExact := hGood γ hγ Q hQ hClose
  obtain ⟨P, hP, hFold, hAgreement⟩ := exists_parentPolynomial_of_exactAgreement
    domain word hk (fold_parameters i).2.2 γ Q hClose hExact
  refine ⟨P, ?_, hFold, hAgreement⟩
  simpa only [(fold_parameters i).2.1] using hP

end
end ArkLibExamples.ReedSolomon.LambdaVM.CPU
