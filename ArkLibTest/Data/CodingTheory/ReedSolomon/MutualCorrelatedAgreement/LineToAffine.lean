/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Acceptance tests for the line-to-affine transfer

Every finite field satisfies `LineExactAgreementBound domain k A (Fintype.card F)` with the whole
field as exceptional set, and then the affine-line error bound is `1`. The source statements, over
`Fin n` with the threshold `⌈n * (1 - radius)⌉₊` and the hypothesis `1 ≤ s`, are derived from the
general ones. The dimension `s = 0` is covered without that hypothesis.
-/

open Polynomial CoreDefinitions

namespace ReedSolomon.LineToAffineTest

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The whole field is always an exceptional set. -/
theorem lineExactAgreementBound_card {ι : Type} [Fintype ι] (domain : ι ↪ F) (k A : ℕ) :
    LineExactAgreementBound domain k A (Fintype.card F) := fun _ _ ↦
  ⟨Finset.univ, by simp, fun z hz ↦ absurd (Finset.mem_univ z) hz⟩

variable [SampleableType F]

/-- With the trivial bound, the affine-line error bound is `1`. -/
example {ι : Type} [Fintype ι] (domain : ι ↪ F) (k : ℕ) (radius : ℝ) :
    mcaError (AffineLineGenerator F) (code domain k) radius ≤ ENNReal.ofReal 1 := by
  have h := mcaError_affineLine_le_of_exactAgreement (A := 0) domain _
    (lineExactAgreementBound_card domain k 0) radius (Nat.zero_le _)
  rwa [div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)] at h

/-- The dimension `s = 0` needs no hypothesis `1 ≤ s`. -/
example {ι : Type} [Fintype ι] (domain : ι ↪ F) (k A : ℕ) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F 0) (code domain k) radius ≤
      ENNReal.ofReal (B / ((Fintype.card F : ℝ) - 1)) :=
  mcaError_affineSpace_le_of_exactAgreement domain B hline radius hthreshold

open Classical in
/-- The source statement of `affineLine_bad_set_card_le_of_exactAgreement`, over `Fin n`. -/
example {n k A : ℕ} (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) (U : Fin 2 → Fin n → F) :
    ((Finset.univ.filter fun z : F ↦
      IsMCA (AffineLineGenerator F) (code domain k) z U radius).card : ℝ) ≤ B :=
  affineLine_bad_set_card_le_of_exactAgreement domain B hline radius
    (by simpa using hthreshold) U

/-- The source statement of `mcaError_affineSpace_le_of_exactAgreement`, over `Fin n` and with
the unused hypothesis `1 ≤ s`. -/
example {n k A s : ℕ} (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (_hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain k) radius ≤
      ENNReal.ofReal (B / ((Fintype.card F : ℝ) - 1)) :=
  mcaError_affineSpace_le_of_exactAgreement domain B hline radius (by simpa using hthreshold)

/-- The source statement of `exists_affine_exceptionalSet_full_agreement_of_exactLine`, over
`Fin n` and with the unused hypothesis `1 ≤ s`. -/
example {n k A s : ℕ} (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (_hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊)
    (hkThreshold : (k : ℝ) ≤ n * (1 - radius)) (U : Fin (s + 1) → Fin n → F) :
    ∃ exceptional : Finset (Fin s → F),
      (exceptional.card : ℝ) ≤ B * (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
      ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
        ((Finset.univ.filter fun i ↦
          P.eval (domain i) = ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
            Fintype.card (Fin n) * (1 - radius) →
        ∃ P₀ : Fin (s + 1) → F[X], (∀ j, (P₀ j).degree < k) ∧
          P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
          ∀ i, (P.eval (domain i) = ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
            ∀ j, (P₀ j).eval (domain i) = U j i :=
  exists_affine_exceptionalSet_full_agreement_of_exactLine domain B hline radius
    (by simpa using hthreshold) (by simpa using hkThreshold) U

end ReedSolomon.LineToAffineTest
