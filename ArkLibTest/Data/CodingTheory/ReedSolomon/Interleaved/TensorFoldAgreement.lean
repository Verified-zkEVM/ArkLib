/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement

/-!
# Reed–Solomon shared-level tensor-fold clients

These clients state a scalar line hypothesis `LineExactAgreementBound` with a real-valued
exceptional count, derive the power-agreement line guarantee from it, and derive the level
witness and the height-three count from it, with the extra guard `0 < width` unused. They also
check an empty row type and the height-three count at count `0`.
-/

open Polynomial Code TensorMCA ReedSolomon

namespace ReedSolomonTensorFoldAgreementTest

/-- A scalar line hypothesis: outside at most `B` challenges, every degree-`< k`
polynomial with at least `A` agreements with `f + z • g` splits as `P₀ + z • P₁` with the same
agreement set as the common agreement set of `P₀, P₁` with `f, g`. -/
def LineExactAgreementBound {F : Type} [Field F] [DecidableEq F] {n : ℕ} (domain : Fin n ↪ F)
    (k A : ℕ) (B : ℝ) : Prop :=
  ∀ f g : Fin n → F, ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ B ∧
    ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
      ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧ P = P₀ + Polynomial.C z * P₁ ∧
        polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
          commonPolynomialAgreementSet domain f g P₀ P₁

/-- `LineExactAgreementBound` with a natural-number count is the power-agreement line guarantee
at `ℓ = 1`. -/
theorem uniformExactPowerAgreement_of_lineExactAgreementBound {F : Type} [Field F]
    [DecidableEq F] {n k A e : ℕ} {domain : Fin n ↪ F}
    (h : LineExactAgreementBound domain k A e) (w : Fin 2 → Fin n → F) :
    UniformExactPowerAgreement domain w k A e := by
  obtain ⟨bad, hcard, hbad⟩ := h (w 0) (w 1)
  have hword (z : F) : powerBatchedWord w z = fun i ↦ w 0 i + z * w 1 i := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  refine ⟨bad, by exact_mod_cast hcard, fun z hz Q hQ hA ↦ ?_⟩
  rw [hword] at hA
  obtain ⟨P₀, P₁, h₀, h₁, hQP, hset⟩ := hbad z hz Q hQ hA
  refine (hasExactPowerAgreement_id_iff domain w k z Q).mpr
    ⟨![P₀, P₁], fun t ↦ by fin_cases t <;> assumption, ?_, ?_⟩
  · simp [hQP, powerBatchedPolynomial, Fin.sum_univ_two, Polynomial.smul_eq_C_mul]
  · rw [hword, hset]
    ext i
    simp [commonPolynomialAgreementSet, Fin.forall_fin_two]

variable {F : Type} [Field F] [DecidableEq F] {n k agreement exceptionalCount width : ℕ}

/-- The level witness for `code domain k ^⋈ Fin width` from `LineExactAgreementBound`, with the
extra guard `0 < width`, derived from the general theorem. The guard is not used. -/
theorem fullSetLevelWitness_interleaved_of_lineExactAgreementBound (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (_hwidth : 0 < width) (hkAgreement : k ≤ agreement) :
    FullSetLevelWitness ((code domain k)^⋈(Fin width)) agreement exceptionalCount :=
  fullSetLevelWitness_interleaved_of_exactAgreement domain
    (uniformExactPowerAgreement_of_lineExactAgreementBound hline) hkAgreement (Fin width)

-- The height-three count from `LineExactAgreementBound`, with the extra guard `0 < width`.
example [Fintype F] (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (u : (Fin 3 → Bool) → Fin n → Fin width → F) :
    (tensorFoldBad
      (fullSetLevelWitness_interleaved_of_lineExactAgreementBound domain hline hwidth hkAgreement)
        u).card ≤ 3 * exceptionalCount * Fintype.card F ^ 2 :=
  tensorFoldBad_card_le _ u

-- The general statement also covers zero rows.
example (domain : Fin n ↪ F) (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hkAgreement : k ≤ agreement) :
    FullSetLevelWitness ((code domain k)^⋈(Fin 0)) agreement exceptionalCount :=
  fullSetLevelWitness_interleaved_of_exactAgreement domain
    (uniformExactPowerAgreement_of_lineExactAgreementBound hline) hkAgreement (Fin 0)

-- With no exceptional challenge on lines, no height-three challenge triple is bad.
example [Fintype F] {ι : Type} [Fintype ι] [DecidableEq ι] (domain : ι ↪ F) {κ : Type} [Fintype κ]
    (hline : ∀ w : Fin 2 → ι → F, UniformExactPowerAgreement domain w k agreement 0)
    (hk : k ≤ agreement) (u : (Fin 3 → Bool) → ι → κ → F) :
    tensorFoldBad (fullSetLevelWitness_interleaved_of_exactAgreement domain hline hk κ) u = ∅ :=
  Finset.card_eq_zero.mp (Nat.le_zero.mp
    (by simpa using interleavedRS_tensorFoldBad_card_le_heightThree domain hline hk u))

-- Outside the bad set, a close root codeword decomposes into eight interleaved codewords.
example [Fintype F] {ι : Type} [Fintype ι] [DecidableEq ι] (domain : ι ↪ F) {κ : Type}
    [Fintype κ] {e : ℕ}
    (hline : ∀ w : Fin 2 → ι → F, UniformExactPowerAgreement domain w k agreement e)
    (hk : k ≤ agreement) (u : (Fin 3 → Bool) → ι → κ → F) (r : Fin 3 → F)
    (hr : r ∉
      tensorFoldBad (fullSetLevelWitness_interleaved_of_exactAgreement domain hline hk κ) u) :
    HasFullTensorDecomposition ((code domain k)^⋈κ) agreement r u :=
  hasFullTensorDecomposition_of_not_mem_bad _ r u hr

end ReedSolomonTensorFoldAgreementTest
