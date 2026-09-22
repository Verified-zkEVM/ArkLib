/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.HalfGap.Line
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for mutual correlated agreement at a half gap

On the domain `0, 1` in `ℚ` with `f = (0, 1)`, `g = (1, 0)`, `k = 1` and `A = 2`, the half-gap
theorem gives at most `3` exceptional challenges, and the challenge `1` must be one of them: there
the constant `1` agrees with `f + g` everywhere, but no constant agrees with `f` everywhere. The
hypothesis `k ≤ A` of the certificate theorem is needed: a certificate with `A = 0 < k = 1`
exists for `f = g = 0`, and its conclusion fails. The bivariate degree bound is checked on a small
polynomial. The forms over `Fin n` with the hypotheses `0 < k` and `A ≤ n` are derived from the
general ones.
-/

open Polynomial Finset

namespace ReedSolomon.HalfGapLineTest

/-- The domain `0, 1` in `ℚ`. -/
def dom : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

@[simp] lemma dom_apply (i : Fin 2) : dom i = ![0, 1] i := rfl

/-- The half-gap theorem at `n = 2`, `k = 1`, `A = 2`: one pair and at most `3` exceptional
challenges, and the challenge `1` is necessarily exceptional. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 3 ∧ (1 : ℚ) ∈ exceptional ∧
      ∀ z ∉ exceptional, ∀ P : ℚ[X], P.degree < 1 →
        2 ≤ (polynomialAgreementSet dom (fun i ↦ ![0, 1] i + z * ![1, 0] i) P).card →
        P = F₀ + C z * G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, hpair⟩ :=
    exists_exactPair_of_messageDim_add_half_blockLength_le (k := 1) (A := 2) dom ![0, 1] ![1, 0]
      (by simp)
  refine ⟨F₀, G₀, hF₀, hG₀, exceptional, by simpa using hcard, ?_,
    fun z hz P hP hA ↦ (hpair z hz P hP hA).1⟩
  by_contra h1
  have hagree : polynomialAgreementSet dom (fun i ↦ ![0, 1] i + 1 * ![1, 0] i) (C 1) = univ := by
    ext i
    fin_cases i <;> simp
  obtain ⟨-, hset⟩ := hpair 1 h1 (C 1) (by simp) (by rw [hagree]; simp)
  rw [hagree] at hset
  have h0 := ((mem_commonPolynomialAgreementSet ..).mp (hset ▸ mem_univ (0 : Fin 2))).1
  have h1 := ((mem_commonPolynomialAgreementSet ..).mp (hset ▸ mem_univ (1 : Fin 2))).1
  rw [eq_C_of_degree_le_zero (p := F₀) (Nat.WithBot.lt_one_iff_le_zero.mp
    (by exact_mod_cast hF₀))] at h0 h1
  simp only [dom_apply, eval_C] at h0 h1
  simp [h0] at h1

/-- A certificate with `A = 0 < k = 1` for `f = g = 0` on one coordinate: numerator `0` and
denominator `1`. -/
noncomputable def zeroCertificate (domain : Fin 1 ↪ ℚ) : HalfGapCertificate domain 0 0 1 0 0 where
  numerator := 0
  denominator := 1
  numeratorDegree := by simp
  denominatorDegree := by simp
  coefficientDegree := ⟨by simp, fun j ↦ by rw [coeff_one]; split_ifs <;> simp⟩
  denominator_ne_zero := one_ne_zero
  identity := by simp

/-- The hypothesis `k ≤ A` is needed in `exists_exactPair_of_halfGapCertificate`. A certificate
with `k = 1` and `A = 0` exists, and the conclusion fails for it: at a challenge outside any finite
set, the constants `0` and `1` both meet the threshold `0`, so they cannot both equal
`F₀ + C z * G₀`. -/
example (domain : Fin 1 ↪ ℚ) : Nonempty (HalfGapCertificate domain 0 0 1 0 0) ∧
    ¬∃ F₀ G₀ : ℚ[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 * 0 + (Fintype.card (Fin 1) - 1) ∧
      ∀ z ∉ exceptional, ∀ P : ℚ[X], P.degree < 1 →
        0 ≤ (polynomialAgreementSet domain (fun i ↦ (0 : Fin 1 → ℚ) i + z * (0 : Fin 1 → ℚ) i)
          P).card →
        P = F₀ + C z * G₀ := by
  refine ⟨⟨zeroCertificate domain⟩, ?_⟩
  rintro ⟨F₀, G₀, -, -, exceptional, -, hpair⟩
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset exceptional
  have h0 := hpair z hz 0 (by simp) (Nat.zero_le _)
  have h1 := hpair z hz 1 (by simp) (Nat.zero_le _)
  exact one_ne_zero (h1.trans h0.symm)

/-- The bivariate degree bound: the coefficients of `C X * Y + C 1` have degree at most `1`, and
so does its specialization at `C 5`. -/
example : ((C X * X + C 1 : ℚ[X][X]).eval (C 5)).natDegree ≤ 1 :=
  natDegree_eval_C_le (fun j ↦ by
    rw [coeff_add, coeff_C_mul_X, coeff_C]
    split_ifs <;> simp) 5

section FinCoordinates

variable {F : Type*} [Field F] [DecidableEq F]

/-- `exists_exceptionalSet_exactAgreement_of_halfGapCertificate` over `Fin n`, with the
hypotheses `0 < k` and `A ≤ n`. -/
example {n k A height : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (_hk : 0 < k) (hkA : k ≤ A) (_hAn : A ≤ n) (hheight : k * height ≤ n)
    (certificate : HalfGapCertificate domain f g k A height) :
    ∃ exceptional : Finset F, exceptional.card ≤ 2 * n ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  simpa using exists_exceptionalSet_exactAgreement_of_halfGapCertificate domain f g hkA
    (by simpa using hheight) certificate

/-- `exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le` over `Fin n`,
with the hypotheses `0 < k` and `A ≤ n`. -/
example {n k A : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (_hk : 0 < k) (_hAn : A ≤ n) (hhalf : k + n / 2 ≤ A) :
    ∃ exceptional : Finset F, exceptional.card ≤ 2 * n ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  simpa using exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le
    domain f g (by simpa using hhalf)

end FinCoordinates

end ReedSolomon.HalfGapLineTest
