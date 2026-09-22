/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullDimension
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for full-dimension line agreement

On the domain `0, 1` in `ℚ`, the pair of `exists_exactPair_fullDimension` identifies every
full-agreement candidate for `f = (1, 2)` and `g = (0, 1)`; a concrete candidate is
`C 1 + C (1 + z) * X`. The threshold `Fintype.card ι` is needed: with threshold `1`, the candidates
`0` and `X` for `f = g = 0` cannot both be `F₀ + C z * G₀`. The source statements over `Fin n`
are derived from the general ones.
-/

open Polynomial Finset

namespace ReedSolomon.FullDimensionTest

/-- The domain `0, 1` in `ℚ`. -/
def dom : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

@[simp] lemma dom_apply (i : Fin 2) : dom i = ![0, 1] i := rfl

/-- One pair explains `C 1 + C (1 + z) * X` at every challenge, and its agreement set is every
coordinate. -/
example : ∃ F₀ G₀ : ℚ[X], ∀ z : ℚ, C 1 + C (1 + z) * X = F₀ + C z * G₀ ∧
    commonPolynomialAgreementSet dom ![1, 2] ![0, 1] F₀ G₀ = univ := by
  obtain ⟨F₀, G₀, -, -, hpair⟩ := exists_exactPair_fullDimension dom ![1, 2] ![0, 1]
  refine ⟨F₀, G₀, fun z ↦ ?_⟩
  have hagree : polynomialAgreementSet dom (fun i ↦ ![1, 2] i + z * ![0, 1] i)
      (C 1 + C (1 + z) * X) = univ := by
    ext i
    fin_cases i
    · simp
    · simp only [mem_polynomialAgreementSet, mem_univ, iff_true]
      simp
      ring
  obtain ⟨hP, hset⟩ := hpair z (C 1 + C (1 + z) * X) (by
    rw [Fintype.card_fin]
    compute_degree!) (by rw [hagree, card_univ])
  exact ⟨hP, hset.symm.trans hagree⟩

/-- The threshold is needed: with threshold `1` instead of `2`, no pair explains both candidates
`0` and `X` for `f = g = 0`, although each agrees with `f + z • g` at the coordinate `0`. -/
example : ¬∃ F₀ G₀ : ℚ[X], ∀ z (P : ℚ[X]), P.degree < 2 →
    1 ≤ (polynomialAgreementSet dom (fun i ↦ (0 : Fin 2 → ℚ) i + z * (0 : Fin 2 → ℚ) i) P).card →
    P = F₀ + C z * G₀ := by
  rintro ⟨F₀, G₀, h⟩
  have hone : ∀ P : ℚ[X], P.eval 0 = 0 →
      1 ≤ (polynomialAgreementSet dom
        (fun i ↦ (0 : Fin 2 → ℚ) i + 0 * (0 : Fin 2 → ℚ) i) P).card := by
    intro P hP
    exact card_pos.mpr ⟨0, by simpa using hP⟩
  have h0 := h 0 0 (by rw [degree_zero]; exact WithBot.bot_lt_coe 2) (hone 0 (eval_zero))
  have hX := h 0 X (by rw [degree_X]; decide) (hone X eval_X)
  exact X_ne_zero (hX.trans h0.symm)

section Source

variable {F : Type*} [Field F] [DecidableEq F]

/-- Source statement `exists_exactPair_fullDimension`. -/
example (n : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ F₀ G₀ : F[X], F₀.degree < n ∧ G₀.degree < n ∧
      ∀ z (P : F[X]), P.degree < n →
        n ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  simpa using exists_exactPair_fullDimension domain f g

/-- Source statement `exists_exceptional_fullDimension_lineMCA`. -/
example (n : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ exceptional : Finset F, exceptional.card = 0 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < n →
        n ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < n ∧ G₀.degree < n ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  simpa using exists_exceptional_fullDimension_lineMCA domain f g

end Source

end ReedSolomon.FullDimensionTest
