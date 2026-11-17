/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegreeSampling
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the equal-degree combiner -/

open ReedSolomon
open scoped Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- At `d = 1`, `A = 4` on `F₅`, the Johnson quotient is `5 / 2`.
Its floor gives an additive error term of `2 / 5`. -/
example :
    equalDegreeMcaError fullDomain 1 4 1 ≤ affineMcaError fullDomain 1 4 1 + 2 / 5 := by
  have h := equalDegreeMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

open scoped ProbabilityTheory

-- The bound controls native probabilities for independently uniform triples.
example (f g : ZMod 5 → ZMod 5) :
    Pr{let c ← $ᵗ (ZMod 5 × ZMod 5 × ZMod 5)}[∃ P,
      IsEqualDegreeExceptional fullDomain f g 1 4 1 c.1 c.2.1 c.2.2 P] ≤
        affineMcaError fullDomain 1 4 1 + 2 / 5 := by
  refine (prob_isEqualDegreeExceptional_le fullDomain f g 1 4 1).trans ?_
  have h := equalDegreeMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

-- The agreement lemma accepts the caller's decidable equality instance.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] (domain : ι ↪ F)
    (f g : ι → F) {d : ℕ} {F₀ G₀ F₁ G₁ : Polynomial F}
    (hF₀ : F₀.degree ≤ d) (hG₀ : G₀.degree ≤ d)
    (hF₁ : F₁.degree ≤ d) (hG₁ : G₁.degree ≤ d) (hne : (F₀, G₀) ≠ (F₁, G₁)) :
    #(commonPolynomialAgreementSet domain f g F₀ G₀ ∩
      commonPolynomialAgreementSet domain f g F₁ G₁) ≤ d :=
  card_inter_commonPolynomialAgreementSet_le domain f g hF₀ hG₀ hF₁ hG₁ hne

#print axioms ReedSolomon.equalDegreeMcaError_le_affineMcaError_add
#print axioms ReedSolomon.equalDegreeMcaError_eq_iSup_prob
