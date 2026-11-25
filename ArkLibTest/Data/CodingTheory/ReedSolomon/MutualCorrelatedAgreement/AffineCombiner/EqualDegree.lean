/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegreeSampling

/-! # Acceptance cases for the equal-degree combiner -/

open ReedSolomon
open scoped Finset

-- The agreement lemma accepts the caller's decidable equality instance.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] (domain : ι ↪ F)
    (f g : ι → F) {d : ℕ} {F₀ G₀ F₁ G₁ : Polynomial F}
    (hF₀ : F₀.degree ≤ d) (hG₀ : G₀.degree ≤ d)
    (hF₁ : F₁.degree ≤ d) (hG₁ : G₁.degree ≤ d) (hne : (F₀, G₀) ≠ (F₁, G₁)) :
    #(commonPolynomialAgreementSet domain f g F₀ G₀ ∩
      commonPolynomialAgreementSet domain f g F₁ G₁) ≤ d :=
  card_inter_commonPolynomialAgreementSet_le domain f g hF₀ hG₀ hF₁ hG₁ hne

-- At `n = 5`, `d = 1`, `L = 3`, a list of two passes the integer count `2 · (9 - 5) ≤ 5 · 2`.
-- So its size is at most the Johnson floor `⌊10 / 4⌋ = 2`.
example : 2 ≤ ⌊(5 : ℝ) * ((3 : ℝ) - 1) / ((3 : ℝ) ^ 2 - 5 * 1)⌋₊ := by
  exact_mod_cast le_floor_johnson_of_mul_le (k := 2) (n := 5) (d := 1) (L := 3)
    (by norm_num) (by norm_num)

/-- info: 'ReedSolomon.card_badEqualDegreeChallenges_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_badEqualDegreeChallenges_mul_le

/-- info: 'ReedSolomon.IsEqualDegreeExceptional.isAffineExceptional_or_exists_degree_eq' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.IsEqualDegreeExceptional.isAffineExceptional_or_exists_degree_eq

#print axioms ReedSolomon.equalDegreeMcaError_eq_iSup_prob
