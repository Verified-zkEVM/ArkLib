/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability

/-!
# Uniform probabilities for equal-degree combiners

The counting definition of `ReedSolomon.equalDegreeMcaError` is the supremum of native uniform
exceptional-event probabilities over received word pairs.
The three challenge coefficients are sampled uniformly from `F × F × F`.
The counting definition and reduction theorem have no sampler assumptions.
These characterizations use `SampleableType F` to connect them to probability bounds.

The error follows the equal-degree combiner in Section 5 of [CWYZ26].
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the first assertion of
Theorem 5.1 and the separate linear-claims assertion.

## Main statements

* `ReedSolomon.prob_isEqualDegreeExceptional_eq`: the uniform probability as a counting fraction.
* `ReedSolomon.equalDegreeMcaError_eq_iSup_prob`: the error as a supremum of native probabilities.
* `ReedSolomon.prob_isEqualDegreeExceptional_le`: the error bounds each word pair's probability.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open scoped ProbabilityTheory Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [Fintype F] [SampleableType F]

open Classical in
/-- The uniform exceptional-event probability equals the fraction of exceptional triples. -/
theorem prob_isEqualDegreeExceptional_eq (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P,
      IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P] =
      ENNReal.ofReal
        ((#{c : F × F × F | ∃ P,
          IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P} : ℝ) /
            (Fintype.card F : ℝ) ^ 3) := by
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp [pow_succ, mul_assoc]

/-- The equal-degree error is the worst-case native probability of exceptionality. -/
theorem equalDegreeMcaError_eq_iSup_prob (domain : ι ↪ F) (d A s : ℕ) :
    equalDegreeMcaError domain d A s =
      ⨆ w : (ι → F) × (ι → F),
        Pr{let c ← $ᵗ (F × F × F)}[∃ P,
          IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P] := by
  simp only [equalDegreeMcaError, prob_isEqualDegreeExceptional_eq]

/-- The equal-degree error bounds the exceptional-event probability for each word pair. -/
theorem prob_isEqualDegreeExceptional_le (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P,
      IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P] ≤
        equalDegreeMcaError domain d A s := by
  rw [prob_isEqualDegreeExceptional_eq]
  exact le_equalDegreeMcaError domain d A s f g

end ReedSolomon
