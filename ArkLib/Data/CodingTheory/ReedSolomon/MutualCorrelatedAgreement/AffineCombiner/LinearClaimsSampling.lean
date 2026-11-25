/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LinearClaims
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability

/-!
# Uniform probabilities for linear-claim combiners

The counting definition of `ReedSolomon.linearClaimMcaError` is the supremum of native uniform
exceptional-event probabilities over linear-claim instances.
The three challenge coefficients are sampled uniformly from `F × F × F`.
The prover's message is the instance's function of the first challenge.
The counting definition and reduction theorem have no sampler assumptions.
These characterizations use `SampleableType F` to connect them to probability bounds.

The error follows the linear-claims combiner in Section 5 of [CWYZ26].
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedSolomon.prob_isLinearClaimExceptional_eq`: the uniform probability as a counting fraction.
* `ReedSolomon.linearClaimMcaError_eq_iSup_prob`: the error as a supremum of native probabilities.
* `ReedSolomon.prob_isLinearClaimExceptional_le`: the error bounds each instance's probability.

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
theorem prob_isLinearClaimExceptional_eq (domain : ι ↪ F) (d A s : ℕ)
    (w : LinearClaimInstance ι F d) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
      (w.message c.1) c.1 c.2.1 c.2.2 P] =
      ENNReal.ofReal
        ((#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
          (w.message c.1) c.1 c.2.1 c.2.2 P} : ℝ) / (Fintype.card F : ℝ) ^ 3) := by
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp [pow_succ, mul_assoc]

/-- The linear-claim error is the worst-case native probability of exceptionality. -/
theorem linearClaimMcaError_eq_iSup_prob (domain : ι ↪ F) (d A s : ℕ) :
    linearClaimMcaError domain d A s =
      ⨆ w : LinearClaimInstance ι F d,
        Pr{let c ← $ᵗ (F × F × F)}[∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v
          w.γ₀ w.γ₁ (w.message c.1) c.1 c.2.1 c.2.2 P] := by
  simp only [linearClaimMcaError, prob_isLinearClaimExceptional_eq]

/-- The linear-claim error bounds the exceptional-event probability for each instance. -/
theorem prob_isLinearClaimExceptional_le (domain : ι ↪ F) (d A s : ℕ)
    (w : LinearClaimInstance ι F d) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
      (w.message c.1) c.1 c.2.1 c.2.2 P] ≤ linearClaimMcaError domain d A s := by
  rw [prob_isLinearClaimExceptional_eq]
  exact le_linearClaimMcaError domain d A s w

end ReedSolomon
