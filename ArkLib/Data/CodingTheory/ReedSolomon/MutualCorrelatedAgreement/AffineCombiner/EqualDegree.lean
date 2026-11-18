/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic

/-!
# Equal-degree combiners

The combiner maps received words `f, g` to `g + (α + β x)(f + θ g)`.
It uses three independent uniform challenges.
Both witnesses have degree below `d`, while the output has degree at most `d`.

This module defines the exceptional event and its error, after Section 5 of [CWYZ26].
The bound of Theorem 5.1 by the affine error plus `ℓ₀/q` is proved for any number of rows.
It lives in the folding-round module, with the one-row bound as its case `t = 1`.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

The error is a mathematical supremum with classical decidability for polynomial witnesses.
Its counting definition requires no sampler.
The sampling module identifies it with native uniform probabilities.

## Main definitions

* `ReedSolomon.equalDegreeWord`: the combined received word.
* `ReedSolomon.IsEqualDegreeExceptional`: an exceptional candidate for three challenges.
* `ReedSolomon.equalDegreeMcaError`: the supremum of exceptional-event probabilities.

## Main statements

* `ReedSolomon.equalDegreeWord_eq_combinedWord`: the word is an affine combined word.
* `ReedSolomon.le_equalDegreeMcaError` and `ReedSolomon.equalDegreeMcaError_le_one`: basic
  bounds on the error.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- The equal-degree combined word `g + (α + β x) (f + θ g)`. -/
def equalDegreeWord (domain : ι ↪ F) (f g : ι → F) (θ α β : F) : ι → F :=
  fun i ↦ g i + (α + β * domain i) * (f i + θ * g i)

/-- The challenge `(θ, α, β)` makes `P` exceptional for the equal-degree combiner.

`P` has degree at most `d` and agrees with `g + (α + β x)(f + θ g)` on at least `A` points.
No pair `F₀, G₀` of degrees below `d` satisfies
`P = G₀ + (α + βX)(F₀ + θG₀)` while losing at most `s` of these points. -/
def IsEqualDegreeExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree < d → G₀.degree < d →
      P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) →
      s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P |
        F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i}

open Classical in
/-- The supremum over received word pairs of the probability that some candidate is exceptional
for independent uniform challenges `(θ, α, β)`.

The output degree bound is `d`, both witness degrees are below `d`, the agreement threshold
is `A`, and the allowed agreement loss is `s`.
`ReedSolomon.equalDegreeMcaError_eq_iSup_prob` gives the native sampling characterization. -/
noncomputable def equalDegreeMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ENNReal :=
  ⨆ w : (ι → F) × (ι → F),
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P,
        IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 3)

omit [DecidableEq F] [Fintype ι] in
/-- The equal-degree word is the affine word of the pair `(g, f + θ g)`. -/
theorem equalDegreeWord_eq_combinedWord (domain : ι ↪ F) (f g : ι → F) (θ α β : F) :
    equalDegreeWord domain f g θ α β =
      combinedWord domain g (fun i ↦ f i + θ * g i) (affineMultiplier α β) := by
  funext i
  simp [equalDegreeWord]

open Classical in
/-- One received word pair bounds the equal-degree error from below. -/
theorem le_equalDegreeMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) (f g : ι → F) :
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P,
        IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 3) ≤ equalDegreeMcaError domain d A s := by
  unfold equalDegreeMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- The equal-degree error is at most one. -/
theorem equalDegreeMcaError_le_one [Fintype F] (domain : ι ↪ F) (d A s : ℕ) :
    equalDegreeMcaError domain d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : F × F × F | ∃ P,
        IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F × F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 3 := by simp [pow_succ, mul_assoc]

end ReedSolomon
