/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interleaved

/-!
# Uniform probabilities for interleaved affine combiners

The counting interleaved affine error is a supremum of native uniform probabilities.
The supremum ranges over pairs of row tuples.
The shared challenge `(α, β)` is sampled uniformly from `F × F`.
The counting definition and the bound (5.7) have no sampler assumptions.
These characterizations use `SampleableType F` to connect them to probability bounds.

The error follows the one-round guarantee in the proof of Theorem 5.2 of [CWYZ26].
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedSolomon.prob_isInterleavedAffineExceptional_eq`: the uniform probability as a counting
  fraction.
* `ReedSolomon.interleavedAffineMcaError_eq_iSup_prob`: the error as a supremum of native
  probabilities.
* `ReedSolomon.prob_isInterleavedAffineExceptional_le`: the error bounds the probability for
  each pair of row tuples.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open scoped ProbabilityTheory Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [Fintype F] [SampleableType F]
  {t : ℕ}

open Classical in
/-- The uniform exceptional-event probability equals the fraction of exceptional challenges. -/
theorem prob_isInterleavedAffineExceptional_eq (domain : ι ↪ F) (f g : Fin t → ι → F)
    (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F)}[∃ P, IsInterleavedAffineExceptional domain f g d A s c.1 c.2 P] =
      ENNReal.ofReal
        ((#{c : F × F | ∃ P, IsInterleavedAffineExceptional domain f g d A s c.1 c.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 2) := by
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp [sq]

/-- The interleaved error is the worst-case native probability of exceptionality. -/
theorem interleavedAffineMcaError_eq_iSup_prob (domain : ι ↪ F) (t d A s : ℕ) :
    interleavedAffineMcaError domain t d A s =
      ⨆ w : (Fin t → ι → F) × (Fin t → ι → F),
        Pr{let c ← $ᵗ (F × F)}[∃ P,
          IsInterleavedAffineExceptional domain w.1 w.2 d A s c.1 c.2 P] := by
  simp only [interleavedAffineMcaError, prob_isInterleavedAffineExceptional_eq]

/-- The interleaved error bounds the exceptional-event probability for each pair of rows. -/
theorem prob_isInterleavedAffineExceptional_le (domain : ι ↪ F) (f g : Fin t → ι → F)
    (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F)}[∃ P, IsInterleavedAffineExceptional domain f g d A s c.1 c.2 P] ≤
      interleavedAffineMcaError domain t d A s := by
  rw [prob_isInterleavedAffineExceptional_eq]
  exact le_interleavedAffineMcaError domain d A s f g

end ReedSolomon
