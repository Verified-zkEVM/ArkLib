/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform probabilities for the Reed–Muller affine combiner

The Reed–Muller error is a supremum of native uniform exceptional-event probabilities.
Its counting definition and counting bounds do not require a sampler instance.
This module supplies the sampling characterization under `SampleableType F`.
A coefficient vector is sampled uniformly from `F^{k+1}`.

The error follows the definition in Section 7 of [CWYZ26].
Theorem 7.1 itself is not proved here.
The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedMuller.prob_isAffineExceptional_eq`: the uniform probability as a counting fraction.
* `ReedMuller.affineMcaError_eq_iSup_prob`: the error as a supremum of native probabilities.
* `ReedMuller.prob_isAffineExceptional_le`: the error bounds the probability for each
  received word pair.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open Finset
open scoped ProbabilityTheory

variable {K₀ F : Type} [Field K₀] [Fintype K₀] [Field F] [Fintype F] [DecidableEq F]
  [Algebra K₀ F] [SampleableType F] {k : ℕ}

open Classical in
/-- A uniform Reed–Muller exceptional-event probability equals its counting fraction. -/
theorem prob_isAffineExceptional_eq (f g : (Fin k → K₀) → F) (d A s : ℕ) :
    Pr{let α ← $ᵗ (Fin (k + 1) → F)}[∃ P, IsAffineExceptional f g d A s α P] =
      ENNReal.ofReal
        ((#{α : Fin (k + 1) → F | ∃ P, IsAffineExceptional f g d A s α P} : ℝ) /
          (Fintype.card F : ℝ) ^ (k + 1)) := by
  classical
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp

/-- The Reed–Muller counting error is the worst-case native probability of exceptionality. -/
theorem affineMcaError_eq_iSup_prob (k d A s : ℕ) :
    affineMcaError K₀ F k d A s =
      ⨆ w : ((Fin k → K₀) → F) × ((Fin k → K₀) → F),
        Pr{let α ← $ᵗ (Fin (k + 1) → F)}[∃ P, IsAffineExceptional w.1 w.2 d A s α P] := by
  simp only [affineMcaError, prob_isAffineExceptional_eq]

/-- The Reed–Muller error bounds the exceptional-event probability for each pair of words. -/
theorem prob_isAffineExceptional_le (f g : (Fin k → K₀) → F) (d A s : ℕ) :
    Pr{let α ← $ᵗ (Fin (k + 1) → F)}[∃ P, IsAffineExceptional f g d A s α P] ≤
      affineMcaError K₀ F k d A s := by
  rw [prob_isAffineExceptional_eq]
  exact le_affineMcaError d A s f g

end ReedMuller
