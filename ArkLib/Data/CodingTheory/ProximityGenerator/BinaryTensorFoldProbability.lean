/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement

/-!
# Probability of exceptional shared-level tensor challenges

The count theorem divides by `|F|^h`, since each of the `h` levels receives one independent
uniform field challenge. All parents at one level are controlled by the same packed event.
At height three this gives `3E/|F|`, with the same full-set decomposition outside the bad set.
-/

@[expose] public section

namespace TensorMCA

open CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

variable {ι F A : Type} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
  [AddCommMonoid A] [Module F A] [DecidableEq A]

open Classical in
/-- Uniform independent challenges by level give the counted tensor exceptional probability. -/
theorem tensorFoldBad_probability_le
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin h → Bool) → ι → A) :
    Pr_{let r ←$ᵖ (Fin h → F)}[r ∈ tensorFoldBad hlevel u] ≤
      ENNReal.ofReal ((h * exceptionalCount : ℕ) / (Fintype.card F : ℝ)) := by
  rw [Probability.prob_uniform_eq_ofReal]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow]
  by_cases hh : h = 0
  · subst h
    rw [tensorFoldBad_eq_empty_height_zero]
    simp
  · apply ENNReal.ofReal_le_ofReal
    have hcard : ((tensorFoldBad hlevel u).card : ℝ) ≤
        ((h * exceptionalCount : ℕ) : ℝ) *
          (Fintype.card F : ℝ) ^ (h - 1) := by
      exact_mod_cast tensorFoldBad_card_le hlevel u
    have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have hpow : (Fintype.card F : ℝ) ^ h =
        (Fintype.card F : ℝ) ^ (h - 1) * Fintype.card F := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      _ ≤ (((h * exceptionalCount : ℕ) : ℝ) *
          (Fintype.card F : ℝ) ^ (h - 1)) / (Fintype.card F : ℝ) ^ h :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = ((h * exceptionalCount : ℕ) : ℝ) / Fintype.card F := by
        rw [hpow]
        field_simp

open Classical in
/-- Three shared challenge levels cost at most three level exceptional counts. -/
theorem tensorFoldBad_probability_height_three
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin 3 → Bool) → ι → A) :
    Pr_{let r ←$ᵖ (Fin 3 → F)}[r ∈ tensorFoldBad hlevel u] ≤
      ENNReal.ofReal ((3 * exceptionalCount : ℕ) / (Fintype.card F : ℝ)) := by
  simpa using tensorFoldBad_probability_le hlevel u

end TensorMCA
