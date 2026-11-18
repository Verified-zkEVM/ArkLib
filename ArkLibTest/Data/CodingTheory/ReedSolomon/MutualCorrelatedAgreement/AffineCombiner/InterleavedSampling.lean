/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterleavedSampling
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for interleaved affine-combiner probabilities -/

open ReedSolomon
open scoped ProbabilityTheory

private theorem sqrt_degreeFraction : √((16 : ℝ) / 100) = 2 / 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private noncomputable instance : SampleableType (GaloisField 2 64) :=
  SampleableType.ofFintype _

private theorem field_card : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- A 100-point domain in the field with `2^64` elements. -/
private noncomputable def largeDomain : Fin 100 ↪ GaloisField 2 64 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin, field_card]; norm_num))

-- For any three rows over the field with `2⁶⁴` elements at `d = 16`, `n = 100`, `η = 1/2`,
-- a uniform shared challenge has an exceptional tuple with probability below `2⁻⁶⁰`.
open Classical in
example (f g : Fin 3 → Fin 100 → GaloisField 2 64) :
    Pr{let c ← $ᵗ (GaloisField 2 64 × GaloisField 2 64)}[∃ P,
      IsInterleavedAffineExceptional largeDomain f g 16 90 1 c.1 c.2 P] <
        (1 : ENNReal) / 2 ^ 60 := by
  refine (prob_isInterleavedAffineExceptional_le largeDomain f g 16 90 1).trans_lt ?_
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := interleavedAffineMcaError_le largeDomain 3 (d := 16) (η := 1 / 2)
    (by norm_num) (by simp) (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin, field_card] at h
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  simp only [hA, Nat.cast_pow, Nat.cast_ofNat] at h
  apply lt_of_le_of_lt h
  have hreal :
      (4 / ((1 / 2 : ℝ) * 2 ^ 64) + 2 ^ 14 * (100 : ℝ) ^ 2 /
        (((16 : ℝ) / 100) ^ 3 * (1 / 2) ^ 10 * (2 ^ 64 : ℝ) ^ 2)) < 1 / 2 ^ 60 := by
    norm_num
  calc _ < ENNReal.ofReal ((1 : ℝ) / 2 ^ 60) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal
    _ = _ := by norm_num [ENNReal.ofReal_div_of_pos, one_div]

/-- info: 'ReedSolomon.interleavedAffineMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedAffineMcaError_eq_iSup_prob
