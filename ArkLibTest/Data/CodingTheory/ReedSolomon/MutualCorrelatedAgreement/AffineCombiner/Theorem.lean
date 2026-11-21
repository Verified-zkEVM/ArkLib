/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Theorem
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for the affine MCA bound -/

open ReedSolomon

private theorem sqrt_degreeFraction : √((16 : ℝ) / 100) = 2 / 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

/-- The bound applies at `d = 16`, `n = 100`, `η = 1/2`, where `√ρ = 2/5` and `A = 90`. -/
example {F : Type*} [Field F] [DecidableEq F] [Fintype F] (domain : Fin 100 ↪ F) :
    affineMcaError domain 16 90 1 ≤
      ENNReal.ofReal (8 / Fintype.card F + 2 ^ 22 * 5 ^ 10 / (Fintype.card F : ℝ) ^ 2) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := affineMcaError_le domain (d := 16) (η := 1 / 2) (by norm_num) (by simp)
    (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin] at h
  convert h using 2
  · norm_num
  · field_simp
    ring

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private noncomputable instance : SampleableType (GaloisField 2 64) :=
  SampleableType.ofFintype _

private theorem field_card : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- A 100-point domain in the field with `2^64` elements. -/
private noncomputable def largeDomain : Fin 100 ↪ GaloisField 2 64 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin, field_card]; norm_num))

-- A concrete finite-field instance with an error bound below 2⁻⁶⁰.
open Classical in
private theorem largeDomain_error_lt :
    affineMcaError largeDomain 16 90 1 < (1 : ENNReal) / 2 ^ 60 := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := affineMcaError_le largeDomain (d := 16) (η := 1 / 2)
    (by norm_num) (by simp) (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin, field_card] at h
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  simp only [hA, Nat.cast_pow, Nat.cast_ofNat] at h
  apply lt_of_le_of_lt h
  calc _ < ENNReal.ofReal ((1 : ℝ) / 2 ^ 60) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        norm_num
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-- info: 'ReedSolomon.affineMcaError_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.affineMcaError_le
/-- info: 'ReedSolomon.exists_affineExceptional_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_affineExceptional_finset_card_le

open scoped ProbabilityTheory

-- The same concrete security bound applies to each word pair under native uniform sampling.
open Classical in
example (f g : Fin 100 → GaloisField 2 64) :
    Pr{let c ← $ᵗ (GaloisField 2 64 × GaloisField 2 64)}[∃ P,
      IsAffineExceptional largeDomain f g 16 90 1 c.1 c.2 P] < (1 : ENNReal) / 2 ^ 60 :=
  (prob_isAffineExceptional_le largeDomain f g 16 90 1).trans_lt largeDomain_error_lt
