/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FoldingSampling
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for folding probabilities -/

open Polynomial ReedSolomon
open scoped ProbabilityTheory Finset

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

open Classical in
-- One pair at `d = 16`, `n = 100`, `η = 1/2` over the field with `2⁶⁴` elements.
-- The paper's value `(4/η + ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)` is `9 / 2⁶⁴ + 2²² 5¹⁰ / 2¹²⁸`.
private theorem onePair_error_le :
    interleavedEqualDegreeMcaError largeDomain 1 16 90 1 ≤
      ENNReal.ofReal (9 / 2 ^ 64 + 2 ^ 22 * 5 ^ 10 / 2 ^ 128) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := interleavedEqualDegreeMcaError_le largeDomain 1 (d := 16) (η := 1 / 2)
    (by norm_num) (by simp) (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin, field_card] at h
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  have hℓ : ⌊(100 : ℝ) * ((90 : ℝ) - 1 - 16) / (((90 : ℝ) - 1) ^ 2 - 100 * 16)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  simp only [hA, Nat.cast_ofNat, Nat.cast_pow] at h
  rw [hℓ] at h
  convert h using 2
  norm_num

open Classical in
-- Two words folded in one round from degree `15` to degree `16` at threshold `90`.
-- Every candidate of degree at most `16` agreeing on `91` points then has witnesses of degree
-- at most `15`, except with probability below `2⁻⁶⁰`.
example (f : Fin (2 ^ 1) → Fin 100 → GaloisField 2 64) :
    Pr{let c ← $ᵗ (Fin 1 → GaloisField 2 64 × GaloisField 2 64 × GaloisField 2 64)}[
      ∃ P : (GaloisField 2 64)[X], P.degree ≤ ↑(15 + 1) ∧ ∃ S : Finset (Fin 100),
        (∀ i ∈ S, P.eval (largeDomain i) = foldWords largeDomain 1 c f i) ∧ 90 + 1 ≤ #S ∧
        ¬ ∃ W : Fin (2 ^ 1) → (GaloisField 2 64)[X], (∀ k, (W k).degree ≤ (15 : ℕ)) ∧
          foldPolynomials 1 c W = P ∧
          #{i ∈ S | ∃ k, (W k).eval (largeDomain i) ≠ f k i} ≤ 1] <
      (1 : ENNReal) / 2 ^ 60 := by
  refine (prob_exists_not_exists_foldPolynomials_eq_le_mul largeDomain
    (ε := ENNReal.ofReal (9 / 2 ^ 64 + 2 ^ 22 * 5 ^ 10 / 2 ^ 128)) (fun j hj ↦ ?_) f).trans_lt ?_
  · obtain rfl : j = 0 := by omega
    exact onePair_error_le
  · have hreal : (9 / 2 ^ 64 + 2 ^ 22 * 5 ^ 10 / 2 ^ 128 : ℝ) < 1 / 2 ^ 60 := by norm_num
    rw [Nat.cast_one, one_mul]
    calc _ < ENNReal.ofReal ((1 : ℝ) / 2 ^ 60) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal
      _ = _ := by norm_num [ENNReal.ofReal_div_of_pos, one_div]

/-- info: 'ReedSolomon.prob_exists_not_exists_foldPolynomials_eq_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_exists_not_exists_foldPolynomials_eq_le_mul

/-- info: 'ReedSolomon.prob_isFoldingExceptional_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_isFoldingExceptional_le_mul

/-- info: 'ReedSolomon.prob_isFoldingExceptional_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_isFoldingExceptional_le

/-- info: 'ReedSolomon.foldingMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldingMcaError_eq_iSup_prob

/-- info: 'ReedSolomon.prob_isFoldingExceptional_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_isFoldingExceptional_eq

/-- info: 'ReedSolomon.interleavedEqualDegreeMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeMcaError_eq_iSup_prob

/-- info: 'ReedSolomon.prob_isInterleavedEqualDegreeExceptional_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_isInterleavedEqualDegreeExceptional_le

/-- info: 'ReedSolomon.prob_isInterleavedEqualDegreeExceptional_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_isInterleavedEqualDegreeExceptional_eq
