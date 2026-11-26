/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegreeSampling
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegreeTheorem
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for the explicit equal-degree and linear-claim bounds -/

open ReedSolomon

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- At `d = 1`, `A = 4` on `F₅`, the Johnson quotient is `5 / 2`.
Its floor gives an additive error term of `2 / 5`. -/
example :
    equalDegreeMcaError fullDomain 1 4 1 ≤ affineMcaError fullDomain 1 4 1 + 2 / 5 := by
  have h := equalDegreeMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

open scoped ProbabilityTheory

-- The bound controls native probabilities for independently uniform triples.
example (f g : ZMod 5 → ZMod 5) :
    Pr{let c ← $ᵗ (ZMod 5 × ZMod 5 × ZMod 5)}[∃ P,
      IsEqualDegreeExceptional fullDomain f g 1 4 1 c.1 c.2.1 c.2.2 P] ≤
        affineMcaError fullDomain 1 4 1 + 2 / 5 := by
  refine (prob_isEqualDegreeExceptional_le fullDomain f g 1 4 1).trans ?_
  have h := equalDegreeMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

private theorem sqrt_degreeFraction : √((16 : ℝ) / 100) = 2 / 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private theorem field_card : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- A 100-point domain in the field with `2^64` elements. -/
private noncomputable def largeDomain : Fin 100 ↪ GaloisField 2 64 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin, field_card]; norm_num))

/-- At `A = 90`, `n = 100`, `d = 16`, the Johnson floor is `ℓ₀ = ⌊100 · 73 / 6321⌋ = 1`. -/
private theorem johnson_floor :
    ⌊(100 : ℝ) * ((90 : ℝ) - 1 - 16) / (((90 : ℝ) - 1) ^ 2 - 100 * 16)⌋₊ = 1 := by
  rw [Nat.floor_eq_iff (by norm_num)]
  norm_num

-- At `d = 16`, `n = 100`, `η = 1/2`, the equal-degree bound is `(8 + ℓ₀)/q + 2²² 5¹⁰/q²`
-- with `ℓ₀ = 1`.
example {F : Type*} [Field F] [DecidableEq F] [Fintype F] (domain : Fin 100 ↪ F) :
    equalDegreeMcaError domain 16 90 1 ≤
      ENNReal.ofReal (9 / Fintype.card F + 2 ^ 22 * 5 ^ 10 / (Fintype.card F : ℝ) ^ 2) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := equalDegreeMcaError_le domain (d := 16) (η := 1 / 2) (by norm_num) (by simp)
    (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  rw [hsqrt, Fintype.card_fin] at h
  push_cast at h
  rw [hA] at h
  push_cast at h
  rw [johnson_floor] at h
  convert h using 2
  field_simp
  ring

-- At the same parameters, the linear-claim bound is `(8 + ℓ₀)/q + 2²² 5¹⁰/q²` with `ℓ₀ = 1`.
example {F : Type*} [Field F] [DecidableEq F] [Fintype F] (domain : Fin 100 ↪ F) :
    linearClaimMcaError domain 16 90 1 ≤
      ENNReal.ofReal (9 / Fintype.card F + 2 ^ 22 * 5 ^ 10 / (Fintype.card F : ℝ) ^ 2) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := linearClaimMcaError_le domain (d := 16) (η := 1 / 2) (by norm_num) (by simp)
    (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  rw [hsqrt, Fintype.card_fin] at h
  push_cast at h
  rw [hA] at h
  push_cast at h
  rw [johnson_floor] at h
  convert h using 2
  field_simp
  ring

-- In the field with `2⁶⁴` elements on a 100-point domain, the linear-claim error is below `2⁻⁶⁰`.
open Classical in
example : linearClaimMcaError largeDomain 16 90 1 < (1 : ENNReal) / 2 ^ 60 := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := linearClaimMcaError_le largeDomain (d := 16) (η := 1 / 2) (by norm_num) (by simp)
    (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  rw [hsqrt, Fintype.card_fin, field_card] at h
  push_cast at h
  rw [hA] at h
  push_cast at h
  rw [johnson_floor] at h
  apply lt_of_le_of_lt h
  have hone : ENNReal.ofReal ((1 : ℝ) / 2 ^ 60) = (1 : ENNReal) / 2 ^ 60 := by
    norm_num [ENNReal.ofReal_div_of_pos, one_div]
  rw [← hone]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by norm_num)

/-- info: 'ReedSolomon.equalDegreeMcaError_le_affineMcaError_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.equalDegreeMcaError_le_affineMcaError_add

/-- info: 'ReedSolomon.equalDegreeMcaError_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.equalDegreeMcaError_le

/-- info: 'ReedSolomon.linearClaimMcaError_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.linearClaimMcaError_le
