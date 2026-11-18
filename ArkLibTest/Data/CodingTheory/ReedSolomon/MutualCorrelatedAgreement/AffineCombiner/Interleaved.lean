/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interleaved
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for interleaved affine combiners -/

open Polynomial ReedSolomon
open scoped Finset

private theorem sqrt_degreeFraction : √((16 : ℝ) / 100) = 2 / 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

-- With one row, the bound of Theorem 1.1 is the interleaved bound at `d = 16`, `n = 100`,
-- `η = 1/2`, where `√ρ = 2/5` and `A = 90`.
example {F : Type*} [Field F] [DecidableEq F] [Fintype F] (domain : Fin 100 ↪ F) :
    interleavedAffineMcaError domain 1 16 90 1 ≤
      ENNReal.ofReal (8 / Fintype.card F + 2 ^ 22 * 5 ^ 10 / (Fintype.card F : ℝ) ^ 2) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := affineMcaError_le domain (d := 16) (η := 1 / 2) (by norm_num) (by simp)
    (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin] at h
  rw [interleavedAffineMcaError_one]
  convert h using 2
  · norm_num
  · field_simp
    ring

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private theorem field_card : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- A 100-point domain in the field with `2^64` elements. -/
private noncomputable def largeDomain : Fin 100 ↪ GaloisField 2 64 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin, field_card]; norm_num))

-- Two rows over the field with `2⁶⁴` elements at `d = 16`, `n = 100`, `η = 1/2`.
-- The paper's value `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)` is `2⁻⁶¹ + 2²² 5¹⁰ / 2¹²⁸` here.
open Classical in
private theorem twoRows_error_le :
    interleavedAffineMcaError largeDomain 2 16 90 1 ≤
      ENNReal.ofReal (1 / 2 ^ 61 + 2 ^ 22 * 5 ^ 10 / 2 ^ 128) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := interleavedAffineMcaError_le largeDomain 2 (d := 16) (η := 1 / 2)
    (by norm_num) (by simp) (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin, field_card] at h
  have hA : ⌈((2 : ℝ) / 5 + 1 / 2) * 100⌉₊ = 90 := by norm_num
  simp only [hA, Nat.cast_pow, Nat.cast_ofNat] at h
  convert h using 2
  norm_num

-- The two-row value is below `2⁻⁶⁰`.
open Classical in
example : interleavedAffineMcaError largeDomain 2 16 90 1 < (1 : ENNReal) / 2 ^ 60 := by
  refine twoRows_error_le.trans_lt ?_
  have hreal : (1 / 2 ^ 61 + 2 ^ 22 * 5 ^ 10 / 2 ^ 128 : ℝ) < 1 / 2 ^ 60 := by norm_num
  calc _ < ENNReal.ofReal ((1 : ℝ) / 2 ^ 60) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal
    _ = _ := by norm_num [ENNReal.ofReal_div_of_pos, one_div]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The received rows `f r = 𝟙₀` for both rows. -/
private def spike : Fin 2 → ZMod 5 → ZMod 5 := fun _ x ↦ if x = 0 then 1 else 0

-- Both rows lose the point `0` against the zero witnesses at the challenge `(1, 0)`.
-- The shared loss counts that point once, so the zero witnesses keep loss one.
example :
    #(interleavedAgreementLoss (Function.Embedding.refl _) spike (-spike) 1 0 0 0 0) = 1 ∧
      IsInterleavedLossWitness (Function.Embedding.refl _) spike (-spike) 1 1 0 0 0 0 := by
  have hloss : interleavedAgreementLoss (Function.Embedding.refl _) spike (-spike) 1 0 0 0 0 =
      {0} := by
    ext x
    by_cases hx : x = 0 <;> simp [spike, hx]
  refine ⟨by rw [hloss, Finset.card_singleton], fun r ↦ by simp, by rw [hloss]; simp⟩

-- Each row alone loses the point `0`, so summing the row losses would count it twice.
example (r : Fin 2) :
    #(agreementLoss (Function.Embedding.refl _) (spike r) (-spike r) (affineMultiplier 1 0)
      0 0 0) = 1 := by
  have hloss : agreementLoss (Function.Embedding.refl _) (spike r) (-spike r)
      (affineMultiplier 1 0) 0 0 0 = {0} := by
    ext x
    by_cases hx : x = 0 <;> simp [agreementLoss, spike, hx]
  rw [hloss, Finset.card_singleton]

-- Two rows over `𝔽₅` with the zero challenge, words `f = 0` and `g = (x², 0)`, and `d = 1`.
-- The zero tuple agrees everywhere, so it has `5` shared agreements.
-- A witness `G₀ 0` is constant and meets `x²` in at most two points, so at least `3` are lost.
-- So the zero tuple is exceptional at threshold `5` and loss `2`.
example : IsInterleavedAffineExceptional (Function.Embedding.refl (ZMod 5)) 0
    ![fun x ↦ x ^ 2, 0] 1 5 2 0 0 0 := by
  have hall : interleavedAgreementSet (Function.Embedding.refl (ZMod 5)) 0
      ![fun x ↦ x ^ 2, 0] 0 0 0 = Finset.univ := by
    ext x
    simp
  refine ⟨fun r ↦ by simp, by rw [hall, Finset.card_univ, ZMod.card], fun F₀ G₀ _ hG hw ↦ ?_⟩
  have hC : G₀ 0 = C ((G₀ 0).coeff 0) := eq_C_of_degree_le_zero (Order.le_of_lt_succ (hG 0))
  set c := (G₀ 0).coeff 0
  have hsub : ({x | c ≠ x ^ 2} : Finset (ZMod 5)) ⊆
      interleavedAgreementLoss (Function.Embedding.refl (ZMod 5)) 0 ![fun x ↦ x ^ 2, 0] 0 0 0
        F₀ G₀ := by
    intro x hx
    rw [mem_interleavedAgreementLoss, hall]
    refine ⟨Finset.mem_univ x, 0, Or.inr ?_⟩
    rw [hC]
    simpa using (Finset.mem_filter.mp hx).2
  have hcard : ∀ c' : ZMod 5, 3 ≤ #({x | c' ≠ x ^ 2} : Finset (ZMod 5)) := by decide
  have := (hcard c).trans ((Finset.card_le_card hsub).trans hw.2)
  omega

-- A caller may supply its own decidable equality on the field.
example {F ι : Type*} [Field F] [Fintype F] [inst : DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (t d A s : ℕ) :
    @interleavedAffineMcaError F _ inst ι _ _ domain t d A s ≤ 1 :=
  interleavedAffineMcaError_le_one domain t d A s

/-- info: 'ReedSolomon.interleavedAffineMcaError_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedAffineMcaError_le

/-- info: 'ReedSolomon.exists_interleavedAffineExceptional_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_interleavedAffineExceptional_finset_card_le

/-- info: 'ReedSolomon.IsInterleavedAffineExceptional.pack' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.IsInterleavedAffineExceptional.pack

/-- info: 'ReedSolomon.interleavedAffineMcaError_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedAffineMcaError_one

/-- info: 'ReedSolomon.isInterleavedAffineExceptional_one_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.isInterleavedAffineExceptional_one_iff
