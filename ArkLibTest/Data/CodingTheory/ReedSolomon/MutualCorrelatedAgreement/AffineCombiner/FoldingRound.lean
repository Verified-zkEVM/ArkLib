/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FoldingRound
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for interleaved equal-degree combiners -/

open Polynomial ReedSolomon
open scoped Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

-- With one row, the interleaved equal-degree error is the equal-degree error.
example (d A s : ℕ) :
    interleavedEqualDegreeMcaError fullDomain 1 d A s = equalDegreeMcaError fullDomain d A s :=
  interleavedEqualDegreeMcaError_one fullDomain d A s

/-- The rows `f = (x², 0)`. -/
private def squareRows : Fin 2 → ZMod 5 → ZMod 5 := ![fun x ↦ x ^ 2, 0]

-- Two rows over `𝔽₅` with `f = (x², 0)`, `g = 0`, the zero challenge, and `d = 1`.
-- The combined words vanish, so the zero tuple has `5` shared agreements.
-- A witness `F₀ 0` is constant and meets `x²` in at most two points.
-- So at least `3` points are lost, and the zero tuple is exceptional at loss `2`.
example : IsInterleavedEqualDegreeExceptional fullDomain squareRows 0 1 5 2 0 0 0 0 := by
  have hall : interleavedEqualDegreeAgreementSet fullDomain squareRows 0 0 0 0 0 =
      Finset.univ := by
    ext x
    simp [equalDegreeWord]
  refine ⟨fun r ↦ by simp, by rw [hall, Finset.card_univ, ZMod.card],
    fun F₀ G₀ hF _ _ ↦ ?_⟩
  have hC : F₀ 0 = C ((F₀ 0).coeff 0) := eq_C_of_degree_le_zero (Order.le_of_lt_succ (hF 0))
  set c := (F₀ 0).coeff 0
  have hsub : ({x | c ≠ x ^ 2} : Finset (ZMod 5)) ⊆
      interleavedEqualDegreeAgreementLoss fullDomain squareRows 0 0 0 0 0 F₀ G₀ := by
    intro x hx
    rw [mem_interleavedEqualDegreeAgreementLoss, hall]
    refine ⟨Finset.mem_univ x, 0, Or.inl ?_⟩
    rw [hC]
    simpa [squareRows, fullDomain] using (Finset.mem_filter.mp hx).2
  have hcard : ∀ c' : ZMod 5, 3 ≤ #({x | c' ≠ x ^ 2} : Finset (ZMod 5)) := by decide
  exact (hcard c).trans_lt' (by omega) |>.trans_le (Finset.card_le_card hsub)

-- At loss `3` the same tuple is not exceptional.
-- The witnesses `F₀ = (1, 0)` and `G₀ = 0` lose exactly the three points where `x² ≠ 1`.
example : ¬ IsInterleavedEqualDegreeExceptional fullDomain squareRows 0 1 5 3 0 0 0 0 := by
  rintro ⟨-, -, h⟩
  have hloss : interleavedEqualDegreeAgreementLoss fullDomain squareRows 0 0 0 0 0
      ![C 1, 0] 0 = {0, 2, 3} := by
    ext x
    simp only [mem_interleavedEqualDegreeAgreementLoss, mem_interleavedEqualDegreeAgreementSet,
      Finset.mem_insert, Finset.mem_singleton, Fin.forall_fin_two, Fin.exists_fin_two]
    simp only [squareRows, fullDomain, equalDegreeWord, Pi.zero_apply, eval_zero,
      Function.Embedding.refl_apply, Matrix.cons_val_zero, Matrix.cons_val_one, eval_C]
    revert x
    decide
  have := h ![C 1, 0] 0 (fun r ↦ by fin_cases r <;> simp) (fun r ↦ by simp)
    (fun r ↦ by simp [affineMultiplier])
  rw [hloss] at this
  exact absurd this (by decide)

/-- The received rows `f r = 𝟙₀` for both rows. -/
private def spike : Fin 2 → ZMod 5 → ZMod 5 := fun _ x ↦ if x = 0 then 1 else 0

-- Both rows lose the point `0` against zero witnesses at the challenge `(0, 1, 0)`.
-- The combined word of each row is `0 + 1 · (𝟙₀ - 𝟙₀) = 0`, so the zero tuple agrees everywhere.
-- The shared loss counts the point `0` once.
example : #(interleavedEqualDegreeAgreementLoss fullDomain spike (-spike) 0 1 0 0 0 0) = 1 := by
  have hloss : interleavedEqualDegreeAgreementLoss fullDomain spike (-spike) 0 1 0 0 0 0 =
      {0} := by
    ext x
    by_cases hx : x = 0 <;> simp [spike, equalDegreeWord, fullDomain, hx]
  rw [hloss, Finset.card_singleton]

private theorem sqrt_degreeFraction : √((16 : ℝ) / 100) = 2 / 5 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

-- At `d = 16`, `n = 100`, `η = 1/2`, the threshold is `A = 90`.
-- The paper's `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋` is `⌊7300 / 6321⌋ = 1`.
example : ⌊(100 : ℝ) * ((90 : ℝ) - 1 - 16) / (((90 : ℝ) - 1) ^ 2 - 100 * 16)⌋₊ = 1 := by
  rw [Nat.floor_eq_iff (by norm_num)]
  norm_num

-- The paper's example in Section 5: `n = 2²⁰`, `d = 2¹⁸`, `A = 576717` give `ℓ₀ = 5`.
example : ⌊((2 ^ 20 : ℕ) : ℝ) * ((576717 : ℝ) - 1 - (2 ^ 18 : ℕ)) /
    (((576717 : ℝ) - 1) ^ 2 - (2 ^ 20 : ℕ) * (2 ^ 18 : ℕ))⌋₊ = 5 := by
  rw [Nat.floor_eq_iff (by norm_num)]
  norm_num

-- The Johnson condition `nd < (A - 1)²` at these parameters: `1600 < 89²`.
example : 100 * 16 < (⌈(√((16 : ℕ) / ((100 : ℕ) : ℝ)) + 1 / 2) * (100 : ℕ)⌉₊ - 1) ^ 2 :=
  mul_lt_sq_ceil_sqrt_add_mul_sub_one (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((16 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) = 16 / 100 by norm_num]; norm_num)

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private theorem field_card : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- A 100-point domain in the field with `2^64` elements. -/
private noncomputable def largeDomain : Fin 100 ↪ GaloisField 2 64 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin, field_card]; norm_num))

open Classical in
-- Two rows over the field with `2⁶⁴` elements at `d = 16`, `n = 100`, `η = 1/2`.
-- The paper's value `(4/η + ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)` is `9 / 2⁶⁴ + 2²² 5¹⁰ / 2¹²⁸`.
private theorem twoRows_error_le :
    interleavedEqualDegreeMcaError largeDomain 2 16 90 1 ≤
      ENNReal.ofReal (9 / 2 ^ 64 + 2 ^ 22 * 5 ^ 10 / 2 ^ 128) := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    simpa using sqrt_degreeFraction
  have h := interleavedEqualDegreeMcaError_le largeDomain 2 (d := 16) (η := 1 / 2)
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
-- The two-row value is below `2⁻⁶⁰`.
example : interleavedEqualDegreeMcaError largeDomain 2 16 90 1 < (1 : ENNReal) / 2 ^ 60 := by
  refine twoRows_error_le.trans_lt ?_
  calc _ < ENNReal.ofReal ((1 : ℝ) / 2 ^ 60) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        norm_num
    _ = _ := by norm_num [ENNReal.ofReal_div_of_pos, one_div]

-- A caller may supply its own decidable equality on the field.
example {F ι : Type*} [Field F] [Fintype F] [inst : DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (t d A s : ℕ) :
    @interleavedEqualDegreeMcaError F _ inst ι _ _ domain t d A s ≤ 1 :=
  interleavedEqualDegreeMcaError_le_one domain t d A s

-- The tuple agreement lemma accepts the caller's decidable equality on the coordinates.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [inst : DecidableEq ι]
    (domain : ι ↪ F) (f g : Fin 2 → ι → F) {d : ℕ} {F₀ G₀ F₁ G₁ : Fin 2 → F[X]}
    (hF₀ : ∀ r, (F₀ r).degree ≤ d) (hG₀ : ∀ r, (G₀ r).degree ≤ d)
    (hF₁ : ∀ r, (F₁ r).degree ≤ d) (hG₁ : ∀ r, (G₁ r).degree ≤ d) (hne : (F₀, G₀) ≠ (F₁, G₁)) :
    #(@Min.min _ (@Finset.instMin _ inst)
      (interleavedCommonAgreementSet domain f g F₀ G₀)
      (interleavedCommonAgreementSet domain f g F₁ G₁)) ≤ d :=
  card_inter_interleavedCommonAgreementSet_le domain f g hF₀ hG₀ hF₁ hG₁ hne

/-- info: 'ReedSolomon.interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add

/-- info: 'ReedSolomon.interleavedEqualDegreeMcaError_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeMcaError_le

/-- info: 'ReedSolomon.card_badInterleavedEqualDegreeChallenges_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_badInterleavedEqualDegreeChallenges_mul_le

/-- info: 'ReedSolomon.IsInterleavedEqualDegreeExceptional.isInterleavedAffineExceptional_or_exists'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsInterleavedEqualDegreeExceptional.isInterleavedAffineExceptional_or_exists

/-- info: 'ReedSolomon.interleavedEqualDegreeMcaError_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeMcaError_one

/-- info: 'ReedSolomon.isInterleavedEqualDegreeExceptional_one_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.isInterleavedEqualDegreeExceptional_one_iff

/-- info: 'ReedSolomon.le_interleavedEqualDegreeMcaError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_interleavedEqualDegreeMcaError

/-- info: 'ReedSolomon.interleavedEqualDegreeMcaError_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeMcaError_le_one

/-- info: 'ReedSolomon.interleavedEqualDegreeAgreementSet_eq_interleavedAgreementSet' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeAgreementSet_eq_interleavedAgreementSet

/-- info: 'ReedSolomon.card_inter_interleavedCommonAgreementSet_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_inter_interleavedCommonAgreementSet_le

/-- info: 'ReedSolomon.mul_lt_sq_ceil_sqrt_add_mul_sub_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mul_lt_sq_ceil_sqrt_add_mul_sub_one

/-- info: 'ReedSolomon.mem_interleavedEqualDegreeAgreementSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mem_interleavedEqualDegreeAgreementSet

/-- info: 'ReedSolomon.mem_interleavedEqualDegreeAgreementLoss' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mem_interleavedEqualDegreeAgreementLoss

/-- info: 'ReedSolomon.mem_badInterleavedEqualDegreeChallenges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mem_badInterleavedEqualDegreeChallenges

/-- info: 'ReedSolomon.mem_interleavedCommonAgreementSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mem_interleavedCommonAgreementSet

/-- info: 'ReedSolomon.interleavedEqualDegreeMcaError_anti_threshold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.interleavedEqualDegreeMcaError_anti_threshold

/-- info: 'ReedSolomon.equalDegreeMcaError_le_affineMcaError_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.equalDegreeMcaError_le_affineMcaError_add

/-- info: 'ReedSolomon.card_badEqualDegreeChallenges_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_badEqualDegreeChallenges_mul_le

/-- info: 'ReedSolomon.IsEqualDegreeExceptional.isAffineExceptional_or_exists_degree_eq' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.IsEqualDegreeExceptional.isAffineExceptional_or_exists_degree_eq
