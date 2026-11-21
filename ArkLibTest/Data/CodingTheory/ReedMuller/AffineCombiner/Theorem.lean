/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Theorem
import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Probability
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Acceptance cases for the Reed–Muller affine MCA bound

The worked case has `q₀ = 2⁸`, `d = 64` (so `ρ = 1/4`), `η = 1/4` and `q = 2⁶⁴`.
Then `q₀ η² = 16 = 4 / ρ`, so the slack condition holds with equality.
With `k = 2` variables, `n = 2¹⁶`, the threshold is `A = 49152` and the loss is `2⁸`.
The bound `4 / (η q²) + 2²⁰ n³ / (ρ⁴ η¹⁴ q³)` is `2⁻¹²⁴ + 2⁻⁸⁸`.
With `k = 1`, `n = 2⁸`, `A = 192`, the loss is one and the bound is `16 / q + 2⁵⁶ / q²`.
Field sizes enter only through explicit cardinality hypotheses.
-/

open ReedMuller

private theorem sqrt_degreeFraction : √((64 : ℝ) / 256) = 1 / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num

open Polynomial.SymbolicInterpolation in
-- The general count at the worked parameters `q₀ = 2⁸`, `k = 2`, `d = 64`, `η = 1/4`:
-- `m = 8`, `D = 96`, `M = 22`, `A = 49152` and `B = 40704`, so `A - B - e + 1 = 8193`.
-- The surplus is `2¹⁶ · 3408 < 389267456` monomials.
example {K₀ F : Type*} [Field K₀] [Fintype K₀] [Field F] [Fintype F] [DecidableEq F]
    [Algebra K₀ F] (hK : Fintype.card K₀ = 2 ^ 8) (f g : (Fin 2 → K₀) → F) :
    ∃ Ex : Finset (Fin 3 → F), (Ex.card : ℝ) ≤
        65536 * (40704 - 65 * 256) / (40704 ^ 2 - 65536 * (65 * 256)) *
          max (Fintype.card F : ℝ) ((65536).choose 3 : ℕ) +
        (96 ^ 2 + (2 * 16384 * 22 * (65536 / 8193)) ^ 3 * 96 ^ 4) ∧
      ∀ α ∉ Ex, ∀ P, ¬ IsAffineExceptional f g 64 49152 (2 ^ 8) α P := by
  obtain ⟨Ex, hcard, hgood⟩ := exists_affineExceptional_finset_card_le_of_interpolation
    (k := 2) f g (d := 64) (A := 49152) (B := 40704) (m := 8) (D := 96) (M := 22)
    (by norm_num) (by rw [hK]; norm_num) (by rw [hK]; norm_num) (by rw [hK]; norm_num)
    (by
      rw [hK, card_constraintSupport, card_monomialSupport]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num)
  rw [hK] at hcard hgood
  simp only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at hcard hgood
  -- Keep the binomial coefficient symbolic: evaluating it is not needed.
  generalize ((Nat.choose 65536 3 : ℕ) : ℝ) = c at hcard ⊢
  refine ⟨Ex, hcard.trans (le_of_eq ?_), hgood⟩
  norm_num

-- Theorem 7.1 at `q₀ = 2⁸`, `k = 1`, `d = 64`, `η = 1/4`: the error is at most
-- `16 / q + 2⁵⁶ / q²`.
example {K₀ F : Type*} [Field K₀] [Fintype K₀] [Field F] [Fintype F] [DecidableEq F]
    [Algebra K₀ F] (hK : Fintype.card K₀ = 2 ^ 8) :
    affineMcaError K₀ F 1 64 192 1 ≤
      ENNReal.ofReal (16 / Fintype.card F + 2 ^ 56 / (Fintype.card F : ℝ) ^ 2) := by
  have h := affineMcaError_le (K₀ := K₀) (F := F) (k := 1) (d := 64) (η := 1 / 4)
    (by norm_num) (by norm_num) (by rw [hK]; push_cast; rw [sqrt_degreeFraction]; norm_num)
    (by rw [hK]; norm_num)
  rw [hK] at h
  push_cast at h
  rw [sqrt_degreeFraction] at h
  have hA : ⌈((1 : ℝ) / 2 + 1 / 4) * 256 ^ 1⌉₊ = 192 := by norm_num
  rw [hA] at h
  convert h using 2
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  field_simp
  ring

-- At `q₀ = 2⁸`, `k = 2`, `d = 64`, `η = 1/4`, `q = 2⁶⁴`, at most `4 q / η + 2²⁰ n³ / (ρ⁴ η¹⁴)`,
-- that is `2⁶⁸ + 2¹⁰⁴`, coefficient vectors carry an exceptional candidate.
example {K₀ F : Type*} [Field K₀] [Fintype K₀] [Field F] [Fintype F] [DecidableEq F]
    [Algebra K₀ F] (hK : Fintype.card K₀ = 2 ^ 8) (hF : Fintype.card F = 2 ^ 64)
    (f g : (Fin 2 → K₀) → F) :
    ∃ Ex : Finset (Fin 3 → F), (Ex.card : ℝ) ≤ 2 ^ 68 + 2 ^ 104 ∧
      ∀ α ∉ Ex, ∀ P, ¬ IsAffineExceptional f g 64 49152 (2 ^ 8) α P := by
  obtain ⟨Ex, hcard, hgood⟩ := exists_affineExceptional_finset_card_le (k := 2) f g
    (d := 64) (η := 1 / 4) (by norm_num) (by norm_num)
    (by rw [hK]; push_cast; rw [sqrt_degreeFraction]; norm_num) (by rw [hK]; norm_num)
  rw [hK] at hcard hgood
  rw [hF] at hcard
  push_cast at hcard hgood
  rw [sqrt_degreeFraction] at hgood
  have hA : ⌈((1 : ℝ) / 2 + 1 / 4) * 256 ^ 2⌉₊ = 49152 := by norm_num
  rw [hA] at hgood
  exact ⟨Ex, hcard.trans (by norm_num), fun α hα P ↦ by simpa using hgood α hα P⟩

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable instance : Fintype (GaloisField 2 8) := Fintype.ofFinite _

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private noncomputable instance : DecidableEq (GaloisField 2 64) := Classical.decEq _

private noncomputable instance : SampleableType (GaloisField 2 64) :=
  SampleableType.ofFintype _

/-- `𝔽_{2⁸}` embeds in `𝔽_{2⁶⁴}`, since `8` divides `64`. -/
private noncomputable instance : Algebra (GaloisField 2 8) (GaloisField 2 64) :=
  (Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 8) (L := GaloisField 2 64) (by
      rw [GaloisField.finrank 2 (by norm_num), GaloisField.finrank 2 (by norm_num)]
      norm_num))).toRingHom.toAlgebra

private theorem card_subfield : Fintype.card (GaloisField 2 8) = 2 ^ 8 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 8 (by norm_num)]

private theorem card_field : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

-- The worked case over the concrete fields `𝔽_{2⁸} ⊆ 𝔽_{2⁶⁴}`.
private theorem galoisField_error_le :
    affineMcaError (GaloisField 2 8) (GaloisField 2 64) 2 64 49152 (2 ^ 8) ≤
      ENNReal.ofReal (2⁻¹ ^ 124 + 2⁻¹ ^ 88) := by
  have h := affineMcaError_le (K₀ := GaloisField 2 8) (F := GaloisField 2 64) (k := 2)
    (d := 64) (η := 1 / 4) (by norm_num) (by norm_num)
    (by rw [card_subfield]; push_cast; rw [sqrt_degreeFraction]; norm_num)
    (by rw [card_subfield]; norm_num)
  rw [card_subfield, card_field] at h
  push_cast at h
  rw [sqrt_degreeFraction] at h
  have hA : ⌈((1 : ℝ) / 2 + 1 / 4) * 256 ^ 2⌉₊ = 49152 := by norm_num
  rw [hA] at h
  convert h using 2
  norm_num

open scoped ProbabilityTheory in
-- The same bound holds for each word pair under native uniform sampling of `α ∈ 𝔽_{2⁶⁴}³`.
example (f g : (Fin 2 → GaloisField 2 8) → GaloisField 2 64) :
    Pr{let α ← $ᵗ (Fin 3 → GaloisField 2 64)}[∃ P,
      IsAffineExceptional f g 64 49152 (2 ^ 8) α P] ≤ ENNReal.ofReal (2⁻¹ ^ 124 + 2⁻¹ ^ 88) :=
  (prob_isAffineExceptional_le f g 64 49152 (2 ^ 8)).trans galoisField_error_le

/-- info: 'ReedMuller.exists_affineExceptional_finset_card_le_of_interpolation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_affineExceptional_finset_card_le_of_interpolation

/-- info: 'ReedMuller.affineMcaError_le_of_interpolation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_le_of_interpolation

/-- info: 'ReedMuller.exists_affineExceptional_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_affineExceptional_finset_card_le

/-- info: 'ReedMuller.affineMcaError_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_le
