/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Block-length thresholds and heights for the rate-dependent partition construction

At code rate `R`, derivative order `d` and multiplicity `m`, the rate-dependent partition
construction interpolates with ambient degree `D = ⌊R n⌋₊` at block length `n`. Weighted support
bounds the total jet degree of an interpolation monomial by the cap `⌈2m / R⌉₊`. This file
defines two block-length thresholds and proves that every block length above them satisfies the
guards the construction needs:

* `rateBlockThreshold R d m = ⌈max ((d + 1)/R, cap + 1, 1/(1 - R))⌉₊` gives
  `d + 1 ≤ D`, `R n / 2 ≤ D`, `D + 1 ≤ n`, `cap < n`, `2m < n` and `2 ≤ n`;
* `paddedRateBlockThreshold R d m`, the larger threshold
  `⌈max (2(d + 2)/R, 4m/R, 2/(1 - R), cap + 1, 2)⌉₊`, gives the same guards.

Both also give `k ≤ D` for a message dimension `k ≤ R n` and `⌈a n⌉₊ ≤ A` for an agreement
`a n ≤ A`.

The height of a curve family is chosen from a certified ratio `γ > 1` as
`marginHeight ν γ = max 1 ⌈ν / (γ - 1)⌉₊`; at `γ = 1 + 1/k` it is exactly `k ν`.

## Main definitions

* `rateJetCap`, `rateBlockThreshold`, `paddedRateBlockThreshold`, `marginHeight`.

## Main statements

* `rateBlockThreshold_guards`, `paddedRateBlockThreshold_guards`: the guards above.
* `marginHeight_one_add_inv`: `marginHeight ν (1 + 1/k) = k ν` for positive `k` and `ν`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The total-jet-degree cap `⌈2m / R⌉₊` at code rate `R` and multiplicity `m`. -/
def rateJetCap (rate : ℝ) (multiplicity : ℕ) : ℕ := ⌈2 * (multiplicity : ℝ) / rate⌉₊

/-- The block-length threshold `⌈max ((d + 1)/R, ⌈2m/R⌉₊ + 1, 1/(1 - R))⌉₊` at code rate `R`,
derivative order `d` and multiplicity `m`. -/
def rateBlockThreshold (rate : ℝ) (order multiplicity : ℕ) : ℕ :=
  ⌈max (((order : ℝ) + 1) / rate)
    (max ((rateJetCap rate multiplicity : ℝ) + 1) (1 / (1 - rate)))⌉₊

/-- The padded block-length threshold
`⌈max (2(d + 2)/R, 4m/R, 2/(1 - R), ⌈2m/R⌉₊ + 1, 2)⌉₊` at code rate `R`, derivative order `d`
and multiplicity `m`. -/
def paddedRateBlockThreshold (rate : ℝ) (order multiplicity : ℕ) : ℕ :=
  ⌈max (2 * ((order : ℝ) + 2) / rate)
    (max (4 * (multiplicity : ℝ) / rate)
      (max (2 / (1 - rate)) (max ((rateJetCap rate multiplicity : ℝ) + 1) 2)))⌉₊

/-- The height `max 1 ⌈ν / (γ - 1)⌉₊` chosen from a bound `ν` and a ratio `γ`. It is positive
for every input; it is meaningful when `γ > 1`. -/
def marginHeight (bound : ℕ) (ratio : ℝ) : ℕ := max 1 ⌈(bound : ℝ) / (ratio - 1)⌉₊

/-- The jet-degree cap is positive at positive rate and multiplicity. -/
theorem rateJetCap_pos {rate : ℝ} {multiplicity : ℕ} (hrate : 0 < rate)
    (hmultiplicity : 0 < multiplicity) : 0 < rateJetCap rate multiplicity :=
  Nat.lt_ceil.mpr (by norm_num; positivity)

/-- A block length `n ≥ rateBlockThreshold R d m` with `0 < R < 1` satisfies, for
`D = ⌊R n⌋₊`, the guards `d + 1 ≤ D`, `R n / 2 ≤ D`, `k ≤ D`, `D + 1 ≤ n`, `⌈2m/R⌉₊ < n`,
`2m < n`, `⌈a n⌉₊ ≤ A` and `2 ≤ n`, where `k ≤ R n` and `a n ≤ A`. -/
theorem rateBlockThreshold_guards {rate agreement : ℝ} {order multiplicity n k A : ℕ}
    (hrate : 0 < rate) (hrateOne : rate < 1)
    (hn : rateBlockThreshold rate order multiplicity ≤ n)
    (hk : (k : ℝ) ≤ rate * n) (hA : agreement * n ≤ A) :
    order + 1 ≤ ⌊rate * n⌋₊ ∧ rate * n / 2 ≤ ⌊rate * n⌋₊ ∧ k ≤ ⌊rate * n⌋₊ ∧
      ⌊rate * n⌋₊ + 1 ≤ n ∧ rateJetCap rate multiplicity < n ∧ 2 * multiplicity < n ∧
      ⌈agreement * n⌉₊ ≤ A ∧ 2 ≤ n := by
  have hbound := (Nat.le_ceil (max (((order : ℝ) + 1) / rate)
    (max ((rateJetCap rate multiplicity : ℝ) + 1) (1 / (1 - rate))))).trans
    (show (rateBlockThreshold rate order multiplicity : ℝ) ≤ n by exact_mod_cast hn)
  simp only [max_le_iff] at hbound
  obtain ⟨horderBound, hcapBound, hgapBound⟩ := hbound
  have hrn : 0 ≤ rate * (n : ℝ) := by positivity
  have horderScaled : (order : ℝ) + 1 ≤ rate * n := by
    simpa [mul_comm] using (div_le_iff₀ hrate).mp horderBound
  have hgap : 1 ≤ (1 - rate) * (n : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ (sub_pos.mpr hrateOne)).mp hgapBound
  have hfloorLower := Nat.lt_floor_add_one (rate * (n : ℝ))
  have hfloorUpper := Nat.floor_le hrn
  have hD : order + 1 ≤ ⌊rate * n⌋₊ := (Nat.le_floor_iff hrn).mpr (by simpa using horderScaled)
  have hDone : (1 : ℝ) ≤ ⌊rate * n⌋₊ := by exact_mod_cast (show 1 ≤ ⌊rate * n⌋₊ by omega)
  have hone : (1 : ℝ) ≤ rate * n := by linarith [Nat.cast_nonneg order (α := ℝ)]
  have hrateN : rate * (n : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
  refine ⟨hD, by linarith, Nat.le_floor hk, ?_, ?_, ?_, Nat.ceil_le.mpr hA, ?_⟩
  · exact_mod_cast (show (⌊rate * n⌋₊ : ℝ) + 1 ≤ n by linarith)
  · exact_mod_cast (show (rateJetCap rate multiplicity : ℝ) < n by linarith)
  · have hcap : 2 * (multiplicity : ℝ) / rate ≤ rateJetCap rate multiplicity := Nat.le_ceil _
    have hscaled : 2 * (multiplicity : ℝ) ≤ 2 * multiplicity / rate := by
      rw [le_div_iff₀ hrate]
      nlinarith [Nat.cast_nonneg multiplicity (α := ℝ)]
    exact_mod_cast (show 2 * (multiplicity : ℝ) < n by linarith)
  · exact_mod_cast (show (2 : ℝ) ≤ n by linarith)

/-- A block length `n ≥ paddedRateBlockThreshold R d m` with `0 < R < 1` satisfies, for
`D = ⌊R n⌋₊`, the guards `d + 1 ≤ D`, `R n / 2 ≤ D`, `k ≤ D`, `D + 1 ≤ n`, `⌈2m/R⌉₊ < n`,
`2m < n`, `⌈a n⌉₊ ≤ A` and `2 ≤ n`, where `k ≤ R n` and `a n ≤ A`. -/
theorem paddedRateBlockThreshold_guards {rate agreement : ℝ} {order multiplicity n k A : ℕ}
    (hrate : 0 < rate) (hrateOne : rate < 1)
    (hn : paddedRateBlockThreshold rate order multiplicity ≤ n)
    (hk : (k : ℝ) ≤ rate * n) (hA : agreement * n ≤ A) :
    order + 1 ≤ ⌊rate * n⌋₊ ∧ rate * n / 2 ≤ ⌊rate * n⌋₊ ∧ k ≤ ⌊rate * n⌋₊ ∧
      ⌊rate * n⌋₊ + 1 ≤ n ∧ rateJetCap rate multiplicity < n ∧ 2 * multiplicity < n ∧
      ⌈agreement * n⌉₊ ≤ A ∧ 2 ≤ n := by
  have hbound := (Nat.le_ceil (max (2 * ((order : ℝ) + 2) / rate)
    (max (4 * (multiplicity : ℝ) / rate)
      (max (2 / (1 - rate)) (max ((rateJetCap rate multiplicity : ℝ) + 1) 2))))).trans
    (show (paddedRateBlockThreshold rate order multiplicity : ℝ) ≤ n by exact_mod_cast hn)
  simp only [max_le_iff] at hbound
  obtain ⟨horderBound, hmultiplicityBound, hgapBound, hcapBound, htwo⟩ := hbound
  have hrn : 0 ≤ rate * (n : ℝ) := by positivity
  have hfloorUpper := Nat.floor_le hrn
  have hfloorLower := Nat.lt_floor_add_one (rate * (n : ℝ))
  have horderScaled : 2 * ((order : ℝ) + 2) ≤ rate * n := by
    simpa [mul_comm] using (div_le_iff₀ hrate).mp horderBound
  have hmultiplicityScaled : 4 * (multiplicity : ℝ) ≤ rate * n := by
    simpa [mul_comm] using (div_le_iff₀ hrate).mp hmultiplicityBound
  have hgap : 2 ≤ (1 - rate) * (n : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ (sub_pos.mpr hrateOne)).mp hgapBound
  refine ⟨?_, by linarith, Nat.le_floor hk, ?_, ?_, ?_, Nat.ceil_le.mpr hA, ?_⟩
  · exact_mod_cast (show (order : ℝ) + 1 ≤ ⌊rate * n⌋₊ by linarith)
  · exact_mod_cast (show (⌊rate * n⌋₊ : ℝ) + 1 ≤ n by linarith)
  · exact_mod_cast (show (rateJetCap rate multiplicity : ℝ) < n by linarith)
  · have hrateN : rate * (n : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast (show 2 * (multiplicity : ℝ) < n by linarith)
  · exact_mod_cast htwo

/-- At the ratio `1 + 1/k`, the margin height of a bound `ν` is `k ν`, for positive `k`
and `ν`. -/
theorem marginHeight_one_add_inv {bound k : ℕ} (hbound : 0 < bound) (hk : 0 < k) :
    marginHeight bound (1 + 1 / (k : ℝ)) = k * bound := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hquotient : (bound : ℝ) / (1 + 1 / (k : ℝ) - 1) = ((k * bound : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  unfold marginHeight
  rw [hquotient, Nat.ceil_natCast]
  exact max_eq_right (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hk.ne' hbound.ne'))

end ReedSolomon.HiddenDerivative.RatePartition
