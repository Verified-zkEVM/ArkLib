/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite parameters for the rate-dependent partition gate

For rate envelope R and agreement fraction a, the limiting dimension/rank ratio
is `Γ = (27/20)R(d+1)/(6d)^(R/a)`. A multiplicity m determines an integer
derivative-weight budget W and a finite ratio with the explicit floor and rank
losses. A strict gate requires choosing m from its margin; the closed uniform
multiplicity is justified only after the stronger uniform margin is proved.

All executed inputs are natural numbers. Real parameters here select and certify
those inputs; they are not representations of executable real-number arithmetic.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- The limiting source/rank ratio for the derivative-order partition support. -/
def ratePartitionGamma (R a : ℝ) (d : ℕ) : ℝ :=
  (27 / 20) * R * (d + 1) / (6 * d : ℝ) ^ (R / a)

/-- Integer derivative-weight budget at multiplicity m. -/
def ratePartitionWeight (R a : ℝ) (d m : ℕ) : ℕ :=
  ⌊(m : ℝ) * a * d / (R * Real.log (6 * d))⌋₊

/-- The finite source/rank lower ratio, including all rounding terms. -/
def ratePartitionFiniteRatio (R a : ℝ) (d m : ℕ) : ℝ :=
  let w := (ratePartitionWeight R a d m : ℝ) / m
  let lam := (d : ℝ) / w
  let S := (d : ℝ) * (d + 1) / 2
  (27 / 20) * R * (d + 1) * Real.exp (-lam * (1 + S / m)) /
    (1 + (d + 1) * lam / m)

/-- Closed multiplicity used only under the uniform strict ratio margin. -/
def ratePartitionClosedMultiplicity (d : ℕ) : ℕ :=
  ⌈1000 * (d : ℝ) ^ 2 * Real.log (6 * d)⌉₊

/-- A safe weak total-jet-degree bound for the general rate envelope. -/
def ratePartitionJetBound (R : ℝ) (m : ℕ) : ℕ := ⌈2 * (m : ℝ) / R⌉₊

/-- The explicit block threshold for the general rate construction. -/
def ratePartitionLength (R : ℝ) (d m : ℕ) : ℕ :=
  ⌈max (2 * ((d : ℝ) + 2) / R)
    (max (4 * (m : ℝ) / R)
      (max (2 / (1 - R)) (max ((ratePartitionJetBound R m : ℝ) + 1) 2)))⌉₊

/-- A symbolic height chosen from any certified real ratio above one. -/
def ratePartitionHeight (ν : ℕ) (γ : ℝ) : ℕ := max 1 ⌈(ν : ℝ) / (γ - 1)⌉₊

/-- The factor 27/20 is exactly half the positive-part second-moment constant. -/
theorem ratePartition_moment_normalization : (27 / 10 : ℝ) / 2 = 27 / 20 := by
  norm_num

/-- The finite block threshold gives every ambient, jet, and quadratic-extension guard.
Actual messages retain dimension k even though interpolation uses floor(Rn)+1. -/
theorem ratePartition_length_guards {R a : ℝ} {d m n k A : ℕ}
    (hR : 0 < R) (hRone : R < 1)
    (hn : ratePartitionLength R d m ≤ n)
    (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) :
    let D := ⌊R * n⌋₊
    d + 1 ≤ D ∧ R * n / 2 ≤ D ∧ k ≤ D ∧ D + 1 ≤ n ∧
      ratePartitionJetBound R m < n ∧ 2 * m ≤ n ∧
      ⌈a * n⌉₊ ≤ A ∧ 2 ≤ n := by
  have hnR : (ratePartitionLength R d m : ℝ) ≤ n := by exact_mod_cast hn
  have hb := (Nat.le_ceil (max (2 * ((d : ℝ) + 2) / R)
    (max (4 * (m : ℝ) / R)
      (max (2 / (1 - R)) (max ((ratePartitionJetBound R m : ℝ) + 1) 2))))).trans hnR
  have hb₁ : 2 * ((d : ℝ) + 2) / R ≤ n := (le_max_left _ _).trans hb
  have hb₂ : 4 * (m : ℝ) / R ≤ n :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hb
  have hb₃ : 2 / (1 - R) ≤ n :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hb
  have hb₄ : (ratePartitionJetBound R m : ℝ) + 1 ≤ n :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))).trans hb
  have hb₅ : (2 : ℝ) ≤ n :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))).trans hb
  have hRn : 0 ≤ R * (n : ℝ) := by positivity
  have hfloor := Nat.floor_le hRn
  have hfloor' := Nat.lt_floor_add_one (R * (n : ℝ))
  have hlarge : 2 * ((d : ℝ) + 2) ≤ R * n := by
    simpa [mul_comm] using (div_le_iff₀ hR).mp hb₁
  have hm' : 4 * (m : ℝ) ≤ R * n := by
    simpa [mul_comm] using (div_le_iff₀ hR).mp hb₂
  have hspace : 2 ≤ (1 - R) * (n : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ (sub_pos.mpr hRone)).mp hb₃
  refine ⟨?_, ?_, Nat.le_floor hkR, ?_, ?_, ?_, Nat.ceil_le.mpr haA, ?_⟩
  · have : (d : ℝ) + 1 ≤ ⌊R * n⌋₊ := by linarith
    exact_mod_cast this
  · linarith
  · have : (⌊R * n⌋₊ : ℝ) + 1 ≤ n := by linarith
    exact_mod_cast this
  · exact_mod_cast (show (ratePartitionJetBound R m : ℝ) < n by linarith)
  · have hRle : R * (n : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    have : (2 : ℝ) * m ≤ n := by nlinarith [Nat.cast_nonneg m (α := ℝ)]
    exact_mod_cast this
  · exact_mod_cast hb₅

end ReedSolomon.HiddenDerivative
