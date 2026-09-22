/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank

/-!
# Weighted support local rank acceptance tests

* At `d = 1`, `D = 2`, `L = 4`, `m = 2`, `W = 0` the jet-degree cutoff is `⌈4 / 2⌉₊ = 2` and the
  local rank on the weighted support space is at most `4`.
* The support bound needs `0 < D`: at `D = 0` the constant `1` is eligible with cutoff `1`, its
  local constraint of order `1` contains the monomial `1`, and the jet-degree bound
  `0 < 1 / 0 = 0` fails. (The space itself requires `0 < D`, so the counterexample is stated
  through eligibility.)
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `d = 1`, `D = 2`, `L = 4`, `m = 2`, `W = 0` the local rank is at most `4`. -/
example (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range (weightedSupportLocalConstraint (d := 1) (W := 0)
      (L := 4) 2 (by norm_num : 0 < 2) center received)) ≤ 4 := by
  have hceil : ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have h := finrank_weightedSupportLocalConstraint_le (D := 2) (d := 1) (W := 0) (L := 4)
    (m := 2) Nat.one_pos (by norm_num) center received
  rw [hceil] at h
  exact h.trans (by decide)

/-- The jet-degree conclusion of `weightedSupport_localConstraint_support` fails at `D = 0`: the
constant `1` has only the eligible exponent `0`, and its local constraint of order `1` contains
the monomial `1`, whose jet degree `0` is not below `1 / 0 = 0`. -/
example : (∀ u ∈ (1 : DifferentialPolynomial ℚ 1).support, WeightedSupportEligible 0 1 0 1 u) ∧
    ∃ e ∈ (localConstraintAt 1 (0 : ℚ) 0 1).support,
      ¬ ((e.weight (localJetDegreeWeight 1) : ℝ) < 1 / ((0 : ℕ) : ℝ)) := by
  refine ⟨fun u hu => ?_, 0, ?_, by simp⟩
  · rw [show (1 : DifferentialPolynomial ℚ 1) = monomial 0 1 from rfl] at hu
    obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hu)
    simp [WeightedSupportEligible, fullHigherJetWeight]
  · rw [mem_support_iff, localConstraintAt, LinearMap.comp_apply, coeff_projectLowContact]
    simp [localContactOrder]
