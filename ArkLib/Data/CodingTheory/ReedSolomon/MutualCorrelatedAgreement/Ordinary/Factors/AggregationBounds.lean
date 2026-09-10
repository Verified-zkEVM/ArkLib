/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.FactorBounds
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
/-!
# Aggregating ordinary factor charges

Distinct factors spend their coordinate degrees additively. This calculation includes the
root-independent content and controls the sum of height-times-root-degree products by the
original total degree budgets.
-/

@[expose] public section

namespace ReedSolomon

open scoped BigOperators

/-- The ordinary positive-root-degree factor charge. -/
def ordinaryFactorRaw (theta : ℚ) (n D a h : ℕ) : ℚ :=
  ((2 * a - 1) * h : ℕ) + theta * (h + a + 4 * D * a * h : ℕ) +
    ((n - D - 1) * a : ℕ)

/-- A pulled factor spends only its original root degree `s*b`, with no extra power loss. -/
theorem ordinaryFrobenius_charge_le (theta : ℚ) (n D h s b : ℕ)
    (htheta : 0 ≤ theta) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusMixedDegree D h s b +
        ((n - D - 1) * b : ℕ) ≤ ordinaryFactorRaw theta n D (s * b) h := by
  have hbs : b ≤ s * b := by nlinarith
  unfold ordinaryFactorRaw
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h (Nat.sub_le_sub_right
        (Nat.mul_le_mul_left 2 hbs) 1)
    · apply mul_le_mul_of_nonneg_left _ htheta
      have hmixed := ordinaryFrobeniusMixedDegree_le D h s b hb
      rw [show 4 * D * h * (s * b) = 4 * D * (s * b) * h by ring] at hmixed
      exact_mod_cast hmixed
  · exact_mod_cast Nat.mul_le_mul_left (n - D - 1) hbs

/-- Content plus every distinct positive-degree factor fits in the original ordinary budget. -/
theorem ordinaryFactorRaw_sum_le {I : Type*} (S : Finset I) (a height : I → ℕ)
    (theta : ℚ) (n D mu H contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (ha : ∑ i ∈ S, a i ≤ mu)
    (hh : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) + ∑ i ∈ S, ordinaryFactorRaw theta n D (a i) (height i) ≤
      ordinaryFactorRaw theta n D mu H := by
  let c : ℚ := (2 * mu - 1 : ℕ) + theta * (1 + 4 * D * mu)
  let d : ℚ := theta + (n - D - 1 : ℕ)
  have hc : 1 ≤ c := by
    have hnat : 1 ≤ 2 * mu - 1 := by omega
    have hcast : (1 : ℚ) ≤ (2 * mu - 1 : ℕ) := by exact_mod_cast hnat
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hterm (i : I) (hi : i ∈ S) :
      ordinaryFactorRaw theta n D (a i) (height i) ≤ c * height i + d * a i := by
    have hai : a i ≤ mu := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans ha
    have hsub : 2 * a i - 1 ≤ 2 * mu - 1 := by omega
    have hfirst : (((2 * a i - 1) * height i : ℕ) : ℚ) ≤
        (2 * mu - 1 : ℕ) * (height i : ℚ) := by exact_mod_cast Nat.mul_le_mul_right (height i) hsub
    have hprod : ((a i : ℚ) * height i) ≤ (mu : ℚ) * height i := by gcongr
    unfold ordinaryFactorRaw
    push_cast
    dsimp [c, d]
    push_cast at hfirst ⊢
    nlinarith [mul_nonneg htheta (mul_nonneg (show (0 : ℚ) ≤ 4 * D by positivity)
      (sub_nonneg.mpr hprod))]
  have hsum := Finset.sum_le_sum hterm
  have hcontent : (contentHeight : ℚ) ≤ c * contentHeight := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg contentHeight)
  have hhQ : (contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ) ≤ H := by exact_mod_cast hh
  have haQ : (∑ i ∈ S, (a i : ℚ)) ≤ mu := by exact_mod_cast ha
  calc
    (contentHeight : ℚ) + ∑ i ∈ S, ordinaryFactorRaw theta n D (a i) (height i) ≤
        c * contentHeight + ∑ i ∈ S, (c * height i + d * a i) := add_le_add hcontent hsum
    _ = c * ((contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ)) +
        d * ∑ i ∈ S, (a i : ℚ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ c * H + d * mu := add_le_add (mul_le_mul_of_nonneg_left hhQ hc0)
      (mul_le_mul_of_nonneg_left haQ hd0)
    _ = ordinaryFactorRaw theta n D mu H := by
      dsimp [c, d, ordinaryFactorRaw]
      push_cast
      ring

end ReedSolomon
