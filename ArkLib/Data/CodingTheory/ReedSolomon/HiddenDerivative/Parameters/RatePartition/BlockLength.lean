/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FiniteRatio
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.Basic

/-!
# Finite block-length guards for the Gamma construction

The threshold keeps ambient degree, jet budget, and quadratic-extension work
conditions strictly below the block length while allowing field size equal to it.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The rate-dependent jet degree cap. The executable strict budget is one larger. -/
def rateJetCap (rate : ℝ) (multiplicity : ℕ) : ℕ := ⌈2 * (multiplicity : ℝ) / rate⌉₊

/-- The variable-margin per-unit-curve height budget. -/
def rateHeight (rate agreement : ℝ) (order multiplicity : ℕ) : ℕ :=
  max 1 ⌈(rateJetCap rate multiplicity : ℝ) /
    (finiteGamma rate agreement order multiplicity - 1)⌉₊

/-- A positive multiplicity gives a positive jet cap independently of block length. -/
theorem rateJetCap_pos {rate : ℝ} {multiplicity : ℕ}
    (hrate : 0 < rate) (hm : 0 < multiplicity) : 0 < rateJetCap rate multiplicity := by
  apply (Nat.cast_pos (α := ℝ)).mp
  exact (show (0 : ℝ) < 2 * multiplicity / rate by positivity).trans_le (Nat.le_ceil _)

/-- The explicit block-length threshold in the arbitrary strict-Gamma theorem. -/
def rateBlockThreshold (rate : ℝ) (order multiplicity : ℕ) : ℕ :=
  ⌈max (2 * ((order : ℝ) + 2) / rate)
    (max (4 * (multiplicity : ℝ) / rate)
      (max (2 / (1 - rate)) (max ((rateJetCap rate multiplicity : ℝ) + 1) 2)))⌉₊

/-- Each term of the exact maximum is bounded by every admissible block length. -/
theorem rateBlockThreshold_guards {rate : ℝ} {order multiplicity n : ℕ}
    (hn : rateBlockThreshold rate order multiplicity ≤ n) :
    2 * ((order : ℝ) + 2) / rate ≤ n ∧ 4 * (multiplicity : ℝ) / rate ≤ n ∧
      2 / (1 - rate) ≤ n ∧ (rateJetCap rate multiplicity : ℝ) + 1 ≤ n ∧ (2 : ℝ) ≤ n := by
  have hmax := (Nat.le_ceil (max (2 * ((order : ℝ) + 2) / rate)
    (max (4 * (multiplicity : ℝ) / rate)
      (max (2 / (1 - rate)) (max ((rateJetCap rate multiplicity : ℝ) + 1) 2))))).trans
    (show (rateBlockThreshold rate order multiplicity : ℝ) ≤ n by exact_mod_cast hn)
  simpa only [max_le_iff] using hmax

/-- Ambient and jet guards derived from the explicit maximum, rather than assumed. -/
theorem rateBlockThreshold_ambient {rate : ℝ} {order multiplicity n k : ℕ}
    (hrate : 0 < rate) (hrateOne : rate < 1)
    (hn : rateBlockThreshold rate order multiplicity ≤ n) (hk : (k : ℝ) ≤ rate * n) :
    let ambient := ⌊rate * n⌋₊
    order + 1 ≤ ambient ∧ rate * n / 2 ≤ ambient ∧ k ≤ ambient ∧
      ambient + 1 ≤ n ∧ rateJetCap rate multiplicity < n ∧ 2 * multiplicity ≤ n ∧ 0 < n := by
  obtain ⟨horder, hmult, hrateGap, hjet, htwo⟩ := rateBlockThreshold_guards hn
  have hnReal : (0 : ℝ) < n := by linarith
  have hRn : 0 ≤ rate * n := by positivity
  have horderScaled := (div_le_iff₀ hrate).mp horder
  have hmultScaled := (div_le_iff₀ hrate).mp hmult
  have hgapScaled := (div_le_iff₀ (sub_pos.mpr hrateOne)).mp hrateGap
  have hfloorLower := Nat.lt_floor_add_one (rate * n)
  have hfloorUpper := Nat.floor_le hRn
  have horderFloor : order + 1 ≤ ⌊rate * n⌋₊ := by
    apply (Nat.le_floor_iff hRn).mpr
    push_cast
    nlinarith
  have hhalf : rate * n / 2 ≤ (⌊rate * n⌋₊ : ℝ) := by nlinarith
  have hkFloor : k ≤ ⌊rate * n⌋₊ := (Nat.le_floor_iff hRn).mpr hk
  have hfloorN : ⌊rate * n⌋₊ + 1 ≤ n := by
    have : (⌊rate * n⌋₊ : ℝ) + 1 ≤ n := by nlinarith
    exact_mod_cast this
  have hjetN : rateJetCap rate multiplicity < n := by exact_mod_cast hjet
  have hmultN : 2 * multiplicity ≤ n := by
    have : (2 : ℝ) * multiplicity ≤ n := by nlinarith
    exact_mod_cast this
  exact ⟨horderFloor, hhalf, hkFloor, hfloorN, hjetN, hmultN, Nat.cast_pos.mp hnReal⟩

/-- The actual support admits the new jet cap at every admissible block length. -/
theorem partitionSupport_totalJetDegree_le_rateJetCap {rate : ℝ} {D d W m n A : ℕ}
    (hrate : 0 < rate) (hn : 0 < n) (hD : rate * n / 2 ≤ D) (hA : A ≤ n)
    {exponent : PolynomialDifferential.JetVariable d →₀ ℕ}
    (heligible : PartitionSupportEligible D d W (m * A : ℕ) exponent) :
    totalJetDegree exponent ≤ rateJetCap rate m := by
  have hnat : D * totalJetDegree exponent < m * A := by
    have hcutoff := heligible.2
    exact_mod_cast (lt_of_le_of_lt
      (show ((D * totalJetDegree exponent : ℕ) : ℝ) ≤
        ((exponent none + D * totalJetDegree exponent : ℕ) : ℝ) by
          exact_mod_cast Nat.le_add_left (D * totalJetDegree exponent) _)
      hcutoff)
  have hbound : (D : ℝ) * totalJetDegree exponent < (m : ℝ) * n := by
    exact_mod_cast hnat.trans_le (Nat.mul_le_mul_left m hA)
  have hmul := mul_le_mul_of_nonneg_right hD
    (Nat.cast_nonneg (totalJetDegree exponent))
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcap : (totalJetDegree exponent : ℝ) < 2 * m / rate := by
    apply (lt_div_iff₀ hrate).mpr
    nlinarith
  exact Nat.cast_le.mp (hcap.le.trans (Nat.le_ceil _))

/-- Rounded agreement lies below every integer agreement meeting the real threshold. -/
theorem rate_ceil_agreement_bounds {agreement : ℝ} {n A : ℕ}
    (hagreement : 0 < agreement) (hn : 0 < n) (hA : agreement * n ≤ A) (hAn : A ≤ n) :
    0 < ⌈agreement * n⌉₊ ∧ agreement * n ≤ ⌈agreement * n⌉₊ ∧
      ⌈agreement * n⌉₊ ≤ A ∧ ⌈agreement * n⌉₊ ≤ n := by
  have hceil := Nat.le_ceil (agreement * n)
  have hpositive : 0 < ⌈agreement * n⌉₊ := Nat.cast_pos.mp
    ((mul_pos hagreement (Nat.cast_pos.mpr hn)).trans_le hceil)
  have hle : ⌈agreement * n⌉₊ ≤ A := Nat.ceil_le.mpr hA
  exact ⟨hpositive, hceil, hle, hle.trans hAn⟩

end ReedSolomon.HiddenDerivative.RatePartition
