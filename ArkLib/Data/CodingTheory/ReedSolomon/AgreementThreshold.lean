/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
/-!
# Integral agreement thresholds and relative capacity gaps

The threshold is `k + ⌈δn⌉`; its real form is `k + δn ≤ A`.
These definitions and rounding lemmas do not choose an interpolation construction.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

/-- The absolute agreement threshold used by the all-rate theorem. -/
def agreementThreshold (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  messageDim + Nat.ceil (delta * (blockLength : ℝ))

/-- The corresponding real-valued radius in ArkLib's `Code.Lambda` convention. -/
def capacityRadius (delta : ℝ) (blockLength messageDim : ℕ) : ℝ :=
  1 - (messageDim : ℝ) / blockLength - delta

/-- The natural agreement threshold is equivalent to its real-valued unrounded inequality. -/
lemma agreementThreshold_le_iff_real {delta : ℝ} (hdelta : 0 ≤ delta)
    (blockLength messageDim agreement : ℕ) :
    agreementThreshold delta blockLength messageDim ≤ agreement ↔
      (messageDim : ℝ) + delta * blockLength ≤ agreement := by
  constructor
  · intro hThreshold
    have hCast :
        ((messageDim + Nat.ceil (delta * (blockLength : ℝ)) : ℕ) : ℝ) ≤ agreement := by
      exact_mod_cast hThreshold
    have hCeil :
        delta * (blockLength : ℝ) ≤ (Nat.ceil (delta * (blockLength : ℝ)) : ℝ) :=
      Nat.le_ceil _
    rw [Nat.cast_add] at hCast
    linarith
  · intro hReal
    have hMessageReal : (messageDim : ℝ) ≤ agreement := by
      have hProduct : 0 ≤ delta * (blockLength : ℝ) :=
        mul_nonneg hdelta (Nat.cast_nonneg blockLength)
      linarith
    have hMessage : messageDim ≤ agreement := by
      exact_mod_cast hMessageReal
    have hRemainder :
        delta * (blockLength : ℝ) ≤ ((agreement - messageDim : ℕ) : ℝ) := by
      rw [Nat.cast_sub hMessage]
      linarith
    have hCeil : Nat.ceil (delta * (blockLength : ℝ)) ≤ agreement - messageDim :=
      Nat.ceil_le.mpr hRemainder
    rw [agreementThreshold]
    omega

/-- Relative distance at the capacity-gap radius is exactly the integral agreement condition.

The distance is written from `received` to `codeword`, while agreement is written from `codeword`
to `received`, matching the two public APIs. Symmetry of Hamming distance reconciles the order. -/
lemma relHammingDist_le_capacityRadius_iff_agreementThreshold_le
    {F : Type*} [DecidableEq F] {delta : ℝ} (hdelta : 0 ≤ delta)
    {blockLength messageDim : ℕ} (hBlockLength : 0 < blockLength)
    (codeword received : Fin blockLength → F) :
    (Code.relHammingDist received codeword : ℝ) ≤
        capacityRadius delta blockLength messageDim ↔
      agreementThreshold delta blockLength messageDim ≤ Code.agree codeword received := by
  rw [agreementThreshold_le_iff_real hdelta]
  rw [Code.relHammingDist_coe]
  simp only [Fintype.card_fin]
  rw [hammingDist_comm received codeword]
  have hLengthReal : (0 : ℝ) < blockLength := by
    exact_mod_cast hBlockLength
  have hAgreementDistance :
      (Code.agree codeword received : ℝ) + (hammingDist codeword received : ℝ) =
        blockLength := by
    have hNat :
        Code.agree codeword received + hammingDist codeword received = blockLength := by
      simpa only [Fintype.card_fin] using
        (Code.agree_add_hammingDist (u := codeword) (v := received))
    exact_mod_cast hNat
  have hRadiusMul :
      capacityRadius delta blockLength messageDim * (blockLength : ℝ) =
        blockLength - messageDim - delta * blockLength := by
    rw [capacityRadius]
    field_simp
  constructor
  · intro hDistance
    have hMul := (div_le_iff₀ hLengthReal).mp hDistance
    rw [hRadiusMul] at hMul
    linarith
  · intro hAgreement
    apply (div_le_iff₀ hLengthReal).mpr
    rw [hRadiusMul]
    linarith

end ReedSolomon
