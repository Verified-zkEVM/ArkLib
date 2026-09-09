/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.UniformRateCertificate

/-! # Uniform list decoding with derivative order `ceil(exp(3/(2δ)))` -/

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The uniform small-gap bound uses the actual message dimension in its agreement gap. -/
theorem uniformRatePartition_close_list_bound {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformRatePartitionJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionJetBound δ / δ) ^ uniformRatePartitionOrder δ *
          n ^ uniformRatePartitionOrder δ := by
  obtain ⟨e⟩ := exists_uniformRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_500 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionClosedMultiplicity_ge_order hd)
  obtain ⟨hsize, hmn, hν, hνn⟩ := uniformRatePartition_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  have hchar' : ringChar F = 0 ∨
      max (e.ambientDegree + 1 - 1) (uniformRatePartitionJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hD := e.ambient_le
    exact (max_lt (by omega) hνn).trans_le hc
  exact close_list_bound_of_curve_certificate_of_jetCharacteristic
    domain received cert hk e.message_le
    (by have := e.order_le; omega) e.ambient_le hkA hAn hν hδ hgap hchar'

end ReedSolomon
