/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.UniformEnvelope

/-! # Uniform interpolation with the sharper jet cap and height `150ν` -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial PolynomialDifferential

universe u

/-- The shared envelope yields a nonvanishing equation with the exact uniform integer budgets. -/
theorem UniformRatePartitionEnvelope.exists_curve_certificate {F : Type u} [Field F]
    {δ : ℝ} {n k A ℓ : ℕ} (e : UniformRatePartitionEnvelope δ n k A)
    (hδ : 0 < δ) (hδone : δ < 1) (hd : 500 ≤ uniformRatePartitionOrder δ)
    (hn : uniformRatePartitionLength δ ≤ n) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ
      (uniformRatePartitionJetBound δ) (uniformRatePartitionOrder δ)
      (ℓ * (150 * uniformRatePartitionJetBound δ)) domain w) := by
  have hmpos : 0 < uniformRatePartitionMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionClosedMultiplicity_ge_order hd)
  have hν := (uniformRatePartition_integer_guards hδ hδone hmpos hn).2.2.1
  have hD : 0 < e.ambientDegree := by have := e.order_le; omega
  have hnpos : 0 < n := by have := e.ambient_le; omega
  have hW := (ratePartition_closed_floor_bounds e.rate_pos e.rate_lt_agreement hd).2.1
  obtain ⟨cert⟩ := exists_ratePartitionFinite_certificate hD hd hmpos hnpos e.rate_pos
    (e.rate_pos.trans e.rate_lt_agreement) hW e.message_le e.rate_upper e.agreement_lower
    domain w hw (fun _ hu ↦ uniformRatePartition_totalJetDegree_le hδ hD e.ambient_lower hAn hu)
    (by norm_num : (1 : ℝ) < 151 / 150) e.ratio_gt.le
  simpa only [ratePartitionHeight_uniform hν] using (show Nonempty _ from ⟨cert⟩)

end ReedSolomon.HiddenDerivative
