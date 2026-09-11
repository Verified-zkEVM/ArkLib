/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.MathematicalUniform

/-! # Uniform interpolation for the revised 300-based mathematical recipe -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial PolynomialDifferential

universe u

/-- The revised mathematical envelope yields a nonvanishing equation with the same sharp jet
cap and integral height as the retained executable recipe. This theorem changes only the
mathematical interpolation multiplicity; it does not alter the reference executor. -/
theorem MathematicalRatePartitionEnvelope.exists_curve_certificate
    {F : Type u} [Field F]
    {δ : ℝ} {n k A ℓ : ℕ} (e : MathematicalRatePartitionEnvelope δ n k A)
    (hδ : 0 < δ) (hδone : δ < 1) (hd : 519 ≤ uniformRatePartitionOrder δ)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ
      (uniformRatePartitionMathematicalJetBound δ) (uniformRatePartitionOrder δ)
      (ℓ * (150 * uniformRatePartitionMathematicalJetBound δ)) domain w) := by
  have hmpos : 0 < uniformRatePartitionMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionMathematicalMultiplicity_ge_order hd)
  have hν :=
    (uniformRatePartitionMathematical_integer_guards hδ hδone hmpos hn).2.2.1
  have hD : 0 < e.ambientDegree := by have := e.order_le; omega
  have hnpos : 0 < n := by have := e.ambient_le; omega
  have hW := (ratePartition_mathematical_floor_bounds e.rate_pos
    e.rate_lt_agreement hd).2.1
  obtain ⟨cert⟩ := exists_ratePartitionFinite_certificate hD (by omega) hmpos hnpos
    e.rate_pos (e.rate_pos.trans e.rate_lt_agreement) hW e.message_le e.rate_upper
    e.agreement_lower domain w hw
    (fun _ hu ↦ uniformRatePartitionMathematical_totalJetDegree_le
      hδ hD e.ambient_lower hAn hu)
    (by norm_num : (1 : ℝ) < 151 / 150) e.ratio_gt.le
  simpa only [ratePartitionHeight_uniform hν] using (show Nonempty _ from ⟨cert⟩)

end ReedSolomon.HiddenDerivative
