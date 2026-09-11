/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.SharpRatio
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.GuardedUniform

/-! # Interpolation for the archived guarded `1.489` selector -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial PolynomialDifferential

universe u

/-- The guarded envelope yields a nonvanishing curve equation over every field.  The proof uses
the headline `27/20` source estimate on the headline-order branch and the sharpened `273/200`
estimate on the archived comparison branch. -/
theorem GuardedRatePartitionEnvelope.exists_curve_certificate
    {F : Type u} [Field F]
    {δ : ℝ} {n k A ℓ : ℕ} (e : GuardedRatePartitionEnvelope δ n k A)
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : guardedRatePartitionLength δ ≤ n) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ
      (guardedRatePartitionJetBound δ) (guardedRatePartitionOrder δ)
      (ℓ * (150 * guardedRatePartitionJetBound δ)) domain w) := by
  let d := guardedRatePartitionOrder δ
  let m := guardedRatePartitionMultiplicity δ
  let ν := guardedRatePartitionJetBound δ
  let W := ratePartitionWeight e.rate e.agreement d m
  let r := n * ratePartitionRankBound d m W
  let N := (ratePartitionExponents e.ambientDegree d W (m * A : ℕ)
    (by have := e.order_le; omega)).card
  have hd519 := guardedRatePartitionOrder_ge_519 hδ hδsmall
  have hmpos : 0 < m := by
    dsimp [m]
    exact lt_of_lt_of_le (by omega)
      (ratePartitionMathematicalMultiplicity_ge_order hd519)
  have hδone : δ < 1 := by linarith
  have hν := (guardedRatePartition_integer_guards hδ hδone hmpos hn).2.2.1
  have hD : 0 < e.ambientDegree := by have := e.order_le; omega
  have hnpos : 0 < n := by have := e.ambient_le; omega
  have hW : 0 < W := by
    dsimp [W, d, m]
    exact (ratePartition_mathematical_floor_bounds e.rate_pos
      e.rate_lt_agreement hd519).2.1
  have hs : guardedRatePartitionFiniteRatio δ e.rate e.agreement * r < N := by
    by_cases heq : guardedRatePartitionOrder δ = uniformRatePartitionOrder δ
    · have hs0 := ratePartition_dimension_gt_finiteRatio hD (by omega) hmpos hnpos
        e.rate_pos (e.rate_pos.trans e.rate_lt_agreement) hW e.rate_upper e.agreement_lower
      simpa only [guardedRatePartitionFiniteRatio, heq, if_pos, if_true, r, N, W, d, m,
        Nat.cast_mul, mul_assoc] using hs0
    · have hd1000 : 1000 ≤ d := by
        rcases guardedRatePartitionOrder_eq_uniform_or_ge_1000 δ with h | h
        · exact (heq h).elim
        · exact h
      have hs0 := ratePartition_dimension_gt_sharpFiniteRatio hD hd1000 hmpos hnpos
        e.rate_pos (e.rate_pos.trans e.rate_lt_agreement) hW e.rate_upper e.agreement_lower
      simpa only [guardedRatePartitionFiniteRatio, heq, if_neg, if_false, r, N, W, d, m,
        Nat.cast_mul, mul_assoc] using hs0
  have hmargin : (151 / 150 : ℝ) * r < N :=
    (mul_le_mul_of_nonneg_right e.ratio_gt.le (Nat.cast_nonneg r)).trans_lt hs
  have hsurplus : r < N := by
    have : (r : ℝ) < N := by nlinarith [Nat.cast_nonneg r (α := ℝ)]
    exact_mod_cast this
  obtain ⟨cert⟩ := SymbolicReceivedCurve.exists_ratePartition_certificate.{u, u}
    (k := k) hD (le_refl ((m * A : ℕ) : ℝ)) (mul_pos hmpos (by
      have : (0 : ℝ) < A :=
        (mul_pos (e.rate_pos.trans e.rate_lt_agreement) (by exact_mod_cast hnpos)).trans_le
          e.agreement_lower
      exact_mod_cast this)) e.message_le domain w hw
    (fun _ hu ↦ guardedRatePartition_totalJetDegree_le hδ hD e.ambient_lower hAn hu)
    hsurplus
  have hheight := SymbolicReceivedCurve.kernel_height_le_ratePartitionHeight
    (ℓ := ℓ) (ν := ν) (by norm_num : (1 : ℝ) < 151 / 150) hmargin
  have hheight' : ratePartitionHeight ν (151 / 150 : ℝ) = 150 * ν := by
    exact ratePartitionHeight_uniform hν
  rw [hheight'] at hheight
  exact ⟨{ cert with challengeDegree_le := fun u ↦ (cert.challengeDegree_le u).trans hheight }⟩

end ReedSolomon.HiddenDerivative
