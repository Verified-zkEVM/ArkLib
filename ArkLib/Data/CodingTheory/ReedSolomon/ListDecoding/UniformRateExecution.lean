/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.BudgetedExecution
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Eligibility
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.UniformEnvelope
/-!
# Executed decoding from the rate-partition parameters

The finite rate choice supplies a candidate to the existing descending ambient search. The
program uses integer inputs and strict jet budget `ν+1`; its actual returned coefficient list is
exact. The bound records primitive work in that execution.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityDecoderMachine

open HiddenDerivative ReedSolomon PolynomialDifferential
open SeparateSampleFieldExecution (ExactOutput)

/-- The uniform envelope supplies an actual candidate to the executable decoder. -/
theorem UniformRatePartitionEnvelope.run_exact {q n k A : ℕ} [Fact q.Prime]
    {δ : ℝ} (e : UniformRatePartitionEnvelope δ n k A)
    (hδ : 0 < δ) (hδone : δ < 1) (hd : 500 ≤ uniformRatePartitionOrder δ)
    (hn : uniformRatePartitionLength δ ≤ n) (hAn : A ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (hnq : n ≤ q) :
    let d := uniformRatePartitionOrder δ
    let m := uniformRatePartitionMultiplicity δ
    let J := uniformRatePartitionJetBound δ + 1
    ∃ (out : List (List (ZMod q))) (cost : ℕ)
      (found : AmbientSearchMachine.Output (ZMod q)),
      runWithBudget n k d m J A (List.ofFn (fun i ↦ (domain i, received i))) =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k d m J A n +
        QuadraticAlgebra.SetupMachine.budget q (m * A) +
        QuadraticDecoderMachine.decoderFuelWithBudget d m J q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 152 := by
  let d := uniformRatePartitionOrder δ
  let m := uniformRatePartitionMultiplicity δ
  let D := e.ambientDegree
  let W := ratePartitionWeight e.rate e.agreement d m
  have hmpos : 0 < m :=
    lt_of_lt_of_le (by omega) (ratePartitionClosedMultiplicity_ge_order hd)
  obtain ⟨hsize, hmn, hν, hνn⟩ := uniformRatePartition_integer_guards hδ hδone hmpos hn
  have hD : 0 < D := by have := e.order_le; dsimp [D]; omega
  have hnpos : 0 < n := hmpos.trans_le hmn
  have hW := (ratePartition_closed_floor_bounds e.rate_pos e.rate_lt_agreement hd).2.1
  have hs := ratePartition_dimension_gt_finiteRatio hD hd hmpos hnpos
    e.rate_pos (e.rate_pos.trans e.rate_lt_agreement) hW e.rate_upper e.agreement_lower
  have hsurplus : n * ratePartitionRankBound d m W <
      (ratePartitionExponents D d W (m * A : ℕ) hD).card := by
    have hg := e.ratio_gt
    have hr : (0 : ℝ) ≤ n * ratePartitionRankBound d m W := by positivity
    have h : (n : ℝ) * ratePartitionRankBound d m W <
        (ratePartitionExponents D d W (m * A : ℕ) hD).card := by
      nlinarith
    exact_mod_cast h
  obtain ⟨Q, hQ, he, hlocal⟩ := exists_ratePartition_eligible_candidate hD domain received
    (fun _ hu ↦ uniformRatePartition_totalJetDegree_le hδ hD e.ambient_lower hAn hu) hsurplus
  have hL : m * A ≤ q ^ 2 := by
    calc
      m * A ≤ n * n := Nat.mul_le_mul hmn hAn
      _ ≤ q * q := Nat.mul_le_mul hnq hnq
      _ = q ^ 2 := by ring
  have hdD := e.order_le
  have hDn := e.ambient_le
  have hkD := e.message_le
  exact runWithBudget_exact_of_candidate domain received (by omega) (by omega) hAn hnq hL
    (by omega) (by dsimp [D]; omega) (by dsimp [D]; omega) Q hQ he hlocal

/-- The explicit uniform recipe makes the integer decoder succeed on every promised input;
no interpolation envelope is supplied by the caller. -/
theorem uniformRatePartition_run_exact {q n k A : ℕ} [Fact q.Prime]
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (hnq : n ≤ q) :
    let d := uniformRatePartitionOrder δ
    let m := uniformRatePartitionMultiplicity δ
    let J := uniformRatePartitionJetBound δ + 1
    ∃ (out : List (List (ZMod q))) (cost : ℕ)
      (found : AmbientSearchMachine.Output (ZMod q)),
      runWithBudget n k d m J A (List.ofFn (fun i ↦ (domain i, received i))) =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k d m J A n +
        QuadraticAlgebra.SetupMachine.budget q (m * A) +
        QuadraticDecoderMachine.decoderFuelWithBudget d m J q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 152 := by
  obtain ⟨e⟩ := exists_uniformRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  exact UniformRatePartitionEnvelope.run_exact e hδ (by linarith)
    (uniformRatePartitionOrder_ge_500 hδ hδsmall)
    hn hAn domain received hnq

end ReedSolomon.ListDecoding.CapacityDecoderMachine
