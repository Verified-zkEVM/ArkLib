/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.BudgetedExecution
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Eligibility
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter
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

/-- The general rate recipe runs the budgeted decoder and returns its exact physical list. -/
theorem ratePartition_run_exact {q n k A d : ℕ} [Fact q.Prime]
    {R a : ℝ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : ratePartitionLength R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (hnq : n ≤ q) :
    let m := p.multiplicity
    let J := ratePartitionJetBound R m + 1
    ∃ (out : List (List (ZMod q))) (cost : ℕ)
      (found : AmbientSearchMachine.Output (ZMod q)),
      runWithBudget n k d m J A (List.ofFn (fun i ↦ (domain i, received i))) =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k d m J A n +
        QuadraticAlgebra.SetupMachine.budget q (m * A) +
        QuadraticDecoderMachine.decoderFuelWithBudget d m J q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 152 := by
  let m := p.multiplicity
  let D := ⌊R * n⌋₊
  let W := ratePartitionWeight R a d m
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_length_guards hR (hRa.trans haone) hn hkR haA
  have hD : 0 < D := by dsimp [D]; omega
  have hnpos : 0 < n := hk.trans_le (hkD.trans (by omega))
  have hDrate : (D : ℝ) ≤ R * n := Nat.floor_le (by positivity)
  have hs := ratePartition_dimension_gt_finiteRatio hD hd p.multiplicity_pos hnpos
    hR (hR.trans hRa) p.weight_pos hDrate haA
  have hsurplus : n * ratePartitionRankBound d m W <
      (ratePartitionExponents D d W (m * A : ℕ) hD).card := by
    have hg := p.ratio_gt_one
    have hr : (0 : ℝ) ≤ n * ratePartitionRankBound d m W := by positivity
    have h : (n : ℝ) * ratePartitionRankBound d m W <
        (ratePartitionExponents D d W (m * A : ℕ) hD).card := by
      nlinarith
    exact_mod_cast h
  obtain ⟨Q, hQ, he, hlocal⟩ := exists_ratePartition_eligible_candidate hD domain received
    (fun _ hu ↦ ratePartition_totalJetDegree_le hD hR hDlower hAn hu) hsurplus
  have hm : m ≤ n := by dsimp [m]; omega
  have hL : m * A ≤ q ^ 2 := by
    calc
      m * A ≤ n * n := Nat.mul_le_mul hm hAn
      _ ≤ q * q := Nat.mul_le_mul hnq hnq
      _ = q ^ 2 := by ring
  exact runWithBudget_exact_of_candidate domain received (by omega) (by omega) hAn hnq hL
    (by omega) (by dsimp [D]; omega) (by dsimp [D]; omega) Q hQ he hlocal

end ReedSolomon.ListDecoding.CapacityDecoderMachine
