/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.RatePartition.Basic
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.RatePartition.Interpolation

/-!
# Acceptance tests for interpolation in the partition support

The identification of the source's rate-partition rank bound with
`localDerivativeCoordinateBudget`, a concrete interpolant over `ℚ` whose surplus is computed from
the exact counts, the order-zero case, and the source form of
`exists_nonzero_ratePartition_interpolant`.
-/

open Finset PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The source's `ratePartitionRankBound d m W` is `localDerivativeCoordinateBudget d m W`
definitionally, with its tuple count `ratePartitionTupleCount d B` being
`weightedHigherJetCount (d + 1) B`. -/
example (d m W : ℕ) :
    localDerivativeCoordinateBudget d m W =
      ∑ s ∈ range m, ((m - s) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + s) :=
  rfl

/-- At `d = 0` there are no visible jets, so each tuple count is `1` and the budget at `m = 2` is
`⌈2/1⌉ + ⌈1/1⌉ = 3`. At `d = 1`, `m = 2`, `W = 0` the residual `0` allows `⌈2/2⌉ = 1` error
exponent and one exponent of `Y₁` (weight `0`), the residual `1` allows `⌈1/2⌉ = 1` error exponent
and two exponents of `Y₁` (weights `0, 1`), so the budget is `1 + 2 = 3`. -/
example :
    localDerivativeCoordinateBudget 0 2 1 = 3 ∧ localDerivativeCoordinateBudget 1 2 0 = 3 := by
  decide

/-- One point, `d = 0`, `m = 1`, `W = 0`, `D = 1`, `L = 2`: the budget is `1` and the space has
dimension `3`, so an interpolant exists. -/
example (center received : ℚ) :
    ∃ Q : DifferentialPolynomial ℚ 0, Q ≠ 0 ∧
      Q ∈ partitionSupportSpace ℚ 1 0 0 ((2 : ℕ) : ℝ) one_pos ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 1 center received Q := by
  refine exists_nonzero_partitionSupport_interpolant one_pos (fun _ => center)
    (fun _ => received) ?_
  rw [card_partitionSupportExponents]
  decide

/-- At order `m = 0` the budget is zero, so any number of points admits an interpolant as soon as
the space is nonzero, here at the cutoff `1 / 2`. -/
example (centers received : Fin 5 → ℚ) :
    ∃ Q : DifferentialPolynomial ℚ 2, Q ≠ 0 ∧
      Q ∈ partitionSupportSpace ℚ 3 2 4 (1 / 2 : ℝ) three_pos ∧
      ∀ i, SatisfiesLocalConstraints 0 (centers i) (received i) Q := by
  refine exists_nonzero_partitionSupport_interpolant three_pos centers received ?_
  rw [show localDerivativeCoordinateBudget 2 0 4 = 0 from rfl, mul_zero,
    card_partitionSupportExponents_pos_iff]
  norm_num

/-- Source shape `exists_nonzero_ratePartition_interpolant`, with the source's rank bound written
out. -/
example {F ι : Type*} [Field F] [Fintype ι] {D d m W : ℕ} {L : ℝ}
    (hD : 0 < D) (centers received : ι → F)
    (hdim : Fintype.card ι *
        ∑ s ∈ range m, ((m - s) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + s) <
      #(partitionSupportExponents D d W L hD)) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ partitionSupportSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_partitionSupport_interpolant hD centers received hdim
