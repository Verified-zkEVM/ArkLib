/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank

/-!
# Partition support local rank acceptance tests

* `localDerivativeCoordinateBudget` unfolds to the sum over `s < m` of
  `((m - s) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + s)`.
* At `d = 1`, `m = 2`, `W = 0` the budget is `1 · 1 + 1 · 2 = 3`, so the local rank on every
  partition support space with these parameters is at most `3`, whatever `0 < D` and `L` are.
* At `d = 0` every polynomial has derivative-order weight `0`, so the general bound
  `finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight` applies to the whole
  space: the local constraint map of order `3` has rank at most `3 + 2 + 1 = 6`.
* Interpolation: a concrete interpolant over `ℚ` whose surplus is computed from the exact counts,
  the order-zero case, and the interpolant with the budget written out.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The budget with `(m - s) ⌈/⌉ (d + 1)` in place of `contactThreshold (d + 1) m s`. -/
example (d m W : ℕ) : localDerivativeCoordinateBudget d m W =
    ∑ s ∈ Finset.range m, ((m - s) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + s) :=
  rfl

example : localDerivativeCoordinateBudget 1 2 0 = 3 := by decide

/-- At `d = 1`, `m = 2`, `W = 0` the local rank on the partition support space is at most `3`,
for every `0 < D` and `L`. -/
example (D : ℕ) (hD : 0 < D) (L : ℝ) (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range (partitionSupportLocalConstraint (d := 1) (W := 0)
      (L := L) 2 hD center received)) ≤ 3 :=
  (finrank_partitionSupportLocalConstraint_le hD center received).trans (by decide)

example : localDerivativeCoordinateBudget 0 3 0 = 6 := by decide

/-- At `d = 0` the derivative-order weight vanishes, so the local constraint map of order `3` on
the whole space of differential polynomials has rank at most `6`. -/
example (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range
      ((localConstraintAt (d := 0) 3 center received).domRestrict ⊤)) ≤ 6 := by
  refine (finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight 3 0 center received
    ⊤ fun _ _ u _ => ?_).trans (by decide)
  simp [fullDerivativeJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
    jetDerivativeWeight]

/-! ### Interpolation -/

section

open Finset

/-- `localDerivativeCoordinateBudget d m W` unfolds to its defining sum. -/
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

/-- The interpolant in the partition support space, with the coordinate budget written out. -/
example {F ι : Type*} [Field F] [Fintype ι] {D d m W : ℕ} {L : ℝ}
    (hD : 0 < D) (centers received : ι → F)
    (hdim : Fintype.card ι *
        ∑ s ∈ range m, ((m - s) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + s) <
      #(partitionSupportExponents D d W L hD)) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ partitionSupportSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_partitionSupport_interpolant hD centers received hdim

end
