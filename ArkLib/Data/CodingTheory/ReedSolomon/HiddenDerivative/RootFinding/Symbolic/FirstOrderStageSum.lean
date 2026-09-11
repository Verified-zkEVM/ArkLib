/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.SeparantChain

/-!
# Cap-sensitive sums along first-order separant chains

A first-order separant chain visits strictly decreasing positive total jet degrees. Its active
jet orders also decrease, and order one can be selected no more often than the initial exponent
of the first derivative. This file turns those structural facts into the sharp two-block sum used
by first-order agreement geometry.

## Reading the statement

Give an order-zero charge `c₀ j` and an order-one charge `c₁ j r` for a stage of total jet
degree `j` and first-derivative degree `r`. If both charges increase in their degree arguments,
are nonnegative, and the first order-one slot dominates the order-zero charge, then a chain of
total jet degree at most `μ` and first-derivative degree at most `M` costs no more than the full
schedule with `c₁ j (j - (μ - min M μ))` on the largest `min M μ` degrees and `c₀` on the rest.

The result is purely an aggregation theorem. Concrete joint and fiber degree formulas are supplied
by later geometry modules.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicSeparantChain

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- Charge a first-order stage according to its actual active jet order, total jet degree, and
first-derivative degree. -/
def firstOrderStageCharge (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (stage : Stage R 1) : ℚ :=
  if stage.2 = 0 then c₀ (jetWeight stage.1)
  else c₁ (jetWeight stage.1) (jetDegree stage.1 1)

/-- The extremal two-block schedule: order zero on the lower degrees and order one on the
largest `min M μ` degrees, with the derivative degree increasing from one across the
order-one block. -/
def firstOrderStageCap (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (μ M : ℕ) : ℚ :=
  ∑ t ∈ Finset.range (μ - min M μ), c₀ (t + 1) +
    ∑ t ∈ Finset.Ico (μ - min M μ) μ,
      c₁ (t + 1) (t + 1 - (μ - min M μ))

/-- When the initial polynomial has derivative degree zero, the schedule contains only ordinary
stages.  This boundary is kept separate from the positive derivative-degree recurrence. -/
@[simp]
theorem firstOrderStageCap_derivativeDegree_zero
    (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (μ : ℕ) :
    firstOrderStageCap c₀ c₁ μ 0 = ∑ t ∈ Finset.range μ, c₀ (t + 1) := by
  simp [firstOrderStageCap]

@[simp]
private theorem firstOrderStageCap_zero (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (M : ℕ) :
    firstOrderStageCap c₀ c₁ 0 M = 0 := by
  simp [firstOrderStageCap]

@[simp]
private theorem firstOrderStageCap_succ_zero (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (μ : ℕ) :
    firstOrderStageCap c₀ c₁ (μ + 1) 0 =
      firstOrderStageCap c₀ c₁ μ 0 + c₀ (μ + 1) := by
  simp [firstOrderStageCap, Finset.sum_range_succ]

@[simp]
private theorem firstOrderStageCap_succ_succ (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (μ M : ℕ) :
    firstOrderStageCap c₀ c₁ (μ + 1) (M + 1) =
      firstOrderStageCap c₀ c₁ μ M + c₁ (μ + 1) (min (M + 1) (μ + 1)) := by
  rw [firstOrderStageCap, firstOrderStageCap]
  simp only [Nat.succ_min_succ, Nat.succ_sub_succ_eq_sub]
  rw [Finset.sum_Ico_succ_top (Nat.sub_le μ (min M μ))]
  have hlast : μ + 1 - (μ - min M μ) = (min M μ).succ := by omega
  rw [hlast]
  ring

private theorem firstOrderStageCap_nonneg (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (μ M : ℕ)
    (hc₀ : ∀ j, 0 ≤ c₀ j) (hc₁ : ∀ j r, 0 ≤ c₁ j r) :
    0 ≤ firstOrderStageCap c₀ c₁ μ M := by
  unfold firstOrderStageCap
  exact add_nonneg (Finset.sum_nonneg fun j _ ↦ hc₀ (j + 1))
    (Finset.sum_nonneg fun j _ ↦ hc₁ (j + 1) (j + 1 - (μ - min M μ)))

private theorem jetDegree_one_separant_le_sub_one
    (Q : DifferentialPolynomial R 1) (j : Fin 2)
    (hhighest : highestActiveJet Q = some j) :
    jetDegree (separant Q j) 1 ≤ jetDegree Q 1 - 1 := by
  fin_cases j
  · have hroot := isHighestActiveJet_of_highestActiveJet_eq_some hhighest
    have hzero : jetDegree Q 1 = 0 := by
      apply Nat.eq_zero_of_not_pos
      exact hroot.2 1 (by decide)
    have hle := jetDegree_separant_le Q 0 1
    simpa [hzero] using hle
  · exact degreeOf_pderiv_le_sub_one (some (1 : Fin 2)) Q

/-- The sum of monotone nonnegative first-order stage charges is bounded by the sharp schedule
that assigns order one to the largest `min M μ` possible stage degrees. -/
theorem Chain.sum_firstOrderStageCharge_le
    {Q terminal : DifferentialPolynomial R 1} {stages : List (Stage R 1)}
    (hc : Chain Q stages terminal) (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) {μ M : ℕ}
    (hμ : jetWeight Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (hc₀ : ∀ j, 0 ≤ c₀ j) (hc₁ : ∀ j r, 0 ≤ c₁ j r)
    (hmono₀ : Monotone c₀)
    (hmono₁Total : ∀ {j w r}, r ≤ j → j ≤ w → c₁ j r ≤ c₁ w r)
    (hmono₁Derivative : ∀ {j r q}, r ≤ q → q ≤ j → c₁ j r ≤ c₁ j q)
    (hc₀₁ : ∀ j, c₀ j ≤ c₁ j 1) :
    (stages.map (firstOrderStageCharge c₀ c₁)).sum ≤
      firstOrderStageCap c₀ c₁ μ M := by
  induction hc generalizing μ M with
  | terminal hne hterminal =>
      simpa using firstOrderStageCap_nonneg c₀ c₁ μ M hc₀ hc₁
  | @active Q tail terminal j hne hhighest next ih =>
      have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
      have hweightPos : 0 < jetWeight Q :=
        hactive.trans_le (jetDegree_le_jetWeight Q j)
      cases μ with
      | zero => omega
      | succ μ =>
          have htailWeight : jetWeight (separant Q j) ≤ μ := by
            have hstep := jetWeight_separant_le Q j
            omega
          cases M with
          | zero =>
              have hj : j = 0 := by
                fin_cases j
                · rfl
                · have hactive' : 0 < jetDegree Q (1 : Fin 2) := by
                    simpa [DependsOnJet] using hactive
                  omega
              subst j
              have htailDegree : jetDegree (separant Q 0) 1 ≤ 0 := by
                have hstep := jetDegree_one_separant_le_sub_one Q 0 hhighest
                omega
              have htail := ih htailWeight htailDegree
              simp only [List.map_cons, List.sum_cons]
              calc
                firstOrderStageCharge c₀ c₁ (Q, 0) +
                    (tail.map (firstOrderStageCharge c₀ c₁)).sum ≤
                    c₀ (μ + 1) + firstOrderStageCap c₀ c₁ μ 0 := by
                  apply add_le_add
                  · simpa [firstOrderStageCharge] using hmono₀ hμ
                  · exact htail
                _ = firstOrderStageCap c₀ c₁ (μ + 1) 0 := by
                  rw [firstOrderStageCap_succ_zero]
                  ring
          | succ M =>
              have htailDegree : jetDegree (separant Q j) 1 ≤ M := by
                have hstep := jetDegree_one_separant_le_sub_one Q j hhighest
                omega
              have htail := ih htailWeight htailDegree
              have hdegreeCap : jetDegree Q 1 ≤ min (M + 1) (μ + 1) := by
                apply le_min hM
                exact (jetDegree_le_jetWeight Q 1).trans hμ
              have hcapPos : 1 ≤ min (M + 1) (μ + 1) := by
                have hweightOne : 1 ≤ μ + 1 := by omega
                omega
              have hhead : firstOrderStageCharge c₀ c₁ (Q, j) ≤
                  c₁ (μ + 1) (min (M + 1) (μ + 1)) := by
                fin_cases j
                · simp only [firstOrderStageCharge, Fin.isValue]
                  exact (hmono₀ hμ).trans ((hc₀₁ _).trans
                    (hmono₁Derivative hcapPos (by omega)))
                · simp only [firstOrderStageCharge, Fin.isValue]
                  exact (hmono₁Total (jetDegree_le_jetWeight Q 1) hμ).trans
                    (hmono₁Derivative hdegreeCap (by omega))
              simp only [List.map_cons, List.sum_cons]
              calc
                firstOrderStageCharge c₀ c₁ (Q, j) +
                    (tail.map (firstOrderStageCharge c₀ c₁)).sum ≤
                    c₁ (μ + 1) (min (M + 1) (μ + 1)) +
                      firstOrderStageCap c₀ c₁ μ M :=
                  add_le_add hhead htail
                _ = firstOrderStageCap c₀ c₁ (μ + 1) (M + 1) := by
                  rw [firstOrderStageCap_succ_succ]
                  ring

end

end ReedSolomon.HiddenDerivative.SymbolicSeparantChain
