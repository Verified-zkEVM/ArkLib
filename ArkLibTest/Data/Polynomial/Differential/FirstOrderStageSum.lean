/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.FirstOrderStageSum

/-!
# Acceptance tests for charge sums along first-order separant chains

* In depth `1` over `ℚ`, `Y₀` has the chain `Y₀` with terminal equation `1`. Its total charge is
  `c₀ 1`, which is `firstOrderStageCap c₀ c₁ 1 0`, so the bound is attained.
* With `c₀ = 1` and `c₁ = 0`, every hypothesis except `c₀ j ≤ c₁ j 1` holds, the schedule for
  `μ = M = 1` is `0`, and the chain of `Y₀` has total charge `1`: that hypothesis is needed.
* The schedule `firstOrderStageCap (fun j ↦ j) (fun j r ↦ j + r) 3 1` is `1 + 2 + (3 + 1) = 7`,
  over `ℚ` and over `ℕ`.
* The bound with charges in `ℚ` is an instance of the general statement.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- `Y₀` in depth `1`. -/
private abbrev orderZeroEquation : DifferentialPolynomial ℚ 1 :=
  X (some 0)

private theorem jetDegree_orderZeroEquation (j : Fin 2) :
    jetDegree orderZeroEquation j = if j = 0 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_X]
  simp

private theorem jetTotalDegree_orderZeroEquation : jetTotalDegree orderZeroEquation = 1 := by
  change MvPolynomial.weightedTotalDegree jetDegreeWeight
    (monomial (Finsupp.single (some (0 : Fin 2)) 1) (1 : ℚ)) = 1
  rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
  simp [Finsupp.weight_apply, jetDegreeWeight]

private theorem highestActiveJet_orderZeroEquation :
    highestActiveJet orderZeroEquation = some 0 := by
  cases h : highestActiveJet orderZeroEquation with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, jetDegree_orderZeroEquation] at this
  | some j =>
      have hj := (isHighestActiveJet_of_highestActiveJet_eq_some h).1
      fin_cases j
      · rfl
      · simp [DependsOnJet, jetDegree_orderZeroEquation] at hj

/-- The chain `Y₀` with terminal equation `1`. -/
private theorem orderZeroChain :
    SeparantChain orderZeroEquation [(orderZeroEquation, 0)] (C 1) := by
  refine .active 0 (X_ne_zero _) highestActiveJet_orderZeroEquation ?_
  have hsep : separant orderZeroEquation 0 = C 1 := by simp [separant, pderiv_X]
  rw [hsep]
  refine .terminal (by simp) ((highestActiveJet_eq_none_iff _).mpr fun j hj ↦ ?_)
  simp [DependsOnJet, jetDegree] at hj

/-! ### The bound is attained -/

/-- The total charge of the chain of `Y₀` is `c₀ 1`. -/
private theorem sum_orderZeroChain (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) :
    ([(orderZeroEquation, (0 : Fin 2))].map (firstOrderStageCharge c₀ c₁)).sum = c₀ 1 := by
  simp [firstOrderStageCharge, jetTotalDegree_orderZeroEquation]

example (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) :
    ([(orderZeroEquation, (0 : Fin 2))].map (firstOrderStageCharge c₀ c₁)).sum =
      firstOrderStageCap c₀ c₁ 1 0 := by
  rw [sum_orderZeroChain]
  simp

/-- The general bound, for the charges `c₀ j = j` and `c₁ j r = j + r`. -/
example :
    ([(orderZeroEquation, (0 : Fin 2))].map
        (firstOrderStageCharge (fun j ↦ (j : ℚ)) fun j r ↦ (j + r : ℚ))).sum ≤
      firstOrderStageCap (fun j ↦ (j : ℚ)) (fun j r ↦ (j + r : ℚ)) 1 0 :=
  orderZeroChain.sum_firstOrderStageCharge_le jetTotalDegree_orderZeroEquation.le
    (by simp [jetDegree_orderZeroEquation]) (fun j ↦ by positivity)
    (fun j r ↦ by positivity) (fun _ _ h ↦ by exact_mod_cast h)
    (fun _ h ↦ by simp only [add_le_add_iff_right]; exact_mod_cast h)
    (fun h _ ↦ by simp only [add_le_add_iff_left]; exact_mod_cast h) (fun j ↦ by simp)

/-! ### The hypothesis `c₀ j ≤ c₁ j 1` is needed -/

/-- With `c₀ = 1` and `c₁ = 0`, the chain of `Y₀` has total charge `1`, above the schedule `0`
for `μ = M = 1`. Every hypothesis of the bound except `c₀ j ≤ c₁ j 1` holds. -/
example :
    jetTotalDegree orderZeroEquation ≤ 1 ∧ jetDegree orderZeroEquation 1 ≤ 1 ∧
      ¬ ([(orderZeroEquation, (0 : Fin 2))].map
          (firstOrderStageCharge (fun _ ↦ (1 : ℚ)) fun _ _ ↦ 0)).sum ≤
        firstOrderStageCap (fun _ ↦ (1 : ℚ)) (fun _ _ ↦ 0) 1 1 := by
  refine ⟨jetTotalDegree_orderZeroEquation.le, by simp [jetDegree_orderZeroEquation], ?_⟩
  rw [sum_orderZeroChain]
  simp [firstOrderStageCap]

/-! ### Evaluating the schedule -/

example : firstOrderStageCap (fun j ↦ (j : ℚ)) (fun j r ↦ (j + r : ℚ)) 3 1 = 7 := by
  rw [firstOrderStageCap_succ_succ, firstOrderStageCap_zero_right]
  norm_num [Finset.sum_range_succ]

example : firstOrderStageCap (fun j ↦ j) (fun j r ↦ j + r) 3 1 = 7 := by
  decide

example (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) (M : ℕ) : firstOrderStageCap c₀ c₁ 0 M = 0 :=
  firstOrderStageCap_zero_left c₀ c₁ M

/-! ### Charges in `ℚ` -/

example {R : Type*} [CommSemiring R] {Q terminal : DifferentialPolynomial R 1}
    {stages : List (SeparantStage R 1)} (hc : SeparantChain Q stages terminal)
    (c₀ : ℕ → ℚ) (c₁ : ℕ → ℕ → ℚ) {μ M : ℕ}
    (hμ : jetTotalDegree Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (hc₀ : ∀ j, 0 ≤ c₀ j) (hc₁ : ∀ j r, 0 ≤ c₁ j r) (hmono₀ : Monotone c₀)
    (hmono₁Total : ∀ {j w r}, r ≤ j → j ≤ w → c₁ j r ≤ c₁ w r)
    (hmono₁Derivative : ∀ {j r q}, r ≤ q → q ≤ j → c₁ j r ≤ c₁ j q)
    (hc₀₁ : ∀ j, c₀ j ≤ c₁ j 1) :
    (stages.map (firstOrderStageCharge c₀ c₁)).sum ≤ firstOrderStageCap c₀ c₁ μ M :=
  hc.sum_firstOrderStageCharge_le hμ hM hc₀ hc₁ hmono₀ hmono₁Total hmono₁Derivative hc₀₁

end

end PolynomialDifferential
