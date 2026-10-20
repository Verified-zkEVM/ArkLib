/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.SeparantChain

/-!
# Charge sums along first-order separant chains

Along a separant chain of a first-order equation `Q(X, Y₀, Y₁)`, the total jet degrees of the
stages strictly decrease and are positive, and the highest active jets decrease from `Y₁` to `Y₀`.
Each stage with highest active jet `Y₁` lowers the degree in `Y₁` by at least one, and stages with
highest active jet `Y₀` have degree zero in `Y₁`.

Charge a stage with highest active jet `Y₀` by `c₀ j` and a stage with highest active jet `Y₁` by
`c₁ j r`, where `j` is its total jet degree and `r` its degree in `Y₁`. If the charges are
nonnegative, `c₀` is monotone, `c₁` is monotone in each argument on the range `r ≤ j`, and
`c₀ j ≤ c₁ j 1`, then the total charge of a chain from an equation of total jet degree at most `μ`
and degree at most `M` in `Y₁` is at most `firstOrderStageCap c₀ c₁ μ M`. This schedule charges
`c₀` at total jet degrees `1, ..., μ - min M μ` and charges `c₁` at the largest `min M μ` total jet
degrees, with the degree in `Y₁` running from `1` to `min M μ`.

The charges take values in any ordered additive commutative monoid.

## Main statements

* `firstOrderStageCharge` and `firstOrderStageCap`: the charge of a stage and the extremal
  schedule.
* `SeparantChain.sum_firstOrderStageCharge_le`: the total charge along a first-order separant chain
  is at most the extremal schedule.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

variable {R : Type*} [CommSemiring R] {α : Type*} [AddCommMonoid α]

/-- The charge of a first-order stage: `c₀ j` if its highest active jet is `Y₀`, and `c₁ j r` if
it is `Y₁`, where `j` is the total jet degree of the stage equation and `r` its degree in `Y₁`. -/
def firstOrderStageCharge (c₀ : ℕ → α) (c₁ : ℕ → ℕ → α) (stage : SeparantStage R 1) : α :=
  if stage.2 = 0 then c₀ (jetTotalDegree stage.1)
  else c₁ (jetTotalDegree stage.1) (jetDegree stage.1 1)

/-- The extremal schedule for a first-order chain from an equation of total jet degree `μ` and
degree `M` in `Y₁`: the charge `c₀ (t + 1)` for `t < μ - min M μ`, and the charge
`c₁ (t + 1) (t + 1 - (μ - min M μ))` for `μ - min M μ ≤ t < μ`. -/
def firstOrderStageCap (c₀ : ℕ → α) (c₁ : ℕ → ℕ → α) (μ M : ℕ) : α :=
  ∑ t ∈ Finset.range (μ - min M μ), c₀ (t + 1) +
    ∑ t ∈ Finset.Ico (μ - min M μ) μ, c₁ (t + 1) (t + 1 - (μ - min M μ))

/-- With degree zero in `Y₁`, the extremal schedule charges only `c₀`. -/
@[simp]
theorem firstOrderStageCap_zero_right (c₀ : ℕ → α) (c₁ : ℕ → ℕ → α) (μ : ℕ) :
    firstOrderStageCap c₀ c₁ μ 0 = ∑ t ∈ Finset.range μ, c₀ (t + 1) := by
  simp [firstOrderStageCap]

/-- With total jet degree zero, the extremal schedule is empty. -/
@[simp]
theorem firstOrderStageCap_zero_left (c₀ : ℕ → α) (c₁ : ℕ → ℕ → α) (M : ℕ) :
    firstOrderStageCap c₀ c₁ 0 M = 0 := by
  simp [firstOrderStageCap]

/-- Raising the total jet degree with degree zero in `Y₁` adds one `c₀` charge. -/
theorem firstOrderStageCap_succ_zero (c₀ : ℕ → α) (c₁ : ℕ → ℕ → α) (μ : ℕ) :
    firstOrderStageCap c₀ c₁ (μ + 1) 0 = c₀ (μ + 1) + firstOrderStageCap c₀ c₁ μ 0 := by
  simp [Finset.sum_range_succ, add_comm]

/-- Raising both the total jet degree and the degree in `Y₁` adds one `c₁` charge at the top. -/
theorem firstOrderStageCap_succ_succ (c₀ : ℕ → α) (c₁ : ℕ → ℕ → α) (μ M : ℕ) :
    firstOrderStageCap c₀ c₁ (μ + 1) (M + 1) =
      c₁ (μ + 1) (min (M + 1) (μ + 1)) + firstOrderStageCap c₀ c₁ μ M := by
  rw [firstOrderStageCap, firstOrderStageCap]
  simp only [Nat.succ_min_succ, Nat.succ_sub_succ_eq_sub]
  rw [Finset.sum_Ico_succ_top (Nat.sub_le μ (min M μ))]
  have hlast : μ + 1 - (μ - min M μ) = min M μ + 1 := by omega
  rw [hlast, add_comm _ (c₁ (μ + 1) (min M μ + 1)), add_left_comm]

/-- The extremal schedule of nonnegative charges is nonnegative. -/
theorem firstOrderStageCap_nonneg [PartialOrder α] [IsOrderedAddMonoid α] {c₀ : ℕ → α}
    {c₁ : ℕ → ℕ → α} (hc₀ : ∀ j, 0 ≤ c₀ j) (hc₁ : ∀ j r, 0 ≤ c₁ j r) (μ M : ℕ) :
    0 ≤ firstOrderStageCap c₀ c₁ μ M :=
  add_nonneg (Finset.sum_nonneg fun _ _ ↦ hc₀ _) (Finset.sum_nonneg fun _ _ ↦ hc₁ _ _)

/-- If the highest active jet of `Q` is `Y_j`, the separant in `Y_j` has degree at most
`jetDegree Q (Fin.last d) - 1` in the top variable. -/
private theorem jetDegree_separant_last_le_sub_one {d : ℕ} (Q : DifferentialPolynomial R d)
    {j : Fin (d + 1)} (hhighest : highestActiveJet Q = some j) :
    jetDegree (separant Q j) (Fin.last d) ≤ jetDegree Q (Fin.last d) - 1 := by
  rcases (Fin.le_last j).lt_or_eq with hlt | rfl
  · have hzero : jetDegree Q (Fin.last d) = 0 := Nat.eq_zero_of_not_pos
      ((isHighestActiveJet_of_highestActiveJet_eq_some hhighest).2 _ hlt)
    simpa [hzero] using jetDegree_separant_le Q j (Fin.last d)
  · exact jetDegree_separant_le_sub_one Q (Fin.last d)

/-- Let `c₀` and `c₁` be nonnegative charges such that `c₀` is monotone, `c₁ j r` is monotone in
`j ≥ r` and in `r ≤ j`, and `c₀ j ≤ c₁ j 1`. Along a separant chain from a first-order equation
`Q` with `jetTotalDegree Q ≤ μ` and degree at most `M` in `Y₁`, the total stage charge is at most
`firstOrderStageCap c₀ c₁ μ M`. -/
theorem SeparantChain.sum_firstOrderStageCharge_le [PartialOrder α] [IsOrderedAddMonoid α]
    {Q terminal : DifferentialPolynomial R 1}
    {stages : List (SeparantStage R 1)} (hc : SeparantChain Q stages terminal)
    {c₀ : ℕ → α} {c₁ : ℕ → ℕ → α} {μ M : ℕ} (hμ : jetTotalDegree Q ≤ μ)
    (hM : jetDegree Q 1 ≤ M) (hc₀ : ∀ j, 0 ≤ c₀ j) (hc₁ : ∀ j r, 0 ≤ c₁ j r)
    (hmono₀ : Monotone c₀) (hmono₁Total : ∀ {j w r}, r ≤ j → j ≤ w → c₁ j r ≤ c₁ w r)
    (hmono₁Degree : ∀ {j r q}, r ≤ q → q ≤ j → c₁ j r ≤ c₁ j q)
    (hc₀₁ : ∀ j, c₀ j ≤ c₁ j 1) :
    (stages.map (firstOrderStageCharge c₀ c₁)).sum ≤ firstOrderStageCap c₀ c₁ μ M := by
  induction hc generalizing μ M with
  | terminal => simpa using firstOrderStageCap_nonneg hc₀ hc₁ μ M
  | @active Q tail terminal j hne hhighest next ih =>
      have hactive : 0 < jetDegree Q j :=
        (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
      have hpos : 0 < jetTotalDegree Q := hactive.trans_le (jetDegree_le_total Q j)
      have hstep := separant_total_le Q j
      have hlast : jetDegree (separant Q j) 1 ≤ jetDegree Q 1 - 1 :=
        jetDegree_separant_last_le_sub_one Q hhighest
      obtain _ | μ := μ
      · omega
      have htailTotal : jetTotalDegree (separant Q j) ≤ μ := by omega
      rw [List.map_cons, List.sum_cons]
      obtain _ | M := M
      · obtain rfl : j = 0 := by
          fin_cases j
          · rfl
          · exact absurd (hactive.trans_le hM) (lt_irrefl 0)
        rw [firstOrderStageCap_succ_zero]
        refine add_le_add ?_ (ih htailTotal (by omega))
        simpa [firstOrderStageCharge] using hmono₀ hμ
      · rw [firstOrderStageCap_succ_succ]
        refine add_le_add ?_ (ih htailTotal (by omega))
        have hdegreeCap : jetDegree Q 1 ≤ min (M + 1) (μ + 1) :=
          le_min hM ((jetDegree_le_total Q 1).trans hμ)
        have hcapPos : 1 ≤ min (M + 1) (μ + 1) := by omega
        by_cases hj : j = 0
        · subst hj
          simp only [firstOrderStageCharge, ↓reduceIte]
          exact (hmono₀ hμ).trans ((hc₀₁ _).trans (hmono₁Degree hcapPos (by omega)))
        · simp only [firstOrderStageCharge, hj, ↓reduceIte]
          exact (hmono₁Total (jetDegree_le_total Q 1) hμ).trans
            (hmono₁Degree hdegreeCap (by omega))

end

end PolynomialDifferential
