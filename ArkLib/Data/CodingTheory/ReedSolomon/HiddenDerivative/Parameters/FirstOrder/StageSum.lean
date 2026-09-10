/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageComparison
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.FirstOrderStageSum
/-!
# Summing first-order polynomial-curve stage charges

The geometric cost of a regular separant stage depends on its actual total jet degree and on
whether its highest active jet has order zero or one. The first-derivative exponent cap limits
the expensive order-one stages. Combining the generic cap-sensitive chain sum with the concrete
joint-and-fiber charges gives exactly the nonterminal part of `firstOrderCurveBound`.

## Reading the statement

The inequalities `k ≤ L ≤ A ≤ n` place the split threshold between message degree and received
agreement. They make both incidence ratios at least one. For every actual symbolic separant chain
whose initial equation has total jet degree at most `μ` and first-derivative degree at most `M`,
the terminal height charge plus all regular-stage charges is bounded by the displayed curve
envelope. No exceptional-set or root-counting premise is assumed here.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial Polynomial SymbolicSeparantChain
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The joint incidence ratio used by the first-order curve envelope. -/
def firstOrderCurveJointRatio (n L A : ℕ) : ℚ :=
  ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)

/-- The fiber incidence ratio used by the first-order curve envelope. -/
def firstOrderCurveFiberRatio (n k L : ℕ) : ℚ :=
  ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)

/-- The direct joint incidence ratio for an order-one stage. -/
def firstOrderCurveDirectRatio (n k A : ℕ) : ℚ :=
  ((n - k + 1 : ℕ) : ℚ) / (A - k + 1 : ℕ)

/-- The split joint ratio is at least one throughout its geometric range. -/
theorem firstOrderCurveJointRatio_one_le {n L A : ℕ} (hLA : L ≤ A) (hAn : A ≤ n) :
    1 ≤ firstOrderCurveJointRatio n L A := by
  unfold firstOrderCurveJointRatio
  apply (le_div_iff₀ (by positivity)).2
  simpa only [one_mul] using
    (show ((A - L + 1 : ℕ) : ℚ) ≤ (n - L + 1 : ℕ) by exact_mod_cast (by omega))

/-- The fiber ratio is at least one throughout its geometric range. -/
theorem firstOrderCurveFiberRatio_one_le {n k L : ℕ} (hkL : k ≤ L) (hLn : L ≤ n) :
    1 ≤ firstOrderCurveFiberRatio n k L := by
  unfold firstOrderCurveFiberRatio
  apply (le_div_iff₀ (by positivity)).2
  simpa only [one_mul] using
    (show ((L - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))

/-- The direct order-one joint ratio is at least one throughout its geometric range. -/
theorem firstOrderCurveDirectRatio_one_le {n k A : ℕ} (hkA : k ≤ A) (hAn : A ≤ n) :
    1 ≤ firstOrderCurveDirectRatio n k A := by
  unfold firstOrderCurveDirectRatio
  apply (le_div_iff₀ (by positivity)).2
  simpa only [one_mul] using
    (show ((A - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))

/-- Splitting at `L` can only increase the joint ratio relative to going directly from `k`
to `A`. -/
theorem firstOrderCurveDirectRatio_le_jointRatio {n k L A : ℕ}
    (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    firstOrderCurveDirectRatio n k A ≤ firstOrderCurveJointRatio n L A := by
  unfold firstOrderCurveDirectRatio firstOrderCurveJointRatio
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hkL' : (k : ℚ) ≤ L := by exact_mod_cast hkL
  have hAn' : (A : ℚ) ≤ n := by exact_mod_cast hAn
  push_cast [Nat.cast_sub ((hkL.trans hLA).trans hAn),
    Nat.cast_sub (hkL.trans hLA), Nat.cast_sub (hLA.trans hAn), Nat.cast_sub hLA]
  nlinarith [mul_nonneg
    (show (0 : ℚ) ≤ (L : ℚ) - k by linarith)
    (show (0 : ℚ) ≤ (n : ℚ) - A by linarith)]

/-- The actual regular-stage charge whose sum appears in the curve envelope. -/
def firstOrderCurveStageCharge (n K k L A ell h : ℕ) (stage : Stage F[X] 1)
    (τ : ℕ) (η : ℚ) : ℚ :=
  firstOrderStageCharge
    (fun v ↦ curveStageZero K ell h (firstOrderCurveJointRatio n L A)
      ((ell * (n - L) : ℕ) : ℚ) v (τ := τ))
    (fun v r ↦ curveStageOne K ell h (firstOrderCurveJointRatio n L A)
      (firstOrderCurveFiberRatio n k L) ((ell * (n - L) : ℕ) : ℚ) v r (τ := τ)
      (η := η)) stage

private theorem sum_Ico_eq_sum_range_ite {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {a μ : ℕ} (_ha : a ≤ μ) :
    ∑ t ∈ Finset.Ico a μ, f t = ∑ t ∈ Finset.range μ, if a ≤ t then f t else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  · intro t _
    rfl

private theorem sum_curveStageZero_eq (K μ M ell h τ : ℕ) (s c : ℚ) :
    (∑ t ∈ Finset.range (μ - min M μ), curveStageZero K ell h s c (t + 1) (τ := τ)) =
      s * firstOrderCurveJointZero K μ M ell h (τ := τ) +
        c * firstOrderCurveFiberZero μ M := by
  unfold curveStageZero firstOrderCurveJointZero firstOrderCurveFiberZero
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  rfl

private theorem sum_curveStageOne_eq (K μ M ell h τ : ℕ) (s η t c : ℚ) :
    (∑ j ∈ Finset.Ico (μ - min M μ) μ,
        curveStageOne K ell h s t c (j + 1) (j + 1 - (μ - min M μ))
          (τ := τ) (η := η)) =
      s * η * firstOrderCurveJointOne K μ M ell h (τ := τ) +
        c * t * firstOrderCurveFiberOne K μ M (τ := τ) := by
  rw [sum_Ico_eq_sum_range_ite _ (Nat.sub_le μ (min M μ))]
  unfold curveStageOne firstOrderCurveJointOne firstOrderCurveFiberOne
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : μ - min M μ ≤ j
  · simp [hj]
  · simp [hj]

/-- Parameterized form of the exact cap identity, keeping the common exponent and order-one
joint factor independent. -/
theorem firstOrderCurveStageCap_add_height_eq_of_factors
    (n K k L A μ M ell h τ : ℕ) (η : ℚ) :
    (h : ℚ) + firstOrderStageCap
        (fun v ↦ curveStageZero K ell h (firstOrderCurveJointRatio n L A)
          ((ell * (n - L) : ℕ) : ℚ) v (τ := τ))
        (fun v r ↦ curveStageOne K ell h (firstOrderCurveJointRatio n L A)
          (firstOrderCurveFiberRatio n k L) ((ell * (n - L) : ℕ) : ℚ) v r (τ := τ)
          (η := η)) μ M =
      firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
  rw [firstOrderStageCap, sum_curveStageZero_eq, sum_curveStageOne_eq]
  unfold firstOrderCurveBound firstOrderCurveJointRatio firstOrderCurveFiberRatio
  ring

/-- The dimension-sensitive specialization uses the direct `k`-to-`A` ratio at order one. -/
theorem firstOrderCurveStageCap_add_height_eq_of_exponent
    (n K k L A μ M ell h τ : ℕ) :
    (h : ℚ) + firstOrderStageCap
        (fun v ↦ curveStageZero K ell h (firstOrderCurveJointRatio n L A)
          ((ell * (n - L) : ℕ) : ℚ) v (τ := τ))
        (fun v r ↦ curveStageOne K ell h (firstOrderCurveJointRatio n L A)
          (firstOrderCurveFiberRatio n k L) ((ell * (n - L) : ℕ) : ℚ) v r (τ := τ)
          (η := firstOrderCurveDirectRatio n k A)) μ M =
      firstOrderCurveBound n K k L A μ M ell h (τ := τ)
        (η := firstOrderCurveDirectRatio n k A) :=
  firstOrderCurveStageCap_add_height_eq_of_factors n K k L A μ M ell h τ
    (firstOrderCurveDirectRatio n k A)

/-- Terminal height plus all actual regular-stage charges is at most the first-order curve
envelope for any order-one joint factor at least one. -/
theorem SymbolicSeparantChain.Chain.sum_firstOrderCurveStageCharge_add_height_le_of_factors
    {Q terminal : DifferentialPolynomial F[X] 1} {stages : List (Stage F[X] 1)}
    (hc : Chain Q stages terminal) {n K k L A μ M ell h : ℕ}
    (τ : ℕ) (η : ℚ) (hη : 1 ≤ η)
    (hμ : jetWeight Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (hK : 2 ≤ K) (_hk : 0 < k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    (h : ℚ) +
        (stages.map (fun stage ↦
          firstOrderCurveStageCharge n K k L A ell h stage (τ := τ) (η := η))).sum ≤
      firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
  let s := firstOrderCurveJointRatio n L A
  let t := firstOrderCurveFiberRatio n k L
  let c : ℚ := ((ell * (n - L) : ℕ) : ℚ)
  have hs : 1 ≤ s := firstOrderCurveJointRatio_one_le hLA hAn
  have ht : 1 ≤ t := firstOrderCurveFiberRatio_one_le hkL (hLA.trans hAn)
  have hs0 : 0 ≤ s := (by positivity)
  have ht0 : 0 ≤ t := (by positivity)
  have hη0 : 0 ≤ η := (by positivity)
  have hc0 : 0 ≤ c := by positivity
  have hsum := hc.sum_firstOrderStageCharge_le
    (fun v ↦ curveStageZero K ell h s c v (τ := τ))
    (fun v r ↦ curveStageOne K ell h s t c v r (τ := τ) (η := η))
    hμ hM (fun v ↦ curveStageZero_nonneg K ell h hs0 hc0 v (τ := τ))
    (fun v r ↦ curveStageOne_nonneg_of_factors K ell h hs0 hη0 ht0 hc0 v r τ)
    (curveStageZero_mono_of_exponent K ell h hs0 hc0 τ)
    (curveStageOne_mono_total_of_factors K ell h hs0 hη0 ht0 hc0 τ)
    (curveStageOne_mono_derivative_of_factors K ell h hs0 hη0 ht0 hc0 τ)
    (fun v ↦ curveStageZero_le_one_of_factors K ell h hK hs hη ht hc0 v τ)
  change (h : ℚ) + (stages.map (firstOrderStageCharge
    (fun v ↦ curveStageZero K ell h s c v (τ := τ))
    (fun v r ↦ curveStageOne K ell h s t c v r (τ := τ) (η := η)))).sum ≤ _
  calc
    (h : ℚ) + (stages.map (firstOrderStageCharge
        (fun v ↦ curveStageZero K ell h s c v (τ := τ))
        (fun v r ↦ curveStageOne K ell h s t c v r (τ := τ) (η := η)))).sum ≤
        (h : ℚ) + firstOrderStageCap (fun v ↦ curveStageZero K ell h s c v (τ := τ))
          (fun v r ↦ curveStageOne K ell h s t c v r (τ := τ) (η := η)) μ M := by
            simpa [add_comm] using add_le_add_left hsum (h : ℚ)
    _ = firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
      exact firstOrderCurveStageCap_add_height_eq_of_factors n K k L A μ M ell h τ η

/-- Dimension-sensitive specialization using the direct `k`-to-`A` order-one factor. -/
theorem SymbolicSeparantChain.Chain.sum_firstOrderCurveStageCharge_add_height_le_of_exponent
    {Q terminal : DifferentialPolynomial F[X] 1} {stages : List (Stage F[X] 1)}
    (hc : Chain Q stages terminal) {n K k L A μ M ell h : ℕ}
    (τ : ℕ)
    (hμ : jetWeight Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (hK : 2 ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    (h : ℚ) +
        (stages.map (fun stage ↦ firstOrderCurveStageCharge n K k L A ell h stage
          (τ := τ) (η := firstOrderCurveDirectRatio n k A))).sum ≤
      firstOrderCurveBound n K k L A μ M ell h (τ := τ)
        (η := firstOrderCurveDirectRatio n k A) :=
  hc.sum_firstOrderCurveStageCharge_add_height_le_of_factors τ
    (firstOrderCurveDirectRatio n k A)
    (firstOrderCurveDirectRatio_one_le (hkL.trans hLA) hAn)
    hμ hM hK hk hkL hLA hAn

end

end ReedSolomon.HiddenDerivative
