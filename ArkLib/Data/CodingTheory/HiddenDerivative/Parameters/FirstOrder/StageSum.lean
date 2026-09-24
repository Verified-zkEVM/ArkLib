/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageComparison
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import ArkLib.Data.Polynomial.Differential.FirstOrderStageSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Summing first-order polynomial-curve stage charges

This module specializes the cap-sensitive separant-chain bound to the joint and fiber charges of
the first-order curve envelope. It identifies the extremal stage cap with the displayed curve
bound, provides a common incidence-ratio API, and bounds the sum of actual charges along every
separant chain.

## Main statements

* `firstOrderCurveStageCap_add_height_eq_of_factors` identifies the stage cap with the curve
  bound.
* `firstOrderCurveIncidenceRatio_one_le` bounds the common incidence ratio for nested sets.
* `SeparantChain.sum_firstOrderCurveStageCharge_add_height_le_of_factors` bounds the terminal
  height and all stage charges by the curve bound.
* `sum_firstOrderCurveStageCharge_add_height_le_of_directRatio` specializes the order-one factor
  to the direct incidence ratio.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial Polynomial PolynomialDifferential.SeparantChain
open scoped BigOperators

variable {F : Type*} [CommSemiring F]

/-- The incidence ratio for nested coordinate sets of sizes `lower ≤ upper ≤ n`. -/
def firstOrderCurveIncidenceRatio (n lower upper : ℕ) : ℚ :=
  ((n - lower + 1 : ℕ) : ℚ) / (upper - lower + 1 : ℕ)

/-- The joint incidence ratio used by the first-order curve envelope. -/
def firstOrderCurveJointRatio (n L A : ℕ) : ℚ :=
  firstOrderCurveIncidenceRatio n L A

/-- The fiber incidence ratio used by the first-order curve envelope. -/
def firstOrderCurveFiberRatio (n k L : ℕ) : ℚ :=
  firstOrderCurveIncidenceRatio n k L

/-- The direct joint incidence ratio for an order-one stage. -/
def firstOrderCurveDirectRatio (n k A : ℕ) : ℚ :=
  firstOrderCurveIncidenceRatio n k A

/-- The incidence ratio is at least one when the larger set is contained in the `n` coordinates. -/
theorem firstOrderCurveIncidenceRatio_one_le {n lower upper : ℕ} (hLower : lower ≤ upper)
    (hUpper : upper ≤ n) :
    1 ≤ firstOrderCurveIncidenceRatio n lower upper := by
  unfold firstOrderCurveIncidenceRatio
  apply (le_div_iff₀ (by positivity)).2
  push_cast [Nat.cast_sub hLower, Nat.cast_sub (hLower.trans hUpper)]
  nlinarith [show (upper : ℚ) ≤ n by exact_mod_cast hUpper]

/-- The split joint ratio is at least one throughout its geometric range. -/
theorem firstOrderCurveJointRatio_one_le {n L A : ℕ} (hLA : L ≤ A) (hAn : A ≤ n) :
    1 ≤ firstOrderCurveJointRatio n L A := by
  change 1 ≤ firstOrderCurveIncidenceRatio n L A
  exact firstOrderCurveIncidenceRatio_one_le hLA hAn

/-- The fiber ratio is at least one throughout its geometric range. -/
theorem firstOrderCurveFiberRatio_one_le {n k L : ℕ} (hkL : k ≤ L) (hLn : L ≤ n) :
    1 ≤ firstOrderCurveFiberRatio n k L := by
  change 1 ≤ firstOrderCurveIncidenceRatio n k L
  exact firstOrderCurveIncidenceRatio_one_le hkL hLn

/-- The direct order-one joint ratio is at least one throughout its geometric range. -/
theorem firstOrderCurveDirectRatio_one_le {n k A : ℕ} (hkA : k ≤ A) (hAn : A ≤ n) :
    1 ≤ firstOrderCurveDirectRatio n k A := by
  change 1 ≤ firstOrderCurveIncidenceRatio n k A
  exact firstOrderCurveIncidenceRatio_one_le hkA hAn

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
def firstOrderCurveStageCharge (n K k L A ell h : ℕ) (stage : SeparantStage F[X] 1)
    (τ : ℕ) (η : ℚ) : ℚ :=
  firstOrderStageCharge
    (fun v ↦ orderZeroCurveStageCharge ell h (firstOrderCurveJointRatio n L A)
      ((ell * (n - L) : ℕ) : ℚ) v (τ := τ))
    (fun v r ↦ orderOneCurveStageCharge K ell h (firstOrderCurveJointRatio n L A)
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

private theorem sum_curveStageZero_eq (μ M ell h τ : ℕ) (s c : ℚ) :
    (∑ t ∈ Finset.range (μ - min M μ),
        orderZeroCurveStageCharge ell h s c (t + 1) (τ := τ)) =
      s * firstOrderCurveJointZero μ M ell h (τ := τ) +
        c * firstOrderCurveFiberZero μ M := by
  unfold orderZeroCurveStageCharge firstOrderCurveJointZero firstOrderCurveFiberZero
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  simp [firstOrderTaylorTotalCap]

private theorem sum_curveStageOne_eq (K μ M ell h τ : ℕ) (s η t c : ℚ) :
    (∑ j ∈ Finset.Ico (μ - min M μ) μ,
        orderOneCurveStageCharge K ell h s t c (j + 1) (j + 1 - (μ - min M μ))
          (τ := τ) (η := η)) =
      s * η * firstOrderCurveJointOne K μ M ell h (τ := τ) +
        c * t * firstOrderCurveFiberOne K μ M (τ := τ) := by
  rw [sum_Ico_eq_sum_range_ite _ (Nat.sub_le μ (min M μ))]
  unfold orderOneCurveStageCharge firstOrderCurveJointOne firstOrderCurveFiberOne
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
        (fun v ↦ orderZeroCurveStageCharge ell h (firstOrderCurveJointRatio n L A)
          ((ell * (n - L) : ℕ) : ℚ) v (τ := τ))
        (fun v r ↦ orderOneCurveStageCharge K ell h (firstOrderCurveJointRatio n L A)
          (firstOrderCurveFiberRatio n k L) ((ell * (n - L) : ℕ) : ℚ) v r (τ := τ)
          (η := η)) μ M =
      firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
  rw [firstOrderStageCap, sum_curveStageZero_eq, sum_curveStageOne_eq]
  unfold firstOrderCurveBound firstOrderCurveJointRatio firstOrderCurveFiberRatio
    firstOrderCurveIncidenceRatio
  ring_nf

end

end ReedSolomon.HiddenDerivative

namespace PolynomialDifferential.SeparantChain

open Polynomial ReedSolomon.HiddenDerivative

variable {F : Type*} [CommSemiring F]

/-- Terminal height plus all actual regular-stage charges is at most the first-order curve
envelope for any order-one joint factor at least one. -/
theorem sum_firstOrderCurveStageCharge_add_height_le_of_factors
    {Q terminal : DifferentialPolynomial F[X] 1} {stages : List (SeparantStage F[X] 1)}
    (hc : SeparantChain Q stages terminal) {n K k L A μ M ell h : ℕ}
    (τ : ℕ) (η : ℚ) (hη : 1 ≤ η)
    (hμ : jetTotalDegree Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (hK : 2 ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
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
  have hsum := hc.sum_firstOrderStageCharge_le hμ hM
    (fun v ↦ orderZeroCurveStageCharge_nonneg ell h hs0 hc0 v τ)
    (fun v r ↦ orderOneCurveStageCharge_nonneg K ell h hs0 hη0 ht0 hc0 v r τ)
    (orderZeroCurveStageCharge_mono ell h hs0 hc0 τ)
    (fun {_j _w _r} _ _hvw ↦
      orderOneCurveStageCharge_mono_total K ell h hs0 hη0 ht0 hc0 τ _hvw)
    (orderOneCurveStageCharge_mono_derivative K ell h hs0 hη0 ht0 hc0 τ)
    (fun v ↦ orderZeroCurveStageCharge_le_orderOne K ell h hK hs0 hη ht hc0 v τ)
  change (h : ℚ) + (stages.map (firstOrderStageCharge
    (fun v ↦ orderZeroCurveStageCharge ell h s c v (τ := τ))
    (fun v r ↦ orderOneCurveStageCharge K ell h s t c v r (τ := τ) (η := η)))).sum ≤ _
  calc
    (h : ℚ) + (stages.map (firstOrderStageCharge
        (fun v ↦ orderZeroCurveStageCharge ell h s c v (τ := τ))
        (fun v r ↦ orderOneCurveStageCharge K ell h s t c v r (τ := τ) (η := η)))).sum ≤
        (h : ℚ) + firstOrderStageCap (fun v ↦ orderZeroCurveStageCharge ell h s c v (τ := τ))
          (fun v r ↦ orderOneCurveStageCharge K ell h s t c v r (τ := τ) (η := η)) μ M := by
            simpa [add_comm] using add_le_add_left hsum (h : ℚ)
    _ = firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
      exact firstOrderCurveStageCap_add_height_eq_of_factors n K k L A μ M ell h τ η

/-- The stage-charge sum is bounded with the direct `k`-to-`A` order-one factor. -/
theorem sum_firstOrderCurveStageCharge_add_height_le_of_directRatio
    {Q terminal : DifferentialPolynomial F[X] 1} {stages : List (SeparantStage F[X] 1)}
    (hc : SeparantChain Q stages terminal) {n K k L A μ M ell h : ℕ}
    (τ : ℕ)
    (hμ : jetTotalDegree Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (hK : 2 ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    (h : ℚ) +
        (stages.map (fun stage ↦ firstOrderCurveStageCharge n K k L A ell h stage
          (τ := τ) (η := firstOrderCurveDirectRatio n k A))).sum ≤
      firstOrderCurveBound n K k L A μ M ell h (τ := τ)
        (η := firstOrderCurveDirectRatio n k A) :=
  hc.sum_firstOrderCurveStageCharge_add_height_le_of_factors τ
    (firstOrderCurveDirectRatio n k A)
    (firstOrderCurveDirectRatio_one_le (hkL.trans hLA) hAn)
    hμ hM hK hkL hLA hAn

end PolynomialDifferential.SeparantChain
