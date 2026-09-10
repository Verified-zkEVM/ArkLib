/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.DerivativeBidegree
/-!
# The finite first-order curve envelope

The first-derivative cap separates the differential equation's successive separant stages
into two groups. The last `min M μ` stages have order one; the remaining stages have order
zero. Within the order-one block, the derivative degree grows from one to `min M μ`.
Keeping that degree in the Taylor image removes the unused triangular corner from the old
total-degree envelope.

The joint degrees count components while retaining the challenge coordinate. The fiber
degrees count candidates after fixing that coordinate. Their incidence ratios use a split
threshold `L`, between the candidate degree bound `k` and agreement threshold `A`. The
order-one joint count also uses the independent ratio from `k` directly to `A`.

These definitions record the rational expression to be evaluated in concrete examples.
This module alone makes no assertion about the cardinality of an exceptional set.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- Joint degree summed over the order-zero separant stages at common denominator exponent
`τ`. -/
def firstOrderCurveJointZero (_K μ M ell h τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ),
    (h * (1 + τ * t) + (t + 1) * (ell + τ * h))

/-- Fiber degree summed over the order-zero stages. -/
def firstOrderCurveFiberZero (μ M : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ), (t + 1)

/-- Total jet-degree cap of the cleared Taylor coordinates at a stage of degree `j`. -/
def firstOrderTaylorTotalCap (j τ : ℕ) : ℕ :=
  1 + τ * (j - 1)

/-- Distinguished first-derivative cap of the cleared Taylor coordinates. -/
def firstOrderTaylorDerivativeCap (K j r τ : ℕ) : ℕ :=
  min (firstOrderTaylorTotalCap j τ) (τ * (r - 1) + (K - 1))

/-- Cap-sensitive fixed-fiber degree for one order-one stage. -/
def firstOrderCurveFiberStageOne (K j r τ : ℕ) : ℕ :=
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  AffineHilbert.fixedFiberDerivativeImageDegree j r b c

/-- Every nonzero first-order stage degree dominates the order-zero charge at the same total
jet degree. -/
theorem le_firstOrderCurveFiberStageOne {K j r τ : ℕ}
    (hK : 2 ≤ K) :
    j ≤ firstOrderCurveFiberStageOne K j r τ := by
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  have hc : 0 < c := by
    dsimp only [c]
    unfold firstOrderTaylorDerivativeCap firstOrderTaylorTotalCap
    apply lt_min (by omega)
    omega
  unfold firstOrderCurveFiberStageOne AffineHilbert.fixedFiberDerivativeImageDegree
  exact (Nat.le_mul_of_pos_right j hc).trans (Nat.le_add_right _ _)

/-- Cap-sensitive joint-image degree for one order-one stage. -/
def firstOrderCurveJointStageOne (K ell h j r τ : ℕ) : ℕ :=
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  AffineHilbert.mixedDerivativeImageDegree h j r (ell + τ * h) b c

/-- The fixed-fiber stage degree increases with the total jet degree while the derivative
degree is held fixed. The side condition is the intrinsic derivative-degree bound. -/
theorem firstOrderCurveFiberStageOne_mono_total {K τ j w r : ℕ}
    (hrj : r ≤ j) (hjw : j ≤ w) :
    firstOrderCurveFiberStageOne K j r τ ≤
      firstOrderCurveFiberStageOne K w r τ := by
  let bj := firstOrderTaylorTotalCap j τ
  let bw := firstOrderTaylorTotalCap w τ
  let cj := firstOrderTaylorDerivativeCap K j r τ
  let cw := firstOrderTaylorDerivativeCap K w r τ
  have hb : bj ≤ bw := by
    unfold bj bw firstOrderTaylorTotalCap
    gcongr
  have hc : cj ≤ cw := by
    unfold cj cw firstOrderTaylorDerivativeCap
    exact min_le_min_right _ hb
  have hcj : cj ≤ bj := by exact min_le_left _ _
  have hcw : cw ≤ bw := by exact min_le_left _ _
  have hz : (j : ℤ) * cj + r * (bj - cj) ≤
      (w : ℤ) * cw + r * (bw - cw) := by
    nlinarith
  unfold firstOrderCurveFiberStageOne
  exact_mod_cast hz

/-- At a fixed total jet degree, the fixed-fiber stage degree increases with the actual
first-derivative degree. -/
theorem firstOrderCurveFiberStageOne_mono_derivative {K τ j r q : ℕ}
    (hrq : r ≤ q) (hqj : q ≤ j) :
    firstOrderCurveFiberStageOne K j r τ ≤
      firstOrderCurveFiberStageOne K j q τ := by
  let b := firstOrderTaylorTotalCap j τ
  let cr := firstOrderTaylorDerivativeCap K j r τ
  let cq := firstOrderTaylorDerivativeCap K j q τ
  have hc : cr ≤ cq := by
    unfold cr cq firstOrderTaylorDerivativeCap
    apply min_le_min_left
    gcongr
  have hcr : cr ≤ b := by exact min_le_left _ _
  have hcq : cq ≤ b := by exact min_le_left _ _
  have hz : (j : ℤ) * cr + r * (b - cr) ≤
      (j : ℤ) * cq + q * (b - cq) := by
    nlinarith
  unfold firstOrderCurveFiberStageOne
  exact_mod_cast hz

/-- Forgetting the separate derivative cap recovers the old full-triangle fiber bound. -/
theorem firstOrderCurveFiberStageOne_le_full {K j r τ : ℕ} (hrj : r ≤ j) :
    firstOrderCurveFiberStageOne K j r τ ≤
      j * firstOrderTaylorTotalCap j τ := by
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  have hcb : c ≤ b := min_le_left _ _
  rw [firstOrderCurveFiberStageOne]
  rw [AffineHilbert.fixedFiberDerivativeImageDegree_eq hrj hcb]
  calc
    (j - r) * c + r * b ≤ (j - r) * b + r * b := by gcongr
    _ = j * b := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hrj]

/-- The joint-image stage degree increases with the total jet degree while the derivative
degree is held fixed. -/
theorem firstOrderCurveJointStageOne_mono_total {K ell h τ j w r : ℕ}
    (hrj : r ≤ j) (hjw : j ≤ w) :
    firstOrderCurveJointStageOne K ell h j r τ ≤
      firstOrderCurveJointStageOne K ell h w r τ := by
  have hB := firstOrderCurveFiberStageOne_mono_total (K := K) (τ := τ) hrj hjw
  have hb : firstOrderTaylorTotalCap j τ ≤ firstOrderTaylorTotalCap w τ := by
    unfold firstOrderTaylorTotalCap
    gcongr
  have hc : firstOrderTaylorDerivativeCap K j r τ ≤
      firstOrderTaylorDerivativeCap K w r τ := by
    unfold firstOrderTaylorDerivativeCap
    exact min_le_min_right _ hb
  have hcj : firstOrderTaylorDerivativeCap K j r τ ≤
      firstOrderTaylorTotalCap j τ := min_le_left _ _
  have hcw : firstOrderTaylorDerivativeCap K w r τ ≤
      firstOrderTaylorTotalCap w τ := min_le_left _ _
  have hjarea : firstOrderTaylorDerivativeCap K j r τ ^ 2 ≤
      2 * firstOrderTaylorTotalCap j τ * firstOrderTaylorDerivativeCap K j r τ := by
    nlinarith
  have hwarea : firstOrderTaylorDerivativeCap K w r τ ^ 2 ≤
      2 * firstOrderTaylorTotalCap w τ * firstOrderTaylorDerivativeCap K w r τ := by
    nlinarith
  have hz : (2 * firstOrderTaylorTotalCap j τ *
        firstOrderTaylorDerivativeCap K j r τ -
          firstOrderTaylorDerivativeCap K j r τ ^ 2 : ℤ) ≤
      2 * firstOrderTaylorTotalCap w τ *
        firstOrderTaylorDerivativeCap K w r τ -
          firstOrderTaylorDerivativeCap K w r τ ^ 2 := by
    nlinarith
  unfold firstOrderCurveJointStageOne
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left h (by exact_mod_cast hz)
  · exact Nat.mul_le_mul_left _ hB

/-- The joint-image stage degree increases with the actual first-derivative degree at a
fixed total jet degree. -/
theorem firstOrderCurveJointStageOne_mono_derivative {K ell h τ j r q : ℕ}
    (hrq : r ≤ q) (hqj : q ≤ j) :
    firstOrderCurveJointStageOne K ell h j r τ ≤
      firstOrderCurveJointStageOne K ell h j q τ := by
  have hB := firstOrderCurveFiberStageOne_mono_derivative (K := K) (τ := τ) hrq hqj
  have hc : firstOrderTaylorDerivativeCap K j r τ ≤
      firstOrderTaylorDerivativeCap K j q τ := by
    unfold firstOrderTaylorDerivativeCap firstOrderTaylorTotalCap
    apply min_le_min_left
    gcongr
  have hcr : firstOrderTaylorDerivativeCap K j r τ ≤
      firstOrderTaylorTotalCap j τ := min_le_left _ _
  have hcq : firstOrderTaylorDerivativeCap K j q τ ≤
      firstOrderTaylorTotalCap j τ := min_le_left _ _
  have hrarea : firstOrderTaylorDerivativeCap K j r τ ^ 2 ≤
      2 * firstOrderTaylorTotalCap j τ * firstOrderTaylorDerivativeCap K j r τ := by
    nlinarith
  have hqarea : firstOrderTaylorDerivativeCap K j q τ ^ 2 ≤
      2 * firstOrderTaylorTotalCap j τ * firstOrderTaylorDerivativeCap K j q τ := by
    nlinarith
  have hz : (2 * firstOrderTaylorTotalCap j τ *
        firstOrderTaylorDerivativeCap K j r τ -
          firstOrderTaylorDerivativeCap K j r τ ^ 2 : ℤ) ≤
      2 * firstOrderTaylorTotalCap j τ *
        firstOrderTaylorDerivativeCap K j q τ -
          firstOrderTaylorDerivativeCap K j q τ ^ 2 := by
    nlinarith
  unfold firstOrderCurveJointStageOne
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left h (by exact_mod_cast hz)
  · exact Nat.mul_le_mul_left _ hB

/-- Fiber degree summed over the order-one stages, retaining the actual derivative degree
within the extremal separant schedule. -/
def firstOrderCurveFiberOne (K μ M τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then
      firstOrderCurveFiberStageOne K (t + 1) (t + 1 - (μ - min M μ)) τ
    else 0

/-- Joint degree summed over the order-one stages, retaining the actual derivative degree
within the extremal separant schedule. -/
def firstOrderCurveJointOne (K μ M ell h τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then
      firstOrderCurveJointStageOne K ell h (t + 1) (t + 1 - (μ - min M μ)) τ
    else 0

/-- The rational expression for polynomial-curve exceptional challenges. The common Taylor
exponent and direct order-one joint factor are explicit parameters. -/
def firstOrderCurveBound (n K k L A μ M ell h τ : ℕ) (η : ℚ) : ℚ :=
  let l₁ : ℚ := ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)
  let l₂ : ℚ := ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)
  h + l₁ * firstOrderCurveJointZero K μ M ell h τ +
    l₁ * η * firstOrderCurveJointOne K μ M ell h τ +
    ((ell * (n - L) : ℕ) : ℚ) *
      (firstOrderCurveFiberZero μ M + l₂ * firstOrderCurveFiberOne K μ M τ)

/-- The first-order curve envelope is monotone in its direct joint-incidence factor. -/
theorem firstOrderCurveBound_mono_directFactor
    (n K k L A μ M ell h τ : ℕ) :
    Monotone fun η : ℚ ↦ firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
  intro η η' hη
  have hl₁ : (0 : ℚ) ≤ ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hJ : (0 : ℚ) ≤ firstOrderCurveJointOne K μ M ell h (τ := τ) := by
    exact_mod_cast Nat.zero_le (firstOrderCurveJointOne K μ M ell h (τ := τ))
  have hmiddle :
      (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)) * η *
          firstOrderCurveJointOne K μ M ell h (τ := τ) ≤
        (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)) * η' *
          firstOrderCurveJointOne K μ M ell h (τ := τ) := by
    calc
      _ = (↑(firstOrderCurveJointOne K μ M ell h (τ := τ)) *
          (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ))) * η := by ac_rfl
      _ ≤ (↑(firstOrderCurveJointOne K μ M ell h (τ := τ)) *
          (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ))) * η' :=
        mul_le_mul_of_nonneg_left hη (mul_nonneg hJ hl₁)
      _ = _ := by ac_rfl
  unfold firstOrderCurveBound
  dsimp only
  simpa only [add_assoc, add_comm, add_left_comm] using
    (add_le_add_right (add_le_add_left hmiddle
      ((h : ℚ) + (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)) *
        firstOrderCurveJointZero K μ M ell h (τ := τ)))
      (((ell * (n - L) : ℕ) : ℚ) *
        (firstOrderCurveFiberZero μ M +
          (((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)) *
            firstOrderCurveFiberOne K μ M (τ := τ))))

end ReedSolomon.HiddenDerivative
