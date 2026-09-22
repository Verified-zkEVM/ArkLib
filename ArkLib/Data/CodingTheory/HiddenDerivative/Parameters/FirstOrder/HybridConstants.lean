/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

/-!
# Constants of the first-order list and exception bounds

Fix a candidate degree `D = k - 1`, a total jet-degree cap `μ` and a first-derivative cap
`M ≤ μ`. On a regular chart the order-one stages use the common denominator exponent `2 D - 3`
(`regularTaylorExponent`). An equation of actual first-derivative degree `e ≤ M` has `e`
order-one stages, and their fixed-fiber and joint degrees sum to `regularFiberStageSum D μ e`
and `regularJointStageSum D h μ e`. Both are bounded by multiples of the staircase

`T = ∑_{r=1}^{M} r (2 (μ - M) + r) = (μ - M) M (M + 1) + M (M + 1) (2 M + 1) / 6`

(`stageStaircaseSum`, `stageStaircase`): the fiber sum by `2 D T` and the joint sum by
`(12 D² h + 4 D) T`, uniformly in `e ≤ M`.

The constants come in three forms.

* The charges at a fixed actual degree `e`: the list charge `θ B₁(e) + μ - e`
  (`firstOrderListCharge`), and, at a coordinate split `L`, the exception charge
  (`firstOrderExceptionCharge`). The latter is the sum of the ordinary-tail charge
  (`ordinaryTailCharge`), the joint charge weighted by the retained-coordinate ratio
  `(n - L + 1) / (A - L + 1)` and `θ`, and the fiber charge weighted by `n - L` and the
  fixed-coordinate ratio `(n - D) / (L - D)`.
* The optimized constants: the maximum over `e ≤ M` of the list charge
  (`maxFirstOrderListCharge`), and the maximum over `e ≤ M` of the minimum over the splits
  `D < L ≤ A` of the exception charge (`maxMinFirstOrderExceptionCharge`). Their natural ceilings
  are `firstOrderListBound` and `firstOrderExceptionBound`.
* The closed constants `Λ = 2 D θ T + μ - M` (`firstOrderListConstant`) and
  `E = E₀ + (24 D² h + 8 D) θ² T + 4 D (n - D - 1) θ T` (`firstOrderExceptionConstant`), where
  `E₀` is the ordinary-tail charge at `μ`.

Here `θ = (n - D) / (A - D)` is the agreement-incidence ratio (`agreementIncidenceRatio`). The
optimized constants are at most the closed ones. For the exception constant this uses the
balanced split `L = D + ⌈(A - D) / 2⌉` (`balancedSplit`), at which both coordinate ratios are at
most `2 θ`. All comparisons are between real numbers, before any ceiling is taken.

## Main statements

* `cast_stageStaircaseSum`: the closed form of the staircase.
* `regularFiberStageSum_cast_le`, `regularJointStageSum_cast_le`: the stage sums at any `e ≤ M`
  are at most `2 D T` and `(12 D² h + 4 D) T`.
* `firstOrderListCharge_mono`, `firstOrderListCharge_le_firstOrderListConstant`: the list charge
  increases with `e` and is at most `Λ`.
* `retainedCoordinateRatio_balancedSplit_le`, `fixedCoordinateRatio_balancedSplit_le`: both
  coordinate ratios at the balanced split are at most `2 θ`.
* `firstOrderExceptionCharge_balancedSplit_le`: the exception charge at the balanced split is at
  most `E`.
* `maxFirstOrderListCharge_le_firstOrderListConstant`,
  `maxMinFirstOrderExceptionCharge_le_firstOrderExceptionConstant`: the optimized constants are at
  most the closed ones.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-! ### Regular-stage sums and the staircase -/

/-- The common denominator exponent `2 D - 3` of the cleared Taylor coordinates at an order-one
stage of a regular chart in degree `D`. It is `0` for `D ≤ 1`. -/
def regularTaylorExponent (D : ℕ) : ℕ := 2 * D - 3

/-- The fixed-fiber degrees of the `e` order-one stages in degree `D` with total jet-degree cap
`μ`, summed: the stage `i < e` has total jet degree `μ - i` and first-derivative degree `e - i`. -/
def regularFiberStageSum (D μ e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range e,
    firstOrderCurveFiberStageOne (D + 1) (μ - i) (e - i) (regularTaylorExponent D)

/-- The joint degrees of the `e` order-one stages in degree `D` with total jet-degree cap `μ` and
challenge degree `h`, summed: the stage `i < e` has total jet degree `μ - i` and first-derivative
degree `e - i`. -/
def regularJointStageSum (D h μ e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range e,
    firstOrderCurveJointStageOne (D + 1) 1 h (μ - i) (e - i) (regularTaylorExponent D)

/-- The staircase `∑_{r=1}^{e} r (2 (μ - e) + r)`. -/
def stageStaircaseSum (μ e : ℕ) : ℕ :=
  ∑ r ∈ Finset.range e, (r + 1) * (2 * (μ - e) + (r + 1))

/-- The closed form `(μ - M) M (M + 1) + M (M + 1) (2 M + 1) / 6` of the staircase
`stageStaircaseSum μ M`. -/
def stageStaircase (μ M : ℕ) : ℝ :=
  ((μ - M : ℕ) : ℝ) * M * (M + 1) + (M : ℝ) * (M + 1) * (2 * M + 1) / 6

/-- The closed form of the staircase is nonnegative. -/
theorem stageStaircase_nonneg (μ M : ℕ) : 0 ≤ stageStaircase μ M := by
  unfold stageStaircase
  positivity

private theorem sum_range_succ_mul_two_mul_add (d : ℝ) (M : ℕ) :
    ∑ r ∈ Finset.range M, ((r : ℝ) + 1) * (2 * d + ((r : ℝ) + 1)) =
      d * M * (M + 1) + (M : ℝ) * (M + 1) * (2 * M + 1) / 6 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The staircase equals its closed form. -/
theorem cast_stageStaircaseSum (μ M : ℕ) : (stageStaircaseSum μ M : ℝ) = stageStaircase μ M := by
  rw [stageStaircaseSum, stageStaircase, ← sum_range_succ_mul_two_mul_add]
  push_cast
  rfl

/-- The staircase indexed by the descending stages `i < e`, with first-derivative degree `e - i`
and total jet degree `μ - i`. -/
theorem stageStaircaseSum_eq_sum_stages {μ e : ℕ} (heμ : e ≤ μ) :
    stageStaircaseSum μ e = ∑ i ∈ Finset.range e, (e - i) * (2 * (μ - i) - (e - i)) := by
  rw [stageStaircaseSum, ← Finset.sum_range_reflect (fun r ↦ (r + 1) * (2 * (μ - e) + (r + 1))) e]
  apply Finset.sum_congr rfl
  intro i hi
  have hie : i < e := Finset.mem_range.mp hi
  rw [show e - 1 - i + 1 = e - i by omega, show 2 * (μ - e) + (e - i) = 2 * (μ - i) - (e - i) by
    omega]

/-- For `1 ≤ D` and `1 ≤ j`, the total-degree cap at the regular exponent is at most `2 D j`. -/
theorem firstOrderTaylorTotalCap_le_two_mul {D j : ℕ} (hD : 1 ≤ D) (hj : 1 ≤ j) :
    firstOrderTaylorTotalCap j (regularTaylorExponent D) ≤ 2 * D * j := by
  by_cases hDone : D = 1
  · subst D
    simp [firstOrderTaylorTotalCap, regularTaylorExponent]
    omega
  unfold firstOrderTaylorTotalCap regularTaylorExponent
  zify [(by omega : 3 ≤ 2 * D), hj]
  nlinarith

/-- For `1 ≤ D` and `1 ≤ q`, the first-derivative cap at the regular exponent is at most
`2 D q`. -/
theorem firstOrderTaylorDerivativeCap_le_two_mul {D j q : ℕ} (hD : 1 ≤ D) (hq : 1 ≤ q) :
    firstOrderTaylorDerivativeCap (D + 1) j q (regularTaylorExponent D) ≤ 2 * D * q := by
  by_cases hDone : D = 1
  · subst D
    simp [firstOrderTaylorDerivativeCap, regularTaylorExponent]
    omega
  refine (min_le_right _ _).trans ?_
  unfold regularTaylorExponent
  rw [Nat.add_sub_cancel]
  zify [(by omega : 3 ≤ 2 * D), hq]
  nlinarith

/-- For `1 ≤ D` and `1 ≤ q ≤ j`, the fixed-fiber stage degree at the regular exponent is at most
`2 D q (2 j - q)`. -/
theorem firstOrderCurveFiberStageOne_regularTaylorExponent_le {D j q : ℕ} (hD : 1 ≤ D)
    (hq : 1 ≤ q) (hqj : q ≤ j) :
    firstOrderCurveFiberStageOne (D + 1) j q (regularTaylorExponent D) ≤
      2 * D * q * (2 * j - q) := by
  have hCB : 2 * D * q ≤ 2 * D * j := Nat.mul_le_mul_left _ hqj
  calc
    _ ≤ MvPolynomial.cappedDegreeMixedVolume j q (2 * D * j) (2 * D * q) :=
      MvPolynomial.cappedDegreeMixedVolume_mono_right hqj
        (firstOrderTaylorDerivativeCap_le_totalCap ..) hCB
        (firstOrderTaylorTotalCap_le_two_mul hD (hq.trans hqj))
        (firstOrderTaylorDerivativeCap_le_two_mul hD hq)
    _ = 2 * D * q * (2 * j - q) := by
      rw [MvPolynomial.cappedDegreeMixedVolume_eq hqj hCB]
      zify [hqj, (by omega : q ≤ 2 * j)]
      ring

/-- For `1 ≤ D` and `1 ≤ q ≤ j`, the joint stage degree at the regular exponent with `ℓ = 1` is
at most `(12 D² h + 4 D) q (2 j - q)`. -/
theorem firstOrderCurveJointStageOne_regularTaylorExponent_le {D h j q : ℕ} (hD : 1 ≤ D)
    (hq : 1 ≤ q) (hqj : q ≤ j) :
    firstOrderCurveJointStageOne (D + 1) 1 h j q (regularTaylorExponent D) ≤
      (12 * D ^ 2 * h + 4 * D) * (q * (2 * j - q)) := by
  have hCB : 2 * D * q ≤ 2 * D * j := Nat.mul_le_mul_left _ hqj
  have ha : 1 + regularTaylorExponent D * h ≤ 1 + 2 * D * h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right h (Nat.sub_le _ _)) 1
  calc
    _ ≤ MvPolynomial.cappedBidegreeMixedVolume h j q (1 + 2 * D * h) (2 * D * j) (2 * D * q) :=
      MvPolynomial.cappedBidegreeMixedVolume_mono_right hqj
        (firstOrderTaylorDerivativeCap_le_totalCap ..) hCB ha
        (firstOrderTaylorTotalCap_le_two_mul hD (hq.trans hqj))
        (firstOrderTaylorDerivativeCap_le_two_mul hD hq)
    _ = (12 * D ^ 2 * h + 4 * D) * (q * (2 * j - q)) := by
      rw [MvPolynomial.cappedBidegreeMixedVolume_eq hCB]
      zify [hqj, hCB, (by omega : q ≤ 2 * j),
        hCB.trans (Nat.le_mul_of_pos_left (2 * D * j) two_pos)]
      ring

/-- For `1 ≤ D` and `e ≤ μ`, the fiber stage sum is at most `2 D` times the staircase. -/
theorem regularFiberStageSum_le {D μ e : ℕ} (hD : 1 ≤ D) (heμ : e ≤ μ) :
    regularFiberStageSum D μ e ≤ 2 * D * stageStaircaseSum μ e := by
  rw [regularFiberStageSum, stageStaircaseSum_eq_sum_stages heμ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hie : i < e := Finset.mem_range.mp hi
  simpa only [mul_assoc] using
    firstOrderCurveFiberStageOne_regularTaylorExponent_le hD (show 1 ≤ e - i by omega)
      (show e - i ≤ μ - i by omega)

/-- For `1 ≤ D` and `e ≤ μ`, the joint stage sum is at most `12 D² h + 4 D` times the
staircase. -/
theorem regularJointStageSum_le {D h μ e : ℕ} (hD : 1 ≤ D) (heμ : e ≤ μ) :
    regularJointStageSum D h μ e ≤ (12 * D ^ 2 * h + 4 * D) * stageStaircaseSum μ e := by
  rw [regularJointStageSum, stageStaircaseSum_eq_sum_stages heμ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    firstOrderCurveJointStageOne_regularTaylorExponent_le hD
      (show 1 ≤ e - i by have := Finset.mem_range.mp hi; omega) (show e - i ≤ μ - i by omega)

/-- For `1 ≤ D` and `e < μ`, one more order-one stage increases the fiber stage sum by at least
one. -/
theorem regularFiberStageSum_add_one_le_succ {D μ e : ℕ} (hD : 1 ≤ D) (heμ : e + 1 ≤ μ) :
    regularFiberStageSum D μ e + 1 ≤ regularFiberStageSum D μ (e + 1) := by
  unfold regularFiberStageSum
  rw [Finset.sum_range_succ]
  refine Nat.add_le_add (Finset.sum_le_sum fun i hi ↦ ?_) ?_
  · have hie : i < e := Finset.mem_range.mp hi
    exact firstOrderCurveFiberStageOne_mono_derivative (by omega) (by omega)
  · exact (show 1 ≤ μ - e by omega).trans (le_firstOrderCurveFiberStageOne (by omega))

/-- For `e ≤ M ≤ μ`, the closed staircase at `e` is at most the one at `M`. -/
theorem stageStaircase_mono {μ e M : ℕ} (heM : e ≤ M) (hMμ : M ≤ μ) :
    stageStaircase μ e ≤ stageStaircase μ M := by
  induction M, heM using Nat.le_induction with
  | base => exact le_rfl
  | succ M heM ih =>
    refine (ih (by omega)).trans ?_
    have hstep : stageStaircase μ (M + 1) =
        stageStaircase μ M + ((M : ℝ) + 1) * (2 * (μ : ℝ) - 2 * M - 1) := by
      unfold stageStaircase
      rw [Nat.cast_sub (by omega : M ≤ μ), Nat.cast_sub hMμ]
      push_cast
      ring
    have hfactor : (0 : ℝ) ≤ 2 * (μ : ℝ) - 2 * M - 1 := by
      have : ((2 * M + 1 : ℕ) : ℝ) ≤ (2 * μ : ℕ) := by exact_mod_cast (by omega)
      push_cast at this
      linarith
    rw [hstep]
    nlinarith

/-- For `1 ≤ D` and `e ≤ M ≤ μ`, the fiber stage sum at `e` is at most `2 D T` for the staircase
`T` at `M`. -/
theorem regularFiberStageSum_cast_le {D μ M e : ℕ} (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    (regularFiberStageSum D μ e : ℝ) ≤ 2 * D * stageStaircase μ M := by
  calc
    (regularFiberStageSum D μ e : ℝ) ≤ (2 * D * stageStaircaseSum μ e : ℕ) := by
      exact_mod_cast regularFiberStageSum_le hD (heM.trans hMμ)
    _ = 2 * D * stageStaircase μ e := by push_cast; rw [cast_stageStaircaseSum]
    _ ≤ 2 * D * stageStaircase μ M := by gcongr; exact stageStaircase_mono heM hMμ

/-- For `1 ≤ D` and `e ≤ M ≤ μ`, the joint stage sum at `e` is at most `(12 D² h + 4 D) T` for
the staircase `T` at `M`. -/
theorem regularJointStageSum_cast_le {D h μ M e : ℕ} (hD : 1 ≤ D) (heM : e ≤ M)
    (hMμ : M ≤ μ) :
    (regularJointStageSum D h μ e : ℝ) ≤ (12 * D ^ 2 * h + 4 * D) * stageStaircase μ M := by
  calc
    (regularJointStageSum D h μ e : ℝ) ≤
        ((12 * D ^ 2 * h + 4 * D) * stageStaircaseSum μ e : ℕ) := by
      exact_mod_cast regularJointStageSum_le hD (heM.trans hMμ)
    _ = (12 * D ^ 2 * h + 4 * D) * stageStaircase μ e := by
      push_cast; rw [cast_stageStaircaseSum]
    _ ≤ (12 * D ^ 2 * h + 4 * D) * stageStaircase μ M := by
      gcongr; exact stageStaircase_mono heM hMμ

/-! ### The list constant -/

/-- The list charge `θ B₁(e) + μ - e` at actual first-derivative degree `e`, where `B₁(e)` is the
fiber stage sum. -/
def firstOrderListCharge (θ : ℝ) (D μ e : ℕ) : ℝ :=
  θ * regularFiberStageSum D μ e + (μ - e : ℕ)

/-- The closed list constant `Λ = 2 D θ T + μ - M`, where `T` is the staircase at `M`. -/
def firstOrderListConstant (θ : ℝ) (D μ M : ℕ) : ℝ :=
  2 * D * θ * stageStaircase μ M + (μ - M : ℕ)

/-- For `1 ≤ θ`, `1 ≤ D` and `e < μ`, the list charge increases from `e` to `e + 1`. -/
theorem firstOrderListCharge_le_succ {θ : ℝ} {D μ e : ℕ} (hθ : 1 ≤ θ) (hD : 1 ≤ D)
    (heμ : e + 1 ≤ μ) :
    firstOrderListCharge θ D μ e ≤ firstOrderListCharge θ D μ (e + 1) := by
  have hB : (regularFiberStageSum D μ e : ℝ) + 1 ≤ regularFiberStageSum D μ (e + 1) := by
    exact_mod_cast regularFiberStageSum_add_one_le_succ hD heμ
  unfold firstOrderListCharge
  rw [Nat.cast_sub (by omega : e ≤ μ), Nat.cast_sub heμ]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ θ by linarith)]

/-- For `1 ≤ θ`, `1 ≤ D` and `e ≤ M ≤ μ`, the list charge at `e` is at most the one at `M`. -/
theorem firstOrderListCharge_mono {θ : ℝ} {D μ e M : ℕ} (hθ : 1 ≤ θ) (hD : 1 ≤ D)
    (heM : e ≤ M) (hMμ : M ≤ μ) :
    firstOrderListCharge θ D μ e ≤ firstOrderListCharge θ D μ M := by
  induction M, heM using Nat.le_induction with
  | base => exact le_rfl
  | succ M _ ih => exact (ih (by omega)).trans (firstOrderListCharge_le_succ hθ hD hMμ)

/-- For `1 ≤ θ`, `1 ≤ D` and `e ≤ M ≤ μ`, the list charge at `e` is at most `Λ`. -/
theorem firstOrderListCharge_le_firstOrderListConstant {θ : ℝ} {D μ e M : ℕ} (hθ : 1 ≤ θ)
    (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    firstOrderListCharge θ D μ e ≤ firstOrderListConstant θ D μ M := by
  refine (firstOrderListCharge_mono hθ hD heM hMμ).trans ?_
  unfold firstOrderListCharge firstOrderListConstant
  have hB := regularFiberStageSum_cast_le hD le_rfl hMμ
  nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ θ by linarith)]

/-! ### Coordinate ratios and the balanced split -/

/-- The ordinary-tail charge at degree `b`: `h` for `b = 0`, and otherwise
`(2 b - 1) h + θ (h + b + 4 D b h) + (n - D - 1) b`. -/
def ordinaryTailCharge (θ : ℝ) (n D h b : ℕ) : ℝ :=
  if b = 0 then h else (2 * b - 1 : ℕ) * h + θ * (h + b + 4 * D * b * h) + (n - D - 1 : ℕ) * b

/-- For `0 ≤ θ` and `b ≤ μ`, the ordinary-tail charge at `b` is at most the one at `μ`. -/
theorem ordinaryTailCharge_le {θ : ℝ} {n D h b μ : ℕ} (hθ : 0 ≤ θ) (hbμ : b ≤ μ) :
    ordinaryTailCharge θ n D h b ≤ ordinaryTailCharge θ n D h μ := by
  rcases Nat.eq_zero_or_pos μ with rfl | hμ
  · rw [Nat.le_zero.mp hbμ]
  unfold ordinaryTailCharge
  simp only [show μ ≠ 0 by omega, ↓reduceIte]
  split_ifs with hb
  · have hfirst : (h : ℝ) ≤ (2 * μ - 1 : ℕ) * h := by
      exact_mod_cast Nat.le_mul_of_pos_left h (by omega)
    have : (0 : ℝ) ≤ θ * (h + μ + 4 * D * μ * h) := by positivity
    have : (0 : ℝ) ≤ ((n - D - 1 : ℕ) : ℝ) * μ := by positivity
    linarith
  · gcongr

/-- The agreement-incidence ratio `θ = (n - D) / (A - D)`. -/
def agreementIncidenceRatio (n D A : ℕ) : ℝ :=
  ((n - D : ℕ) : ℝ) / (A - D : ℕ)

/-- The retained-coordinate ratio `(n - L + 1) / (A - L + 1)` at the split `L`. -/
def retainedCoordinateRatio (n A L : ℕ) : ℝ :=
  ((n - L + 1 : ℕ) : ℝ) / (A - L + 1 : ℕ)

/-- The fixed-coordinate ratio `(n - D) / (L - D)` at the split `L`. -/
def fixedCoordinateRatio (n D L : ℕ) : ℝ :=
  ((n - D : ℕ) : ℝ) / (L - D : ℕ)

/-- The balanced split `D + ⌈(A - D) / 2⌉`, computed as `D + (A - D + 1) / 2`. -/
def balancedSplit (D A : ℕ) : ℕ :=
  D + (A - D + 1) / 2

/-- For `D < A ≤ n`, the agreement-incidence ratio is at least `1`. -/
theorem one_le_agreementIncidenceRatio {n D A : ℕ} (hDA : D < A) (hAn : A ≤ n) :
    1 ≤ agreementIncidenceRatio n D A := by
  unfold agreementIncidenceRatio
  rw [one_le_div (by exact_mod_cast Nat.sub_pos_of_lt hDA)]
  exact_mod_cast Nat.sub_le_sub_right hAn D

/-- For `D < A`, the balanced split lies above `D`. -/
theorem lt_balancedSplit {D A : ℕ} (hDA : D < A) : D < balancedSplit D A := by
  unfold balancedSplit
  omega

/-- For `D ≤ A`, the balanced split is at most `A`. -/
theorem balancedSplit_le {D A : ℕ} (hDA : D ≤ A) : balancedSplit D A ≤ A := by
  unfold balancedSplit
  omega

/-- For `D < A`, the split removes at least one coordinate after `D`: `n - L ≤ n - D - 1`. -/
theorem sub_balancedSplit_le {n D A : ℕ} (hDA : D < A) : n - balancedSplit D A ≤ n - D - 1 := by
  unfold balancedSplit
  omega

/-- The balanced split is `D + ⌈(A - D) / 2⌉`. -/
theorem balancedSplit_eq_add_ceil (D A : ℕ) :
    balancedSplit D A = D + ⌈(((A - D : ℕ) : ℝ) / 2)⌉₊ := by
  unfold balancedSplit
  congr 1
  rcases Nat.even_or_odd (A - D) with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, show m + m + 1 = 2 * m + 1 by ring, show ((m + m : ℕ) : ℝ) / 2 = m by push_cast; ring,
      Nat.ceil_natCast]
    omega
  · rw [hm, show ((2 * m + 1 : ℕ) : ℝ) / 2 = m + 1 / 2 by push_cast; ring]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.mul_div_cancel_left _ two_pos, eq_comm,
      Nat.ceil_eq_iff (by omega)]
    push_cast
    constructor <;> linarith

/-- For `D < A` and `D < n`, the retained-coordinate ratio at the balanced split is at most
`2 θ`. -/
theorem retainedCoordinateRatio_balancedSplit_le {n D A : ℕ} (hDA : D < A) (hDn : D < n) :
    retainedCoordinateRatio n A (balancedSplit D A) ≤ 2 * agreementIncidenceRatio n D A := by
  unfold retainedCoordinateRatio agreementIncidenceRatio balancedSplit
  set r := (A - D + 1) / 2
  have hnum : n - (D + r) + 1 ≤ n - D := by omega
  have hden : A - D ≤ 2 * (A - (D + r) + 1) := by omega
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by exact_mod_cast (by omega : 0 < A - D))]
  have := Nat.mul_le_mul hnum hden
  calc
    ((n - (D + r) + 1 : ℕ) : ℝ) * (A - D : ℕ) ≤ ((n - D) * (2 * (A - (D + r) + 1)) : ℕ) := by
      exact_mod_cast this
    _ = _ := by push_cast; ring

/-- The fixed-coordinate ratio at the balanced split is at most `2 θ`. Both are `0` for
`A ≤ D`. -/
theorem fixedCoordinateRatio_balancedSplit_le (n D A : ℕ) :
    fixedCoordinateRatio n D (balancedSplit D A) ≤ 2 * agreementIncidenceRatio n D A := by
  unfold fixedCoordinateRatio agreementIncidenceRatio balancedSplit
  rcases le_or_gt A D with hAD | hDA
  · simp [Nat.sub_eq_zero_of_le hAD]
  set r := (A - D + 1) / 2
  rw [show D + r - D = r by omega, mul_div_assoc',
    div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < r))
      (by exact_mod_cast (by omega : 0 < A - D))]
  have : (A - D : ℕ) ≤ 2 * r := by omega
  have : ((A - D : ℕ) : ℝ) ≤ 2 * r := by exact_mod_cast this
  nlinarith [(Nat.cast_nonneg (n - D) : (0 : ℝ) ≤ (n - D : ℕ))]

/-! ### The exception constant -/

/-- The exception charge at actual first-derivative degree `e` and split `L`: the ordinary-tail
charge at `μ - e`, plus the joint stage sum weighted by the retained-coordinate ratio and `θ`,
plus the fiber stage sum weighted by `n - L` and the fixed-coordinate ratio. -/
def firstOrderExceptionCharge (θ : ℝ) (n D A h μ e L : ℕ) : ℝ :=
  ordinaryTailCharge θ n D h (μ - e) +
    retainedCoordinateRatio n A L * θ * regularJointStageSum D h μ e +
    (n - L : ℕ) * fixedCoordinateRatio n D L * regularFiberStageSum D μ e

/-- The closed exception constant `E₀ + (24 D² h + 8 D) θ² T + 4 D (n - D - 1) θ T`, where `E₀` is
the ordinary-tail charge at `μ` and `T` is the staircase at `M`. -/
def firstOrderExceptionConstant (θ : ℝ) (n D h μ M : ℕ) : ℝ :=
  ordinaryTailCharge θ n D h μ + (24 * D ^ 2 * h + 8 * D) * θ ^ 2 * stageStaircase μ M +
    4 * D * (n - D - 1 : ℕ) * θ * stageStaircase μ M

/-- For `1 ≤ D`, `D < A ≤ n` and `e ≤ M ≤ μ`, the exception charge at the balanced split and
`θ = (n - D) / (A - D)` is at most the closed exception constant. -/
theorem firstOrderExceptionCharge_balancedSplit_le {n D A h μ M e : ℕ} (hD : 1 ≤ D)
    (hDA : D < A) (hAn : A ≤ n) (heM : e ≤ M) (hMμ : M ≤ μ) :
    firstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h μ e (balancedSplit D A) ≤
      firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h μ M := by
  set θ := agreementIncidenceRatio n D A
  set L := balancedSplit D A
  have hθ : 0 ≤ θ := zero_le_one.trans (one_le_agreementIncidenceRatio hDA hAn)
  have hl₁ : retainedCoordinateRatio n A L ≤ 2 * θ :=
    retainedCoordinateRatio_balancedSplit_le hDA (hDA.trans_le hAn)
  have hl₂ : fixedCoordinateRatio n D L ≤ 2 * θ := fixedCoordinateRatio_balancedSplit_le n D A
  have htail : ((n - L : ℕ) : ℝ) ≤ (n - D - 1 : ℕ) := by exact_mod_cast sub_balancedSplit_le hDA
  have hJ := regularJointStageSum_cast_le (h := h) hD heM hMμ
  have hB := regularFiberStageSum_cast_le hD heM hMμ
  have hl₁0 : 0 ≤ retainedCoordinateRatio n A L := by unfold retainedCoordinateRatio; positivity
  have hl₂0 : 0 ≤ fixedCoordinateRatio n D L := by unfold fixedCoordinateRatio; positivity
  have hT := stageStaircase_nonneg μ M
  have hjoint : retainedCoordinateRatio n A L * θ * regularJointStageSum D h μ e ≤
      (24 * D ^ 2 * h + 8 * D) * θ ^ 2 * stageStaircase μ M :=
    calc
      _ ≤ 2 * θ * θ * ((12 * D ^ 2 * h + 4 * D) * stageStaircase μ M) := by gcongr
      _ = _ := by ring
  have hfiber : ((n - L : ℕ) : ℝ) * fixedCoordinateRatio n D L * regularFiberStageSum D μ e ≤
      4 * D * (n - D - 1 : ℕ) * θ * stageStaircase μ M :=
    calc
      _ ≤ ((n - D - 1 : ℕ) : ℝ) * (2 * θ) * (2 * D * stageStaircase μ M) := by gcongr
      _ = _ := by ring
  have hordinary := ordinaryTailCharge_le (n := n) (D := D) (h := h) hθ (Nat.sub_le μ e)
  unfold firstOrderExceptionCharge firstOrderExceptionConstant
  linarith

/-! ### Optimized constants -/

/-- The optimized list charge: the maximum of the list charge over `e ≤ M`. -/
def maxFirstOrderListCharge (θ : ℝ) (D μ M : ℕ) : ℝ := by
  classical
  exact ((Finset.range (M + 1)).image (firstOrderListCharge θ D μ)).max' (by simp)

/-- The ceiling of the optimized list charge. -/
def firstOrderListBound (θ : ℝ) (D μ M : ℕ) : ℕ :=
  ⌈maxFirstOrderListCharge θ D μ M⌉₊

/-- For `D < A`, the minimum of the exception charge at actual degree `e` over the splits
`D < L ≤ A`; it is `0` for `A ≤ D`. -/
def minFirstOrderExceptionCharge (θ : ℝ) (n D A h μ e : ℕ) : ℝ := by
  classical
  exact if hDA : D < A then
    ((Finset.Icc (D + 1) A).image (firstOrderExceptionCharge θ n D A h μ e)).min'
      (Finset.image_nonempty.mpr ⟨D + 1, Finset.mem_Icc.mpr ⟨le_rfl, hDA⟩⟩)
  else 0

/-- The optimized exception charge: the maximum over `e ≤ M` of the minimum over splits. -/
def maxMinFirstOrderExceptionCharge (θ : ℝ) (n D A h μ M : ℕ) : ℝ := by
  classical
  exact ((Finset.range (M + 1)).image (minFirstOrderExceptionCharge θ n D A h μ)).max' (by simp)

/-- The ceiling of the optimized exception charge. -/
def firstOrderExceptionBound (θ : ℝ) (n D A h μ M : ℕ) : ℕ :=
  ⌈maxMinFirstOrderExceptionCharge θ n D A h μ M⌉₊

/-- For `e ≤ M`, the list charge at `e` is at most the optimized list charge. -/
theorem firstOrderListCharge_le_max {θ : ℝ} {D μ e M : ℕ} (heM : e ≤ M) :
    firstOrderListCharge θ D μ e ≤ maxFirstOrderListCharge θ D μ M := by
  classical
  unfold maxFirstOrderListCharge
  convert Finset.le_max' _ _
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega : e < M + 1)))

/-- For `1 ≤ θ`, `1 ≤ D` and `M ≤ μ`, the optimized list charge is at most `Λ`. -/
theorem maxFirstOrderListCharge_le_firstOrderListConstant {θ : ℝ} {D μ M : ℕ} (hθ : 1 ≤ θ)
    (hD : 1 ≤ D) (hMμ : M ≤ μ) :
    maxFirstOrderListCharge θ D μ M ≤ firstOrderListConstant θ D μ M := by
  classical
  unfold maxFirstOrderListCharge
  convert Finset.max'_le _ _ _ fun x hx ↦ ?_
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  exact firstOrderListCharge_le_firstOrderListConstant hθ hD
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp he)) hMμ

/-- For `D < L ≤ A`, the minimum over splits is at most the exception charge at `L`. -/
theorem minFirstOrderExceptionCharge_le {θ : ℝ} {n D A h μ e L : ℕ} (hDL : D < L)
    (hLA : L ≤ A) :
    minFirstOrderExceptionCharge θ n D A h μ e ≤ firstOrderExceptionCharge θ n D A h μ e L := by
  classical
  unfold minFirstOrderExceptionCharge
  simp only [hDL.trans_le hLA, ↓reduceDIte]
  convert Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hDL, hLA⟩))

/-- For `e ≤ M`, the minimum over splits at `e` is at most the optimized exception charge. -/
theorem minFirstOrderExceptionCharge_le_maxMin {θ : ℝ} {n D A h μ e M : ℕ} (heM : e ≤ M) :
    minFirstOrderExceptionCharge θ n D A h μ e ≤ maxMinFirstOrderExceptionCharge θ n D A h μ M := by
  classical
  unfold maxMinFirstOrderExceptionCharge
  convert Finset.le_max' _ _
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega : e < M + 1)))

/-- For `1 ≤ D`, `D < A ≤ n` and `M ≤ μ`, the optimized exception charge at
`θ = (n - D) / (A - D)` is at most the closed exception constant. -/
theorem maxMinFirstOrderExceptionCharge_le_firstOrderExceptionConstant {n D A h μ M : ℕ}
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ) :
    maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h μ M ≤
      firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h μ M := by
  classical
  unfold maxMinFirstOrderExceptionCharge
  convert Finset.max'_le _ _ _ fun x hx ↦ ?_
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  exact (minFirstOrderExceptionCharge_le (lt_balancedSplit hDA) (balancedSplit_le hDA.le)).trans
    (firstOrderExceptionCharge_balancedSplit_le hD hDA hAn
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp he)) hMμ)

end

end ReedSolomon.HiddenDerivative
