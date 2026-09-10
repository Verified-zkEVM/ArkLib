/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
/-!
# Closed constants for the hybrid first-order argument

This file relates three versions of the finite first-order constants.

* The **raw** expressions retain an actual derivative degree `e` and, for exceptional sets, a
  coordinate split `L`.
* The **optimized** expressions maximize over every `e ≤ M` and minimize the exceptional charge
  over admissible splits. Their natural-valued variants apply `ceil` only after this optimization.
* The **closed** expressions `hybridLambdaClosed` and `hybridEClosed` are the formulas displayed
  in the rate theorems.

Here `D = k-1`, `theta = (n-D)/(A-D)`, `mu` is the total jet-degree cap, and `M` is the permitted
`Y₁`-degree cap. The staircase

`T = sum_{r=1}^M r * (2 * (mu-M) + r)`

has the closed form `(mu-M)M(M+1) + M(M+1)(2M+1)/6`. It bounds the stage sums for every actual
degree `e ≤ M`. In particular, the list comparison controls the complete raw expression
`theta * B₁(e) + mu-e` by its endpoint envelope `Lambda = 2DthetaT + mu-M`; the tail term is the
endpoint charge and need not equal the actual residual degree.

The exceptional constant decomposes as `E = E₀ + E₁ + E₂`. Here `E₀` is the ordinary-tail
budget, `E₁ = (24D²h+8D)theta²T` is the joint-family regular-stage budget, and
`E₂ = 4D(n-D-1)thetaT` is the generic-fiber budget. All closed comparisons are stated before
rounding, so a later theorem may compare a coerced cardinality with the real bound without
confusing it with its natural ceiling.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

noncomputable section

/-! ## Regular-stage sums and their closed staircase bound -/

/-- The denominator exponent `tau = 2D-1` used by first-order specialization. -/
def hybridTau (D : ℕ) : ℕ := 2 * D - 1

/-- The raw generic-fiber degree sum `B₁(e)` over the `e` regular derivative stages. -/
def hybridB1 (D μ e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range e,
    firstOrderCurveFiberStageOne (D + 1) (μ - i) (e - i) (hybridTau D)

/-- The raw joint-family degree sum `J₁(e)` over the `e` regular derivative stages. -/
def hybridJ1 (D h μ e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range e,
    firstOrderCurveJointStageOne (D + 1) 1 h (μ - i) (e - i) (hybridTau D)

/-- The staircase `sum_{r=1}^e r * (2 * (mu-e) + r)` controlling stage degrees. -/
def hybridMoment (μ e : ℕ) : ℕ :=
  ∑ r ∈ Finset.range e, (r + 1) * (2 * (μ - e) + (r + 1))

/-- The closed real form `T` of `hybridMoment mu M`. -/
def hybridT (μ M : ℕ) : ℝ :=
  ((μ - M : ℕ) : ℝ) * M * (M + 1) +
    (M : ℝ) * (M + 1) * (2 * M + 1) / 6

private theorem sum_range_succ_cast (M : ℕ) :
    (∑ r ∈ Finset.range M, ((r + 1 : ℕ) : ℝ)) = (M : ℝ) * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at ih
      change (∑ x ∈ Finset.range M, ((x : ℝ) + 1)) + ((M : ℝ) + 1) = _
      rw [ih]
      ring

private theorem sum_range_succ_sq_cast (M : ℕ) :
    (∑ r ∈ Finset.range M, ((r + 1 : ℕ) : ℝ) ^ 2) =
      (M : ℝ) * (M + 1) * (2 * M + 1) / 6 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at ih
      change (∑ x ∈ Finset.range M, ((x : ℝ) + 1) ^ 2) + ((M : ℝ) + 1) ^ 2 = _
      rw [ih]
      ring

/-- The staircase sum is exactly the displayed closed expression `T`. -/
theorem hybridMoment_cast_eq_hybridT {μ M : ℕ} (hMμ : M ≤ μ) :
    (hybridMoment μ M : ℝ) = hybridT μ M := by
  rw [hybridMoment, Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_sub hMμ]
  calc
    (∑ x ∈ Finset.range M,
        (x + 1 : ℝ) * (2 * ((μ : ℝ) - M) + (x + 1))) =
        2 * ((μ : ℝ) - M) * (∑ x ∈ Finset.range M, ((x + 1 : ℕ) : ℝ)) +
          ∑ x ∈ Finset.range M, ((x + 1 : ℕ) : ℝ) ^ 2 := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro x _
              push_cast
              ring
            · apply Finset.sum_congr rfl
              intro x _
              push_cast
              ring
    _ = hybridT μ M := by
      rw [sum_range_succ_cast, sum_range_succ_sq_cast]
      unfold hybridT
      rw [Nat.cast_sub hMμ]
      ring

/-- The cleared total-coordinate degree at a regular stage is at most `2Dj`. -/
theorem firstOrderTaylorTotalCap_le_two_mul {D j : ℕ} (hD : 1 ≤ D) (hj : 1 ≤ j) :
    firstOrderTaylorTotalCap j (hybridTau D) ≤ 2 * D * j := by
  unfold firstOrderTaylorTotalCap hybridTau
  rw [← Nat.cast_le (α := ℤ)]
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * D), Nat.cast_sub hj]
  nlinarith

/-- The cleared derivative-coordinate degree at a regular stage is at most `2Dq`. -/
theorem firstOrderTaylorDerivativeCap_le_two_mul {D j q : ℕ}
    (hD : 1 ≤ D) (hq : 1 ≤ q) :
    firstOrderTaylorDerivativeCap (D + 1) j q (hybridTau D) ≤ 2 * D * q := by
  calc
    firstOrderTaylorDerivativeCap (D + 1) j q (hybridTau D) ≤
        hybridTau D * (q - 1) + ((D + 1) - 1) := min_le_right _ _
    _ ≤ 2 * D * q := by
      unfold hybridTau
      rw [← Nat.cast_le (α := ℤ)]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * D), Nat.cast_sub hq]
      nlinarith

/-- A regular fixed-fiber degree is bounded by its cap-sensitive quadratic envelope. -/
theorem firstOrderCurveFiberStageOne_le_hybridEnvelope {D j q : ℕ}
    (hD : 1 ≤ D) (hq : 1 ≤ q) (hqj : q ≤ j) :
    firstOrderCurveFiberStageOne (D + 1) j q (hybridTau D) ≤
      2 * D * q * (2 * j - q) := by
  let b := firstOrderTaylorTotalCap j (hybridTau D)
  let c := firstOrderTaylorDerivativeCap (D + 1) j q (hybridTau D)
  let B := 2 * D * j
  let C := 2 * D * q
  have hj : 1 ≤ j := hq.trans hqj
  have hcb : c ≤ b := min_le_left _ _
  have hCB : C ≤ B := by dsimp only [B, C]; gcongr
  have hbB : b ≤ B := by
    exact firstOrderTaylorTotalCap_le_two_mul hD hj
  have hcC : c ≤ C := by
    exact firstOrderTaylorDerivativeCap_le_two_mul hD hq
  calc
    firstOrderCurveFiberStageOne (D + 1) j q (hybridTau D) =
        AffineHilbert.fixedFiberDerivativeImageDegree j q b c := by
          rfl
    _ ≤ AffineHilbert.fixedFiberDerivativeImageDegree j q B C :=
      AffineHilbert.fixedFiberDerivativeImageDegree_mono_map hqj hcb hCB hbB hcC
    _ = 2 * D * q * (2 * j - q) := by
      rw [AffineHilbert.fixedFiberDerivativeImageDegree_eq hqj hCB]
      have hjq : 2 * j - q = (j - q) + j := by omega
      rw [hjq]
      dsimp only [B, C]
      ring

/-- A regular joint degree is bounded by the closed first-order stage coefficient. -/
theorem firstOrderCurveJointStageOne_le_hybridEnvelope {D h j q : ℕ}
    (hD : 1 ≤ D) (hq : 1 ≤ q) (hqj : q ≤ j) :
    firstOrderCurveJointStageOne (D + 1) 1 h j q (hybridTau D) ≤
      (12 * D ^ 2 * h + 4 * D) * (q * (2 * j - q)) := by
  let b := firstOrderTaylorTotalCap j (hybridTau D)
  let c := firstOrderTaylorDerivativeCap (D + 1) j q (hybridTau D)
  let B := 2 * D * j
  let C := 2 * D * q
  have hj : 1 ≤ j := hq.trans hqj
  have hcb : c ≤ b := min_le_left _ _
  have hCB : C ≤ B := by dsimp only [B, C]; gcongr
  have hbB : b ≤ B := firstOrderTaylorTotalCap_le_two_mul hD hj
  have hcC : c ≤ C := firstOrderTaylorDerivativeCap_le_two_mul hD hq
  have harea := AffineHilbert.cappedTriangleDegree_le hcb hCB hbB hcC
  have hbeta := firstOrderCurveFiberStageOne_le_hybridEnvelope hD hq hqj
  have halpha : 1 + hybridTau D * h ≤ 1 + 2 * D * h := by
    unfold hybridTau
    exact Nat.add_le_add_left (Nat.mul_le_mul_right h (Nat.sub_le _ _)) 1
  have hareaEq : 2 * B * C - C ^ 2 = 4 * D ^ 2 * q * (2 * j - q) := by
    have hfactor : 2 * B - C = 2 * D * (2 * j - q) := by
      rw [Nat.mul_sub_left_distrib]
      dsimp only [B, C]
      congr 1
      all_goals ring
    calc
      2 * B * C - C ^ 2 = C * (2 * B - C) := by
        rw [Nat.mul_sub_left_distrib]
        congr 1
        all_goals ring
      _ = 4 * D ^ 2 * q * (2 * j - q) := by
        rw [hfactor]
        dsimp only [C]
        ring
  unfold firstOrderCurveJointStageOne AffineHilbert.mixedDerivativeImageDegree
  change h * (2 * b * c - c ^ 2) +
      2 * (1 + hybridTau D * h) *
        firstOrderCurveFiberStageOne (D + 1) j q (hybridTau D) ≤ _
  calc
    _ ≤ h * (2 * B * C - C ^ 2) +
        2 * (1 + 2 * D * h) * (2 * D * q * (2 * j - q)) := by gcongr
    _ = (12 * D ^ 2 * h + 4 * D) * (q * (2 * j - q)) := by
      rw [hareaEq]
      ring

/-- The staircase moment can equivalently be indexed by descending separant stages. -/
theorem hybridMoment_eq_stage_sum {μ e : ℕ} (heμ : e ≤ μ) :
    hybridMoment μ e =
      ∑ i ∈ Finset.range e, (e - i) * (2 * (μ - i) - (e - i)) := by
  rw [hybridMoment, ← Finset.sum_range_reflect
    (fun r ↦ (r + 1) * (2 * (μ - e) + (r + 1))) e]
  apply Finset.sum_congr rfl
  intro i hi
  have hie : i < e := Finset.mem_range.mp hi
  have hq : e - 1 - i + 1 = e - i := by omega
  have hj : 2 * (μ - e) + (e - i) = 2 * (μ - i) - (e - i) := by omega
  rw [hq, hj]

/-- The exact fiber-stage sum is bounded by `2D` times the staircase moment. -/
theorem hybridB1_le_moment {D μ e : ℕ} (hD : 1 ≤ D) (heμ : e ≤ μ) :
    hybridB1 D μ e ≤ 2 * D * hybridMoment μ e := by
  rw [hybridB1, hybridMoment_eq_stage_sum heμ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hie : i < e := Finset.mem_range.mp hi
  simpa only [mul_assoc] using
    firstOrderCurveFiberStageOne_le_hybridEnvelope hD
      (show 1 ≤ e - i by omega) (show e - i ≤ μ - i by omega)

/-- The exact joint-stage sum is bounded by the closed coefficient times the staircase moment. -/
theorem hybridJ1_le_moment {D h μ e : ℕ} (hD : 1 ≤ D) (heμ : e ≤ μ) :
    hybridJ1 D h μ e ≤ (12 * D ^ 2 * h + 4 * D) * hybridMoment μ e := by
  rw [hybridJ1, hybridMoment_eq_stage_sum heμ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hie : i < e := Finset.mem_range.mp hi
  simpa only [mul_assoc] using
    firstOrderCurveJointStageOne_le_hybridEnvelope hD
      (show 1 ≤ e - i by omega) (show e - i ≤ μ - i by omega)

/-- Increasing the actual derivative degree by one increases the exact fiber sum by at least
one. -/
theorem hybridB1_add_one_le_succ {D μ e : ℕ} (hD : 1 ≤ D) (heμ : e + 1 ≤ μ) :
    hybridB1 D μ e + 1 ≤ hybridB1 D μ (e + 1) := by
  have hsum :
      (∑ i ∈ Finset.range e,
          firstOrderCurveFiberStageOne (D + 1) (μ - i) (e - i) (hybridTau D)) ≤
        ∑ i ∈ Finset.range e,
          firstOrderCurveFiberStageOne (D + 1) (μ - i) (e + 1 - i) (hybridTau D) := by
    apply Finset.sum_le_sum
    intro i hi
    have hie : i < e := Finset.mem_range.mp hi
    apply firstOrderCurveFiberStageOne_mono_derivative
    · omega
    · omega
  have hnew : 1 ≤
      firstOrderCurveFiberStageOne (D + 1) (μ - e) (e + 1 - e) (hybridTau D) := by
    have hK : 2 ≤ D + 1 := by omega
    have hj := le_firstOrderCurveFiberStageOne
      (j := μ - e) (r := e + 1 - e) (τ := hybridTau D) hK
    exact (show 1 ≤ μ - e by omega).trans hj
  unfold hybridB1
  rw [Finset.sum_range_succ]
  exact Nat.add_le_add hsum hnew

/-- The real staircase constant grows with the permitted actual derivative degree. -/
theorem hybridT_mono {μ e M : ℕ} (heM : e ≤ M) (hMμ : M ≤ μ) :
    hybridT μ e ≤ hybridT μ M := by
  have hstep : ∀ t, t < μ → hybridT μ t ≤ hybridT μ (t + 1) := by
    intro t htμ
    have htμ' : t + 1 ≤ μ := by omega
    have hdiff :
        hybridT μ (t + 1) = hybridT μ t +
          (t + 1 : ℝ) * (2 * (μ : ℝ) - 2 * t - 1) := by
      unfold hybridT
      rw [Nat.cast_sub htμ.le, Nat.cast_sub htμ']
      push_cast
      ring
    rw [hdiff]
    have hfactor : (0 : ℝ) ≤ 2 * (μ : ℝ) - 2 * t - 1 := by
      have hcast : ((2 * t + 1 : ℕ) : ℝ) ≤ (2 * μ : ℕ) := by
        exact_mod_cast (show 2 * t + 1 ≤ 2 * μ by omega)
      push_cast at hcast
      linarith
    have hproduct : (0 : ℝ) ≤
        (t + 1 : ℝ) * (2 * (μ : ℝ) - 2 * t - 1) :=
      mul_nonneg (by positivity) hfactor
    linarith
  induction M generalizing e with
  | zero =>
      have : e = 0 := by omega
      subst e
      exact le_rfl
  | succ M ih =>
      by_cases heq : e = M + 1
      · subst e
        exact le_rfl
      · have heM' : e ≤ M := by omega
        exact (ih heM' (by omega)).trans (hstep M (by omega))

/-- For every actual derivative degree `e ≤ M`, `B₁(e) ≤ 2D*T`. -/
theorem hybridB1_cast_le_closed {D μ M e : ℕ}
    (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    (hybridB1 D μ e : ℝ) ≤ 2 * D * hybridT μ M := by
  calc
    (hybridB1 D μ e : ℝ) ≤ (2 * D * hybridMoment μ e : ℕ) := by
      exact_mod_cast hybridB1_le_moment hD (heM.trans hMμ)
    _ = (2 * D : ℕ) * hybridT μ e := by
      push_cast
      rw [hybridMoment_cast_eq_hybridT (heM.trans hMμ)]
    _ ≤ 2 * D * hybridT μ M := by
      push_cast
      apply mul_le_mul_of_nonneg_left (hybridT_mono heM hMμ)
      positivity

/-- For every actual derivative degree `e ≤ M`, `J₁(e) ≤ (12D²h+4D)*T`. -/
theorem hybridJ1_cast_le_closed {D h μ M e : ℕ}
    (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    (hybridJ1 D h μ e : ℝ) ≤
      (12 * D ^ 2 * h + 4 * D) * hybridT μ M := by
  calc
    (hybridJ1 D h μ e : ℝ) ≤
        ((12 * D ^ 2 * h + 4 * D) * hybridMoment μ e : ℕ) := by
      exact_mod_cast hybridJ1_le_moment hD (heM.trans hMμ)
    _ = (12 * D ^ 2 * h + 4 * D : ℕ) * hybridT μ e := by
      push_cast
      rw [hybridMoment_cast_eq_hybridT (heM.trans hMμ)]
    _ ≤ (12 * D ^ 2 * h + 4 * D) * hybridT μ M := by
      push_cast
      apply mul_le_mul_of_nonneg_left (hybridT_mono heM hMμ)
      positivity

/-! ## Raw and closed list constants -/

/-- The unrounded list expression `theta*B₁(e) + mu-e` at the actual derivative degree `e`. -/
def hybridListRaw (theta : ℝ) (D μ e : ℕ) : ℝ :=
  theta * hybridB1 D μ e + (μ - e : ℕ)

/-- The displayed closed list constant `Lambda = 2DthetaT + mu-M`.

The tail `mu-M` belongs to the endpoint envelope at `M`; it is not asserted to equal the actual
residual degree `mu-e`. -/
def hybridLambdaClosed (theta : ℝ) (D μ M : ℕ) : ℝ :=
  2 * D * theta * hybridT μ M + (μ - M : ℕ)

/-- The unrounded list expression increases at every admissible derivative stage. -/
theorem hybridListRaw_le_succ {theta : ℝ} {D μ e : ℕ}
    (htheta : 1 ≤ theta) (hD : 1 ≤ D) (heμ : e + 1 ≤ μ) :
    hybridListRaw theta D μ e ≤ hybridListRaw theta D μ (e + 1) := by
  have hB : (hybridB1 D μ e : ℝ) + 1 ≤ hybridB1 D μ (e + 1) := by
    exact_mod_cast hybridB1_add_one_le_succ hD heμ
  unfold hybridListRaw
  rw [Nat.cast_sub (by omega : e ≤ μ), Nat.cast_sub heμ]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ theta by linarith)]

/-- The complete raw list expression is maximized at the endpoint `M` whenever `e ≤ M ≤ mu`. -/
theorem hybridListRaw_mono {theta : ℝ} {D μ e M : ℕ}
    (htheta : 1 ≤ theta) (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    hybridListRaw theta D μ e ≤ hybridListRaw theta D μ M := by
  induction M generalizing e with
  | zero =>
      have : e = 0 := by omega
      subst e
      exact le_rfl
  | succ M ih =>
      by_cases heq : e = M + 1
      · subst e
        exact le_rfl
      · have heM' : e ≤ M := by omega
        exact (ih heM' (by omega)).trans (hybridListRaw_le_succ htheta hD (by omega))

/-- Every raw list expression at an actual `e ≤ M` is bounded by the displayed closed formula. -/
theorem hybridListRaw_le_closed {theta : ℝ} {D μ e M : ℕ}
    (htheta : 1 ≤ theta) (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    hybridListRaw theta D μ e ≤ 2 * D * theta * hybridT μ M + (μ - M : ℕ) := by
  calc
    hybridListRaw theta D μ e ≤ hybridListRaw theta D μ M :=
      hybridListRaw_mono htheta hD heM hMμ
    _ ≤ 2 * D * theta * hybridT μ M + (μ - M : ℕ) := by
      unfold hybridListRaw
      have hB := hybridB1_cast_le_closed hD le_rfl hMμ
      nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ theta by linarith)]

/-- Named form of the raw list comparison against `hybridLambdaClosed`. -/
theorem hybridListRaw_le_lambdaClosed {theta : ℝ} {D μ e M : ℕ}
    (htheta : 1 ≤ theta) (hD : 1 ≤ D) (heM : e ≤ M) (hMμ : M ≤ μ) :
    hybridListRaw theta D μ e ≤ hybridLambdaClosed theta D μ M := by
  simpa only [hybridLambdaClosed] using hybridListRaw_le_closed htheta hD heM hMμ

/-- The ordinary-tail charge, including its separate zero-stage value.

At positive degree `b`, its three terms bound exceptional resultant/content specializations,
incidence for factorwise rational images, and accidental agreements on persistent graph lines.
At the endpoint `b = mu` this is the component `E₀` of `hybridEClosed`. -/
def hybridOrdinaryRaw (theta : ℝ) (n D h b : ℕ) : ℝ :=
  if b = 0 then h else
    (2 * b - 1 : ℕ) * h + theta * (h + b + 4 * D * b * h) +
      (n - D - 1 : ℕ) * b

/-- The ordinary tail is uniformly dominated by the charge at the full multiplicity `μ`. -/
theorem hybridOrdinaryRaw_mono_to_top {theta : ℝ} {n D h b μ : ℕ}
    (htheta : 0 ≤ theta) (hbμ : b ≤ μ) (hμ : 1 ≤ μ) :
    hybridOrdinaryRaw theta n D h b ≤ hybridOrdinaryRaw theta n D h μ := by
  by_cases hb : b = 0
  · subst b
    simp only [hybridOrdinaryRaw, if_pos, Nat.cast_zero]
    rw [if_neg (by omega : μ ≠ 0)]
    have hfirst : (h : ℝ) ≤ (2 * μ - 1 : ℕ) * h := by
      have hfactor : 1 ≤ 2 * μ - 1 := by omega
      exact_mod_cast (show h ≤ (2 * μ - 1) * h by
        simpa only [one_mul] using Nat.mul_le_mul_right h hfactor)
    have hmiddle : (0 : ℝ) ≤ theta * (h + μ + 4 * D * μ * h) :=
      mul_nonneg htheta (by positivity)
    have hlast : (0 : ℝ) ≤ ((n - D - 1 : ℕ) : ℝ) * μ := by positivity
    linarith
  · have hμ0 : μ ≠ 0 := by omega
    simp only [hybridOrdinaryRaw, hb, hμ0, if_false]
    have hfirst : ((2 * b - 1 : ℕ) : ℝ) * h ≤ ((2 * μ - 1 : ℕ) : ℝ) * h := by
      gcongr
    have hmiddle : theta * ((h : ℝ) + b + 4 * D * b * h) ≤
        theta * ((h : ℝ) + μ + 4 * D * μ * h) := by
      gcongr
    have hlast : ((n - D - 1 : ℕ) : ℝ) * b ≤
        ((n - D - 1 : ℕ) : ℝ) * μ := by gcongr
    linarith

/-! ## Retention ratios and exceptional-set constants -/

/-- The agreement-incidence ratio `theta = (n-D)/(A-D)`.

It converts fixed-word degree bounds into candidate counts. The geometric hypotheses
`D < A ≤ n` imply `1 ≤ theta`. -/
def hybridTheta (n D A : ℕ) : ℝ :=
  ((n - D : ℕ) : ℝ) / (A - D : ℕ)

/-- The retained-coordinate ratio after splitting at `L`. -/
def hybridLambdaOne (n A L : ℕ) : ℝ :=
  ((n - L + 1 : ℕ) : ℝ) / (A - L + 1 : ℕ)

/-- The fixed-coordinate ratio after splitting at `L`. -/
def hybridLambdaTwo (n D L : ℕ) : ℝ :=
  ((n - D : ℕ) : ℝ) / (L - D : ℕ)

/-- The balanced split `L = D + ceil((A-D)/2)` used for the regular-stage transfer. -/
def hybridBalancedL (D A : ℕ) : ℕ :=
  D + (A - D + 1) / 2

private theorem balancedHalf_bounds {D A : ℕ} (hDA : D < A) :
    let r := (A - D + 1) / 2
    1 ≤ r ∧ r ≤ A - D ∧ A - D ≤ 2 * r ∧ A - D ≤ 2 * (A - D - r + 1) := by
  dsimp only
  omega

/-- The balanced split lies strictly above `D` and at most `A`. -/
theorem hybridBalancedL_bounds {D A : ℕ} (hDA : D < A) :
    D < hybridBalancedL D A ∧ hybridBalancedL D A ≤ A := by
  unfold hybridBalancedL
  obtain ⟨hr, hrd, _, _⟩ := balancedHalf_bounds hDA
  omega

/-- The integer balanced split is literally the ceiling expression used in the paper. -/
theorem hybridBalancedL_eq_add_ceil {D A : ℕ} (hDA : D < A) :
    hybridBalancedL D A = D + ⌈(((A - D : ℕ) : ℝ) / 2)⌉₊ := by
  unfold hybridBalancedL
  congr 1
  let d := A - D
  let r := (d + 1) / 2
  have hr := balancedHalf_bounds hDA
  have hr1 : 1 ≤ r := by simpa only [r, d] using hr.1
  have hdr : d ≤ 2 * r := by simpa only [r, d] using hr.2.2.1
  have hrlt : 2 * (r - 1) < d := by
    dsimp only [r, d]
    omega
  change r = ⌈((d : ℕ) : ℝ) / 2⌉₊
  symm
  apply (Nat.ceil_eq_iff (by omega : r ≠ 0)).2
  constructor
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (show (r - 1) * 2 < d by simpa only [mul_comm] using hrlt)
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (show d ≤ r * 2 by simpa only [mul_comm] using hdr)

/-- All three denominators used by the balanced retention ratios are positive. -/
theorem hybridBalancedL_denominators_pos {D A : ℕ} (hDA : D < A) :
    0 < A - hybridBalancedL D A + 1 ∧
      0 < hybridBalancedL D A - D ∧ 0 < A - D := by
  obtain ⟨hDL, hLA⟩ := hybridBalancedL_bounds hDA
  omega

/-- At the balanced split, both retained ratios cost at most `2 theta`, and at least one
post-`D` coordinate has been removed. -/
theorem hybridBalancedL_retention {n D A : ℕ} (hDA : D < A) (hAn : A ≤ n) :
    let L := hybridBalancedL D A
    hybridLambdaOne n A L ≤ 2 * hybridTheta n D A ∧
      hybridLambdaTwo n D L ≤ 2 * hybridTheta n D A ∧
      n - L ≤ n - D - 1 := by
  dsimp only
  let d := A - D
  let N := n - D
  let r := (d + 1) / 2
  have hd : 1 ≤ d := by dsimp only [d]; omega
  have hN : d ≤ N := by dsimp only [d, N]; omega
  have hr := balancedHalf_bounds hDA
  have hr1 : 1 ≤ r := by simpa only [r, d] using hr.1
  have hrd : r ≤ d := by simpa only [r, d] using hr.2.1
  have hdr : d ≤ 2 * r := by simpa only [r, d] using hr.2.2.1
  have hdcomp : d ≤ 2 * (d - r + 1) := by simpa only [r, d] using hr.2.2.2
  have hL : hybridBalancedL D A = D + r := by
    simp only [hybridBalancedL, r, d]
  have hnum : n - hybridBalancedL D A + 1 ≤ N := by
    rw [hL]
    dsimp only [N]
    omega
  have hdenOne : A - hybridBalancedL D A + 1 = d - r + 1 := by
    rw [hL]
    dsimp only [d]
    omega
  have hdenTwo : hybridBalancedL D A - D = r := by rw [hL]; omega
  have hcrossOne :
      (n - hybridBalancedL D A + 1) * d ≤ 2 * N * (d - r + 1) := by
    calc
      (n - hybridBalancedL D A + 1) * d ≤ N * d := Nat.mul_le_mul_right d hnum
      _ ≤ N * (2 * (d - r + 1)) := Nat.mul_le_mul_left N hdcomp
      _ = 2 * N * (d - r + 1) := by ring
  have hcrossTwo : N * d ≤ 2 * N * r := by
    calc
      N * d ≤ N * (2 * r) := Nat.mul_le_mul_left N hdr
      _ = 2 * N * r := by ring
  have hone : hybridLambdaOne n A (hybridBalancedL D A) ≤
      2 * hybridTheta n D A := by
    unfold hybridLambdaOne hybridTheta
    rw [hdenOne]
    change ((n - hybridBalancedL D A + 1 : ℕ) : ℝ) / (d - r + 1 : ℕ) ≤
      2 * ((N : ℝ) / d)
    rw [show 2 * ((N : ℝ) / d) = (2 * N : ℝ) / d by ring]
    apply (div_le_div_iff₀
      (show (0 : ℝ) < (d - r + 1 : ℕ) by positivity)
      (show (0 : ℝ) < (d : ℕ) by positivity)).2
    exact_mod_cast hcrossOne
  have htwo : hybridLambdaTwo n D (hybridBalancedL D A) ≤
      2 * hybridTheta n D A := by
    unfold hybridLambdaTwo hybridTheta
    rw [hdenTwo]
    change (N : ℝ) / r ≤ 2 * ((N : ℝ) / d)
    rw [show 2 * ((N : ℝ) / d) = (2 * N : ℝ) / d by ring]
    apply (div_le_div_iff₀
      (show (0 : ℝ) < (r : ℕ) by positivity)
      (show (0 : ℝ) < (d : ℕ) by positivity)).2
    exact_mod_cast hcrossTwo
  have htail : n - (D + r) ≤ n - D - 1 := by omega
  exact ⟨hone, htwo, by simpa only [hL] using htail⟩

/-- In the geometric range, the direct agreement ratio is at least one. -/
theorem hybridTheta_one_le {n D A : ℕ} (hDA : D < A) (hAn : A ≤ n) :
    1 ≤ hybridTheta n D A := by
  unfold hybridTheta
  have hden : (0 : ℝ) < (A - D : ℕ) := by
    exact_mod_cast (show 0 < A - D by omega)
  apply (le_div_iff₀ hden).2
  simp only [one_mul]
  exact_mod_cast (show A - D ≤ n - D by omega)

/-- The raw exceptional-set charge for actual derivative degree `e` and split `L`.

Its three summands are the ordinary-tail charge, the retained joint-family charge, and the
fixed-coordinate generic-fiber charge. -/
def hybridERaw (theta : ℝ) (n D A h μ e L : ℕ) : ℝ :=
  hybridOrdinaryRaw theta n D h (μ - e) +
    hybridLambdaOne n A L * theta * hybridJ1 D h μ e +
    (n - L : ℕ) * hybridLambdaTwo n D L * hybridB1 D μ e

/-- The displayed closed exceptional-set constant `E = E₀ + E₁ + E₂`.

`E₀` is `hybridOrdinaryRaw theta n D h mu`. The remaining summands are
`E₁ = (24D²h+8D)theta²T` and `E₂ = 4D(n-D-1)thetaT`. -/
def hybridEClosed (theta : ℝ) (n D h μ M : ℕ) : ℝ :=
  hybridOrdinaryRaw theta n D h μ +
    (24 * D ^ 2 * h + 8 * D) * theta ^ 2 * hybridT μ M +
    4 * D * (n - D - 1 : ℕ) * theta * hybridT μ M

/-- At the balanced split, every raw charge with actual degree `e ≤ M` is bounded by `E`.

The proof uses `J₁(e) ≤ (12D²h+4D)T` and `B₁(e) ≤ 2DT`; both retention ratios are at most
`2theta`. The ordinary tail is charged once and receives no retention-ratio factor. -/
theorem hybridERaw_balanced_le_closed {n D A h μ M e : ℕ}
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hμ : 1 ≤ μ) (heM : e ≤ M) (hMμ : M ≤ μ) :
    hybridERaw (hybridTheta n D A) n D A h μ e (hybridBalancedL D A) ≤
      hybridEClosed (hybridTheta n D A) n D h μ M := by
  let theta := hybridTheta n D A
  let L := hybridBalancedL D A
  have htheta : 0 ≤ theta := (hybridTheta_one_le hDA hAn).trans' zero_le_one
  have hret := hybridBalancedL_retention hDA hAn
  have hlambdaOne : hybridLambdaOne n A L ≤ 2 * theta := by
    simpa only [L, theta] using hret.1
  have hlambdaTwo : hybridLambdaTwo n D L ≤ 2 * theta := by
    simpa only [L, theta] using hret.2.1
  have htail : n - L ≤ n - D - 1 := by simpa only [L] using hret.2.2
  have hordinary : hybridOrdinaryRaw theta n D h (μ - e) ≤
      hybridOrdinaryRaw theta n D h μ :=
    hybridOrdinaryRaw_mono_to_top htheta (Nat.sub_le _ _) hμ
  have hJ := hybridJ1_cast_le_closed (D := D) (h := h) hD heM hMμ
  have hB := hybridB1_cast_le_closed (D := D) hD heM hMμ
  have hlambdaOne0 : 0 ≤ hybridLambdaOne n A L := by
    unfold hybridLambdaOne
    positivity
  have hlambdaTwo0 : 0 ≤ hybridLambdaTwo n D L := by
    unfold hybridLambdaTwo
    positivity
  have hJ0 : (0 : ℝ) ≤ hybridJ1 D h μ e := by positivity
  have hB0 : (0 : ℝ) ≤ hybridB1 D μ e := by positivity
  have hT0 : 0 ≤ hybridT μ M := by
    rw [← hybridMoment_cast_eq_hybridT hMμ]
    positivity
  have hjoint : hybridLambdaOne n A L * theta * hybridJ1 D h μ e ≤
      (24 * D ^ 2 * h + 8 * D) * theta ^ 2 * hybridT μ M := by
    calc
      hybridLambdaOne n A L * theta * hybridJ1 D h μ e ≤
          (2 * theta) * theta *
            ((12 * D ^ 2 * h + 4 * D) * hybridT μ M) := by gcongr
      _ = (24 * D ^ 2 * h + 8 * D) * theta ^ 2 * hybridT μ M := by ring
  have hfiber : ((n - L : ℕ) : ℝ) * hybridLambdaTwo n D L * hybridB1 D μ e ≤
      4 * D * (n - D - 1 : ℕ) * theta * hybridT μ M := by
    have htailReal : ((n - L : ℕ) : ℝ) ≤ (n - D - 1 : ℕ) := by
      exact_mod_cast htail
    calc
      ((n - L : ℕ) : ℝ) * hybridLambdaTwo n D L * hybridB1 D μ e ≤
          ((n - D - 1 : ℕ) : ℝ) * (2 * theta) *
            (2 * D * hybridT μ M) := by gcongr
      _ = 4 * D * (n - D - 1 : ℕ) * theta * hybridT μ M := by ring
  change hybridOrdinaryRaw theta n D h (μ - e) +
      hybridLambdaOne n A L * theta * hybridJ1 D h μ e +
      (n - L : ℕ) * hybridLambdaTwo n D L * hybridB1 D μ e ≤ _
  unfold hybridEClosed
  change _ ≤ hybridOrdinaryRaw theta n D h μ +
    (24 * D ^ 2 * h + 8 * D) * theta ^ 2 * hybridT μ M +
    4 * D * (n - D - 1 : ℕ) * theta * hybridT μ M
  linarith

/-! ## Optimized and rounded constants -/

/-- The optimized raw list constant: the maximum over every actual degree `e ≤ M`. -/
noncomputable def hybridListOptimizedRaw (theta : ℝ) (D μ M : ℕ) : ℝ := by
  classical
  exact ((Finset.range (M + 1)).image (hybridListRaw theta D μ)).max' (by simp)

/-- The natural list bound obtained by ceiling the optimized raw maximum. -/
noncomputable def hybridListOptimizedCeil (theta : ℝ) (D μ M : ℕ) : ℕ :=
  ⌈hybridListOptimizedRaw theta D μ M⌉₊

/-- At a fixed actual degree, the optimized raw exception charge minimizes over all admissible
splits `D + 1 ≤ L ≤ A`.  Outside the nonempty geometric range it is defined as zero. -/
noncomputable def hybridERawAtDegree
    (theta : ℝ) (n D A h μ e : ℕ) : ℝ := by
  classical
  by_cases hDA : D < A
  · exact ((Finset.Icc (D + 1) A).image (hybridERaw theta n D A h μ e)).min' (by
      simp only [Finset.image_nonempty]
      exact ⟨D + 1, by simp only [Finset.mem_Icc]; omega⟩)
  · exact 0

/-- The optimized raw exceptional-set constant.

For each `e ≤ M` it first minimizes over admissible splits, then maximizes over `e`. -/
noncomputable def hybridEOptimizedRaw
    (theta : ℝ) (n D A h μ M : ℕ) : ℝ := by
  classical
  exact ((Finset.range (M + 1)).image
    (hybridERawAtDegree theta n D A h μ)).max' (by simp)

/-- The natural exceptional-set bound obtained by ceiling the optimized raw constant. -/
noncomputable def hybridEOptimizedCeil
    (theta : ℝ) (n D A h μ M : ℕ) : ℕ :=
  ⌈hybridEOptimizedRaw theta n D A h μ M⌉₊

/-- The optimized raw list maximum is bounded by the displayed closed `Lambda`. -/
theorem hybridListOptimizedRaw_le_closed {n D A μ M : ℕ}
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ) :
    hybridListOptimizedRaw (hybridTheta n D A) D μ M ≤
      2 * D * hybridTheta n D A * hybridT μ M + (μ - M : ℕ) := by
  classical
  unfold hybridListOptimizedRaw
  apply Finset.max'_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  have heM : e ≤ M := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using he
  exact hybridListRaw_le_closed (hybridTheta_one_le hDA hAn) hD heM hMμ

/-- Named form of the optimized raw list comparison against `hybridLambdaClosed`. -/
theorem hybridListOptimizedRaw_le_lambdaClosed {n D A μ M : ℕ}
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMμ : M ≤ μ) :
    hybridListOptimizedRaw (hybridTheta n D A) D μ M ≤
      hybridLambdaClosed (hybridTheta n D A) D μ M := by
  simpa only [hybridLambdaClosed] using
    hybridListOptimizedRaw_le_closed hD hDA hAn hMμ

private theorem hybridERawAtDegree_le_balanced {theta : ℝ} {n D A h μ e : ℕ}
    (hDA : D < A) :
    hybridERawAtDegree theta n D A h μ e ≤
      hybridERaw theta n D A h μ e (hybridBalancedL D A) := by
  classical
  simp only [hybridERawAtDegree, hDA, ↓reduceDIte]
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  refine ⟨hybridBalancedL D A, ?_, rfl⟩
  have hbounds := hybridBalancedL_bounds hDA
  simp only [Finset.mem_Icc]
  omega

/-- The max/min optimized raw exceptional-set expression is bounded by the displayed closed `E`.

This comparison still occurs in `ℝ`; applying a ceiling is a separate final operation. -/
theorem hybridEOptimizedRaw_le_closed {n D A h μ M : ℕ}
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hμ : 1 ≤ μ) (hMμ : M ≤ μ) :
    hybridEOptimizedRaw (hybridTheta n D A) n D A h μ M ≤
      hybridEClosed (hybridTheta n D A) n D h μ M := by
  classical
  unfold hybridEOptimizedRaw
  apply Finset.max'_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  have heM : e ≤ M := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using he
  exact (hybridERawAtDegree_le_balanced hDA).trans
    (hybridERaw_balanced_le_closed hD hDA hAn hμ heM hMμ)

/-- At the canary parameters, the printed raw exception constant is the nonintegral value
`47/2`. -/
theorem hybridEClosed_rounding_canary :
    hybridEClosed (hybridTheta 4 1 3) 4 1 1 2 0 = 47 / 2 := by
  norm_num [hybridEClosed, hybridOrdinaryRaw, hybridTheta, hybridT]

/-- The natural ceiling of the canary raw exception constant is `24`, strictly larger than the
raw value.  This guards the interface against replacing a raw cardinality comparison by a
ceiling comparison. -/
theorem hybridEClosed_rounding_canary_ceil :
    ⌈hybridEClosed (hybridTheta 4 1 3) 4 1 1 2 0⌉₊ = 24 := by
  rw [hybridEClosed_rounding_canary]
  rw [Nat.ceil_eq_iff (by norm_num : (24 : ℕ) ≠ 0)]
  norm_num

end

end ReedSolomon.HiddenDerivative
