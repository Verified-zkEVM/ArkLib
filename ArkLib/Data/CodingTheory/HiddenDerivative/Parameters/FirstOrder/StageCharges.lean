/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# Stage degrees of the first-order curve bound

A first-order differential equation of total jet degree `μ` whose first-derivative degree is at
most `M` is peeled by separant descent in `μ` stages. The last `min M μ` stages have order one and
the others have order zero. At an order-one stage of total jet degree `j` and first-derivative
degree `r`, the cleared Taylor coordinates with common denominator exponent `τ` have total degree
at most `b = 1 + τ (j - 1)` (`firstOrderTaylorTotalCap`) and first-derivative degree at most
`c = min b (τ (r - 1) + K - 1)` (`firstOrderTaylorDerivativeCap`).

The stage degrees are mixed volumes of the Newton polytopes involved.

* The fixed-fiber degree `firstOrderCurveFiberStageOne` is `cappedDegreeMixedVolume j r b c`, the
  mixed volume of the truncated triangles for `(j, r)` and `(b, c)`. It bounds the affine degree
  of the pullback of a curve with bounds `(j, r)` along the Taylor monomial map
  (`MvPolynomial.affineDegree_comap_cappedDegree_span_singleton_le`).
* The joint degree `firstOrderCurveJointStageOne` is
  `cappedBidegreeMixedVolume h j r (ℓ + τ h) b c`, which also retains the challenge coordinate of
  degree `h` (`MvPolynomial.affineDegree_comap_cappedBidegree_span_singleton_le`).

Both increase with the total jet degree and with the first-derivative degree. Summing over the
stages gives `firstOrderCurveBound`, the rational expression for the number of exceptional
challenges of a polynomial curve. Its incidence ratios use a split threshold `L` between the
candidate degree bound `k` and the agreement threshold `A`; the order-one joint term carries a
separate direct incidence factor `η`.

## Main statements

* `firstOrderCurveFiberStageOne`, `firstOrderCurveJointStageOne`: the order-one stage degrees.
* `le_firstOrderCurveFiberStageOne`: an order-one fiber degree is at least `j` when `2 ≤ K`.
* `firstOrderCurveFiberStageOne_mono_total`, `firstOrderCurveFiberStageOne_mono_derivative`,
  `firstOrderCurveJointStageOne_mono_total`, `firstOrderCurveJointStageOne_mono_derivative`:
  monotonicity of the stage degrees.
* `firstOrderCurveFiberStageOne_le_mul_totalCap`: without the derivative cap the fiber degree is
  at most `j b`.
* `firstOrderCurveBound`, `firstOrderCurveBound_mono_directFactor`: the curve bound.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

/-! ### Order-zero stages -/

/-- The joint degree summed over the `μ - min M μ` order-zero stages at common denominator
exponent `τ`: the stage of total jet degree `t + 1` contributes `h (1 + τ t) + (t + 1)(ℓ + τ h)`. -/
def firstOrderCurveJointZero (μ M ell h τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ), (h * (1 + τ * t) + (t + 1) * (ell + τ * h))

/-- The fixed-fiber degree summed over the `μ - min M μ` order-zero stages: the stage of total
jet degree `t + 1` contributes `t + 1`. -/
def firstOrderCurveFiberZero (μ M : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ), (t + 1)

/-! ### Order-one stages -/

/-- The total-degree cap `1 + τ (j - 1)` of the cleared Taylor coordinates at a stage of total
jet degree `j` and common denominator exponent `τ`. -/
def firstOrderTaylorTotalCap (j τ : ℕ) : ℕ :=
  1 + τ * (j - 1)

/-- The first-derivative cap `min (1 + τ (j - 1)) (τ (r - 1) + K - 1)` of the cleared Taylor
coordinates at a stage of total jet degree `j` and first-derivative degree `r`, in ambient
dimension `K`. -/
def firstOrderTaylorDerivativeCap (K j r τ : ℕ) : ℕ :=
  min (firstOrderTaylorTotalCap j τ) (τ * (r - 1) + (K - 1))

/-- The first-derivative cap is at most the total-degree cap. -/
theorem firstOrderTaylorDerivativeCap_le_totalCap (K j r τ : ℕ) :
    firstOrderTaylorDerivativeCap K j r τ ≤ firstOrderTaylorTotalCap j τ :=
  min_le_left _ _

/-- The first-derivative cap is positive in ambient dimension at least `2`. -/
theorem firstOrderTaylorDerivativeCap_pos {K j r τ : ℕ} (hK : 2 ≤ K) :
    0 < firstOrderTaylorDerivativeCap K j r τ :=
  lt_min (by simp [firstOrderTaylorTotalCap]) (by omega)

/-- The total-degree cap increases with the total jet degree. -/
theorem firstOrderTaylorTotalCap_mono {j w τ : ℕ} (hjw : j ≤ w) :
    firstOrderTaylorTotalCap j τ ≤ firstOrderTaylorTotalCap w τ := by
  unfold firstOrderTaylorTotalCap
  gcongr

/-- The first-derivative cap increases with the total jet degree. -/
theorem firstOrderTaylorDerivativeCap_mono_total {K j w r τ : ℕ} (hjw : j ≤ w) :
    firstOrderTaylorDerivativeCap K j r τ ≤ firstOrderTaylorDerivativeCap K w r τ :=
  min_le_min_right _ (firstOrderTaylorTotalCap_mono hjw)

/-- The first-derivative cap increases with the first-derivative degree. -/
theorem firstOrderTaylorDerivativeCap_mono_derivative {K j r q τ : ℕ} (hrq : r ≤ q) :
    firstOrderTaylorDerivativeCap K j r τ ≤ firstOrderTaylorDerivativeCap K j q τ := by
  unfold firstOrderTaylorDerivativeCap
  apply min_le_min_left
  gcongr

/-- The fixed-fiber degree of an order-one stage of total jet degree `j` and first-derivative
degree `r`: the mixed volume `j c + r (b - c)` of the truncated triangles for `(j, r)` and for
the Taylor caps `(b, c)`. -/
def firstOrderCurveFiberStageOne (K j r τ : ℕ) : ℕ :=
  cappedDegreeMixedVolume j r (firstOrderTaylorTotalCap j τ)
    (firstOrderTaylorDerivativeCap K j r τ)

/-- The joint degree of an order-one stage of total jet degree `j` and first-derivative degree
`r`, retaining a challenge coordinate of degree `h`: the mixed volume of the prism of height `h`
over the truncated triangle for `(j, r)` and two prisms of height `ℓ + τ h` over the truncated
triangle for the Taylor caps `(b, c)`. -/
def firstOrderCurveJointStageOne (K ell h j r τ : ℕ) : ℕ :=
  cappedBidegreeMixedVolume h j r (ell + τ * h) (firstOrderTaylorTotalCap j τ)
    (firstOrderTaylorDerivativeCap K j r τ)

/-- In ambient dimension at least `2`, the fixed-fiber degree of an order-one stage is at least
the order-zero charge `j` at the same total jet degree. -/
theorem le_firstOrderCurveFiberStageOne {K j r τ : ℕ} (hK : 2 ≤ K) :
    j ≤ firstOrderCurveFiberStageOne K j r τ :=
  le_cappedDegreeMixedVolume (firstOrderTaylorDerivativeCap_pos hK)

/-- The mixed volume `j c + r (b - c)` with `c = min b x` increases with `j`, `r` and `b`: both
`c` and `b - c = b - x` increase with `b`. -/
private theorem cappedDegreeMixedVolume_min_mono {j j' r r' b b' x : ℕ} (hj : j ≤ j')
    (hr : r ≤ r') (hb : b ≤ b') :
    cappedDegreeMixedVolume j r b (min b x) ≤ cappedDegreeMixedVolume j' r' b' (min b' x) := by
  unfold cappedDegreeMixedVolume
  gcongr ?_ * ?_ + ?_ * ?_
  · exact min_le_min_right _ hb
  · omega

/-- The fixed-fiber stage degree increases with the total jet degree. -/
theorem firstOrderCurveFiberStageOne_mono_total {K τ j w r : ℕ} (hjw : j ≤ w) :
    firstOrderCurveFiberStageOne K j r τ ≤ firstOrderCurveFiberStageOne K w r τ :=
  cappedDegreeMixedVolume_min_mono hjw le_rfl (firstOrderTaylorTotalCap_mono hjw)

/-- For `q ≤ j`, the fixed-fiber stage degree increases with the first-derivative degree. -/
theorem firstOrderCurveFiberStageOne_mono_derivative {K τ j r q : ℕ} (hrq : r ≤ q)
    (hqj : q ≤ j) :
    firstOrderCurveFiberStageOne K j r τ ≤ firstOrderCurveFiberStageOne K j q τ :=
  (cappedDegreeMixedVolume_mono_right (hrq.trans hqj)
      (firstOrderTaylorDerivativeCap_le_totalCap ..)
      (firstOrderTaylorDerivativeCap_le_totalCap ..) le_rfl
      (firstOrderTaylorDerivativeCap_mono_derivative hrq)).trans
    (cappedDegreeMixedVolume_mono_left le_rfl hrq)

/-- For `r ≤ j`, the fixed-fiber stage degree is at most `j b`, the mixed volume without the
first-derivative cap. -/
theorem firstOrderCurveFiberStageOne_le_mul_totalCap {K j r τ : ℕ} (hrj : r ≤ j) :
    firstOrderCurveFiberStageOne K j r τ ≤ j * firstOrderTaylorTotalCap j τ := by
  have hcb := firstOrderTaylorDerivativeCap_le_totalCap K j r τ
  rw [firstOrderCurveFiberStageOne, cappedDegreeMixedVolume_eq hrj hcb]
  calc
    _ ≤ (j - r) * firstOrderTaylorTotalCap j τ + r * firstOrderTaylorTotalCap j τ := by gcongr
    _ = j * firstOrderTaylorTotalCap j τ := by rw [← Nat.add_mul, Nat.sub_add_cancel hrj]

/-- The joint stage degree increases with the total jet degree. -/
theorem firstOrderCurveJointStageOne_mono_total {K ell h τ j w r : ℕ} (hjw : j ≤ w) :
    firstOrderCurveJointStageOne K ell h j r τ ≤ firstOrderCurveJointStageOne K ell h w r τ := by
  have hb := firstOrderTaylorTotalCap_mono (τ := τ) hjw
  unfold firstOrderCurveJointStageOne cappedBidegreeMixedVolume
  exact Nat.add_le_add
    (Nat.mul_le_mul_left h (cappedDegreeMixedVolume_min_mono hb
      (firstOrderTaylorDerivativeCap_mono_total hjw) hb))
    (Nat.mul_le_mul_left _ (cappedDegreeMixedVolume_min_mono hjw le_rfl hb))

/-- For `q ≤ j`, the joint stage degree increases with the first-derivative degree. -/
theorem firstOrderCurveJointStageOne_mono_derivative {K ell h τ j r q : ℕ} (hrq : r ≤ q)
    (hqj : q ≤ j) :
    firstOrderCurveJointStageOne K ell h j r τ ≤ firstOrderCurveJointStageOne K ell h j q τ :=
  (cappedBidegreeMixedVolume_mono_right (hrq.trans hqj)
      (firstOrderTaylorDerivativeCap_le_totalCap ..)
      (firstOrderTaylorDerivativeCap_le_totalCap ..) le_rfl le_rfl
      (firstOrderTaylorDerivativeCap_mono_derivative hrq)).trans
    (cappedBidegreeMixedVolume_mono_left le_rfl le_rfl hrq)

/-- The fixed-fiber degree summed over the order-one stages. The stage of total jet degree
`t + 1` has first-derivative degree `t + 1 - (μ - min M μ)`. -/
def firstOrderCurveFiberOne (K μ M τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then
      firstOrderCurveFiberStageOne K (t + 1) (t + 1 - (μ - min M μ)) τ
    else 0

/-- The joint degree summed over the order-one stages. The stage of total jet degree `t + 1` has
first-derivative degree `t + 1 - (μ - min M μ)`. -/
def firstOrderCurveJointOne (K μ M ell h τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then
      firstOrderCurveJointStageOne K ell h (t + 1) (t + 1 - (μ - min M μ)) τ
    else 0

/-! ### The curve bound -/

/-- The bound on the exceptional challenges of a polynomial curve of degree `h`,

`h + λ₁ J₀ + λ₁ η J₁ + ℓ (n - L) (B₀ + λ₂ B₁)`,

where `J₀, J₁` are the joint and `B₀, B₁` the fixed-fiber stage sums over the order-zero and
order-one stages, `λ₁ = (n - L + 1) / (A - L + 1)` and `λ₂ = (n - k + 1) / (L - k + 1)` are the
incidence ratios at the split `L`, and `η` is the direct incidence factor of the order-one joint
term. -/
def firstOrderCurveBound (n K k L A μ M ell h τ : ℕ) (η : ℚ) : ℚ :=
  let l₁ : ℚ := ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)
  let l₂ : ℚ := ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)
  h + l₁ * firstOrderCurveJointZero μ M ell h τ +
    l₁ * η * firstOrderCurveJointOne K μ M ell h τ +
    ((ell * (n - L) : ℕ) : ℚ) *
      (firstOrderCurveFiberZero μ M + l₂ * firstOrderCurveFiberOne K μ M τ)

/-- The curve bound is monotone in the direct incidence factor. -/
theorem firstOrderCurveBound_mono_directFactor (n K k L A μ M ell h τ : ℕ) :
    Monotone (firstOrderCurveBound n K k L A μ M ell h τ) := by
  intro η η' hη
  unfold firstOrderCurveBound
  dsimp only
  gcongr

end ReedSolomon.HiddenDerivative
