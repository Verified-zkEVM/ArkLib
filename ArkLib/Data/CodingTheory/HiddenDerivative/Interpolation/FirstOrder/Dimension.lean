/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Space

/-!
# The dimension of the first-order interpolation space

The first-order space of `Interpolation/FirstOrder/Space.lean` is spanned by the monomials
`X^x Y₀^a Y₁^b` with `b ≤ M`, `a + b ≤ μ`, and `x + D a + (D - 1) b < m A`. Index them by the
total jet degree `t = a + b`, then by `b ≤ min t M`, then by `x`. For `0 < D`, adding `b` to both
sides of the weight condition turns it into `x + D t < m A + b`, so for fixed `(t, b)` there are
exactly `m A + b - D t` choices of `x`. The order of operations matters: the count is the
positive part of the integer `m A + b - D t`, and computing `m A - D t` first in `ℕ` would
truncate before adding `b`.

## Main statements

* `firstOrderDimensionCount`: the double sum `∑_{t ≤ μ} ∑_{b ≤ min t M} (m A + b - D t)`.
* `card_firstOrderDimensionCoordinates`: the count is the number of coordinate triples it
  describes, for every `D`.
* `card_firstOrderExponents` and `finrank_firstOrderSpace_eq_firstOrderDimensionCount`: for
  `0 < D` the first-order space has dimension `firstOrderDimensionCount D A m M μ`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1.
-/

@[expose] public section

open PolynomialDifferential Finset

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {D A m M μ : ℕ}

/-- For `0 < D`, the weight condition `x + D a + (D - 1) b < m A` says that `x` is below the
residual `m A + b - D (a + b)` left by the total jet degree `a + b`. The hypothesis is needed: at
`D = 0` the left side ignores `b` while the residual grows with it. -/
theorem firstOrderWeight_lt_iff_lt_residual (hD : 0 < D) (x a b : ℕ) :
    x + D * a + (D - 1) * b < m * A ↔ x < m * A + b - D * (a + b) := by
  have hb : (D - 1) * b + b = D * b := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hD]
  rw [Nat.mul_add]
  omega

/-- The first-order dimension count `∑_{t ≤ μ} ∑_{b ≤ min t M} (m A + b - D t)`, with addition
before truncated subtraction.

This counts the eligible exponents of the first-order space when `0 < D`; see
`card_firstOrderExponents`. The expression is defined for all parameters. -/
def firstOrderDimensionCount (D A m M μ : ℕ) : ℕ :=
  ∑ t ∈ range (μ + 1), ∑ b ∈ range (min t M + 1), (m * A + b - D * t)

/-- The coordinate triples `⟨⟨t, b⟩, x⟩` counted by `firstOrderDimensionCount`: `t ≤ μ`,
`b ≤ min t M`, and `x < m A + b - D t`. -/
def firstOrderDimensionCoordinates (D A m M μ : ℕ) : Finset (Σ _ : (Σ _ : ℕ, ℕ), ℕ) :=
  ((range (μ + 1)).sigma fun t => range (min t M + 1)).sigma
    fun p => range (m * A + p.2 - D * p.1)

/-- `firstOrderDimensionCount` is the number of coordinate triples it describes. No hypothesis on
the parameters is needed. -/
theorem card_firstOrderDimensionCoordinates (D A m M μ : ℕ) :
    #(firstOrderDimensionCoordinates D A m M μ) = firstOrderDimensionCount D A m M μ := by
  simp [firstOrderDimensionCoordinates, firstOrderDimensionCount, card_sigma, sum_sigma]

/-- The exponent `X^x Y₀^a Y₁^b` on the first-order variables. -/
private def firstOrderMonomialExponent (x a b : ℕ) : JetVariable 1 →₀ ℕ :=
  Finsupp.single none x + Finsupp.single (some 0) a + Finsupp.single (some 1) b

private theorem firstOrderMonomialExponent_none (x a b : ℕ) :
    firstOrderMonomialExponent x a b none = x := by
  simp [firstOrderMonomialExponent]

private theorem firstOrderMonomialExponent_some_zero (x a b : ℕ) :
    firstOrderMonomialExponent x a b (some 0) = a := by
  simp [firstOrderMonomialExponent]

private theorem firstOrderMonomialExponent_some_one (x a b : ℕ) :
    firstOrderMonomialExponent x a b (some 1) = b := by
  simp [firstOrderMonomialExponent]

private theorem firstOrderMonomialExponent_eta (u : JetVariable 1 →₀ ℕ) :
    firstOrderMonomialExponent (u none) (u (some 0)) (u (some 1)) = u := by
  ext v
  rcases v with _ | j
  · exact firstOrderMonomialExponent_none _ _ _
  · fin_cases j
    · exact firstOrderMonomialExponent_some_zero _ _ _
    · exact firstOrderMonomialExponent_some_one _ _ _

/-- For `0 < D` the first-order space has `firstOrderDimensionCount D A m M μ` eligible
exponents: `u ↦ ⟨⟨a + b, b⟩, x⟩` is a bijection onto `firstOrderDimensionCoordinates`. The
hypothesis `0 < D` is needed: at `D = 0` and `m A = 0` there are no eligible exponents, while the
count is positive once `μ` and `M` are. -/
theorem card_firstOrderExponents (hD : 0 < D) :
    #(firstOrderExponents D A m M μ) = firstOrderDimensionCount D A m M μ := by
  rw [← card_firstOrderDimensionCoordinates]
  refine card_nbij' (fun u => ⟨⟨u (some 0) + u (some 1), u (some 1)⟩, u none⟩)
    (fun q => firstOrderMonomialExponent q.2 (q.1.1 - q.1.2) q.1.2) ?_ ?_ ?_ ?_
  · intro u hu
    rw [mem_coe, mem_firstOrderExponents_iff_coordinates,
      firstOrderWeight_lt_iff_lt_residual hD] at hu
    simp only [coe_sigma, firstOrderDimensionCoordinates, Set.mem_sigma_iff, mem_coe, mem_range]
    omega
  · rintro ⟨⟨t, b⟩, x⟩ hq
    simp only [coe_sigma, firstOrderDimensionCoordinates, Set.mem_sigma_iff, mem_coe,
      mem_range] at hq
    dsimp only
    rw [mem_coe, mem_firstOrderExponents_iff_coordinates, firstOrderMonomialExponent_none,
      firstOrderMonomialExponent_some_zero, firstOrderMonomialExponent_some_one,
      firstOrderWeight_lt_iff_lt_residual hD, Nat.sub_add_cancel (by omega)]
    omega
  · intro u _
    exact (congrArg (fun a => firstOrderMonomialExponent (u none) a (u (some 1)))
      (Nat.add_sub_cancel _ _)).trans (firstOrderMonomialExponent_eta u)
  · rintro ⟨⟨t, b⟩, x⟩ hq
    simp only [coe_sigma, firstOrderDimensionCoordinates, Set.mem_sigma_iff, mem_coe,
      mem_range] at hq
    dsimp only
    simp only [firstOrderMonomialExponent_none, firstOrderMonomialExponent_some_zero,
      firstOrderMonomialExponent_some_one, Nat.sub_add_cancel (by omega : b ≤ t)]

/-- For `0 < D` the first-order space has dimension `firstOrderDimensionCount D A m M μ`. See
`card_firstOrderExponents` for the role of the hypothesis. -/
theorem finrank_firstOrderSpace_eq_firstOrderDimensionCount (F : Type*) [Field F]
    (hD : 0 < D) :
    Module.finrank F (firstOrderSpace F D A m M μ) = firstOrderDimensionCount D A m M μ := by
  rw [finrank_firstOrderSpace_eq_card, card_firstOrderExponents hD]

end

end ReedSolomon.HiddenDerivative
