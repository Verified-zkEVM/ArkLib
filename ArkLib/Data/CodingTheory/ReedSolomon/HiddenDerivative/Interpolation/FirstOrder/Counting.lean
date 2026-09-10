/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Interpolation


/-!
# Exact dimension count for finite first-order interpolation

The first-order support is indexed by monomials `X^x Y₀^a Y₁^b`.  This file reindexes them by
their total jet degree `t = a + b`, then by `b`, and finally by `x`.  For fixed `(t,b)`, the
specialization inequality is

```text
x + D a + (D - 1) b < m A
```

and, when `0 < D`, adding `b` to both sides turns it into

```text
x + D t < m A + b.
```

Consequently there are exactly `m * A + b - D * t` choices of `x`.  The order of the natural
subtraction is essential: this is the positive part of the integer `mA - Dt + b`, whereas
`mA - Dt + b` in `ℕ` would truncate before adding `b` and can overcount.

The resulting equivalence is the executable dimension bridge for the support used by the actual
first-order constraint map.  Combined with `exists_nonzero_firstOrder_interpolant`, it makes the
finite inequality between this sum and the certified local rank a kernel-checked interpolation
certificate.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {F : Type*} {D A m M μ : ℕ}

/-- Coordinate form of the first-order support predicate. -/
def FirstOrderCoordinatesEligible (D A m M μ : ℕ)
    (p : ExactExponentCoordinates 1) : Prop :=
  p.2.1.2 ≤ M ∧
    p.2.1.1 + p.2.1.2 ≤ μ ∧
    p.1 + D * p.2.1.1 + (D - 1) * p.2.1.2 < m * A

/-- Support exponents are equivalent to their eligible `(x,a,b)` coordinates.  The remaining
coordinate is a function out of `Fin 0`, hence carries no data. -/
def firstOrderEligibleCoordinateEquiv :
    ↑(firstOrderExponents D A m M μ) ≃
      {p : ExactExponentCoordinates 1 // FirstOrderCoordinatesEligible D A m M μ p} :=
  Equiv.subtypeEquiv (exactExponentCoordinatesEquiv (by omega : 0 < 1)) fun u ↦ by
    rw [mem_firstOrderExponents_iff_coordinates]
    rfl

/-- For positive `D`, the derivative-weighted cost plus `b` is `D` times total jet degree. -/
theorem firstOrder_weight_add_firstJet_eq (hD : 0 < D) (x a b : ℕ) :
    x + D * a + (D - 1) * b + b = x + D * (a + b) := by
  calc
    x + D * a + (D - 1) * b + b = x + D * a + ((D - 1) * b + b) := by omega
    _ = x + D * a + ((D - 1 + 1) * b) := by simp [Nat.add_mul]
    _ = x + D * a + D * b := by rw [Nat.sub_add_cancel (by omega : 1 ≤ D)]
    _ = x + D * (a + b) := by simp [Nat.mul_add, Nat.add_assoc]

/-- The fixed-`(a,b)` support inequality is equivalent to the residual range for `x`. -/
theorem firstOrder_x_lt_residual_iff (hD : 0 < D) (x a b : ℕ) :
    x < m * A + b - D * (a + b) ↔
      x + D * a + (D - 1) * b < m * A := by
  rw [Nat.lt_sub_iff_add_lt, ← firstOrder_weight_add_firstJet_eq hD]
  exact Nat.add_lt_add_iff_right

/-- Executable dependent index for first-order support monomials. -/
abbrev FirstOrderDimensionIndex (D A m M μ : ℕ) :=
  Σ t : Fin (μ + 1),
    Σ b : Fin (min t.val M + 1),
      Fin (m * A + b.val - D * t.val)

/-- A nondependent natural-coordinate presentation of the nested `(t,b,x)` index. -/
def FirstOrderFlatDimensionEligible (D A m M μ : ℕ) (p : ℕ × (ℕ × ℕ)) : Prop :=
  p.1 ≤ μ ∧ p.2.1 ≤ min p.1 M ∧ p.2.2 < m * A + p.2.1 - D * p.1

/-- Reindex eligible `(x,a,b)` coordinates by `t = a + b`.  Keeping this intermediate
presentation nondependent makes the inverse `a = t - b` transparent. -/
def firstOrderCoordinateFlatDimensionEquiv (hD : 0 < D) :
    {p : ExactExponentCoordinates 1 // FirstOrderCoordinatesEligible D A m M μ p} ≃
      {p : ℕ × (ℕ × ℕ) // FirstOrderFlatDimensionEligible D A m M μ p} where
  toFun p :=
    ⟨(p.1.2.1.1 + p.1.2.1.2, (p.1.2.1.2, p.1.1)),
      ⟨p.2.2.1, le_min (Nat.le_add_left _ _) p.2.1,
        (firstOrder_x_lt_residual_iff hD _ _ _).mpr p.2.2.2⟩⟩
  invFun p :=
    ⟨(p.1.2.2, ((p.1.1 - p.1.2.1, p.1.2.1), default)), by
      have hbt : p.1.2.1 ≤ p.1.1 := p.2.2.1.trans (min_le_left _ _)
      have hbM : p.1.2.1 ≤ M := p.2.2.1.trans (min_le_right _ _)
      have hsum : p.1.1 - p.1.2.1 + p.1.2.1 = p.1.1 :=
        Nat.sub_add_cancel hbt
      refine ⟨hbM, ?_, ?_⟩
      · rw [hsum]
        exact p.2.1
      · apply (firstOrder_x_lt_residual_iff hD _ _ _).mp
        simpa only [hsum] using p.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨x, ⟨⟨a, b⟩, c⟩⟩, hp⟩
    simp only
    congr 3
    · exact Nat.add_sub_cancel_right a b
    · funext i
      exact Fin.elim0 i
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨t, b, x⟩, hp⟩
    simp only
    apply Prod.ext
    · exact Nat.sub_add_cancel (hp.2.1.trans (min_le_left _ _))
    · rfl

/-- The flat bounded coordinates are equivalent to the executable dependent index. -/
def firstOrderFlatDimensionIndexEquiv :
    {p : ℕ × (ℕ × ℕ) // FirstOrderFlatDimensionEligible D A m M μ p} ≃
      FirstOrderDimensionIndex D A m M μ where
  toFun p :=
    ⟨⟨p.1.1, Nat.lt_succ_of_le p.2.1⟩,
      ⟨⟨p.1.2.1, Nat.lt_succ_of_le p.2.2.1⟩, ⟨p.1.2.2, p.2.2.2⟩⟩⟩
  invFun p :=
    ⟨(p.1.val, (p.2.1.val, p.2.2.val)),
      ⟨Nat.le_of_lt_succ p.1.isLt, Nat.le_of_lt_succ p.2.1.isLt, p.2.2.isLt⟩⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨t, b, x⟩
    rfl

/-- Eligible `(x,a,b)` coordinates are equivalent to the nested `(t,b,x)` dimension index. -/
def firstOrderCoordinateDimensionIndexEquiv (hD : 0 < D) :
    {p : ExactExponentCoordinates 1 // FirstOrderCoordinatesEligible D A m M μ p} ≃
      FirstOrderDimensionIndex D A m M μ :=
  (firstOrderCoordinateFlatDimensionEquiv hD).trans firstOrderFlatDimensionIndexEquiv

/-- Canonical equivalence between first-order support columns and the executable nested index. -/
def firstOrderExponentDimensionIndexEquiv (hD : 0 < D) :
    ↑(firstOrderExponents D A m M μ) ≃ FirstOrderDimensionIndex D A m M μ :=
  firstOrderEligibleCoordinateEquiv.trans (firstOrderCoordinateDimensionIndexEquiv hD)

/-- Exact derivative-weighted first-order dimension sum.

The summand uses `(m * A + b) - D * t`, with addition before natural subtraction. -/
def firstOrderDimensionCount (D A m M μ : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      m * A + b - D * t

/-- The nested executable index has cardinality equal to the double sum. -/
theorem card_firstOrderDimensionIndex (D A m M μ : ℕ) :
    Fintype.card (FirstOrderDimensionIndex D A m M μ) =
      firstOrderDimensionCount D A m M μ := by
  rw [Fintype.card_sigma]
  calc
    (∑ t : Fin (μ + 1),
        Fintype.card (Σ b : Fin (min t.val M + 1),
          Fin (m * A + b.val - D * t.val))) =
        Finset.univ.sum fun t : Fin (μ + 1) ↦
          Finset.univ.sum fun b : Fin (min t.val M + 1) ↦
            m * A + b.val - D * t.val := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.univ.sum fun b : Fin (min t M + 1) ↦
            m * A + b.val - D * t := by
      exact Fin.sum_univ_eq_sum_range
        (fun t ↦ Finset.univ.sum fun b : Fin (min t M + 1) ↦
          m * A + b.val - D * t) (μ + 1)
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.sum (Finset.range (min t M + 1)) fun b ↦
            m * A + b - D * t := by
      apply Finset.sum_congr rfl
      intro t _
      exact Fin.sum_univ_eq_sum_range
        (fun b ↦ m * A + b - D * t) (min t M + 1)
    _ = firstOrderDimensionCount D A m M μ := rfl

/-- The finite first-order monomial support has exactly the executable double-sum cardinality. -/
theorem card_firstOrderExponents_eq_dimensionCount (hD : 0 < D) :
    (firstOrderExponents D A m M μ).card = firstOrderDimensionCount D A m M μ := by
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr (firstOrderExponentDimensionIndexEquiv hD)).trans
    (card_firstOrderDimensionIndex D A m M μ)

/-- The capped polynomial space has the exact first-order double-sum dimension. -/
theorem finrank_firstOrderSpace_eq_dimensionCount [Field F] (hD : 0 < D) :
    Module.finrank F (firstOrderSpace F D A m M μ) =
      firstOrderDimensionCount D A m M μ := by
  rw [finrank_firstOrderSpace_eq_card,
    card_firstOrderExponents_eq_dimensionCount hD]

/-- The executable double-sum inequality is directly sufficient for a nonzero interpolant
satisfying the actual local constraints. -/
theorem exists_nonzero_firstOrder_interpolant_of_dimensionCount
    [Field F] {ι : Type*} [Fintype ι] (hD : 1 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      firstOrderDimensionCount D A m M μ) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧
      Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  apply exists_nonzero_firstOrder_interpolant hD centers received
  rwa [card_firstOrderExponents_eq_dimensionCount (by omega : 0 < D)]

end

end ReedSolomon.HiddenDerivative
