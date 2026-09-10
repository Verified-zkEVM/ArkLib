/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Counting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.WeightedSupport


/-!
# Column-height counts for finite first-order interpolation

For a target challenge height `h`, a source column with `Y₀` exponent `a` admits
`h + 1 - a` coefficient slots.  Reindexing the finite first-order support by
`t = a + b` gives `a = t - b`.  Together with the exact number
`m * A + b - D * t` of possible `X` exponents, this yields the executable sum

```text
Σ t ≤ μ, Σ b ≤ min(t,M),
  (m * A + b - D * t) * (h + 1 - (t - b)).
```

All subtractions are natural-number positive parts in their mathematically correct order.  The
last section enumerates the entire support as distinct `SourceColumn`s, providing the column
family required by symbolic received-line interpolation.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {D A m M μ h rowTotal : ℕ}

/-- Total number of polynomial coefficient slots allowed by height `h` across the actual finite
first-order support. -/
def firstOrderColumnSlotCount (D A m M μ h : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦ h + 1 - u (some 0)

/-- Executable nested sum for the first-order column-height slot count. -/
def firstOrderHeightSlotCount (D A m M μ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      (m * A + b - D * t) * (h + 1 - (t - b))

/-- Under the support equivalence, the source `Y₀` exponent is `t - b`. -/
theorem firstOrderExponentDimensionIndex_y₀ (hD : 0 < D)
    (u : ↑(firstOrderExponents D A m M μ)) :
    u.1 (some 0) =
      (firstOrderExponentDimensionIndexEquiv hD u).1.val -
        (firstOrderExponentDimensionIndexEquiv hD u).2.1.val := by
  let hd : 0 < 1 := by omega
  change u.1 (some 0) =
    (exactExponentCoordinatesEquiv hd u.1).2.1.1 +
        (exactExponentCoordinatesEquiv hd u.1).2.1.2 -
      (exactExponentCoordinatesEquiv hd u.1).2.1.2
  rw [Nat.add_sub_cancel_right]
  exact (exactExponentCoordinatesEquiv_y₀ hd u.1).symm

/-- The dependent `(t,b,x)` index has the expected weighted cardinality, where every `x` at a
fixed `(t,b)` contributes the same number of height slots. -/
theorem sum_firstOrderDimensionIndex_height (D A m M μ h : ℕ) :
    (Finset.univ.sum fun q : FirstOrderDimensionIndex D A m M μ ↦
        h + 1 - (q.1.val - q.2.1.val)) =
      firstOrderHeightSlotCount D A m M μ h := by
  rw [Fintype.sum_sigma]
  calc
    (Finset.univ.sum fun t : Fin (μ + 1) ↦
        Finset.univ.sum fun q : (Σ b : Fin (min t.val M + 1),
          Fin (m * A + b.val - D * t.val)) ↦
          h + 1 - (t.val - q.1.val)) =
        Finset.univ.sum fun t : Fin (μ + 1) ↦
          Finset.univ.sum fun b : Fin (min t.val M + 1) ↦
            (m * A + b.val - D * t.val) * (h + 1 - (t.val - b.val)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.univ.sum fun b : Fin (min t M + 1) ↦
            (m * A + b.val - D * t) * (h + 1 - (t - b.val)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun t ↦ Finset.univ.sum fun b : Fin (min t M + 1) ↦
          (m * A + b.val - D * t) * (h + 1 - (t - b.val))) (μ + 1)
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.sum (Finset.range (min t M + 1)) fun b ↦
            (m * A + b - D * t) * (h + 1 - (t - b)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Fin.sum_univ_eq_sum_range
        (fun b ↦ (m * A + b - D * t) * (h + 1 - (t - b))) (min t M + 1)
    _ = firstOrderHeightSlotCount D A m M μ h := rfl

/-- The support-side column-slot sum is exactly the executable nested height sum. -/
theorem firstOrderColumnSlotCount_eq_heightSlotCount (hD : 0 < D) :
    firstOrderColumnSlotCount D A m M μ h =
      firstOrderHeightSlotCount D A m M μ h := by
  rw [firstOrderColumnSlotCount, ← Finset.sum_attach]
  let e := firstOrderExponentDimensionIndexEquiv
    (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    (Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦
        h + 1 - u.1 (some 0)) =
        Finset.univ.sum fun q : FirstOrderDimensionIndex D A m M μ ↦
          h + 1 - (q.1.val - q.2.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderExponentDimensionIndex_y₀ hD]
    _ = firstOrderHeightSlotCount D A m M μ h :=
      sum_firstOrderDimensionIndex_height D A m M μ h

/-! ### A canonical height satisfying the finite slot test -/

/-- Sum of the `Y₀` exponents over all first-order support columns. -/
def firstOrderY₀Weight (D A m M μ : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦ u (some 0)

/-- Every support column has `Y₀` exponent at most the total-jet cap. -/
theorem firstOrder_y₀_le_μ {u : JetVariable 1 →₀ ℕ}
    (hu : u ∈ firstOrderExponents D A m M μ) : u (some 0) ≤ μ := by
  calc
    u (some 0) = u.some 0 := rfl
    _ ≤ totalJetDegree u := Finsupp.le_degree 0 u.some
    _ ≤ μ := (mem_firstOrderExponents.mp hu).2.1

/-- Above the total-jet cap, the slot count plus the `Y₀`-weight is rectangular. -/
theorem firstOrderColumnSlotCount_add_y₀Weight (hμ : μ ≤ h) :
    firstOrderColumnSlotCount D A m M μ h + firstOrderY₀Weight D A m M μ =
      (firstOrderExponents D A m M μ).card * (h + 1) := by
  rw [firstOrderColumnSlotCount, firstOrderY₀Weight, ← Finset.sum_add_distrib]
  calc
    Finset.sum (firstOrderExponents D A m M μ)
        (fun u ↦ h + 1 - u (some 0) + u (some 0)) =
        Finset.sum (firstOrderExponents D A m M μ) (fun _ ↦ h + 1) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Nat.sub_add_cancel]
      exact (firstOrder_y₀_le_μ hu).trans (hμ.trans (Nat.le_add_right h 1))
    _ = (firstOrderExponents D A m M μ).card * (h + 1) := by simp

/-- Canonical column height obtained from the dimension surplus and total `Y₀`-weight. -/
def firstOrderCertificateHeight (D A m M μ rowTotal : ℕ) : ℕ :=
  max μ (firstOrderY₀Weight D A m M μ /
    ((firstOrderExponents D A m M μ).card - rowTotal))

/-- Whenever the total row-rank budget is below the support dimension, the canonical height
satisfies the strict column-slot inequality. -/
theorem firstOrder_rowTotal_mul_height_lt_columnSlotCount
    (hrank : rowTotal < (firstOrderExponents D A m M μ).card) :
    rowTotal * (firstOrderCertificateHeight D A m M μ rowTotal + 1) <
      firstOrderColumnSlotCount D A m M μ
        (firstOrderCertificateHeight D A m M μ rowTotal) := by
  let N := (firstOrderExponents D A m M μ).card
  let W := firstOrderY₀Weight D A m M μ
  let gap := N - rowTotal
  let H := firstOrderCertificateHeight D A m M μ rowTotal
  have hgap : 0 < gap := by simpa [gap, N] using Nat.sub_pos_of_lt hrank
  have hfloor : W < (W / gap + 1) * gap :=
    (Nat.div_lt_iff_lt_mul hgap).mp (Nat.lt_succ_self (W / gap))
  have hμ : μ ≤ H := by simp [H, firstOrderCertificateHeight]
  have hquot : W / gap ≤ H := by
    simp [H, firstOrderCertificateHeight, W, gap, N]
  have hW : W < gap * (H + 1) := by
    calc
      W < (W / gap + 1) * gap := hfloor
      _ ≤ (H + 1) * gap := Nat.mul_le_mul_right gap (Nat.add_le_add_right hquot 1)
      _ = gap * (H + 1) := Nat.mul_comm _ _
  have hid : firstOrderColumnSlotCount D A m M μ H + W = N * (H + 1) := by
    simpa [N, W] using
      (firstOrderColumnSlotCount_add_y₀Weight
        (D := D) (A := A) (m := m) (M := M) (μ := μ) (h := H) hμ)
  have hdecomp : N * (H + 1) =
      rowTotal * (H + 1) + gap * (H + 1) := by
    rw [← Nat.add_mul]
    congr 1
    exact (Nat.add_sub_of_le hrank.le).symm
  change rowTotal * (H + 1) < firstOrderColumnSlotCount D A m M μ H
  omega

/-- Executable form of the canonical strict height test. -/
theorem firstOrder_rowTotal_mul_height_lt_heightSlotCount (hD : 0 < D)
    (hrank : rowTotal < (firstOrderExponents D A m M μ).card) :
    rowTotal * (firstOrderCertificateHeight D A m M μ rowTotal + 1) <
      firstOrderHeightSlotCount D A m M μ
        (firstOrderCertificateHeight D A m M μ rowTotal) := by
  rw [← firstOrderColumnSlotCount_eq_heightSlotCount hD]
  exact firstOrder_rowTotal_mul_height_lt_columnSlotCount hrank

/-! ### Complete symbolic source-column enumeration -/

namespace SymbolicWeightedSupportInterpolation

open SymbolicReceivedInterpolation

/-- Canonical enumeration of every finite first-order support monomial as a symbolic source
column. -/
def firstOrderColumns :
    Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → SourceColumn 1 :=
  fun j ↦ SourceColumn.ofExponent
    (((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).1)

@[simp]
theorem firstOrderColumns_exponent
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent =
      ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).1 := by
  simp [firstOrderColumns]

/-- The complete first-order column enumeration has no duplicate monomials. -/
theorem firstOrderColumns_injective :
    Function.Injective
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) := by
  intro i j hij
  apply (Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm.injective
  apply Subtype.ext
  rw [← firstOrderColumns_exponent i, ← firstOrderColumns_exponent j, hij]

/-- Every enumerated column satisfies the finite first-order support predicate. -/
theorem firstOrderColumns_eligible
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent ∈
      firstOrderExponents D A m M μ := by
  rw [firstOrderColumns_exponent]
  exact ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).2

end SymbolicWeightedSupportInterpolation

end

end ReedSolomon.HiddenDerivative
