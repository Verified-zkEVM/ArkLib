/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveRank
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight

/-!
# Shifted height counts for first-order curve interpolation

For a received curve of degree at most `ℓ`, each first-order source column of total jet degree
`t` has challenge degree at most `ℓ*t`. The shifted source count sums its available coefficient
slots, including inactive columns through natural-number truncated subtraction. The shifted row
count uses the actual graded image ranks, and the numerical profile bounds that count. Their
strict surplus gives a primitive interpolant satisfying the local constraints at every point.

## Main statements

* `firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount`: the support sum equals its
  executable sum over total jet degree and first-jet exponent.
* `firstOrderCurveShiftedRowSlotCount_le_bound`: the actual graded row count is bounded by its
  numerical profile.
* `firstOrderCurveShiftedRowSlotBound_le_of_rankBound`: a pointwise rank profile bounds the
  shifted row-slot sum.
* `exists_primitive_firstOrderCurve_interpolant_of_shifted_height` and its numerical-bound form:
  a shifted slot surplus gives a primitive interpolant with per-column degree bounds.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {D A m M μ ℓ h : ℕ}

/-! ### Shifted source and row profiles -/

/-- Under the support equivalence, the source total jet degree is the outer index `t`. -/
theorem firstOrderCoordinatesEquiv_totalJetDegree (hD : 0 < D)
    (u : ↑(firstOrderExponents D A m M μ)) :
    totalJetDegree u.1 = (firstOrderCoordinatesEquiv hD u).1.1.1 := by
  simp [firstOrderCoordinatesEquiv, totalJetDegree_eq_sum, Fin.sum_univ_two]

/-- Truncated source slots when a degree-`t` column receives challenge weight `ℓ*t`. -/
def firstOrderCurveShiftedColumnSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦
    h + 1 - ℓ * totalJetDegree u

/-- Executable nested form of the shifted source-slot count. -/
def firstOrderCurveShiftedHeightSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      (m * A + b - D * t) * (h + 1 - ℓ * t)

/-- Reindexing by `(t,b,x)` turns the shifted source count into its executable nested sum. -/
theorem firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount (hD : 0 < D) :
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h =
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := by
  rw [firstOrderCurveShiftedColumnSlotCount, ← Finset.sum_attach]
  let e := firstOrderCoordinatesEquiv
    (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    Finset.univ.sum (fun u : ↑(firstOrderExponents D A m M μ) ↦
        h + 1 - ℓ * totalJetDegree u.1) =
        Finset.univ.sum (fun q : ↑(firstOrderDimensionCoordinates D A m M μ) ↦
          h + 1 - ℓ * q.1.1.1) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderCoordinatesEquiv_totalJetDegree hD]
    _ = firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := by
      classical
      let f : (Σ _ : (Σ _ : ℕ, ℕ), ℕ) → ℕ := fun q ↦ h + 1 - ℓ * q.1.1
      have hsum : (Finset.univ.sum fun q :
          ↑(firstOrderDimensionCoordinates D A m M μ) ↦
          f q.1) = (firstOrderDimensionCoordinates D A m M μ).sum f := by
        rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
      rw [hsum, firstOrderDimensionCoordinates, Finset.sum_sigma, Finset.sum_sigma]
      simp [firstOrderCurveShiftedHeightSlotCount, Finset.sum_const,
        Finset.card_range, Nat.mul_comm]

/-- Truncated row slots supplied by the actual base-field graded images at `n` points. -/
def firstOrderCurveShiftedRowSlotCount (F : Type*) [Field F]
    (D A m M μ n ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    n * firstOrderOriginGradedRank F D A m M t * (h + 1 - ℓ * t)

/-- Executable upper bound on shifted row slots obtained from the sharp numerical block
profile. -/
def firstOrderCurveShiftedRowSlotBound
    (D A m M μ n ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    n * firstOrderGradedRankBound D A m M t * (h + 1 - ℓ * t)

/-- The shifted row-slot bound is monotone in any pointwise upper bound on the rank profile. -/
theorem firstOrderCurveShiftedRowSlotBound_le_of_rankBound
    (D A m M μ n ℓ h : ℕ) (rankBound : ℕ → ℕ)
    (hrank : ∀ t, firstOrderGradedRankBound D A m M t ≤ rankBound t) :
    firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h ≤
      ∑ t ∈ Finset.range (μ + 1), n * rankBound t * (h + 1 - ℓ * t) := by
  apply Finset.sum_le_sum
  intro t ht
  exact Nat.mul_le_mul_right (h + 1 - ℓ * t) (Nat.mul_le_mul_left n (hrank t))

/-- The actual compressed-row slot count is bounded by the numerical block-rank profile. -/
theorem firstOrderCurveShiftedRowSlotCount_le_bound
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h ≤
      firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h := by
  apply Finset.sum_le_sum
  intro t ht
  exact Nat.mul_le_mul_right (h + 1 - ℓ * t)
    (Nat.mul_le_mul_left n (firstOrderOriginGradedRank_le_bound (F := F) D A m M t))

private theorem sum_firstOrderCurveGradedRowIndex_profile
    {F : Type*} [Field F] (D A m M μ n : ℕ) (profile : ℕ → ℕ) :
    (Finset.univ.sum fun row : FirstOrderCurveGradedRowIndex F D A m M μ n ↦
      profile row.2.1.val) =
      n * ∑ t ∈ Finset.range (μ + 1),
        firstOrderOriginGradedRank F D A m M t * profile t := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [firstOrderOriginGradedRank]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp

/-- The finite type of fixed compressed rows has exactly the truncated weighted slot count. -/
theorem sum_firstOrderCurveGradedRowIndex_slots
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    (Finset.univ.sum fun row : FirstOrderCurveGradedRowIndex F D A m M μ n ↦
      h + 1 - ℓ * row.2.1.val) =
      firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h := by
  rw [firstOrderCurveShiftedRowSlotCount]
  simpa [Nat.mul_assoc, Finset.mul_sum] using
    (sum_firstOrderCurveGradedRowIndex_profile (F := F) D A m M μ n
      (fun t ↦ h + 1 - ℓ * t))

/-- Flattening the compressed row index preserves its exact truncated weighted slot count. -/
theorem sum_firstOrderCurveGradedFinRowWeight_slots
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    (Finset.univ.sum fun i :
        Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)) ↦
      h + 1 - firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i) =
      firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h := by
  rw [← Equiv.sum_comp
    (Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n))]
  simpa [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight] using
    (sum_firstOrderCurveGradedRowIndex_slots (F := F) D A m M μ n ℓ h)

/-- Enumerating the canonical first-order columns by `Fin` preserves the exact truncated
shifted source-slot count. -/
theorem sum_firstOrderColumns_shifted_slots (D A m M μ ℓ h : ℕ) :
    (Finset.univ.sum fun j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) ↦
      h + 1 - ℓ * totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent) =
      firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h := by
  let e := Fintype.equivFin ↑(firstOrderExponents D A m M μ)
  calc
    (Finset.univ.sum fun j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) ↦
        h + 1 - ℓ * totalJetDegree
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent) =
        Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦
          h + 1 - ℓ * totalJetDegree u.1 := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderColumns_exponent]
      simp [e]
    _ = Finset.sum (firstOrderExponents D A m M μ)
          (fun u ↦ h + 1 - ℓ * totalJetDegree u) := by
      simpa using Finset.sum_attach (firstOrderExponents D A m M μ)
        (fun u ↦ h + 1 - ℓ * totalJetDegree u)
    _ = firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h := rfl

/-- The exact truncated shifted-height test. -/
def FirstOrderCurveShiftedHeightSurplus (F : Type*) [Field F]
    (D A m M μ n ℓ h : ℕ) : Prop :=
  firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h <
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h

/-- Total source weight, used to simplify the shifted test when every source block is active. -/
def firstOrderTotalJetWeight (D A m M μ : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) totalJetDegree

/-- Total row weight of the actual graded image at one point. -/
def firstOrderGradedRowWeight (F : Type*) [Field F]
    (D A m M μ : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    firstOrderOriginGradedRank F D A m M t * t

/-- In the all-active range, the source slots equal a rectangle minus the weighted profile. -/
theorem firstOrderCurveShiftedColumnSlotCount_add_weight
    (hactive : ℓ * μ ≤ h) :
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h +
        ℓ * firstOrderTotalJetWeight D A m M μ =
      (firstOrderExponents D A m M μ).card * (h + 1) := by
  rw [firstOrderCurveShiftedColumnSlotCount, firstOrderTotalJetWeight,
    Finset.mul_sum]
  exact Finset.sum_tsub_add_sum_eq_card_mul (firstOrderExponents D A m M μ)
    (fun u ↦ ℓ * totalJetDegree u) h
    (fun u hu => (Nat.mul_le_mul_left ℓ (mem_firstOrderExponents.mp hu).2.1).trans
      (hactive.trans (Nat.le_add_right h 1)))

/-- In the all-active range, compressed row slots also equal a rectangle minus the weighted
actual-rank profile. -/
theorem firstOrderCurveShiftedRowSlotCount_add_weight
    {F : Type*} [Field F] {n : ℕ} (hactive : ℓ * μ ≤ h) :
    firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h +
        n * ℓ * firstOrderGradedRowWeight F D A m M μ =
      n * (∑ t ∈ Finset.range (μ + 1), firstOrderOriginGradedRank F D A m M t) *
        (h + 1) := by
  classical
  let rows := FirstOrderCurveGradedRowIndex F D A m M μ n
  have hcard : Fintype.card rows =
      n * ∑ t ∈ Finset.range (μ + 1), firstOrderOriginGradedRank F D A m M t := by
    simpa [rows] using
      (sum_firstOrderCurveGradedRowIndex_profile (F := F) D A m M μ n (fun _ ↦ 1))
  have hweight :
      (Finset.univ.sum fun row : rows ↦ ℓ * row.2.1.val) =
        n * ℓ * firstOrderGradedRowWeight F D A m M μ := by
    rw [sum_firstOrderCurveGradedRowIndex_profile (F := F) D A m M μ n (fun t ↦ ℓ * t),
      firstOrderGradedRowWeight]
    have hfactor :
        (∑ t ∈ Finset.range (μ + 1),
          firstOrderOriginGradedRank F D A m M t * (ℓ * t)) =
        ℓ * ∑ t ∈ Finset.range (μ + 1),
          firstOrderOriginGradedRank F D A m M t * t := by
      calc
        _ = ∑ t ∈ Finset.range (μ + 1),
            ℓ * (firstOrderOriginGradedRank F D A m M t * t) := by
          apply Finset.sum_congr rfl
          intro t ht
          ring
        _ = _ := by rw [Finset.mul_sum]
    rw [hfactor]
    ring
  have hslots := Finset.sum_tsub_add_sum_eq_card_mul (Finset.univ : Finset rows)
    (fun row ↦ ℓ * row.2.1.val) h (by
      intro row hrow
      have ht : row.2.1.val ≤ μ := Nat.le_of_lt_succ row.2.1.isLt
      exact (Nat.mul_le_mul_left ℓ ht).trans
        (hactive.trans (Nat.le_add_right h 1)))
  rw [sum_firstOrderCurveGradedRowIndex_slots, hweight, Finset.card_univ, hcard] at hslots
  exact hslots

/-! ### Concrete primitive shifted-height constructor -/

/-- The exact shifted surplus for the actual compressed graded rows constructs a primitive
first-order curve interpolant. Every kernel premise is discharged by the translated
base-field row-compression theorem. -/
theorem exists_primitive_firstOrderCurve_interpolant_of_shifted_height
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) (hD : 0 < D)
    (centers : Fin n → F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hsurplus : FirstOrderCurveShiftedHeightSurplus F D A m M μ n ℓ h) :
    ∃ v : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → F[X],
      v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F
        (h + 1 - ℓ * totalJetDegree
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant
            (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (SourceColumn.interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) := by
  apply exists_primitive_interpolant_of_shifted_height
    m ℓ h centers w
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
    firstOrderColumns_injective
    (firstOrderCurveGradedFinMatrix D A m M μ n centers w)
    (firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ)
  · intro v hv
    exact (firstOrderCurveGradedFinMatrix_kernel_iff
      D A m M μ n hD centers w v).mp hv
  · intro i j hweight
    exact firstOrderCurveGradedFinMatrix_degree_le
      D A m M μ n ℓ centers w hw i j
  · intro i j hweight
    exact firstOrderCurveGradedFinMatrix_eq_zero_of_weight_lt
      D A m M μ n ℓ centers w i j hweight
  · rw [sum_firstOrderCurveGradedFinRowWeight_slots,
      sum_firstOrderColumns_shifted_slots]
    exact hsurplus

/-- The executable numerical row bound and nested source count suffice for the concrete
primitive constructor. This public adapter exposes no matrix or rank premise. -/
theorem exists_primitive_firstOrderCurve_interpolant_of_shifted_height_bound
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) (hD : 0 < D)
    (centers : Fin n → F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hsurplus : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) :
    ∃ v : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → F[X],
      v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F
        (h + 1 - ℓ * totalJetDegree
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant
            (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (SourceColumn.interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) := by
  apply exists_primitive_firstOrderCurve_interpolant_of_shifted_height
    D A m M μ n ℓ h hD centers w hw
  unfold FirstOrderCurveShiftedHeightSurplus
  exact (firstOrderCurveShiftedRowSlotCount_le_bound D A m M μ n ℓ h).trans_lt
    (hsurplus.trans_eq
      (firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount hD).symm)


end

end ReedSolomon.HiddenDerivative
