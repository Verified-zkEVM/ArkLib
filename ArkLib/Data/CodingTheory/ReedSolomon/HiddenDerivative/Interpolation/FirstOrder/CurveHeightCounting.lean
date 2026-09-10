/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveRank
public import ArkLib.ToMathlib.Finset.SumRangeFrom
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveColumnHeight


/-!
# Exact finite height sums for polynomial received curves

For a received curve of degree at most `ℓ`, a source monomial with `Y₀` exponent `a`
has challenge-column degree at most `ℓ * a`. Reindexing the full first-order support
by total jet degree `t` and first-derivative exponent `b` gives `a = t - b`.
The resulting executable sum counts every permitted scalar coefficient, including inactive
columns through natural-number truncated subtraction. The shifted construction below grades
both sides by total jet degree. A degree-`t` source column then has weight `ℓ*t`, while the
actual degree-`t` local image contributes `r_t` rows of that same weight.
-/

@[expose] public section

open PolynomialDifferential Polynomial


namespace ReedSolomon.HiddenDerivative

open SymbolicWeightedSupportInterpolation SymbolicReceivedInterpolation

noncomputable section

open scoped BigOperators

variable {D A m M μ ℓ h : ℕ}

/-! ### Shifted source and row profiles -/

/-- Under the support equivalence, the source total jet degree is the outer index `t`. -/
theorem firstOrderExponentDimensionIndex_totalJetDegree (hD : 0 < D)
    (u : ↑(firstOrderExponents D A m M μ)) :
    totalJetDegree u.1 = (firstOrderExponentDimensionIndexEquiv hD u).1.val := by
  let hd : 0 < 1 := by omega
  change totalJetDegree u.1 =
    (exactExponentCoordinatesEquiv hd u.1).2.1.1 +
      (exactExponentCoordinatesEquiv hd u.1).2.1.2
  simp only [totalJetDegree, Finsupp.degree_eq_sum,
    exactExponentCoordinatesEquiv_y₀, Finsupp.some_apply]
  rw [Fin.sum_univ_two]
  simp [exactExponentCoordinatesEquiv_y₁]

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
  let e := firstOrderExponentDimensionIndexEquiv
    (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    Finset.univ.sum (fun u : ↑(firstOrderExponents D A m M μ) ↦
        h + 1 - ℓ * totalJetDegree u.1) =
        Finset.univ.sum (fun q : FirstOrderDimensionIndex D A m M μ ↦
          h + 1 - ℓ * q.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderExponentDimensionIndex_totalJetDegree hD]
    _ = firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := by
      rw [Fintype.sum_sigma]
      calc
        (Finset.univ.sum fun t : Fin (μ + 1) ↦
            Finset.univ.sum fun q : (Σ b : Fin (min t.val M + 1),
              Fin (m * A + b.val - D * t.val)) ↦ h + 1 - ℓ * t.val) =
            Finset.univ.sum fun t : Fin (μ + 1) ↦
              Finset.univ.sum fun b : Fin (min t.val M + 1) ↦
                (m * A + b.val - D * t.val) * (h + 1 - ℓ * t.val) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro b _
          simp
        _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
              Finset.univ.sum fun b : Fin (min t M + 1) ↦
                (m * A + b.val - D * t) * (h + 1 - ℓ * t) := by
          exact Fin.sum_univ_eq_sum_range
            (fun t ↦ Finset.univ.sum fun b : Fin (min t M + 1) ↦
              (m * A + b.val - D * t) * (h + 1 - ℓ * t)) (μ + 1)
        _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
              Finset.sum (Finset.range (min t M + 1)) fun b ↦
                (m * A + b - D * t) * (h + 1 - ℓ * t) := by
          apply Finset.sum_congr rfl
          intro t _
          exact Fin.sum_univ_eq_sum_range
            (fun b ↦ (m * A + b - D * t) * (h + 1 - ℓ * t)) (min t M + 1)
        _ = firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h := rfl

/-- Truncated row slots supplied by the actual base-field graded images at `n` points. -/
def firstOrderCurveShiftedRowSlotCount (F : Type*) [Field F]
    (D A m M μ n ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    n * firstOrderGradedRank F D A m M t * (h + 1 - ℓ * t)

/-- Executable upper bound on shifted row slots obtained from the sharp numerical block
profile. -/
def firstOrderCurveShiftedRowSlotBound
    (D A m M μ n ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    n * firstOrderGradedRankBound D A m M t * (h + 1 - ℓ * t)

/-- Express the shifted row-slot bound as one finite interval sum. This form supports bounded
kernel evaluation of large concrete grade ranges. -/
theorem firstOrderCurveShiftedRowSlotBound_eq_sumRangeFrom
    (D A m M μ n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h =
      Finset.sumRangeFrom (fun t ↦ n * firstOrderGradedRankBound D A m M t *
        (h + 1 - ℓ * t)) 0 (μ + 1) := by
  simp [firstOrderCurveShiftedRowSlotBound, Finset.sumRangeFrom]

/-- Express the shifted source-slot count as one finite interval sum. -/
theorem firstOrderCurveShiftedHeightSlotCount_eq_sumRangeFrom
    (D A m M μ ℓ h : ℕ) :
    firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h =
      Finset.sumRangeFrom (fun t ↦ ∑ b ∈ Finset.range (min t M + 1),
        (m * A + b - D * t) * (h + 1 - ℓ * t)) 0 (μ + 1) := by
  simp [firstOrderCurveShiftedHeightSlotCount, Finset.sumRangeFrom]

/-- A pointwise numerical rank profile bounds the corresponding shifted row-slot sum. -/
theorem firstOrderCurveShiftedRowSlotBound_le_of_rankBound
    (D A m M μ n ℓ h : ℕ) (rankBound : ℕ → ℕ)
    (hrank : ∀ t, firstOrderGradedRankBound D A m M t ≤ rankBound t) :
    firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h ≤
      ∑ t ∈ Finset.range (μ + 1), n * rankBound t * (h + 1 - ℓ * t) := by
  apply Finset.sum_le_sum
  intro t ht
  exact Nat.mul_le_mul_right (h + 1 - ℓ * t) (Nat.mul_le_mul_left n (hrank t))

/-- The actual compressed-row slot count is bounded by the sharp paper profile. -/
theorem firstOrderCurveShiftedRowSlotCount_le_bound
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h ≤
      firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h := by
  apply Finset.sum_le_sum
  intro t ht
  exact Nat.mul_le_mul_right (h + 1 - ℓ * t)
    (Nat.mul_le_mul_left n (firstOrderOriginGradedRank_le_bound (F := F) D A m M t))

/-- The finite type of fixed compressed rows has exactly the truncated weighted slot count. -/
theorem sum_firstOrderCurveGradedRowIndex_slots
    {F : Type*} [Field F] (D A m M μ n ℓ h : ℕ) :
    (Finset.univ.sum fun row : FirstOrderCurveGradedRowIndex F D A m M μ n ↦
      h + 1 - ℓ * row.2.1.val) =
      firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rw [firstOrderCurveShiftedRowSlotCount, ← Fin.sum_univ_eq_sum_range]
  simp_rw [Nat.mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [firstOrderGradedRank, firstOrderOriginGradedRank]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp

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
    firstOrderGradedRank F D A m M t * t

/-- In the all-active range, the source slots equal a rectangle minus the weighted profile. -/
theorem firstOrderCurveShiftedColumnSlotCount_add_weight
    (hactive : ℓ * μ ≤ h) :
    firstOrderCurveShiftedColumnSlotCount D A m M μ ℓ h +
        ℓ * firstOrderTotalJetWeight D A m M μ =
      (firstOrderExponents D A m M μ).card * (h + 1) := by
  rw [firstOrderCurveShiftedColumnSlotCount, firstOrderTotalJetWeight,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    Finset.sum (firstOrderExponents D A m M μ)
        (fun u ↦ h + 1 - ℓ * totalJetDegree u + ℓ * totalJetDegree u) =
        Finset.sum (firstOrderExponents D A m M μ) (fun _ ↦ h + 1) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Nat.sub_add_cancel]
      have hut : totalJetDegree u ≤ μ :=
        (mem_firstOrderExponents.mp hu).2.1
      exact (Nat.mul_le_mul_left ℓ hut).trans (hactive.trans (Nat.le_add_right h 1))
    _ = (firstOrderExponents D A m M μ).card * (h + 1) := by simp

/-- In the all-active range, compressed row slots also equal a rectangle minus the weighted
actual-rank profile. -/
theorem firstOrderCurveShiftedRowSlotCount_add_weight
    {F : Type*} [Field F] {n : ℕ} (hactive : ℓ * μ ≤ h) :
    firstOrderCurveShiftedRowSlotCount F D A m M μ n ℓ h +
        n * ℓ * firstOrderGradedRowWeight F D A m M μ =
      n * (∑ t ∈ Finset.range (μ + 1), firstOrderGradedRank F D A m M t) *
        (h + 1) := by
  rw [firstOrderCurveShiftedRowSlotCount, firstOrderGradedRowWeight,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ t ∈ Finset.range (μ + 1),
        (n * firstOrderGradedRank F D A m M t * (h + 1 - ℓ * t) +
          n * ℓ * (firstOrderGradedRank F D A m M t * t))) =
        (∑ t ∈ Finset.range (μ + 1),
          n * firstOrderGradedRank F D A m M t * (h + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htμ : t ≤ μ := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ht)
      have hweight : ℓ * t ≤ h + 1 :=
        (Nat.mul_le_mul_left ℓ htμ).trans (hactive.trans (Nat.le_add_right h 1))
      rw [show n * ℓ * (firstOrderGradedRank F D A m M t * t) =
          n * firstOrderGradedRank F D A m M t * (ℓ * t) by ring]
      rw [← Nat.mul_add, Nat.sub_add_cancel hweight]
    _ = (∑ t ∈ Finset.range (μ + 1),
        n * firstOrderGradedRank F D A m M t) * (h + 1) := by
      rw [Finset.sum_mul]

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
          (SymbolicReceivedInterpolation.interpolant
            (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (SymbolicReceivedInterpolation.interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) := by
  apply SymbolicReceivedCurve.exists_primitive_interpolant_of_shifted_height
    m ℓ h centers w
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
    firstOrderColumns_injective
    (firstOrderCurveGradedFinMatrix D A m M μ n centers w)
    (firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ)
  · exact firstOrderCurveGradedFinMatrix_kernel_iff
      D A m M μ n hD centers w
  · intro i j hweight
    exact firstOrderCurveGradedFinMatrix_degree_le
      D A m M μ n ℓ centers w hw i j hweight
  · intro i j hweight
    exact firstOrderCurveGradedFinMatrix_eq_zero_of_weight_lt
      D A m M μ n ℓ centers w hw i j hweight
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
          (SymbolicReceivedInterpolation.interpolant
            (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (SymbolicReceivedInterpolation.interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) := by
  apply exists_primitive_firstOrderCurve_interpolant_of_shifted_height
    D A m M μ n ℓ h hD centers w hw
  unfold FirstOrderCurveShiftedHeightSurplus
  exact (firstOrderCurveShiftedRowSlotCount_le_bound D A m M μ n ℓ h).trans_lt
    (hsurplus.trans_eq
      (firstOrderCurveShiftedColumnSlotCount_eq_heightSlotCount hD).symm)


end

end ReedSolomon.HiddenDerivative
