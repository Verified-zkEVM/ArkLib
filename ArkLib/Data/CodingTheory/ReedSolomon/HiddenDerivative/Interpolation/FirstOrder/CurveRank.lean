/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Interpolation
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.GradedRank
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve

/-!
# First-order rank bounds for polynomial received curves

The first-order constraint-rank theorem holds over every field. At the origin, the local map
splits into homogeneous blocks indexed by total jet degree, counting the error variable `E` as
degree one. This file defines each profile entry as the dimension of the actual block image.
Thus the profile records upper bounds coming from the constraint map itself; it does not assert
that a preselected numerical budget equals a rank.

Applying the aggregate theorem over `F(Z)` still controls polynomial received curves. The
received polynomials may have any degree: batching degree affects coefficient heights, while
the base-field graded images determine how many projected rows are needed at each degree.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open MvPolynomial SymbolicReceivedInterpolation SymbolicReceivedCurve
open SymbolicWeightedSupportInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-! ### Translation stability of the finite first-order source -/

private def firstOrderFirstJetWeight : JetVariable 1 → ℕ
  | none => 0
  | some j => if j.val = 1 then 1 else 0

private theorem weight_firstOrderFirstJetWeight (u : JetVariable 1 →₀ ℕ) :
    Finsupp.weight firstOrderFirstJetWeight u = firstJetExponent u := by
  simp [firstOrderFirstJetWeight, firstJetExponent, Finsupp.weight_eq_sum,
    Fintype.sum_option]

/-- Translation in `X,Y₀` preserves all three defining bounds of the finite first-order
support: the `Y₁` cap, total jet-degree cap, and exact specialization-degree cutoff. -/
theorem globalPointTranslation_mem_firstOrderSpace
    {R : Type*} [CommRing R]
    (D A m M μ : ℕ) (center received : R) {Q : DifferentialPolynomial R 1}
    (hQ : Q ∈ firstOrderSpace R D A m M μ) :
    globalPointTranslation center received Q ∈ firstOrderSpace R D A m M μ := by
  rw [mem_firstOrderSpace_iff] at hQ ⊢
  intro e he
  have hfirst := globalPointTranslation_support_weight_le firstOrderFirstJetWeight
    (by simp [firstOrderFirstJetWeight]) (by simp [firstOrderFirstJetWeight])
    center received (a := M) (fun u hu => by
      rw [weight_firstOrderFirstJetWeight]
      exact (mem_firstOrderExponents.mp (hQ u hu)).1) he
  have htotal := totalJetDegree_le_of_mem_globalPointTranslation_support
    center received (t := μ) (fun u hu => (mem_firstOrderExponents.mp (hQ u hu)).2.1) he
  have hQne : Q ≠ 0 := by
    intro hzero
    simp [hzero] at he
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hQne
  have hbudget : 0 < m * A :=
    (Nat.zero_le (exactInterpolationMonomialWeight D u)).trans_lt
      (mem_firstOrderExponents.mp (hQ u hu)).2.2
  have hdegree := globalPointTranslation_support_weight_le (differentialWeight D)
    (by simp [differentialWeight]) (by simp [differentialWeight]) center received
    (a := m * A - 1) (fun u hu => by
      change exactInterpolationMonomialWeight D u ≤ m * A - 1
      have hu' := (mem_firstOrderExponents.mp (hQ u hu)).2.2
      omega) he
  rw [weight_firstOrderFirstJetWeight] at hfirst
  change exactInterpolationMonomialWeight D e ≤ m * A - 1 at hdegree
  rw [mem_firstOrderExponents]
  exact ⟨hfirst, htotal, by omega⟩

/-! ### The second origin grading by displacement degree -/

private def firstOrderSourceSliceWeight : JetVariable 1 → ℕ
  | none => 1
  | some j => if j.val = 0 then 1 else 0

def firstOrderLocalSliceWeight : LocalVariable 1 → ℕ
  | none => 1
  | some _ => 0

private theorem localCorrection_one_isSliceHomogeneous
    {R : Type*} [CommRing R] :
    (localCorrection (R := R) 1).IsWeightedHomogeneous firstOrderLocalSliceWeight 1 := by
  rw [localCorrection, Fin.sum_univ_one]
  simpa [firstOrderLocalSliceWeight, localT, localY] using
    ((isWeightedHomogeneous_C firstOrderLocalSliceWeight (1 : R)).mul
      ((isWeightedHomogeneous_X
        (R := R) firstOrderLocalSliceWeight (localT 1)).pow 1)).mul
      (isWeightedHomogeneous_X
        (R := R) firstOrderLocalSliceWeight (localY (0 : Fin 1)))

private theorem unscaledLocalSubstitution_zero_Y_zero_isSliceHomogeneous
    {R : Type*} [CommRing R] :
    (unscaledLocalSubstitution (R := R) 1 0 0 (MvPolynomial.X (some 0))).IsWeightedHomogeneous
      firstOrderLocalSliceWeight 1 := by
  rw [unscaledLocalSubstitution_Y_zero]
  have hT := isWeightedHomogeneous_X
    (R := R) firstOrderLocalSliceWeight (localT 1)
  have hE := isWeightedHomogeneous_X
    (R := R) firstOrderLocalSliceWeight (localE 1)
  simpa [firstOrderLocalSliceWeight] using
    (isWeightedHomogeneous_zero R firstOrderLocalSliceWeight 1).add
      (localCorrection_one_isSliceHomogeneous (R := R)) |>.add (hT.mul hE)

/-- At the origin, a first-order source monomial with ordinary exponent `x` and hidden-value
exponent `a` contributes only to local monomials of `T`-degree `x+a`. -/
theorem localConstraintAt_zero_sourceMonomial_isSliceHomogeneous
    {R : Type*} [CommRing R]
    (m x a : ℕ) (higher : Fin 1 → ℕ) :
    (localConstraintAt (R := R) (d := 1) m 0 0
      (sourceMonomial x a higher)).IsWeightedHomogeneous
        firstOrderLocalSliceWeight (x + a) := by
  have hT := isWeightedHomogeneous_X
    (R := R) firstOrderLocalSliceWeight (localT 1)
  have hY₀ := unscaledLocalSubstitution_zero_Y_zero_isSliceHomogeneous (R := R)
  have hhigher' : (∏ j, MvPolynomial.X (localY j) ^ higher j :
      LocalPolynomial R 1).IsWeightedHomogeneous firstOrderLocalSliceWeight
        (∑ _j : Fin 1, 0) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod
    intro j _
    simpa [firstOrderLocalSliceWeight, localY] using
      (isWeightedHomogeneous_X
        (R := R) firstOrderLocalSliceWeight (localY j)).pow (higher j)
  have hhigher : (∏ j, MvPolynomial.X (localY j) ^ higher j :
      LocalPolynomial R 1).IsWeightedHomogeneous firstOrderLocalSliceWeight 0 := by
    simpa using hhigher'
  have hunscaled :
      (unscaledLocalSubstitution (R := R) 1 0 0
        (sourceMonomial x a higher)).IsWeightedHomogeneous
          firstOrderLocalSliceWeight (x + a) := by
    simp only [sourceMonomial, map_mul, map_pow, map_prod,
      unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
      unscaledLocalSubstitution_Y_succ]
    simpa [firstOrderLocalSliceWeight, localT, add_assoc] using
      ((hT.pow x).mul (hY₀.pow a)).mul hhigher
  intro e he
  apply hunscaled
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, coeff_filterLocalMonomials] at he
  split at he
  · exact he
  · simp at he

/-- An origin coefficient vanishes unless its `T`-degree matches `x+a`. -/
theorem coeff_localConstraintAt_zero_sourceMonomial_eq_zero_of_T_degree_ne
    {R : Type*} [CommRing R]
    (m x a : ℕ) (higher : Fin 1 → ℕ) (e : LocalVariable 1 →₀ ℕ)
    (hdegree : e (localT 1) ≠ x + a) :
    MvPolynomial.coeff e (localConstraintAt (R := R) (d := 1) m 0 0
      (sourceMonomial x a higher)) = 0 := by
  apply (localConstraintAt_zero_sourceMonomial_isSliceHomogeneous
    (R := R) m x a higher).coeff_eq_zero
  simpa [Finsupp.weight_eq_sum, Fintype.sum_option, firstOrderLocalSliceWeight, localT]
    using hdegree

/-! ### Exact origin slice matrices -/

/-- Number of first-order source monomials of total jet degree `t` whose origin image has
`T`-degree `s`.  The source exponent `a` ranges from `t-M` through `min t s`; the whole slice
is inactive when its common specialization cost misses the strict cutoff. -/
def firstOrderGradedSourceCount (D A m M s t : ℕ) : ℕ :=
  if s + (D - 1) * t < m * A then min t s + 1 - (t - M) else 0

/-- The numerical block-rank profile from the paper: each `(s,t)` block is bounded by the
smaller of its source count and its `m-s` low-contact target coordinates. -/
def firstOrderGradedRankBound (D A m M t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m, min (m - s) (firstOrderGradedSourceCount D A m M s t)

/-- Canonical source column for the `q`-th monomial in the `(s,t)` origin slice. -/
def firstOrderGradedSourceColumn (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) : SourceColumn 1 :=
  let a := t - M + q.val
  { x := s - a
    y₀ := a
    higher := fun _ ↦ t - a }

@[simp] theorem firstOrderGradedSourceColumn_x (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).x = s - (t - M + q.val) := rfl

@[simp] theorem firstOrderGradedSourceColumn_y₀ (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).y₀ = t - M + q.val := rfl

@[simp] theorem firstOrderGradedSourceColumn_higher (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) (j : Fin 1) :
    (firstOrderGradedSourceColumn D A m M s t q).higher j = t - (t - M + q.val) := rfl

/-- The interval coordinate uniquely determines a canonical source column in a fixed slice. -/
theorem firstOrderGradedSourceColumn_injective (D A m M s t : ℕ) :
    Function.Injective (firstOrderGradedSourceColumn D A m M s t) := by
  intro q r hqr
  have hy := congrArg SourceColumn.y₀ hqr
  simp only [firstOrderGradedSourceColumn_y₀] at hy
  apply Fin.ext
  omega

/-- An inhabited source slice is active and its encoded `Y₀` exponent lies in the paper's
interval `t-M ≤ a ≤ min t s`. -/
theorem firstOrderGradedSourceColumn_bounds (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    s + (D - 1) * t < m * A ∧
      t - M ≤ (firstOrderGradedSourceColumn D A m M s t q).y₀ ∧
      (firstOrderGradedSourceColumn D A m M s t q).y₀ ≤ min t s := by
  have hq := q.isLt
  simp only [firstOrderGradedSourceCount] at hq
  split at hq
  next hactive =>
    change s + (D - 1) * t < m * A ∧ t - M ≤ t - M + q.val ∧
      t - M + q.val ≤ min t s
    omega
  next hinactive => simp at hq

/-- Every canonical slice column has total jet degree `t`. -/
theorem firstOrderGradedSourceColumn_totalJetDegree (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    totalJetDegree (firstOrderGradedSourceColumn D A m M s t q).exponent = t := by
  have hbounds := firstOrderGradedSourceColumn_bounds D A m M s t q
  simp only [firstOrderGradedSourceColumn_y₀] at hbounds
  rw [SourceColumn.totalJetDegree_exponent]
  simp only [firstOrderGradedSourceColumn_y₀, firstOrderGradedSourceColumn_higher]
  rw [Fin.sum_univ_one]
  omega

/-- Every canonical column in the `(s,t)` slice has origin `T`-degree `s`. -/
theorem firstOrderGradedSourceColumn_x_add_y₀ (D A m M s t : ℕ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).x +
      (firstOrderGradedSourceColumn D A m M s t q).y₀ = s := by
  have hbounds := firstOrderGradedSourceColumn_bounds D A m M s t q
  simp only [firstOrderGradedSourceColumn_y₀] at hbounds
  simp only [firstOrderGradedSourceColumn_x, firstOrderGradedSourceColumn_y₀]
  omega

/-- For positive `D`, every canonical slice column belongs to the uncapped first-order support;
the separate hypothesis `t ≤ μ` inserts it into the chosen finite support. -/
theorem firstOrderGradedSourceColumn_mem {D A m M s t μ : ℕ}
    (hD : 0 < D) (ht : t ≤ μ)
    (q : Fin (firstOrderGradedSourceCount D A m M s t)) :
    (firstOrderGradedSourceColumn D A m M s t q).exponent ∈
      firstOrderExponents D A m M μ := by
  have hbounds := firstOrderGradedSourceColumn_bounds D A m M s t q
  simp only [firstOrderGradedSourceColumn_y₀] at hbounds
  rw [mem_firstOrderExponents_iff_coordinates]
  simp only [exactExponentCoordinatesEquiv_y₀, exactExponentCoordinatesEquiv_y₁,
    exactExponentCoordinatesEquiv_x, SourceColumn.exponent_none]
  have hindex0 : (⟨0, by omega⟩ : Fin 2) = 0 := by ext; rfl
  have hindex1 : (⟨1, by omega⟩ : Fin 2) = (0 : Fin 1).succ := by ext; rfl
  rw [hindex0, hindex1, SourceColumn.exponent_zero, SourceColumn.exponent_succ]
  simp only [firstOrderGradedSourceColumn_y₀, firstOrderGradedSourceColumn_higher,
    firstOrderGradedSourceColumn_x]
  change t - (t - M + q.val) ≤ M ∧
    (t - M + q.val) + (t - (t - M + q.val)) ≤ μ ∧
    (s - (t - M + q.val)) + D * (t - M + q.val) +
      (D - 1) * (t - (t - M + q.val)) < m * A
  let a := t - M + q.val
  have ha_t : a ≤ t := hbounds.2.2.trans (min_le_left _ _)
  have ha_s : a ≤ s := hbounds.2.2.trans (min_le_right _ _)
  have ht_split : a + (t - a) = t := Nat.add_sub_of_le ha_t
  have hs_split : s - a + a = s := Nat.sub_add_cancel ha_s
  have hDform : D - 1 + 1 = D := Nat.sub_add_cancel (by omega : 1 ≤ D)
  have hDa : D * a = (D - 1) * a + a := by
    calc
      D * a = (D - 1 + 1) * a := by rw [hDform]
      _ = _ := by rw [Nat.add_mul, one_mul]
  refine ⟨by omega, by omega, ?_⟩
  calc
    (s - a) + D * a + (D - 1) * (t - a) =
        (s - a + a) + (D - 1) * (a + (t - a)) := by
      rw [hDa]
      ring
    _ = s + (D - 1) * t := by rw [hs_split, ht_split]
    _ < m * A := hbounds.1

/-- The first-jet statistic of a first-order source column is its sole higher coordinate. -/
@[simp] theorem SourceColumn.firstJetExponent_exponent (c : SourceColumn 1) :
    firstJetExponent c.exponent = c.higher 0 := by
  rw [firstJetExponent, Finsupp.weight_eq_sum, Fin.sum_univ_two]
  simp only [Fin.isValue, nsmul_eq_mul]
  simp [SourceColumn.exponent]

/-- The exact specialization weight in first-order source-column coordinates. -/
@[simp] theorem SourceColumn.exactInterpolationMonomialWeight_exponent
    (D : ℕ) (c : SourceColumn 1) :
    exactInterpolationMonomialWeight D c.exponent =
      c.x + D * c.y₀ + (D - 1) * c.higher 0 := by
  rw [exactInterpolationMonomialWeight_eq_coordinates (by omega : 0 < 1)]
  simp only [exactExponentCoordinatesEquiv_x, exactExponentCoordinatesEquiv_y₀,
    exactExponentCoordinatesEquiv_y₁, SourceColumn.exponent_none]
  simp [SourceColumn.exponent, higherJetTupleSpecializationCost]

/-- Every eligible source column is represented in its unique origin `(s,t)` slice. -/
noncomputable def firstOrderGradedSourceColumnIndex
    {D A m M μ : ℕ} (hD : 0 < D) (c : SourceColumn 1)
    (hc : c.exponent ∈ firstOrderExponents D A m M μ) :
    Fin (firstOrderGradedSourceCount D A m M (c.x + c.y₀)
      (totalJetDegree c.exponent)) := by
  let a := c.y₀
  let b := c.higher 0
  let t := totalJetDegree c.exponent
  let s := c.x + c.y₀
  have hc' := (mem_firstOrderExponents.mp hc)
  have ht : t = a + b := by
    simp [t, a, b, SourceColumn.totalJetDegree_exponent]
  have hbM : b ≤ M := by simpa [b] using hc'.1
  have hdegree : c.x + D * a + (D - 1) * b < m * A := by
    simpa [a, b] using hc'.2.2
  have hDa : D * a = (D - 1) * a + a := by
    calc
      D * a = (D - 1 + 1) * a := by rw [Nat.sub_add_cancel (by omega : 1 ≤ D)]
      _ = _ := by rw [Nat.add_mul, one_mul]
  have hactive : s + (D - 1) * t < m * A := by
    have hcost : s + (D - 1) * t =
        c.x + D * a + (D - 1) * b := by
      dsimp [s]
      rw [ht, Nat.mul_add, hDa]
      omega
    rw [hcost]
    exact hdegree
  change Fin (firstOrderGradedSourceCount D A m M s t)
  refine ⟨a - (t - M), ?_⟩
  rw [firstOrderGradedSourceCount, if_pos hactive]
  have haM : t - M ≤ a := by rw [ht]; omega
  have hat : a ≤ t := by rw [ht]; omega
  have has : a ≤ s := by dsimp [s]; omega
  omega

/-- The canonical slice column reconstructed from an eligible column is the original column. -/
theorem firstOrderGradedSourceColumn_index_eq
    {D A m M μ : ℕ} (hD : 0 < D) (c : SourceColumn 1)
    (hc : c.exponent ∈ firstOrderExponents D A m M μ) :
    firstOrderGradedSourceColumn D A m M (c.x + c.y₀)
      (totalJetDegree c.exponent)
      (firstOrderGradedSourceColumnIndex hD c hc) = c := by
  let a := c.y₀
  let b := c.higher 0
  let t := totalJetDegree c.exponent
  have hc' := (mem_firstOrderExponents.mp hc)
  have ht : t = a + b := by
    simp [t, a, b, SourceColumn.totalJetDegree_exponent]
  have hbM : b ≤ M := by simpa [b] using hc'.1
  have haM : t - M ≤ a := by rw [ht]; omega
  apply SourceColumn.exponent_injective
  ext v
  rcases v with _ | j
  · simp only [SourceColumn.exponent_none, firstOrderGradedSourceColumn_x,
      firstOrderGradedSourceColumnIndex]
    dsimp [a, t]
    omega
  · induction j using Fin.cases with
    | zero =>
        simp only [SourceColumn.exponent_zero, firstOrderGradedSourceColumn_y₀,
          firstOrderGradedSourceColumnIndex]
        dsimp [a, t]
        omega
    | succ j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simp only [SourceColumn.exponent_succ, firstOrderGradedSourceColumn_higher,
          firstOrderGradedSourceColumnIndex]
        dsimp [a, b, t]
        omega

/-- The canonical basis of the finite first-order space evaluates to the corresponding
monomial over any coefficient semiring. -/
theorem firstOrderSpaceBasis_apply_commSemiring
    {R : Type*} [CommSemiring R] (D A m M μ : ℕ)
    (u : ↑(firstOrderExponents D A m M μ)) :
    (firstOrderSpaceBasis R D A m M μ u).1 = MvPolynomial.monomial u.1 1 := by
  let b := firstOrderSpaceBasis R D A m M μ
  let q : firstOrderSpace R D A m M μ := ⟨MvPolynomial.monomial u.1 1, by
    rw [mem_firstOrderSpace_iff]
    intro v hv
    have heq : v = u.1 := by simpa using MvPolynomial.support_monomial_subset hv
    exact heq ▸ u.2⟩
  have hbq : b u = q := by
    apply b.repr.injective
    rw [b.repr_self]
    ext j
    change (Finsupp.single u 1) j =
      MvPolynomial.coeff j.1 (MvPolynomial.monomial u.1 1)
    by_cases h : u = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  exact congrArg Subtype.val hbq

/-- Field-specialized spelling of `firstOrderSpaceBasis_apply_commSemiring`. -/
theorem firstOrderSpaceBasis_apply (D A m M μ : ℕ)
    (u : ↑(firstOrderExponents D A m M μ)) :
    (firstOrderSpaceBasis F D A m M μ u).1 = MvPolynomial.monomial u.1 1 :=
  firstOrderSpaceBasis_apply_commSemiring D A m M μ u

/-- The target exponent `T^s E^e Y₁^(t-e)` used by the literal `(s,t)` block matrix. -/
def firstOrderGradedTargetExponent (s t e : ℕ) : LocalVariable 1 →₀ ℕ :=
  Finsupp.single (localT 1) s + Finsupp.single (localE 1) e +
    Finsupp.single (localY (0 : Fin 1)) (t - e)

/-- In one derivative variable, local jet degree is the sum of the `E` and `Y₁`
exponents. -/
theorem localJetDegree_one (e : LocalVariable 1 →₀ ℕ) :
    localJetDegree e = e (localE 1) + e (localY (0 : Fin 1)) := by
  simp [localJetDegree, localJetDegreeWeight, Finsupp.weight_eq_sum,
    Fintype.sum_option, localE, localAux, localY]

/-- In one derivative variable, contact order is the sum of the `T` and `E`
exponents. -/
theorem localContactOrder_one (e : LocalVariable 1 →₀ ℕ) :
    localContactOrder 1 e = e (localT 1) + e (localE 1) := by
  simp [localContactOrder, localContactWeight, Finsupp.weight_eq_sum,
    Fintype.sum_option, localT, localE, localAux]

/-- The canonical `(T`-degree, jet-grade, `E`-degree) coordinates exhaust every local
monomial in the first-order target. -/
theorem firstOrderGradedTargetExponent_of_local (e : LocalVariable 1 →₀ ℕ) :
    firstOrderGradedTargetExponent (e (localT 1)) (localJetDegree e)
      (e (localE 1)) = e := by
  ext v
  rcases v with _ | (_ | j)
  · simp [firstOrderGradedTargetExponent, localT, localE, localAux, localY]
  · simp [firstOrderGradedTargetExponent, localJetDegree_one,
      localT, localE, localAux, localY]
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp [firstOrderGradedTargetExponent, localJetDegree_one,
      localT, localE, localAux, localY]

@[simp] theorem firstOrderGradedTargetExponent_localT (s t e : ℕ) :
    firstOrderGradedTargetExponent s t e (localT 1) = s := by
  simp [firstOrderGradedTargetExponent, localT, localE, localAux, localY]

/-- A bounded target coordinate has local jet grade exactly `t`. -/
@[simp] theorem localJetDegree_firstOrderGradedTargetExponent
    {s t e : ℕ} (he : e ≤ t) :
    localJetDegree (firstOrderGradedTargetExponent s t e) = t := by
  simp [localJetDegree, localJetDegreeWeight, firstOrderGradedTargetExponent,
    Finsupp.weight_eq_sum, Fintype.sum_option, localT, localE, localAux, localY]
  omega

/-- Contact order of a literal first-order target coordinate. -/
@[simp] theorem localContactOrder_firstOrderGradedTargetExponent (s t e : ℕ) :
    localContactOrder 1 (firstOrderGradedTargetExponent s t e) = s + e := by
  simp [localContactOrder, localContactWeight, firstOrderGradedTargetExponent,
    Finsupp.weight_eq_sum, Fintype.sum_option, localT, localE, localAux, localY]

/-- The literal target coordinate as a certified low-contact row. -/
def firstOrderGradedTargetLowContactIndex {m : ℕ} (s : Fin m) (t : ℕ)
    (e : Fin (min (m - s.val) (t + 1))) : LowContactIndex 1 m :=
  ⟨firstOrderGradedTargetExponent s t e, by
    rw [localContactOrder_firstOrderGradedTargetExponent]
    have he : e.val < m - s.val := e.isLt.trans_le (min_le_left _ _)
    omega⟩

@[simp] theorem localJetDegree_firstOrderGradedTargetLowContactIndex
    {m : ℕ} (s : Fin m) (t : ℕ) (e : Fin (min (m - s.val) (t + 1))) :
    localJetDegree (firstOrderGradedTargetLowContactIndex s t e).1 = t := by
  apply localJetDegree_firstOrderGradedTargetExponent
  have := e.isLt.trans_le (min_le_right (m - s.val) (t + 1))
  omega

/-- Origin constraint matrix on one fixed displacement/jet-grade block over an arbitrary
coefficient ring. Its rows are literal local coefficients and its columns are the exact
admissible source slice. -/
def firstOrderOriginGradedSliceMatrixOver (R : Type*) [CommRing R]
    (D A m M s t : ℕ) :
    Matrix (Fin (min (m - s) (t + 1))) (Fin (firstOrderGradedSourceCount D A m M s t)) R :=
  fun e q ↦ MvPolynomial.coeff (firstOrderGradedTargetExponent s t e)
    (localConstraintAt m 0 0 (firstOrderGradedSourceColumn D A m M s t q).polynomial)

/-- Actual base-field origin constraint matrix on one fixed displacement/jet-grade block. -/
abbrev firstOrderOriginGradedSliceMatrix (D A m M s t : ℕ) :=
  firstOrderOriginGradedSliceMatrixOver F D A m M s t

/-- A literal origin slice acts on the matching coefficients of any polynomial in the finite
first-order source space. This is the canonical elimination bridge from the whole homogeneous
map to the concrete `(s,t)` block. -/
theorem firstOrderOriginGradedSliceMatrix_mulVec_coeff
    {R : Type*} [CommRing R] (D A m M μ s t : ℕ) (hD : 0 < D)
    (e : Fin (min (m - s) (t + 1))) (Q : firstOrderSpace R D A m M μ) :
    (firstOrderOriginGradedSliceMatrixOver R D A m M s t *ᵥ
        (fun q ↦ MvPolynomial.coeff
          (firstOrderGradedSourceColumn D A m M s t q).exponent Q.1)) e =
      MvPolynomial.coeff (firstOrderGradedTargetExponent s t e)
        (localConstraintAt m 0 0 Q.1) := by
  classical
  let V := firstOrderSpace R D A m M μ
  let target := firstOrderGradedTargetExponent s t e
  let lhs : V →ₗ[R] R := {
    toFun := fun P ↦ ∑ q, firstOrderOriginGradedSliceMatrixOver R D A m M s t e q *
      MvPolynomial.coeff (firstOrderGradedSourceColumn D A m M s t q).exponent P.1
    map_add' := by
      intro P R
      simp only [Submodule.coe_add, MvPolynomial.coeff_add, mul_add,
        Finset.sum_add_distrib]
    map_smul' := by
      intro a P
      simp only [Submodule.coe_smul_of_tower, MvPolynomial.coeff_smul,
        RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring }
  let rhs : V →ₗ[R] R :=
    (MvPolynomial.lcoeff R target).comp ((localConstraintAt m 0 0).domRestrict V)
  have hmaps : lhs = rhs := by
    let b := firstOrderSpaceBasis R D A m M μ
    apply b.ext
    intro u
    let c := SourceColumn.ofExponent u.1
    have hc : c.exponent ∈ firstOrderExponents D A m M μ := by
      rw [show c.exponent = u.1 by simp [c]]
      exact u.2
    have hb : (b u).1 = c.polynomial := by
      rw [firstOrderSpaceBasis_apply_commSemiring]
      simp [c, SourceColumn.polynomial]
    by_cases hslice : c.x + c.y₀ = s ∧ totalJetDegree c.exponent = t
    · rcases hslice with ⟨hslice, hgrade⟩
      subst s
      subst t
      let q := firstOrderGradedSourceColumnIndex hD c hc
      have hq : firstOrderGradedSourceColumn D A m M
          (c.x + c.y₀) (totalJetDegree c.exponent) q = c := by
        simpa [q] using firstOrderGradedSourceColumn_index_eq hD c hc
      change lhs (b u) = rhs (b u)
      rw [show lhs (b u) = ∑ q', MvPolynomial.coeff
            (firstOrderGradedSourceColumn D A m M
              (c.x + c.y₀) (totalJetDegree c.exponent) q').exponent (b u).1 *
            firstOrderOriginGradedSliceMatrixOver R D A m M
              (c.x + c.y₀) (totalJetDegree c.exponent) e q' by
          simp [lhs, mul_comm],
        show rhs (b u) = MvPolynomial.coeff target
            (localConstraintAt m 0 0 (b u).1) by rfl]
      rw [Finset.sum_eq_single q]
      · rw [hb]
        have hexponent := congrArg SourceColumn.exponent hq
        have hpolynomial :
            (firstOrderGradedSourceColumn D A m M
              (c.x + c.y₀) (totalJetDegree c.exponent) q).polynomial =
                (c.polynomial : DifferentialPolynomial R 1) :=
          congrArg (fun z ↦ (z.polynomial : DifferentialPolynomial R 1)) hq
        simp only [firstOrderOriginGradedSliceMatrixOver]
        rw [hpolynomial]
        simp [target, SourceColumn.polynomial, hexponent]
      · intro q' _ hq'
        have hne : (firstOrderGradedSourceColumn D A m M
            (c.x + c.y₀) (totalJetDegree c.exponent) q').exponent ≠ u.1 := by
          intro heq
          have hcol : firstOrderGradedSourceColumn D A m M
              (c.x + c.y₀) (totalJetDegree c.exponent) q' = c := by
            apply SourceColumn.exponent_injective
            simpa [c] using heq
          exact hq' ((firstOrderGradedSourceColumn_injective D A m M
            (c.x + c.y₀) (totalJetDegree c.exponent)) (hcol.trans hq.symm))
        have hcoeff : MvPolynomial.coeff
            (firstOrderGradedSourceColumn D A m M
              (c.x + c.y₀) (totalJetDegree c.exponent) q').exponent (b u).1 = 0 := by
          have hne' : (firstOrderGradedSourceColumn D A m M
              (c.x + c.y₀) (totalJetDegree c.exponent) q').exponent ≠ c.exponent := by
            simpa [c] using hne
          rw [hb]
          simp only [SourceColumn.polynomial, MvPolynomial.coeff_monomial]
          rw [if_neg (Ne.symm hne')]
        rw [hcoeff]
        simp
      · intro hqmem
        exact (hqmem (Finset.mem_univ q)).elim
    · change lhs (b u) = rhs (b u)
      rw [show lhs (b u) = ∑ q, MvPolynomial.coeff
            (firstOrderGradedSourceColumn D A m M s t q).exponent (b u).1 *
            firstOrderOriginGradedSliceMatrixOver R D A m M s t e q by
          simp [lhs, mul_comm],
        show rhs (b u) = MvPolynomial.coeff target
            (localConstraintAt m 0 0 (b u).1) by rfl]
      have hlhs : (∑ q,
          MvPolynomial.coeff
              (firstOrderGradedSourceColumn D A m M s t q).exponent (b u).1 *
            firstOrderOriginGradedSliceMatrixOver R D A m M s t e q) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        have hne : (firstOrderGradedSourceColumn D A m M s t q).exponent ≠ u.1 := by
          intro heq
          have hcol : firstOrderGradedSourceColumn D A m M s t q = c := by
            apply SourceColumn.exponent_injective
            simpa [c] using heq
          apply hslice
          rw [← hcol]
          exact ⟨firstOrderGradedSourceColumn_x_add_y₀ D A m M s t q,
            firstOrderGradedSourceColumn_totalJetDegree D A m M s t q⟩
        have hcoeff : MvPolynomial.coeff
            (firstOrderGradedSourceColumn D A m M s t q).exponent (b u).1 = 0 := by
          have hne' : (firstOrderGradedSourceColumn D A m M s t q).exponent ≠
              c.exponent := by
            simpa [c] using hne
          rw [hb]
          simp only [SourceColumn.polynomial, MvPolynomial.coeff_monomial]
          rw [if_neg (Ne.symm hne')]
        rw [hcoeff]
        simp
      rw [hlhs]
      by_cases hgrade : localJetDegree target ≠ totalJetDegree c.exponent
      · have hgrade' : localJetDegree target ≠ c.y₀ + ∑ j, c.higher j := by
          simpa [SourceColumn.totalJetDegree_exponent] using hgrade
        have hz := coeff_localConstraintAt_zero_sourceMonomial_eq_zero
          (R := R) (m := m) c.x c.y₀ c.higher target
        rw [hb, SourceColumn.polynomial_eq_sourceMonomial]
        exact (hz hgrade').symm
      · have hT : target (localT 1) ≠ c.x + c.y₀ := by
          intro hEq
          apply hslice
          constructor
          · simpa only [target, firstOrderGradedTargetExponent_localT] using hEq.symm
          · have htgt : localJetDegree target = t := by
              dsimp only [target]
              apply localJetDegree_firstOrderGradedTargetExponent
              have he := e.isLt.trans_le (min_le_right (m - s) (t + 1))
              omega
            exact (not_ne_iff.mp hgrade).symm.trans htgt
        have hz := coeff_localConstraintAt_zero_sourceMonomial_eq_zero_of_T_degree_ne
          (R := R) m c.x c.y₀ c.higher target hT
        rw [hb, SourceColumn.polynomial_eq_sourceMonomial]
        exact hz.symm
  have h := LinearMap.congr_fun hmaps Q
  change lhs Q = rhs Q
  exact h

/-- Sum of the actual origin `(s,t)` slice ranks at fixed jet grade `t`. -/
noncomputable def firstOrderOriginGradedRank (F : Type*) [Field F]
    (D A m M t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m, (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank

/-- Each actual origin slice rank is bounded by both the literal target-row count and the exact
source-column count. -/
theorem firstOrderOriginGradedSliceMatrix_rank_le (D A m M s t : ℕ) :
    (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank ≤
      min (m - s) (firstOrderGradedSourceCount D A m M s t) := by
  apply le_min
  · exact (Matrix.rank_le_card_height
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t)).trans
        (by simp)
  · simpa using
      (Matrix.rank_le_card_width (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t))

/-- Fixed literal output rows, chosen over the base field, that form a basis of one actual
origin block's row space. -/
noncomputable def firstOrderOriginGradedSelectedRow (F : Type*) [Field F]
    (D A m M s t : ℕ) :
    Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank →
      Fin (min (m - s) (t + 1)) :=
  Classical.choose
    (Matrix.exists_rows_fin_rank (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t))

/-- The selected literal rows span every row of the actual origin block. -/
theorem firstOrderOriginGradedSelectedRow_span (D A m M s t : ℕ) :
    Submodule.span F (Set.range fun i ↦
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).row
        (firstOrderOriginGradedSelectedRow F D A m M s t i)) =
      Submodule.span F (Set.range
        (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).row) :=
  (Classical.choose_spec
    (Matrix.exists_rows_fin_rank
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t))).2

/-- One origin block compressed to exactly its actual rank many fixed coefficient rows. -/
noncomputable def firstOrderOriginGradedCompressedMatrix (F : Type*) [Field F]
    (D A m M s t : ℕ) :
    Matrix (Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank)
      (Fin (firstOrderGradedSourceCount D A m M s t)) F :=
  (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).submatrix
    (firstOrderOriginGradedSelectedRow F D A m M s t) id

/-- Compression keeps the full row space, hence keeps the kernel of the actual origin block. -/
theorem firstOrderOriginGradedCompressedMatrix_mulVec_eq_zero_iff
    (D A m M s t : ℕ)
    (v : Fin (firstOrderGradedSourceCount D A m M s t) → F) :
    (firstOrderOriginGradedCompressedMatrix F D A m M s t) *ᵥ v = 0 ↔
      (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t) *ᵥ v = 0 := by
  classical
  let A₀ := firstOrderOriginGradedSliceMatrix (F := F) D A m M s t
  let rows := firstOrderOriginGradedSelectedRow F D A m M s t
  constructor
  · intro hselected
    funext i
    change dotProduct (A₀.row i) v = 0
    have hi : A₀.row i ∈ Submodule.span F (Set.range fun j ↦ A₀.row (rows j)) := by
      rw [firstOrderOriginGradedSelectedRow_span (F := F) D A m M s t]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hzero_of_mem {x : Fin (firstOrderGradedSourceCount D A m M s t) → F}
        (hx : x ∈ Submodule.span F (Set.range fun j ↦ A₀.row (rows j))) :
        dotProduct x v = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          have hj := congrFun hselected j
          simpa [firstOrderOriginGradedCompressedMatrix, A₀, rows, Matrix.mulVec,
            dotProduct] using hj
      | zero => simp
      | add x y _ _ hx hy => simp [add_dotProduct, hx, hy]
      | smul a x _ hx => simp [smul_dotProduct, hx]
    exact hzero_of_mem hi
  · intro hall
    funext i
    have hi := congrFun hall (rows i)
    simpa [firstOrderOriginGradedCompressedMatrix, A₀, rows, Matrix.mulVec,
      dotProduct] using hi

/-- The base-field selected row indices applied after extension to another coefficient ring. -/
noncomputable def firstOrderOriginGradedBaseSelectedMatrix
    (F : Type*) [Field F] (R : Type*) [CommRing R]
    (D A m M s t : ℕ) :
    Matrix (Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).rank)
      (Fin (firstOrderGradedSourceCount D A m M s t)) R :=
  (firstOrderOriginGradedSliceMatrixOver R D A m M s t).submatrix
    (firstOrderOriginGradedSelectedRow F D A m M s t) id

/-- Formation of an origin slice commutes with extension of its base-field coefficients. -/
theorem firstOrderOriginGradedSliceMatrix_map
    (R : Type*) [CommRing R] [Algebra F R] (D A m M s t : ℕ) :
    (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t).map
        (algebraMap F R) =
      firstOrderOriginGradedSliceMatrixOver R D A m M s t := by
  ext e q
  change algebraMap F R (MvPolynomial.coeff (firstOrderGradedTargetExponent s t e)
      (localConstraintAt m 0 0
        (firstOrderGradedSourceColumn D A m M s t q).polynomial)) = _
  rw [← MvPolynomial.coeff_map, map_localConstraintAt]
  simp only [firstOrderOriginGradedSliceMatrixOver, map_zero]
  apply congrArg (MvPolynomial.coeff (firstOrderGradedTargetExponent s t e))
  apply congrArg (localConstraintAt (R := R) (d := 1) m 0 0)
  change MvPolynomial.map (algebraMap F R)
      (MvPolynomial.monomial
        (firstOrderGradedSourceColumn D A m M s t q).exponent (1 : F)) =
    MvPolynomial.monomial
      (firstOrderGradedSourceColumn D A m M s t q).exponent (1 : R)
  simp

/-- Base-field row compression keeps the full origin-block kernel after scalar extension. -/
theorem firstOrderOriginGradedBaseSelectedMatrix_mulVec_eq_zero_iff
    (R : Type*) [CommRing R] [Algebra F R] (D A m M s t : ℕ)
    (v : Fin (firstOrderGradedSourceCount D A m M s t) → R) :
    firstOrderOriginGradedBaseSelectedMatrix F R D A m M s t *ᵥ v = 0 ↔
      firstOrderOriginGradedSliceMatrixOver R D A m M s t *ᵥ v = 0 := by
  classical
  let A₀ := firstOrderOriginGradedSliceMatrix (F := F) D A m M s t
  let Aext := firstOrderOriginGradedSliceMatrixOver R D A m M s t
  let rows := firstOrderOriginGradedSelectedRow F D A m M s t
  have hmap : A₀.map (algebraMap F R) = Aext :=
    firstOrderOriginGradedSliceMatrix_map R D A m M s t
  constructor
  · intro hselected
    funext i
    change dotProduct (Aext.row i) v = 0
    have hi : A₀.row i ∈ Submodule.span F (Set.range fun j ↦ A₀.row (rows j)) := by
      rw [firstOrderOriginGradedSelectedRow_span (F := F) D A m M s t]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hzero_of_mem {x : Fin (firstOrderGradedSourceCount D A m M s t) → F}
        (hx : x ∈ Submodule.span F (Set.range fun j ↦ A₀.row (rows j))) :
        dotProduct (fun q ↦ algebraMap F R (x q)) v = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          have hj := congrFun hselected j
          change dotProduct (Aext.row (rows j)) v = 0 at hj
          rw [← hmap] at hj
          change dotProduct ((A₀.map (algebraMap F R)).row (rows j)) v = 0
          exact hj
      | zero => simp
      | add x y _ _ hx hy =>
          rw [show (fun q ↦ algebraMap F R ((x + y) q)) =
              (fun q ↦ algebraMap F R (x q)) + (fun q ↦ algebraMap F R (y q)) by
            funext q
            simp]
          rw [add_dotProduct, hx, hy, add_zero]
      | smul a x _ hx =>
          rw [show (fun q ↦ algebraMap F R ((a • x) q)) =
              algebraMap F R a • (fun q ↦ algebraMap F R (x q)) by
            funext q
            simp]
          rw [smul_dotProduct, hx, smul_zero]
    rw [← hmap]
    change dotProduct (fun q ↦ algebraMap F R ((A₀.row i) q)) v = 0
    exact hzero_of_mem hi
  · intro hall
    funext i
    have hi := congrFun hall (rows i)
    simpa [firstOrderOriginGradedBaseSelectedMatrix, Aext, rows, Matrix.mulVec,
      dotProduct] using hi

/-- A scalar-extended compressed block evaluates to its selected literal origin
coefficients. -/
theorem firstOrderOriginGradedBaseSelectedMatrix_mulVec_coeff
    (R : Type*) [CommRing R] (D A m M μ s t : ℕ) (hD : 0 < D)
    (Q : firstOrderSpace R D A m M μ) :
    firstOrderOriginGradedBaseSelectedMatrix F R D A m M s t *ᵥ
        (fun q ↦ MvPolynomial.coeff
          (firstOrderGradedSourceColumn D A m M s t q).exponent Q.1) =
      fun i ↦ MvPolynomial.coeff
        (firstOrderGradedTargetExponent s t
          (firstOrderOriginGradedSelectedRow F D A m M s t i))
        (localConstraintAt m 0 0 Q.1) := by
  funext i
  change (firstOrderOriginGradedSliceMatrixOver R D A m M s t *ᵥ
      (fun q ↦ MvPolynomial.coeff
        (firstOrderGradedSourceColumn D A m M s t q).exponent Q.1))
      (firstOrderOriginGradedSelectedRow F D A m M s t i) = _
  exact firstOrderOriginGradedSliceMatrix_mulVec_coeff D A m M μ s t hD _ Q

/-- The compressed block evaluates to its selected literal origin coefficients. -/
theorem firstOrderOriginGradedCompressedMatrix_mulVec_coeff
    (D A m M μ s t : ℕ) (hD : 0 < D)
    (Q : firstOrderSpace F D A m M μ) :
    firstOrderOriginGradedCompressedMatrix F D A m M s t *ᵥ
        (fun q ↦ MvPolynomial.coeff
          (firstOrderGradedSourceColumn D A m M s t q).exponent Q.1) =
      fun i ↦ MvPolynomial.coeff
        (firstOrderGradedTargetExponent s t
          (firstOrderOriginGradedSelectedRow F D A m M s t i))
        (localConstraintAt m 0 0 Q.1) := by
  funext i
  change (firstOrderOriginGradedSliceMatrix (F := F) D A m M s t *ᵥ
      (fun q ↦ MvPolynomial.coeff
        (firstOrderGradedSourceColumn D A m M s t q).exponent Q.1))
      (firstOrderOriginGradedSelectedRow F D A m M s t i) = _
  exact firstOrderOriginGradedSliceMatrix_mulVec_coeff D A m M μ s t hD _ Q

/-- The selected origin rows across the bounded jet grades detect the complete local
constraint on the finite first-order source space. Grades above `μ` vanish because translation
and the origin constraint preserve total jet degree. -/
theorem firstOrderOriginGradedSelectedCoefficients_eq_zero_iff
    {R : Type*} [CommRing R] [Algebra F R]
    (D A m M μ : ℕ) (hD : 0 < D) (Q : firstOrderSpace R D A m M μ) :
    (∀ (t : Fin (μ + 1)) (s : Fin m)
        (i : Fin (firstOrderOriginGradedSliceMatrix (F := F)
          D A m M s.val t.val).rank),
      MvPolynomial.coeff
        (firstOrderGradedTargetExponent s.val t.val
          (firstOrderOriginGradedSelectedRow F D A m M s.val t.val i))
        (localConstraintAt m 0 0 Q.1) = 0) ↔
      localConstraintAt m 0 0 Q.1 = 0 := by
  classical
  constructor
  · intro hselected
    apply MvPolynomial.ext
    intro e
    by_cases hcontact : localContactOrder 1 e < m
    · let s : Fin m := ⟨e (localT 1), by
          rw [localContactOrder_one] at hcontact
          omega⟩
      let t := localJetDegree e
      have he_le_t : e (localE 1) ≤ t := by
        dsimp only [t]
        rw [localJetDegree_one]
        omega
      have he_contact : e (localE 1) < m - s.val := by
        dsimp only [s]
        rw [localContactOrder_one] at hcontact
        omega
      let eIndex : Fin (min (m - s.val) (t + 1)) :=
        ⟨e (localE 1), by omega⟩
      have htarget : firstOrderGradedTargetExponent s.val t eIndex.val = e := by
        simpa [s, t, eIndex] using firstOrderGradedTargetExponent_of_local e
      let v : Fin (firstOrderGradedSourceCount D A m M s.val t) → R :=
        fun q ↦ MvPolynomial.coeff
          (firstOrderGradedSourceColumn D A m M s.val t q).exponent Q.1
      by_cases ht : t ≤ μ
      · let tIndex : Fin (μ + 1) := ⟨t, by omega⟩
        have hcompressed : firstOrderOriginGradedBaseSelectedMatrix
            F R D A m M s.val t *ᵥ v = 0 := by
          rw [firstOrderOriginGradedBaseSelectedMatrix_mulVec_coeff
            (F := F) R D A m M μ s.val t hD Q]
          funext i
          exact hselected tIndex s i
        have hfull :
            firstOrderOriginGradedSliceMatrixOver R D A m M s.val t *ᵥ v = 0 :=
          (firstOrderOriginGradedBaseSelectedMatrix_mulVec_eq_zero_iff
            (F := F) R D A m M s.val t v).mp hcompressed
        have hcoeff := congrFun hfull eIndex
        rw [firstOrderOriginGradedSliceMatrix_mulVec_coeff
          D A m M μ s.val t hD eIndex Q, htarget] at hcoeff
        exact hcoeff
      · have hv : v = 0 := by
          funext q
          apply Classical.byContradiction
          intro hcoeff
          have hmem :
              (firstOrderGradedSourceColumn D A m M s.val t q).exponent ∈ Q.1.support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          have hbound := (mem_firstOrderExponents.mp
            (mem_firstOrderSpace_iff.mp Q.2 _ hmem)).2.1
          rw [firstOrderGradedSourceColumn_totalJetDegree] at hbound
          exact ht hbound
        have hcoeff := firstOrderOriginGradedSliceMatrix_mulVec_coeff
          D A m M μ s.val t hD eIndex Q
        change (firstOrderOriginGradedSliceMatrixOver R D A m M s.val t *ᵥ v)
          eIndex = _ at hcoeff
        rw [hv, Matrix.mulVec_zero, Pi.zero_apply, htarget] at hcoeff
        simpa using hcoeff.symm
    · rw [localConstraintAt, LinearMap.comp_apply, projectLowContact,
        coeff_filterLocalMonomials, if_neg hcontact]
      rfl
  · intro hzero t s i
    simp [hzero]

/-! ### Fixed compressed rows for translated curve constraints -/

/-- Compressed rows at all points, jet grades, and displacement degrees. -/
abbrev FirstOrderCurveGradedRowIndex (F : Type*) [Field F]
    (D A m M μ n : ℕ) :=
  Fin n × Σ t : Fin (μ + 1), Σ s : Fin m,
    Fin (firstOrderOriginGradedSliceMatrix (F := F) D A m M s.val t.val).rank

/-- The literal low-contact coefficient selected by a compressed graded row. -/
noncomputable def firstOrderCurveGradedRowLocalIndex
    (F : Type*) [Field F] (D A m M μ n : ℕ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n) : LowContactIndex 1 m :=
  firstOrderGradedTargetLowContactIndex row.2.2.1 row.2.1.val
    (firstOrderOriginGradedSelectedRow F D A m M row.2.2.1.val row.2.1.val row.2.2.2)

/-- The translated curve matrix on the fixed base-field compressed coefficient rows. -/
noncomputable def firstOrderCurveGradedConstraintMatrix
    (D A m M μ n : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (FirstOrderCurveGradedRowIndex F D A m M μ n)
      (Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) F[X] :=
  fun row j ↦
    constraintMatrix m centers w
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
      (row.1, firstOrderCurveGradedRowLocalIndex F D A m M μ n row) j

/-- Reindex the compressed graded rows by a single `Fin` for the polynomial-kernel theorem. -/
noncomputable def firstOrderCurveGradedFinMatrix
    (D A m M μ n : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)))
      (Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) F[X] :=
  (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w).submatrix
    (Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm id

/-- A compressed translated row evaluates to the corresponding literal coefficient of the
assembled local constraint. -/
theorem firstOrderCurveGradedConstraintMatrix_mulVec_eq_coeff
    (D A m M μ n : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → F[X])
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n) :
    (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w *ᵥ v) row =
      MvPolynomial.coeff
        (firstOrderCurveGradedRowLocalIndex F D A m M μ n row).1
        (localConstraintAt m (Polynomial.C (centers row.1)) (w row.1)
          (interpolant
            (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v)) := by
  classical
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)
  let localRow := firstOrderCurveGradedRowLocalIndex F D A m M μ n row
  have heq :
      ((constraintMatrix m centers w columns) *ᵥ v) (row.1, localRow) =
        localConstraintCoordinatesAt m (Polynomial.C (centers row.1)) (w row.1)
          (interpolant columns v) localRow := by
    rw [interpolant, Matrix.mulVec, dotProduct, map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    change localConstraintCoordinatesAt m (Polynomial.C (centers row.1)) (w row.1)
      (columns j).polynomial localRow * v j = _
    rw [show MvPolynomial.monomial (columns j).exponent (v j) =
        v j • (columns j).polynomial by
          rw [SourceColumn.polynomial, MvPolynomial.smul_monomial]
          simp, LinearMap.map_smul]
    simp [mul_comm]
  change ((constraintMatrix m centers w columns) *ᵥ v) (row.1, localRow) = _
  rw [heq]
  change MvPolynomial.coeff localRow.1
      (unscaledLocalSubstitution 1 (Polynomial.C (centers row.1)) (w row.1)
        (interpolant columns v)) =
    MvPolynomial.coeff localRow.1
      (projectLowContact m
        (unscaledLocalSubstitution 1 (Polynomial.C (centers row.1)) (w row.1)
          (interpolant columns v)))
  rw [projectLowContact, coeff_filterLocalMonomials, if_pos localRow.2]

/-- The fixed compressed translated matrix has exactly the same kernel as the complete local
constraint system on the finite first-order support. The proof translates each point to the
origin, uses support preservation, and then applies scalar-extended base-field row compression. -/
theorem firstOrderCurveGradedConstraintMatrix_kernel_iff
    (D A m M μ n : ℕ) (hD : 0 < D) (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → F[X]) :
    firstOrderCurveGradedConstraintMatrix D A m M μ n centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) := by
  classical
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)
  let Q := interpolant columns v
  have hQ : Q ∈ firstOrderSpace F[X] D A m M μ := by
    change interpolant columns v ∈ firstOrderSpace F[X] D A m M μ
    rw [interpolant]
    apply Submodule.sum_mem
    intro j _
    rw [mem_firstOrderSpace_iff]
    intro u hu
    have hueq : u = (columns j).exponent := by
      simpa using MvPolynomial.support_monomial_subset hu
    rw [hueq]
    exact firstOrderColumns_eligible
      (D := D) (A := A) (m := m) (M := M) (μ := μ) j
  constructor
  · intro hmatrix i
    rw [SatisfiesLocalConstraints,
      localConstraintAt_eq_zero_comp_globalPointTranslation]
    let translated : firstOrderSpace F[X] D A m M μ :=
      ⟨globalPointTranslation (Polynomial.C (centers i)) (w i) Q,
        globalPointTranslation_mem_firstOrderSpace D A m M μ
          (Polynomial.C (centers i)) (w i) hQ⟩
    change localConstraintAt m 0 0 translated.1 = 0
    apply (firstOrderOriginGradedSelectedCoefficients_eq_zero_iff
      (F := F) D A m M μ hD translated).mp
    intro t s j
    let row : FirstOrderCurveGradedRowIndex F D A m M μ n :=
      (i, ⟨t, ⟨s, j⟩⟩)
    have hrow := congrFun hmatrix row
    rw [firstOrderCurveGradedConstraintMatrix_mulVec_eq_coeff
      D A m M μ n centers w v row] at hrow
    rw [localConstraintAt_eq_zero_comp_globalPointTranslation] at hrow
    simpa [row, translated, firstOrderCurveGradedRowLocalIndex,
      firstOrderGradedTargetLowContactIndex, Q, columns] using hrow
  · intro hsatisfies
    have hfull := (constraintMatrix_kernel_iff m centers w
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v).mpr
        hsatisfies
    funext row
    exact congrFun hfull
      (row.1, firstOrderCurveGradedRowLocalIndex F D A m M μ n row)

/-- Flattening the compressed rows by `Fintype.equivFin` preserves the exact kernel. -/
theorem firstOrderCurveGradedFinMatrix_kernel_iff
    (D A m M μ n : ℕ) (hD : 0 < D) (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → F[X]) :
    firstOrderCurveGradedFinMatrix D A m M μ n centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) v) := by
  rw [← firstOrderCurveGradedConstraintMatrix_kernel_iff
    D A m M μ n hD centers w v]
  constructor
  · intro hfin
    funext row
    let i := Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n) row
    have hi := congrFun hfin i
    simpa [firstOrderCurveGradedFinMatrix, i, Matrix.mulVec, dotProduct] using hi
  · intro hrows
    funext i
    exact congrFun hrows
      ((Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i)

/-- The row weight of a compressed coefficient is its local jet grade times the curve degree. -/
noncomputable def firstOrderCurveGradedRowWeight
    (F : Type*) [Field F] (D A m M μ n ℓ : ℕ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n) : ℕ :=
  ℓ * row.2.1.val

/-- Row weights after the fixed compressed rows are reindexed by a single `Fin`. -/
noncomputable def firstOrderCurveGradedFinRowWeight
    (F : Type*) [Field F] (D A m M μ n ℓ : ℕ)
    (i : Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n))) : ℕ :=
  firstOrderCurveGradedRowWeight F D A m M μ n ℓ
    ((Fintype.equivFin (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i)

/-- Every entry of the actual compressed translated matrix satisfies the shifted degree bound. -/
theorem firstOrderCurveGradedConstraintMatrix_degree_le
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n)
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j).natDegree ≤
      ℓ * (totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent -
          row.2.1.val) := by
  have h := constraintMatrix_degree_le_grade_shift m ℓ centers w hw
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
    (row.1, firstOrderCurveGradedRowLocalIndex F D A m M μ n row) j
  simpa only [firstOrderCurveGradedConstraintMatrix,
    firstOrderCurveGradedRowLocalIndex,
    localJetDegree_firstOrderGradedTargetLowContactIndex,
    SourceColumn.totalJetDegree_exponent, Fin.sum_univ_one] using h

/-- Entries into a compressed row above the source grade are identically zero. -/
theorem firstOrderCurveGradedConstraintMatrix_eq_zero_of_grade_lt
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (row : FirstOrderCurveGradedRowIndex F D A m M μ n)
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)))
    (hgrade : totalJetDegree
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent <
        row.2.1.val) :
    firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j = 0 := by
  apply constraintMatrix_eq_zero_of_source_grade_lt_row_grade m ℓ centers w hw
  simpa only [firstOrderCurveGradedRowLocalIndex,
    localJetDegree_firstOrderGradedTargetLowContactIndex,
    SourceColumn.totalJetDegree_exponent, Fin.sum_univ_one] using hgrade

/-- The flattened actual matrix has the shifted row/column degree bound required by the
polynomial-kernel theorem. -/
theorem firstOrderCurveGradedFinMatrix_degree_le
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)))
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)))
    (_hweight : firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i ≤
      ℓ * totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent) :
    (firstOrderCurveGradedFinMatrix D A m M μ n centers w i j).natDegree ≤
      ℓ * totalJetDegree
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent -
        firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i := by
  let row := (Fintype.equivFin
    (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i
  have hdegree := firstOrderCurveGradedConstraintMatrix_degree_le
    D A m M μ n ℓ centers w hw row j
  change (firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j).natDegree ≤ _
  simpa only [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight,
    row, Nat.mul_sub_left_distrib] using hdegree

/-- Flattened entries whose row weight exceeds their source-column weight are zero. -/
theorem firstOrderCurveGradedFinMatrix_eq_zero_of_weight_lt
    (D A m M μ n ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (FirstOrderCurveGradedRowIndex F D A m M μ n)))
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)))
    (hweight : ℓ * totalJetDegree
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent <
      firstOrderCurveGradedFinRowWeight F D A m M μ n ℓ i) :
    firstOrderCurveGradedFinMatrix D A m M μ n centers w i j = 0 := by
  let row := (Fintype.equivFin
    (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i
  change firstOrderCurveGradedConstraintMatrix D A m M μ n centers w row j = 0
  apply firstOrderCurveGradedConstraintMatrix_eq_zero_of_grade_lt
    D A m M μ n ℓ centers w hw row j
  simp only [firstOrderCurveGradedFinRowWeight, firstOrderCurveGradedRowWeight] at hweight
  change totalJetDegree
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent <
    ((Fintype.equivFin
      (FirstOrderCurveGradedRowIndex F D A m M μ n)).symm i).2.1.val
  exact Nat.lt_of_mul_lt_mul_left hweight

/-- The actual sum of origin block ranks satisfies the sharp executable paper profile. -/
theorem firstOrderOriginGradedRank_le_bound (D A m M t : ℕ) :
    firstOrderOriginGradedRank F D A m M t ≤ firstOrderGradedRankBound D A m M t := by
  apply Finset.sum_le_sum
  intro s hs
  exact firstOrderOriginGradedSliceMatrix_rank_le (F := F) D A m M s t

/-! ### Literal graded block-rank profile -/

/-- The degree-`t` row profile is the sum of the literal origin `(s,t)` block-matrix ranks.
This is the unique rank profile used by shifted height counting. -/
noncomputable abbrev firstOrderGradedRank (F : Type*) [Field F]
    (D A m M t : ℕ) : ℕ :=
  firstOrderOriginGradedRank F D A m M t

/-- The complete actual graded row count through the total-degree cap `μ`. -/
noncomputable def firstOrderGradedRowCount (F : Type*) [Field F]
    (D A m M μ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ + 1), firstOrderGradedRank F D A m M t

/-- The symbolic first-order matrix has the certified global rank bound over `F(Z)`.
The proof factors it through the actual global constraint map on the capped support. -/
theorem firstOrder_curve_matrix_rank_le {D A m M μ n N : ℕ}
    (hD : 1 < D) (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      n * certifiedEnlargedRankBound 1 m M 0 := by
  classical
  let K := RatFunc F
  let φ : F[X] →+* K := algebraMap F[X] K
  let V := firstOrderSpace K D A m M μ
  let monomial (j : Fin N) : V := ⟨(columns j).polynomial, by
    apply mem_firstOrderSpace_iff.mpr
    intro u hu
    have heq : u = (columns j).exponent := by
      simpa [SourceColumn.polynomial] using MvPolynomial.support_monomial_subset hu
    exact heq ▸ heligible j⟩
  let assemble : (Fin N → K) →ₗ[K] V :=
    ∑ j, (LinearMap.smulRight (LinearMap.proj j) (monomial j))
  let constraint := firstOrderGlobalConstraint (D := D) (A := A) (m := m) (M := M) (μ := μ)
    (fun i ↦ φ (Polynomial.C (centers i))) (fun i ↦ φ (w i))
  let coefficients : (Fin n → LocalPolynomial K 1) →ₗ[K]
      ((Fin n × LowContactIndex 1 m) → K) :=
    LinearMap.pi fun row ↦ MvPolynomial.lcoeff K row.2.1 ∘ₗ LinearMap.proj row.1
  let mat := (constraintMatrix m centers w columns).map φ
  have hfactor : mat.mulVecLin = coefficients ∘ₗ constraint ∘ₗ assemble := by
    apply LinearMap.ext
    intro v
    funext row
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      LinearMap.comp_apply, coefficients, LinearMap.pi_apply, MvPolynomial.lcoeff_apply,
      LinearMap.proj_apply, assemble, LinearMap.sum_apply, map_sum, LinearMap.smulRight_apply,
      map_smul]
    change (∑ j, φ (constraintMatrix m centers w columns row j) * v j) = _
    simp only [constraint, firstOrderGlobalConstraint, LinearMap.pi_apply,
      firstOrderLocalConstraintAt, LinearMap.domRestrict_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : constraintMatrix m centers w columns row j =
        MvPolynomial.coeff row.2.1
          (localConstraintAt m (Polynomial.C (centers row.1)) (w row.1)
            (columns j).polynomial) := by
      simp [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
        localConstraintAt, projectLowContact, coeff_filterLocalMonomials, row.2.2]
    rw [hentry]
    rw [← MvPolynomial.coeff_map, map_localConstraintAt]
    simp [monomial, SourceColumn.polynomial, mul_comm]
  let _ : Module.Finite K V := Module.Finite.of_basis (firstOrderSpaceBasis K D A m M μ)
  change Module.finrank K mat.mulVecLin.range ≤ _
  rw [hfactor]
  apply (finrank_range_comp_le_outer (coefficients ∘ₗ constraint) assemble).trans
  rw [LinearMap.range_comp]
  apply (Submodule.finrank_map_le coefficients constraint.range).trans
  simpa [constraint] using
    (finrank_firstOrderGlobalConstraint_le (A := A) (m := m) (M := M) (μ := μ) hD
      (fun i ↦ φ (Polynomial.C (centers i)))
      (fun i ↦ φ (w i)))

end

end ReedSolomon.HiddenDerivative
