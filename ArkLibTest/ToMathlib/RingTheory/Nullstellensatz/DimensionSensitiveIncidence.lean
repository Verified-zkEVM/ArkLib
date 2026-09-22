/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.DimensionSensitiveIncidence
import ArkLibTest.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Acceptance tests for dimension-sensitive agreement incidence

These examples use the public API through an ordinary import. In the plane over `ℚ`, the four
cuts `x, x - 1, y, y - 1` meet in the four points of `{0, 1} ^ 2`, each on two cuts. A prime of
positive dimension contains at most one of the cuts, and a prime of dimension two contains none,
so the dimension-sensitive budget holds with `m = 2`. The dimension-sensitive bound for `A = 2`
is `3 * 2 = 6`; the hybrid bound with `L = 2` and `m = 1` is also `6`, directly and after a list
of fixed cuts. In the coefficient space of constant polynomials, the constants agreeing with two
of the values `0, 0, 1, 1` at four distinct points number at most `2`; for lines and three
points the bound is `3`.

The boundary examples show that `m ≤ A` is needed in the fixed-coefficient bound and in the
hybrid bound, and `L ≤ A` in the hybrid bound. The last examples restate the results with cuts
indexed by `Fin n`, the component budgets written as a dimension bound and a count, the product
in dimension `min (d - 1) m + 1`, the two-factor forms, and the first-order fixed-coefficient
bound, and derive the bound on a finite union of loci from the bounds on the members.
-/

open MvPolynomial AgreementIncidenceTest

namespace DimensionSensitiveIncidenceTest

/-! ### Four cuts in the plane -/

/-- The variable of the `i`-th grid cut. -/
def gridVar : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The constant of the `i`-th grid cut. -/
def gridVal : Fin 4 → ℚ := ![0, 1, 0, 1]

/-- The four cuts `x, x - 1, y, y - 1` of the plane over `ℚ`. -/
noncomputable def gridCuts (i : Fin 4) : MvPolynomial (Fin 2) ℚ := X (gridVar i) - C (gridVal i)

/-- The four points of `{0, 1} ^ 2`. -/
def gridPoints : Finset (Fin 2 → ℚ) := {![0, 0], ![0, 1], ![1, 0], ![1, 1]}

/-- Each grid cut has total degree at most `1`. -/
theorem totalDegree_gridCuts_le (i : Fin 4) : (gridCuts i).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (by simp)

/-- An ideal of `ℚ[x, y]` containing a grid cut has dimension at most `1`: its zero locus over
`K` lies in a line parametrized by the other coordinate. -/
theorem natDegree_affineHilbertPolynomial_le_one_of_gridCuts_mem
    {J : Ideal (MvPolynomial (Fin 2) ℚ)} {i : Fin 4} (h : gridCuts i ∈ J) :
    (affineHilbertPolynomial J).natDegree ≤ 1 := by
  have hreg : IsLeftRegular (Ideal.Quotient.mk J 1) := by
    rw [map_one]
    exact isRegular_one.left
  have hother : ∀ j v : Fin 2, j ≠ v → j = v + 1 := by decide
  have hle := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range
    (K := AlgebraicClosure ℚ) (τ := Fin 1) hreg
    (fun j ↦ if j = gridVar i then C (gridVal i) else X 0)
    fun x hx _ ↦ ⟨fun _ ↦ x (gridVar i + 1), ?_⟩
  · simpa using hle
  funext j
  by_cases hj : j = gridVar i
  · subst hj
    have := (mem_zeroLocus_iff.mp hx) _ h
    simpa [gridCuts, sub_eq_zero] using this
  · simp [hj, ← hother j (gridVar i) hj]

/-- A prime of `ℚ[x, y]` of positive dimension contains at most one grid cut: two cuts in the
same variable differ by a nonzero constant, and two cuts in different variables cut out a
point. -/
theorem not_two_le_ncard_gridCuts {Q : Ideal (MvPolynomial (Fin 2) ℚ)} (hQ : Q.IsPrime)
    (hd : 0 < (affineHilbertPolynomial Q).natDegree) : ¬ 2 ≤ {i | gridCuts i ∈ Q}.ncard := by
  intro h
  obtain ⟨i, j, hi, hj, hij⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h
  change gridCuts i ∈ Q at hi
  change gridCuts j ∈ Q at hj
  by_cases hv : gridVar i = gridVar j
  · have hval : ∀ i j : Fin 4, i ≠ j → gridVar i = gridVar j → gridVal i ≠ gridVal j := by
      decide
    have hsub := Q.sub_mem hi hj
    rw [gridCuts, gridCuts, hv, sub_sub_sub_cancel_left, ← map_sub] at hsub
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsub
      ((sub_ne_zero.mpr (hval i j hij hv).symm).isUnit.map C))
  · have key : ∀ {i j : Fin 4}, gridVar i = 0 → gridVar j = 1 → gridCuts i ∈ Q →
        gridCuts j ∈ Q → False := fun hi0 hj1 hi hj ↦ by
      rw [gridCuts, hi0] at hi
      rw [gridCuts, hj1] at hj
      have := natDegree_affineHilbertPolynomial_eq_zero_of_X_sub_C_mem _ _ hi hj
      omega
    have hcases : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
    rcases hcases _ _ hv with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · exact key h0 h1 hi hj
    · exact key h0 h1 hj hi

/-- The plane has dimension `2`, so every ideal of `ℚ[x, y]` has dimension at most `2`. -/
theorem natDegree_affineHilbertPolynomial_le_two (Q : Ideal (MvPolynomial (Fin 2) ℚ)) :
    (affineHilbertPolynomial Q).natDegree ≤ 2 :=
  (natDegree_affineHilbertPolynomial_le_of_le bot_le).trans
    (by simp [natDegree_affineHilbertPolynomial_bot])

/-- The dimension-sensitive budget with `m = 2` for the grid cuts: a positive-dimensional prime
of dimension `e` contains at most `2 - e` of them. -/
theorem natDegree_add_ncard_gridCuts_le {Q : Ideal (MvPolynomial (Fin 2) ℚ)} (hQ : Q.IsPrime)
    (hd : 0 < (affineHilbertPolynomial Q).natDegree) :
    (affineHilbertPolynomial Q).natDegree + {i | gridCuts i ∈ Q}.ncard ≤ 2 := by
  have h2 := natDegree_affineHilbertPolynomial_le_two Q
  have hlt := not_two_le_ncard_gridCuts hQ hd
  rcases Nat.eq_zero_or_pos {i | gridCuts i ∈ Q}.ncard with h0 | hpos
  · omega
  · obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    have := natDegree_affineHilbertPolynomial_le_one_of_gridCuts_mem hi
    omega

/-- Each point of `{0, 1} ^ 2` lies on two of the grid cuts. -/
theorem two_le_ncard_gridCuts_of_mem_gridPoints {x : Fin 2 → ℚ} (hx : x ∈ gridPoints) :
    2 ≤ {i | aeval x (gridCuts i) = 0}.ncard := by
  have hset : {i | aeval x (gridCuts i) = 0} = {i | x (gridVar i) = gridVal i} := by
    ext i
    simp [gridCuts, sub_eq_zero]
  rw [hset, Set.ncard_eq_toFinset_card']
  simp only [gridPoints, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

/-- The dimension-sensitive bound for the grid cuts with `A = 2` and `m = 2`: at most
`1 * ((4 - 2 + 1) / (2 - 2 + 1)) * ((4 - 2 + 2) / (2 - 2 + 2)) = 6` points of the plane agree
with two of the cuts. The four points of `{0, 1} ^ 2` do. -/
example :
    let S := {x : Fin 2 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧ 2 ≤ {i | aeval x (gridCuts i) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 6 := by
  intro S
  have h := finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_agreement (K := ℚ)
    (P := ⊥) 1 gridCuts (b := 1) (A := 2) (m := 2) totalDegree_gridCuts_le le_rfl
    fun Q _ hQ _ hd ↦ natDegree_add_ncard_gridCuts_le hQ hd
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [affineDegree_bot, natDegree_affineHilbertPolynomial_bot, dimensionSensitiveIncidenceProduct]
  norm_num

/-- The hybrid bound for the grid cuts with `A = 2`, `L = 2` and `m = 1`, outside the empty set:
no positive-dimensional prime contains two cuts, and a prime of dimension two contains none. The
bound is `1 * ((4 - 2 + 1) / (2 - 2 + 1)) * ((4 - 1 + 1) / (2 - 1 + 1)) = 6`. -/
example :
    let S := {x : Fin 2 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧ x ∉ (∅ : Set (Fin 2 → ℚ)) ∧
      2 ≤ {i | aeval x (gridCuts i) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 6 := by
  intro S
  have h := finite_and_ncard_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded
    (K := ℚ) (P := ⊥) 1 gridCuts (b := 1) (A := 2) (L := 2) (m := 1) totalDegree_gridCuts_le le_rfl
    (by norm_num) (∅ : Set (Fin 2 → ℚ))
    (fun Q _ hQ _ hd ↦ by
      have := natDegree_add_ncard_gridCuts_le hQ (by omega)
      omega)
    fun Q _ hQ _ hd hL ↦ absurd hL (not_two_le_ncard_gridCuts hQ hd)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [affineDegree_bot, natDegree_affineHilbertPolynomial_bot]
  norm_num

/-- The hybrid bound after the empty list of fixed cuts, for `Ps = {⊥}` in the plane and the
grid cuts with `A = 2`, `L = 2` and `m = 1`: the bound `1 * 6` holds for every set of points
agreeing with two cuts, in any dimension and in the two-factor form. -/
example (S : Finset (Fin 2 → ℚ)) (hA : ∀ x ∈ S, 2 ≤ {i | aeval x (gridCuts i) = 0}.ncard) :
    (S.card : ℚ) ≤ 6 ∧ (S.card : ℚ) ≤ 6 := by
  have hprime : ∀ P ∈ ({⊥} : Finset (Ideal (MvPolynomial (Fin 2) ℚ))), P.IsPrime :=
    fun P hP ↦ by rw [Finset.mem_singleton.mp hP]; exact Ideal.isPrime_bot
  have hdim : ∀ P ∈ ({⊥} : Finset (Ideal (MvPolynomial (Fin 2) ℚ))),
      (affineHilbertPolynomial P).natDegree ≤ 2 := fun P _ ↦
    natDegree_affineHilbertPolynomial_le_two P
  have hdimension : ∀ P ∈ ({⊥} : Finset (Ideal (MvPolynomial (Fin 2) ℚ))),
      ∀ Q : Ideal (MvPolynomial (Fin 2) ℚ), P ≤ Q → Q.IsPrime → 1 ∉ Q →
      (∀ f ∈ ([] : List (MvPolynomial (Fin 2) ℚ)), f ∈ Q) →
      1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | gridCuts i ∈ Q}.ncard ≤ 1 + 1 :=
    fun _ _ Q _ hQ _ _ hd ↦ natDegree_add_ncard_gridCuts_le hQ (by omega)
  have hterminal : ∀ P ∈ ({⊥} : Finset (Ideal (MvPolynomial (Fin 2) ℚ))),
      ∀ Q : Ideal (MvPolynomial (Fin 2) ℚ), P ≤ Q → Q.IsPrime → 1 ∉ Q →
      (∀ f ∈ ([] : List (MvPolynomial (Fin 2) ℚ)), f ∈ Q) →
      0 < (affineHilbertPolynomial Q).natDegree → 2 ≤ {i | gridCuts i ∈ Q}.ncard →
      {x : Fin 2 → ℚ | x ∈ zeroLocus ℚ Q ∧ aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0} ⊆ ∅ :=
    fun _ _ Q _ hQ _ _ hd hL ↦ absurd hL (not_two_le_ncard_gridCuts hQ hd)
  have hS : ∀ x ∈ S, (∃ P ∈ ({⊥} : Finset (Ideal (MvPolynomial (Fin 2) ℚ))),
      x ∈ zeroLocus ℚ P) ∧ aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
      (∀ f ∈ ([] : List (MvPolynomial (Fin 2) ℚ)), aeval x f = 0) ∧
      x ∉ (∅ : Set (Fin 2 → ℚ)) :=
    fun x _ ↦ ⟨⟨⊥, by simp, by simp⟩, by simp, by simp, by simp⟩
  have hV : ∑ P ∈ ({⊥} : Finset (Ideal (MvPolynomial (Fin 2) ℚ))),
      affineDegree P * ((1 : ℕ) : ℚ) ^ (affineHilbertPolynomial P).natDegree ≤ 1 := by
    simp [affineDegree_bot]
  constructor
  · have h := card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily
      hprime hdim 1 (h := 1) le_rfl (by simp) hV gridCuts (b := 1) (A := 2) (L := 2) (m := 1)
      totalDegree_gridCuts_le one_pos le_rfl (by norm_num) ∅ hdimension hterminal S hS hA
    refine h.trans_eq ?_
    simp
    norm_num
  · have h := card_le_hybridDimensionSensitiveIncidenceProduct_two_of_iteratedRetainedCutFamily
      hprime hdim 1 (h := 1) le_rfl (by simp) hV gridCuts (b := 1) (A := 2) (L := 2) (m := 1)
      totalDegree_gridCuts_le one_pos le_rfl (by norm_num) ∅ hdimension hterminal S hS hA
    refine h.trans_eq ?_
    simp
    norm_num

/-! ### Fixed coefficient evaluations -/

/-- The points `0, 1, 2, 3` of `ℚ`. -/
def fourPoints : Fin 4 ↪ ℚ := ⟨![0, 1, 2, 3], by decide⟩

/-- The points `0, 1, 2` of `ℚ`. -/
def threePoints : Fin 3 ↪ ℚ := ⟨![0, 1, 2], by decide⟩

/-- Constant polynomials agreeing with two of the values `0, 0, 1, 1` at `0, 1, 2, 3`: the bound
is `1 * ((4 - 1 + 1) / (2 - 1 + 1)) = 2`, attained by the constants `0` and `1`. -/
example :
    let S := {x : Fin 1 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧
      2 ≤ {i | aeval x (fixedCoefficientEvaluation 1 (fourPoints i) (![0, 0, 1, 1] i)) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 2 := by
  intro S
  have h := finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation
    (K := ℚ) fourPoints ![0, 0, 1, 1] (m := 1) (P := ⊥) 1 (A := 2) (by norm_num)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [affineDegree_bot, natDegree_affineHilbertPolynomial_bot]
  norm_num

/-- Polynomials of degree less than `2` agreeing with two of the values `0, 0, 1` at `0, 1, 2`:
the bound is `1 * ((3 - 2 + 1) / (2 - 2 + 1)) * ((3 - 2 + 2) / (2 - 2 + 2)) = 3`, attained by
the lines through two of the three points `(0, 0)`, `(1, 0)`, `(2, 1)`. -/
example :
    let S := {x : Fin 2 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
      2 ≤ {i | aeval x (fixedCoefficientEvaluation 2 (threePoints i) (![0, 0, 1] i)) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 3 := by
  intro S
  have h := finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation
    (K := ℚ) threePoints ![0, 0, 1] (m := 2) (P := ⊥) 1 (A := 2) le_rfl
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [affineDegree_bot, natDegree_affineHilbertPolynomial_bot, dimensionSensitiveIncidenceProduct]
  norm_num

/-! ### The hypotheses are needed -/

/-- The line over `ℚ` is infinite. -/
theorem infinite_line : (Set.univ : Set (Fin 1 → ℚ)).Infinite := Set.infinite_univ

/-- The hypothesis `m ≤ A` is needed in
`finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation`. With no
evaluation points, `m = 1` and `A = 0`, every constant agrees with at least `0` values, so the set
is the whole line and is infinite. -/
example : ¬ {x : Fin 1 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
    aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧
    0 ≤ {i : Fin 0 | aeval x (fixedCoefficientEvaluation 1 (Fin.elim0 i : ℚ) (Fin.elim0 i)) =
      0}.ncard}.Finite := fun h ↦
  infinite_line (h.subset fun x _ ↦ ⟨by simp, by simp, Nat.zero_le _⟩)

/-- The hypothesis `L ≤ A` is needed in
`finite_and_ncard_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded`. On the
line over `ℚ` with no cuts, `A = 0`, `L = 1`, `m = 0` and `excluded = ∅`, no prime has dimension
greater than `1` and none contains a cut, so both hypotheses on components hold, but every point
agrees with at least `0` cuts and the set is infinite. -/
example :
    (∀ Q : Ideal (MvPolynomial (Fin 1) ℚ), ¬ 1 < (affineHilbertPolynomial Q).natDegree) ∧
    (∀ Q : Ideal (MvPolynomial (Fin 1) ℚ),
      ¬ 1 ≤ {i : Fin 0 | (Fin.elim0 i : MvPolynomial (Fin 1) ℚ) ∈ Q}.ncard) ∧
    ¬ {x : Fin 1 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧ x ∉ (∅ : Set (Fin 1 → ℚ)) ∧
      0 ≤ {i : Fin 0 | aeval x (Fin.elim0 i : MvPolynomial (Fin 1) ℚ) = 0}.ncard}.Finite := by
  refine ⟨fun Q h ↦ ?_, fun Q h ↦ absurd h (by simp [Set.eq_empty_of_isEmpty]), fun h ↦
    infinite_line (h.subset fun x _ ↦
      ⟨by simp, by simp, by simp, Nat.zero_le _⟩)⟩
  have := (natDegree_affineHilbertPolynomial_le_of_le (bot_le (a := Q))).trans_eq
    (natDegree_affineHilbertPolynomial_bot (σ := Fin 1) (k := ℚ))
  simp at this
  omega

/-- The hypothesis `m ≤ A` is needed in
`card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded`. For the grid cuts
with `A = 2`, `L = 2` and `m = 5`, the budget `e + #bad ≤ 6` holds in dimension `e ≥ 2` since
there are four cuts, no positive-dimensional prime contains two cuts, and the four points of
`{0, 1} ^ 2` each agree with two cuts. The bound
`1 * ((4 - 2 + 1) / (2 - 2 + 1)) * ((4 - 5 + 1) / (2 - 5 + 1))` is `3`. -/
example :
    (∀ Q : Ideal (MvPolynomial (Fin 2) ℚ), 1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | gridCuts i ∈ Q}.ncard ≤ 5 + 1) ∧
    (∀ Q : Ideal (MvPolynomial (Fin 2) ℚ), Q.IsPrime →
      0 < (affineHilbertPolynomial Q).natDegree → ¬ 2 ≤ {i | gridCuts i ∈ Q}.ncard) ∧
    (∀ x ∈ gridPoints, 2 ≤ {i | aeval x (gridCuts i) = 0}.ncard) ∧
    ¬ ((gridPoints.card : ℚ) ≤ affineDegree (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) *
      hybridDimensionSensitiveIncidenceProduct (Fintype.card (Fin 4)) 2 2 5 1
        (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))).natDegree) := by
  refine ⟨fun Q _ ↦ ?_, fun _ hQ hd ↦ not_two_le_ncard_gridCuts hQ hd,
    fun _ hx ↦ two_le_ncard_gridCuts_of_mem_gridPoints hx, ?_⟩
  · have h2 := natDegree_affineHilbertPolynomial_le_two Q
    have h4 : {i | gridCuts i ∈ Q}.ncard ≤ 4 := (Set.ncard_le_card _).trans_eq (by simp)
    omega
  · rw [show gridPoints.card = 4 by decide]
    simp [affineDegree_bot, natDegree_affineHilbertPolynomial_bot]
    norm_num

/-! ### Derived forms -/

open Classical in
/-- The dimension-sensitive bound outside an excluded set for cuts indexed by `Fin n`, with the
component budget written as `e ≤ m ∧ (#bad ≤ m - e ∨ U(Q) ⊆ excluded)`, the principal open
subsets written out and the counts written as filters. The hypotheses `s ∉ P` and `A ≤ n` are
not used. -/
theorem card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded_fin
    {F σ : Type*} [Field F] [Finite σ] {n A m b : ℕ} {P : Ideal (MvPolynomial σ F)}
    (hP : P.IsPrime) {s : MvPolynomial σ F} (_hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hmA : m ≤ A) (_hAn : A ≤ n) (excluded : Set (σ → F))
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree ≤ m ∧
        ((Finset.univ.filter fun i ↦ cuts i ∈ Q).card ≤
            m - (affineHilbertPolynomial Q).natDegree ∨
          {x | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0} ⊆ excluded))
    (S : Finset (σ → F)) (hS : ∀ x ∈ S, (x ∈ zeroLocus F P ∧ aeval x s ≠ 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter fun i ↦ aeval x (cuts i) = 0).card) :
    (S.card : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A m b (affineHilbertPolynomial P).natDegree := by
  have := hP
  have h := card_le_dimensionSensitiveIncidenceProduct_of_agreement_off_excluded s cuts hdeg hmA
    excluded (fun Q hPQ hQ hsQ hd ↦ by
      obtain ⟨hdm, hbad | hsub⟩ := hcomponent Q hPQ hQ hsQ hd
      · rw [card_filter_univ_eq_ncard] at hbad
        exact Or.inl (by omega)
      · exact Or.inr hsub)
    S (fun x hx ↦ ⟨(hS x hx).1.1, (hS x hx).1.2, (hS x hx).2⟩)
    fun x hx ↦ by rw [← card_filter_univ_eq_ncard]; exact hA x hx
  rwa [Fintype.card_fin] at h

/-- The hybrid budget written as `e ≤ m + 1 ∧ (1 < e → #bad ≤ m + 1 - e)` implies the form
`1 < e → e + #bad ≤ m + 1`. -/
theorem add_le_of_hybridBudget {e bad m : ℕ} (h : e ≤ m + 1 ∧ (1 < e → bad ≤ m + 1 - e))
    (he : 1 < e) : e + bad ≤ m + 1 := by
  have := h.2 he
  omega

open Classical in
/-- The hybrid bound outside an excluded set for cuts indexed by `Fin n`, with the budget in
dimension `e > 0` written as `e ≤ m + 1 ∧ (1 < e → #bad ≤ m + 1 - e)`, the principal open subsets
written out and the counts written as filters. The hypotheses `s ∉ P` and `A ≤ n` are not
used. -/
theorem card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded_fin
    {F σ : Type*} [Field F] [Finite σ] {n A L m b : ℕ} {P : Ideal (MvPolynomial σ F)}
    (hP : P.IsPrime) {s : MvPolynomial σ F} (_hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hmA : m ≤ A) (_hAn : A ≤ n) (excluded : Set (σ → F))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree ≤ m + 1 ∧
        (1 < (affineHilbertPolynomial Q).natDegree →
          (Finset.univ.filter fun i ↦ cuts i ∈ Q).card ≤
            m + 1 - (affineHilbertPolynomial Q).natDegree))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ (Finset.univ.filter fun i ↦ cuts i ∈ Q).card →
      {x | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → F)) (hS : ∀ x ∈ S, (x ∈ zeroLocus F P ∧ aeval x s ≠ 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter fun i ↦ aeval x (cuts i) = 0).card) :
    (S.card : ℚ) ≤ affineDegree P *
      hybridDimensionSensitiveIncidenceProduct n A L m b (affineHilbertPolynomial P).natDegree := by
  have := hP
  have h := card_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded s cuts
    hdeg hLA hmA excluded
    (fun Q hPQ hQ hsQ hd ↦ by
      have h := add_le_of_hybridBudget (hdimension Q hPQ hQ hsQ (by omega)) hd
      rwa [card_filter_univ_eq_ncard] at h)
    (fun Q hPQ hQ hsQ hd hL ↦ hterminal Q hPQ hQ hsQ hd (by rwa [card_filter_univ_eq_ncard]))
    S (fun x hx ↦ ⟨(hS x hx).1.1, (hS x hx).1.2, (hS x hx).2⟩)
    fun x hx ↦ by rw [← card_filter_univ_eq_ncard]; exact hA x hx
  rwa [Fintype.card_fin] at h

/-- The hybrid bound on the full locus for a prime of dimension at most two, as the product of
the factors at the thresholds `L` and `m`. -/
example {F σ : Type*} [Field F] [Finite σ] {n A L m b : ℕ} {P : Ideal (MvPolynomial σ F)}
    [P.IsPrime] (s : MvPolynomial σ F) (cuts : Fin n → MvPolynomial σ F)
    (hdeg : ∀ i, (cuts i).totalDegree ≤ b) (hLA : L ≤ A) (hmA : m ≤ A) (hAn : A ≤ n)
    (hb : 0 < b) (hPdim : (affineHilbertPolynomial P).natDegree ≤ 2) (excluded : Set (σ → F))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (affineHilbertPolynomial Q).natDegree → L ≤ {i | cuts i ∈ Q}.ncard →
      {x | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0} ⊆ excluded) :
    let S := {x : σ → F | x ∈ zeroLocus F P ∧ aeval x s ≠ 0 ∧ x ∉ excluded ∧
      A ≤ {i | aeval x (cuts i) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ affineDegree P *
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        ((((n - m + 1) * b : ℕ) : ℚ) / ((A - m + 1 : ℕ) : ℚ)) := by
  intro S
  obtain ⟨hfin, hle⟩ :=
    finite_and_ncard_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded s cuts
      hdeg hLA hmA excluded hdimension hterminal
  rw [Fintype.card_fin] at hle
  refine ⟨hfin, hle.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (hybridDimensionSensitiveIncidenceProduct_le_two hPdim hAn hb) (affineDegree_nonneg P)

/-- The hybrid bound after fixed cuts, for members of dimension exactly `d` with `s` off every
member, cuts of degree at most one and the budget written as
`e ≤ m + 1 ∧ (1 < e → #bad ≤ m + 1 - e)`, with the product taken in dimension
`min (d - 1) m + 1`. The hypothesis that `s` lies in no member is not used. -/
example {F σ : Type*} [Field F] [Finite σ] {n A L m B d : ℕ}
    (Ps : Finset (Ideal (MvPolynomial σ F))) (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ Ps, P.IsPrime) (_hopen : ∀ P ∈ Ps, s ∉ P)
    (hdim : ∀ P ∈ Ps, (affineHilbertPolynomial P).natDegree = d)
    {V : ℚ} (hV : ∑ P ∈ Ps, affineDegree P ≤ V)
    (highCuts : List (MvPolynomial σ F)) (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B)
    (hB : 0 < B) (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ 1)
    (hLA : L ≤ A) (hmA : m ≤ A) (hAn : A ≤ n) (excluded : Set (σ → F))
    (hdimension : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 0 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree ≤ m + 1 ∧
        (1 < (affineHilbertPolynomial Q).natDegree →
          {i | cuts i ∈ Q}.ncard ≤ m + 1 - (affineHilbertPolynomial Q).natDegree))
    (hterminal : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ {i | cuts i ∈ Q}.ncard → {x | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, (∃ P ∈ Ps, x ∈ zeroLocus F P) ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (S.card : ℚ) ≤ V * (B : ℚ) ^ d *
      hybridDimensionSensitiveIncidenceProduct n A L m 1 (min (d - 1) m + 1) := by
  have h := card_le_hybridDimensionSensitiveIncidenceProduct_of_iteratedRetainedCutFamily hprime
    (fun P hP ↦ (hdim P hP).le) s hB hhigh
    (sum_affineDegree_mul_pow_le Ps hB (fun P hP ↦ (hdim P hP).le) hV) cuts hdeg one_pos hLA hmA
    excluded
    (fun P hP Q hPQ hQ hsQ hhQ hd ↦
      add_le_of_hybridBudget (hdimension P hP Q hPQ hQ hsQ hhQ (by omega)) hd)
    hterminal S hS hA
  rw [Fintype.card_fin] at h
  refine h.trans (mul_le_mul_of_nonneg_left
    (hybridDimensionSensitiveIncidenceProduct_mono_dimension hAn one_pos (by omega)) ?_)
  exact mul_nonneg ((Finset.sum_nonneg fun P _ ↦ affineDegree_nonneg P).trans hV) (by positivity)

/-- The hybrid bound after fixed cuts for members of dimension exactly two, with cuts of degree
at most one, as the product of the ratios `(n - L + 1) / (A - L + 1)` and
`(n - m + 1) / (A - m + 1)`. -/
example {F σ : Type*} [Field F] [Finite σ] {n A L m B : ℕ}
    (Ps : Finset (Ideal (MvPolynomial σ F))) (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ Ps, P.IsPrime)
    (hdim : ∀ P ∈ Ps, (affineHilbertPolynomial P).natDegree = 2)
    {V : ℚ} (hV : ∑ P ∈ Ps, affineDegree P ≤ V)
    (highCuts : List (MvPolynomial σ F)) (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B)
    (hB : 0 < B) (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ 1)
    (hLA : L ≤ A) (hmA : m ≤ A) (excluded : Set (σ → F))
    (hdimension : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 1 < (affineHilbertPolynomial Q).natDegree →
      (affineHilbertPolynomial Q).natDegree + {i | cuts i ∈ Q}.ncard ≤ m + 1)
    (hterminal : ∀ P ∈ Ps, ∀ Q : Ideal (MvPolynomial σ F), P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) → 0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ {i | cuts i ∈ Q}.ncard → {x | x ∈ zeroLocus F Q ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, (∃ P ∈ Ps, x ∈ zeroLocus F P) ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard) :
    (S.card : ℚ) ≤ V * (B : ℚ) ^ 2 *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - m + 1 : ℕ) : ℚ) / ((A - m + 1 : ℕ) : ℚ)) := by
  simpa only [Fintype.card_fin, mul_one] using
    card_le_hybridDimensionSensitiveIncidenceProduct_two_of_iteratedRetainedCutFamily hprime
      (fun P hP ↦ (hdim P hP).le) s hB hhigh
      (sum_affineDegree_mul_pow_le Ps hB (fun P hP ↦ (hdim P hP).le) hV) cuts hdeg one_pos hLA hmA
      excluded hdimension hterminal S hS hA

/-- For a prime of dimension at most one in the coefficient space of polynomials of degree less
than `m`, the polynomials agreeing with received values at `A` of `n` distinct points are bounded
by `affineDegree P * (n - m + 1) / (A - m + 1)`. -/
example {F : Type*} [Field F] {n A m : ℕ} (α : Fin n ↪ F) (y : Fin n → F)
    {P : Ideal (MvPolynomial (Fin m) F)} [P.IsPrime] (s : MvPolynomial (Fin m) F)
    (hPdim : (affineHilbertPolynomial P).natDegree ≤ 1) (hmA : m ≤ A) (hAn : A ≤ n) :
    let S := {x : Fin m → F | x ∈ zeroLocus F P ∧ aeval x s ≠ 0 ∧
      A ≤ {i | aeval x (fixedCoefficientEvaluation m (α i) (y i)) = 0}.ncard}
    S.Finite ∧
      (S.ncard : ℚ) ≤ affineDegree P * (((n - m + 1 : ℕ) : ℚ) / ((A - m + 1 : ℕ) : ℚ)) := by
  intro S
  obtain ⟨hfin, hle⟩ :=
    finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation
      (K := F) α y (P := P) s hmA
  exact ⟨hfin, hle.trans (mul_le_mul_of_nonneg_left
    (dimensionSensitiveIncidenceProduct_le_one hPdim hAn) (affineDegree_nonneg P))⟩

/-- A finite union of finite sets is finite, with cardinality at most the sum of bounds on the
members. -/
theorem finite_biUnion_and_ncard_le_sum {ι X : Type*} (T : Finset ι) (S : ι → Set X)
    (w : ι → ℚ) (hfinite : ∀ i ∈ T, (S i).Finite) (hcard : ∀ i ∈ T, ((S i).ncard : ℚ) ≤ w i) :
    (⋃ i ∈ T, S i).Finite ∧ (((⋃ i ∈ T, S i).ncard : ℕ) : ℚ) ≤ ∑ i ∈ T, w i :=
  ⟨T.finite_toSet.biUnion hfinite, (Nat.cast_le.mpr (T.set_ncard_biUnion_le S)).trans
    (by push_cast; exact Finset.sum_le_sum hcard)⟩

/-- Over a family of primes whose affine degrees sum to at most `V`, bounds
`affineDegree P * B` on the members give the bound `V * B` on the union. -/
example {σ F X : Type*} [Field F] [Finite σ] (T : Finset (Ideal (MvPolynomial σ F)))
    (S : Ideal (MvPolynomial σ F) → Set X) (B V : ℚ) (hB : 0 ≤ B)
    (hfinite : ∀ i ∈ T, (S i).Finite) (hcard : ∀ i ∈ T, ((S i).ncard : ℚ) ≤ affineDegree i * B)
    (hpotential : ∑ i ∈ T, affineDegree i ≤ V) :
    (⋃ i ∈ T, S i).Finite ∧ (((⋃ i ∈ T, S i).ncard : ℕ) : ℚ) ≤ V * B := by
  obtain ⟨hfin, hsum⟩ := finite_biUnion_and_ncard_le_sum T S _ hfinite hcard
  refine ⟨hfin, hsum.trans ?_⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hpotential hB

end DimensionSensitiveIncidenceTest
