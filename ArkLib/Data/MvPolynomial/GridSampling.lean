/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Anisotropic grid sampling

Scalar samples on a product of finite sets determine a multivariate polynomial when the sum
of its individual degree-to-grid-size ratios is strictly below one. Different variable grids
may have different sizes: a large degree in one variable need not enlarge every other grid.

These are algebraic refinement interfaces for recovering interpolation-constraint coefficients.
They do not implement grid enumeration or matrix solving and make no computational cost claim.
The proof uses Mathlib's degree-sensitive Schwartz--Zippel theorem.
-/

@[expose] public section

namespace MvPolynomial

open scoped BigOperators
open scoped Matrix

variable {F : Type*} [CommRing F] [IsDomain F] {v : ℕ}

/-- A grid whose normalized individual-degree budget is below one detects every nonzero
polynomial satisfying that budget. Every coordinate grid must be nonempty. -/
theorem eq_zero_of_eval_grid_eq_zero (P : MvPolynomial (Fin v) F)
    (grid : Fin v → Finset F) (hne : ∀ i, (grid i).Nonempty)
    (hbudget : (∑ i, (P.degreeOf i / (grid i).card : ℚ≥0)) < 1)
    (hzero : ∀ x ∈ Fintype.piFinset grid, eval x P = 0) : P = 0 := by
  classical
  by_contra hp
  have hbound := schwartz_zippel_sum_degreeOf hp grid
  have hfilter : {x ∈ Fintype.piFinset grid | eval x P = 0} = Fintype.piFinset grid :=
    Finset.filter_eq_self.mpr hzero
  have hprod : (∏ i, ((grid i).card : ℚ≥0)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (hne i).card_pos.ne'
  rw [hfilter, Fintype.card_piFinset] at hbound
  push_cast at hbound
  rw [div_self hprod] at hbound
  exact (not_le_of_gt hbudget) hbound

/-- A shared coordinate-degree budget suffices to compare two sampled polynomials. -/
theorem eq_of_eval_grid_eq (P Q : MvPolynomial (Fin v) F)
    (degreeBudget : Fin v → ℕ) (grid : Fin v → Finset F)
    (hne : ∀ i, (grid i).Nonempty)
    (hP : ∀ i, P.degreeOf i ≤ degreeBudget i)
    (hQ : ∀ i, Q.degreeOf i ≤ degreeBudget i)
    (hbudget : (∑ i, (degreeBudget i / (grid i).card : ℚ≥0)) < 1)
    (heval : ∀ x ∈ Fintype.piFinset grid, eval x P = eval x Q) : P = Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_grid_eq_zero (P - Q) grid hne
  · apply lt_of_le_of_lt _ hbudget
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact (degreeOf_sub_le i P Q).trans (max_le (hP i) (hQ i))
  · intro x hx
    simpa only [map_sub, sub_eq_zero] using heval x hx

/-- The finite-support polynomial represented by a coefficient vector. This is a mathematical
representation map, not an uncharged machine primitive. -/
noncomputable def gridPolynomial (exponents : Finset (Fin v →₀ ℕ))
    (coefficients : exponents → F) : MvPolynomial (Fin v) F :=
  ∑ e : exponents, monomial e.val (coefficients e)

omit [IsDomain F] in
/-- Coefficient coordinates are recovered exactly, even when some input coefficients vanish. -/
theorem coeff_gridPolynomial (exponents : Finset (Fin v →₀ ℕ))
    (coefficients : exponents → F) (e : exponents) :
    coeff e.val (gridPolynomial exponents coefficients) = coefficients e := by
  classical
  rw [gridPolynomial, coeff_sum]
  simp [coeff_monomial]

omit [IsDomain F] in
/-- Finite monomial representation cannot create unsupported exponents. -/
theorem support_gridPolynomial_subset (exponents : Finset (Fin v →₀ ℕ))
    (coefficients : exponents → F) :
    (gridPolynomial exponents coefficients).support ⊆ exponents := by
  classical
  intro e he
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp (support_sum he)
  have heq := Finset.mem_singleton.mp (support_monomial_subset ha)
  exact heq ▸ a.property

omit [IsDomain F] in
/-- The chosen exponent support certifies every coordinate degree of a recovered polynomial. -/
theorem degreeOf_gridPolynomial_le (exponents : Finset (Fin v →₀ ℕ))
    (coefficients : exponents → F) (degreeBudget : Fin v → ℕ)
    (hbound : ∀ e ∈ exponents, ∀ i, e i ≤ degreeBudget i) (i : Fin v) :
    (gridPolynomial exponents coefficients).degreeOf i ≤ degreeBudget i := by
  rw [degreeOf_le_iff]
  intro e he
  exact hbound e (support_gridPolynomial_subset exponents coefficients he) i

/-- Entries of the finite scalar-sampling matrix, with explicit exponent and grid indices. -/
noncomputable def gridMonomialMatrix (grid : Fin v → Finset F)
    (exponents : Finset (Fin v →₀ ℕ)) :
    Matrix (Fintype.piFinset grid) exponents F :=
  fun x e ↦ e.val.prod fun i n ↦ x.val i ^ n

omit [IsDomain F] in
/-- Matrix-vector multiplication is exactly evaluation of the represented polynomial. -/
theorem gridMonomialMatrix_mulVec (grid : Fin v → Finset F)
    (exponents : Finset (Fin v →₀ ℕ)) (coefficients : exponents → F) :
    gridMonomialMatrix grid exponents *ᵥ coefficients =
      fun x ↦ eval x.val (gridPolynomial exponents coefficients) := by
  classical
  funext x
  simp only [gridMonomialMatrix, Matrix.mulVec, dotProduct, gridPolynomial, map_sum,
    eval_monomial]
  exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)

/-- The grid matrix has a trivial kernel under the explicit coordinate-degree budget.
This certifies unique coefficient recovery, without presupposing any particular solver. -/
theorem gridMonomialMatrix_mulVec_injective (grid : Fin v → Finset F)
    (exponents : Finset (Fin v →₀ ℕ)) (degreeBudget : Fin v → ℕ)
    (hne : ∀ i, (grid i).Nonempty)
    (hbound : ∀ e ∈ exponents, ∀ i, e i ≤ degreeBudget i)
    (hbudget : (∑ i, (degreeBudget i / (grid i).card : ℚ≥0)) < 1) :
    Function.Injective (fun coefficients ↦ gridMonomialMatrix grid exponents *ᵥ coefficients) := by
  intro a b hab
  have hpoly : gridPolynomial exponents a = gridPolynomial exponents b := by
    apply eq_of_eval_grid_eq _ _ degreeBudget grid hne
      (degreeOf_gridPolynomial_le exponents a degreeBudget hbound)
      (degreeOf_gridPolynomial_le exponents b degreeBudget hbound) hbudget
    intro x hx
    have h := congrFun hab ⟨x, hx⟩
    simpa only [gridMonomialMatrix_mulVec] using h
  funext e
  simpa only [coeff_gridPolynomial] using congrArg (coeff e.val) hpoly

/-- With displacement degree below `L` and `s` other degrees at most `B`, grids of sizes
`2L` and `2sB+1` meet the strict normalized budget. This is a numerical certificate, not
an uncharged construction of the grids. -/
theorem anisotropic_sampling_budget_lt_one (s B L : ℕ) (hL : 0 < L) :
    ((L - 1 : ℕ) : ℚ≥0) / (2 * L) +
      (s : ℚ≥0) * (B / (2 * (s : ℚ≥0) * B + 1)) < 1 := by
  have hL' : (0 : ℚ≥0) < L := by exact_mod_cast hL
  have hsub : ((L - 1 : ℕ) : ℚ≥0) ≤ L := by exact_mod_cast Nat.sub_le L 1
  have hhalf : (1 / 2 : ℚ≥0) * 2 = 1 := by norm_num
  have hfirst : ((L - 1 : ℕ) : ℚ≥0) / (2 * L) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [← mul_assoc, hhalf, one_mul]
    exact hsub
  have hsecond : (s : ℚ≥0) * (B / (2 * (s : ℚ≥0) * B + 1)) < 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity)).mpr
    rw [mul_add, ← mul_assoc, ← mul_assoc, hhalf, one_mul, mul_one]
    exact lt_add_of_pos_right _ (by norm_num)
  calc
    _ < (1 / 2 : ℚ≥0) + 1 / 2 := add_lt_add_of_le_of_lt hfirst hsecond
    _ = 1 := by norm_num

/-- The two proposed local sampling-grid sizes fit the quadratic witness field under explicit
block and derivative/multiplicity hypotheses. Cardinality, not characteristic, is used here. -/
theorem anisotropic_sampling_sizes_le_square (d m A n q : ℕ)
    (hm : 0 < m) (hd : d + 1 ≤ m) (hn : 8 * m ≤ n) (hA : A ≤ n) (hq : n ≤ q) :
    2 * (m * A) ≤ q ^ 2 ∧ 2 * (d + 1) * (2 * m) + 1 ≤ q ^ 2 := by
  constructor
  · nlinarith
  · nlinarith

end MvPolynomial
