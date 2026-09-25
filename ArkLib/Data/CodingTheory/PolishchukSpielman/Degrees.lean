/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/
module

public import ArkLib.Data.Polynomial.Bivariate
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Degree bounds for Polishchuk-Spielman

This file contains auxiliary lemmas regarding degree bounds, evaluation, and
variable swapping for bivariate polynomials, used in the Polishchuk-Spielman
lemma [BCIKS20].

## Main results

- `ps_bx_lt_nx`, `ps_by_lt_ny`: Bounds on the degrees parameters.
- `ps_card_eval_x_eq_zero_le_degree_x`, `ps_card_eval_y_eq_zero_le_nat_degree_y`:
  Bounds on the number of roots of a bivariate polynomial on lines.
- `ps_eval_y_eq_eval_x_swap`: Relates evaluation in Y to evaluation in X of the swapped polynomial.
- `ps_exists_x_preserve_nat_degree_y`, `ps_exists_y_preserve_degree_x`:
  Existence of evaluation points preserving the degree.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]

-/

@[expose] public section

open Polynomial.Bivariate Polynomial Finset
open scoped BigOperators

lemma ps_bx_lt_nx {b_x b_y : ℕ} {n_x n_y : ℕ+}
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_x < (n_x : ℕ) := by
  contrapose! h_le_1;
  exact le_add_of_le_of_nonneg
    (by rw [le_div_iff₀ (Nat.cast_pos.mpr n_x.pos )]; norm_cast; linarith) (by positivity)

lemma ps_by_lt_ny {b_x b_y : ℕ} {n_x n_y : ℕ+}
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_y < (n_y : ℕ) :=
  ps_bx_lt_nx (b_y := b_x) (n_y := n_x) (by rwa [add_comm])

lemma ps_card_eval_x_eq_zero_le_degree_x {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun x ↦ evalX x A = 0)).card ≤ degreeX A :=
  card_evalX_eq_zero_le_degreeX A hA P

lemma ps_card_eval_y_eq_zero_le_nat_degree_y {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun y ↦ evalY y A = 0)).card ≤ natDegreeY A := by
  calc (P.filter (fun y ↦ evalY y A = 0)).card
      = (P.filter (fun y ↦ evalX y (swap A) = 0)).card := by simp_rw [evalY_eq_evalX_swap]
    _ ≤ degreeX (swap A) :=
      card_evalX_eq_zero_le_degreeX (swap A) (EmbeddingLike.map_ne_zero_iff.mpr hA) P
    _ = natDegreeY A := degreeX_swap A

lemma ps_coeff_mul_monomial_ite {R : Type} [Semiring R]
    (A : R[X]) (j i : ℕ) (r : R) :
    (A * Polynomial.monomial j r).coeff i =
      if j ≤ i then A.coeff (i - j) * r else 0 := by
  classical
  simp [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

lemma ps_coeff_mul_sum_monomial {R : Type} [CommRing R]
    (A : R[X]) (m n : ℕ) (hm : A.natDegree ≤ m)
    (c : Fin n → R) (i : ℕ) :
    (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j))).coeff i =
      ∑ j : Fin n,
        if (j : ℕ) ≤ i ∧ i ≤ (j : ℕ) + m
        then A.coeff (i - (j : ℕ)) * c j else 0 := by
  classical
  have hdeg : ∀ N : ℕ, m < N → A.coeff N = 0 := (natDegree_le_iff_coeff_eq_zero).1 hm
  rw [Finset.mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ps_coeff_mul_monomial_ite]
  by_cases h1 : (j : ℕ) ≤ i
  · by_cases h2 : i ≤ (j : ℕ) + m
    · rw [ite_eq_left h1, ite_eq_left ⟨h1, h2⟩]
    · rw [ite_eq_left h1, ite_eq_right fun h ↦ h2 h.2, hdeg _ (by omega), zero_mul]
  · rw [ite_eq_right h1, ite_eq_right fun h ↦ h1 h.1]

lemma ps_degree_x_swap {F : Type} [CommRing F] (f : F[X][Y]) :
    degreeX (swap f) = natDegreeY f :=
  degreeX_swap f

lemma ps_descend_eval_x {F : Type} [Field F]
    {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
    (x : F) (hx : evalX x G ≠ 0) (q : F[X]) (h : evalX x B = q * evalX x A) :
    evalX x B1 = q * evalX x A1 := by
  simp_all only [evalX_eq_map, ne_eq, Polynomial.map_mul]
  exact mul_left_cancel₀ hx <| by linear_combination h;

lemma ps_descend_eval_y {F : Type} [Field F]
    {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
    (y : F) (hy : evalY y G ≠ 0) (q : F[X]) (h : evalY y B = q * evalY y A) :
    evalY y B1 = q * evalY y A1 := by
  unfold evalY at *
  simp_all only [ne_eq, eval_mul]
  exact mul_left_cancel₀ hy <| by linear_combination h

lemma ps_eval_x_eq_map {F : Type} [CommSemiring F]
    (x : F) (f : F[X][Y]) :
    evalX x f = f.map (evalRingHom x) := by
  classical
  ext n; simp [evalX, toFinsupp_apply]

lemma ps_eval_y_eq_eval_x_swap {F : Type} [CommRing F]
    (y : F) (f : F[X][Y]) :
    evalY y f = evalX y (swap f) := by
  let : Algebra F[X] F[X] := Polynomial.algebra (R := F) (A := F)
  convert aveal_eq_map_swap y f using 1
  · unfold evalY; simp [Polynomial.aeval_def]
  · -- By definition of `evalX`, we have `evalX y (swap f) = (swap f).map (evalRingHom y)`.
    rw [ps_eval_x_eq_map]
    rfl

lemma ps_exists_x_preserve_nat_degree_y {F : Type} [Field F]
    (B : F[X][Y]) (hB : B ≠ 0) (P_x : Finset F)
    (hcard : P_x.card > degreeX B) :
    ∃ x ∈ P_x, (evalX x B).natDegree = natDegreeY B := by
  classical
  exact exists_x_preserve_natDegreeY B hB P_x hcard

lemma ps_exists_y_preserve_degree_x {F : Type} [Field F]
    (B : F[X][Y]) (hB : B ≠ 0) (P_y : Finset F) (hcard : P_y.card > natDegreeY B) :
    ∃ y ∈ P_y, (evalY y B).natDegree = degreeX B := by
  classical
  obtain ⟨y, hy, hdeg⟩ := exists_x_preserve_natDegreeY (swap B)
    (EmbeddingLike.map_ne_zero_iff.mpr hB) P_y (by rwa [degreeX_swap])
  exact ⟨y, hy, by rw [evalY_eq_evalX_swap, hdeg, natDegreeY_swap]⟩

lemma ps_filter_nonzero_card_y {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P_y : Finset F) (bound : ℕ)
    (h_bound_ge : bound ≥ natDegreeY A)
    (h_card_gt : P_y.card > bound) :
    (P_y.filter (fun y ↦ evalY y A ≠ 0)).card > bound - natDegreeY A := by
  have := ps_card_eval_y_eq_zero_le_nat_degree_y A hA P_y;
  simp_all only [ne_eq, ge_iff_le, gt_iff_lt, Finset.filter_not, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]; omega

lemma ps_filter_nonzero_card_x {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P_x : Finset F) (bound : ℕ)
    (h_bound_ge : bound ≥ degreeX A)
    (h_card_gt : P_x.card > bound) :
    (P_x.filter (fun x ↦ evalX x A ≠ 0)).card > bound - degreeX A := by
  have h_card_splits : P_x.card =
      (P_x.filter (fun x ↦ evalX x A = 0)).card + (P_x.filter (fun x ↦ evalX x A ≠ 0)).card := by
    rw [Finset.card_filter_add_card_filter_not]
  linarith [ps_card_eval_x_eq_zero_le_degree_x A hA P_x,
    Nat.sub_add_cancel (show degreeX A ≤ bound from h_bound_ge)]

lemma ps_degX_bound {F : Type} [Field F]
    {A B P : F[X][Y]} (hA : A ≠ 0) (hP : P ≠ 0) (hBA : B = P * A)
    (b_x b_y a_x a_y : ℕ) (n_y : ℕ+) (h_by_ge_ay : b_y ≥ a_y)
    (h_f_degY : a_y ≥ natDegreeY A) (h_g_degY : b_y ≥ natDegreeY B)
    (P_y : Finset F) (h_card_Py : n_y ≤ P_y.card) (quot_x : F → F[X])
    (h_quot_x : ∀ y ∈ P_y, (quot_x y).natDegree ≤ b_x - a_x ∧ evalY y B = (quot_x y) * (evalY y A))
    (h_by_lt_ny : b_y < n_y) :
    degreeX P ≤ b_x - a_x := by
  classical
  have hdegB : natDegreeY B = natDegreeY P + natDegreeY A := hBA ▸ natDegree_mul hP hA
  have h_card : natDegreeY P < (P_y.filter (fun y ↦ evalY y A ≠ 0)).card := by
    have := ps_filter_nonzero_card_y A hA P_y b_y (h_f_degY.trans h_by_ge_ay) (by omega)
    omega
  obtain ⟨y, hy, hdeg⟩ := ps_exists_y_preserve_degree_x P hP _ h_card
  obtain ⟨hyP, hyA⟩ := Finset.mem_filter.1 hy
  -- Since $B = P * A$, we have $evalY y B = evalY y P * evalY y A$.
  have h_eval_Y_B : evalY y B = evalY y P * evalY y A := by rw [hBA, evalY, eval_mul]; rfl
  have h_eval_Y_P : evalY y P = quot_x y :=
    mul_right_cancel₀ hyA (h_eval_Y_B.symm.trans (h_quot_x y hyP).2)
  exact hdeg ▸ h_eval_Y_P ▸ (h_quot_x y hyP).1

lemma ps_degY_bound {F : Type} [Field F]
    {A B P : F[X][Y]} (hA : A ≠ 0) (hP : P ≠ 0) (hBA : B = P * A)
    (b_x b_y a_x a_y : ℕ) (n_x : ℕ+) (h_bx_ge_ax : b_x ≥ a_x)
    (h_f_degX : a_x ≥ degreeX A) (_h_g_degY : b_y ≥ natDegreeY B)
    (P_x : Finset F) (h_card_Px : n_x ≤ P_x.card) (quot_y : F → F[X])
    (h_quot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ b_y - a_y ∧ evalX x B = (quot_y x) * (evalX x A))
    (h_bx_lt_nx : b_x < (n_x : ℕ)) (hdegX_P_le : degreeX P ≤ b_x - a_x) :
    natDegreeY P ≤ b_y - a_y := by
  classical
  have h_filter : degreeX P < (P_x.filter (fun x ↦ evalX x A ≠ 0)).card := by
    have := ps_filter_nonzero_card_x A hA P_x b_x (h_f_degX.trans h_bx_ge_ax) (by omega)
    omega
  obtain ⟨x, hx, hdeg⟩ := ps_exists_x_preserve_nat_degree_y P hP _ h_filter
  obtain ⟨hxP, hxA⟩ := Finset.mem_filter.1 hx
  -- Since $evalX x B = quot_y x * evalX x A$, we have $evalX x P = quot_y x$.
  have h_evalX_P : evalX x P = quot_y x := by
    have h_evalX_P : evalX x B = evalX x P * evalX x A := by rw [hBA, evalX_mul]
    exact mul_right_cancel₀ hxA (h_evalX_P.symm.trans (h_quot_y x hxP).2)
  exact hdeg ▸ h_evalX_P ▸ (h_quot_y x hxP).1

lemma ps_degree_bounds_of_mul {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    {A B P : F[X][Y]} (hA : A ≠ 0) (hBA : B = P * A)
    (h_f_degX : a_x ≥ degreeX A) (h_f_degY : a_y ≥ natDegreeY A)
    (h_g_degY : b_y ≥ natDegreeY B) (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x : F → F[X]) (quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y, (quot_x y).natDegree ≤ b_x - a_x ∧ evalY y B = (quot_x y) * (evalY y A))
    (h_quot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ b_y - a_y ∧ evalX x B = (quot_y x) * (evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    degreeX P ≤ b_x - a_x ∧ natDegreeY P ≤ b_y - a_y := by
  classical
  let : DecidableEq F := Classical.decEq F
  by_cases hB0 : B = 0
  · have hP0 : P = 0 := by
      rcases mul_eq_zero.mp (hBA ▸ hB0 : P * A = 0) with h | h
      · exact h
      · exact absurd h hA
    subst hP0
    constructor <;> simp [degreeX, natDegreeY]
  · have hP : P ≠ 0 := fun h ↦ hB0 (by simp [hBA, h])
    have hdegX := ps_degX_bound hA hP hBA b_x b_y a_x a_y n_y h_by_ge_ay
      h_f_degY h_g_degY P_y h_card_Py quot_x h_quot_x (ps_by_lt_ny h_le_1)
    exact ⟨hdegX, ps_degY_bound hA hP hBA b_x b_y a_x a_y n_x h_bx_ge_ax
      h_f_degX h_g_degY P_x h_card_Px quot_y h_quot_y (ps_bx_lt_nx h_le_1) hdegX⟩

lemma ps_gcd_decompose {F : Type} [Field F]
    {A B : F[X][Y]} (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ G A1 B1 : F[X][Y],
      A = G * A1 ∧ B = G * B1 ∧ IsRelPrime A1 B1 ∧ A1 ≠ 0 ∧ B1 ≠ 0 := by
  have h_ufd : GCDMonoid (F[X][Y]) := UniqueFactorizationMonoid.toGCDMonoid F[X][Y]
  obtain ⟨G, hG⟩ : ∃ G : F[X][Y], G ∣ A ∧ G ∣ B ∧ ∀ C : F[X][Y], C ∣ A → C ∣ B → C ∣ G :=
    ⟨GCDMonoid.gcd A B, GCDMonoid.gcd_dvd_left A B,
      GCDMonoid.gcd_dvd_right A B, fun C h₁ h₂ ↦ GCDMonoid.dvd_gcd h₁ h₂⟩
  obtain ⟨A1, hA1⟩ := hG.left
  obtain ⟨B1, hB1⟩ := hG.right.left
  refine ⟨G, A1, B1, hA1, hB1, ?_, ?_, ?_⟩ <;>
    simp_all only [ne_eq, mul_eq_zero, not_or, false_or, dvd_mul_right, true_and, IsRelPrime]
  · intro d hd1 hd2
    specialize hG (G * d)
    simp_all only [ne_eq, not_false_eq_true, mul_dvd_mul_iff_left, forall_const]
    exact isUnit_of_dvd_one (by
    obtain ⟨k, hk⟩ := hG
    exact ⟨k, mul_left_cancel₀ hA.1 <| by linear_combination hk⟩)
  all_goals push Not

lemma ps_is_rel_prime_swap {F : Type} [CommRing F] {A B : F[X][Y]}
    (h : IsRelPrime A B) : IsRelPrime (swap A) (swap B) := by
  classical
  let f : F[X][Y] ≃+* F[X][Y] := swap.toRingEquiv
  refine fun d hdA hdB ↦ ?_
  have hunit : IsUnit (f.symm d) :=
    h ((map_dvd_iff f).1 (by rw [RingEquiv.apply_symm_apply]; exact hdA))
      ((map_dvd_iff f).1 (by rw [RingEquiv.apply_symm_apply]; exact hdB))
  have : IsUnit (f (f.symm d)) := f.toRingHom.isUnit_map hunit
  simpa [f] using this

lemma ps_nat_degree_y_swap {F : Type} [CommRing F]
    (f : F[X][Y]) : natDegreeY (swap f) = degreeX f := by
  have h := ps_degree_x_swap (swap f)
  have hs : swap (swap f) = f := swap.left_inv f
  rw [hs] at h
  exact h.symm
