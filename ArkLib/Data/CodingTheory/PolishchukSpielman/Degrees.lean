/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.UniqueFactorization

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

open Polynomial.Bivariate Polynomial Finset
open scoped BigOperators

lemma ps_bx_lt_nx {b_x b_y : ℕ} {n_x n_y : ℕ+}
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_x < (n_x : ℕ) := by
  contrapose! h_le_1;
  exact le_add_of_le_of_nonneg
    (by rw [le_div_iff₀ (Nat.cast_pos.mpr n_x.pos )]; norm_cast; linarith) (by positivity)

lemma ps_by_lt_ny {b_x b_y : ℕ} {n_x n_y : ℕ+}
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_y < (n_y : ℕ) := by
  exact_mod_cast
    (by nlinarith [show (0 : ℚ) ≤ b_x / (n_x : ℚ) by positivity,
    show (0 : ℚ) ≤ b_y / (n_y : ℚ) by positivity,
      mul_div_cancel₀ (b_x : ℚ) (show (n_x : ℚ) ≠ 0 by positivity),
      mul_div_cancel₀ (b_y : ℚ) (show (n_y : ℚ) ≠ 0 by positivity),
      show (n_x : ℚ) > 0 by positivity, show (n_y : ℚ) > 0 by positivity] : (b_y : ℚ) < n_y)

lemma ps_card_eval_x_eq_zero_le_degree_x {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun x ↦ evalX x A = 0)).card ≤ degreeX A := by
  by_contra! h_contra;
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, (A.coeff j₀).natDegree = degreeX A ∧ A.coeff j₀ ≠ 0 := by
    have h_exists_j₀ : ∃ j₀ ∈ A.support, ∀ n ∈ A.support,
        (A.coeff n).natDegree ≤ (A.coeff j₀).natDegree := by
      exact exists_max_image _ _ (nonempty_of_ne_empty (by aesop))
    obtain ⟨j₀, hj₀₁, hj₀₂⟩ := h_exists_j₀
    exact ⟨j₀, le_antisymm (le_sup (f := fun n ↦ (A.coeff n).natDegree) hj₀₁)
      (Finset.sup_le fun n hn ↦ hj₀₂ n hn), by aesop⟩
  -- Let $P_A$ be the set of $x \in P$ such that $A(x, Y) = 0$.
  set PA := P.filter (fun x ↦ evalX x A = 0) with hPA_def;
  have h_coeff_zero : ∀ x ∈ PA, (A.coeff j₀).eval x = 0 := by
    intro x hx
    replace hx := congr_arg (fun f ↦ f.coeff j₀) (mem_filter.mp hx |>.2)
    aesop
  exact absurd (Finset.card_le_card
    (show PA ⊆ ((A.coeff j₀).roots.toFinset) from fun x hx ↦ by aesop))
    (by exact not_le.mpr <| lt_of_le_of_lt (Multiset.toFinset_card_le _) <|
      Nat.lt_of_le_of_lt (card_roots' _) <| by aesop)

lemma ps_card_eval_y_eq_zero_le_nat_degree_y {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun y ↦ evalY y A = 0)).card ≤ natDegreeY A := by
  set A_poly : Polynomial (Polynomial F) := A
  have hA_poly : A_poly ≠ 0 := by assumption
  have h_roots : ((P.filter <| fun y ↦ A_poly.eval (C y) = 0).image (fun y ↦ C y)).card ≤
      A_poly.natDegree := by
    have h_roots : (P.filter (fun y ↦ A_poly.eval (C y) = 0)).image (fun y ↦ C y) ⊆
        A_poly.roots.toFinset := by intro; aesop
    exact le_trans (card_le_card h_roots)
      (le_trans (Multiset.toFinset_card_le _) (card_roots' _)) |> le_trans <| by aesop
  generalize_proofs at *
  rw [Finset.card_image_of_injective _ fun x y hxy ↦ by simpa using hxy] at h_roots
  aesop

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
  simp [Finset.mul_sum, finset_sum_coeff, ps_coeff_mul_monomial_ite]
  grind only [cases Or]

private lemma ps_swap_coeff {F : Type} [CommRing F] (g : F[X][Y]) (i j : ℕ) :
    Bivariate.coeff (swap g) i j = Bivariate.coeff g j i := by
  have h_swap_coeff : ∀ (g : F[X][Y]) (i j : ℕ),
      Bivariate.coeff (swap g) i j = Bivariate.coeff g j i := by
    unfold Bivariate.coeff
    -- By definition of swap, we have that swap g = ∑ i, ∑ j, g.coeff j * X^i * Y^j.
    have h_swap_def : ∀ g : F[X][Y], swap g = ∑ i ∈ g.support,
        ∑ j ∈ (g.coeff i).support, monomial j (monomial i ((g.coeff i).coeff j)) := by
      intro g
      simp [swap, eval_finset_sum, aeval_def, eval₂_eq_sum, sum_def,
        ← C_mul_X_pow_eq_monomial, Finset.sum_mul _ _ _ ]
      ac_rfl
    simp only [h_swap_def, finset_sum_coeff, coeff_monomial, sum_ite_eq', mem_support_iff, ne_eq]
    intro g i j
    rw [Finset.sum_eq_single i] <;> simp_all only [swap_apply, mem_support_iff, ne_eq]
    · split_ifs <;> simp_all
    · intro b hb hb'; split_ifs <;> simp_all [coeff_monomial]
    · push Not; intro h; simp [h]
  exact h_swap_coeff g i j

private lemma ps_degree_x_swap_le {F : Type} [CommRing F] (f : F[X][Y]) :
    degreeX (swap f) ≤ natDegreeY f := by
  by_contra h_contra
  obtain ⟨n, hn⟩ : ∃ n ∈ (swap f).support,
      (swap f).coeff n ≠ 0 ∧ (swap f).coeff n ≠ 0 ∧ ((swap f).coeff n).natDegree > f.natDegree := by
    unfold degreeX at h_contra; aesop;
  obtain ⟨m, hm⟩ : ∃ m > f.natDegree, ((swap f).coeff n).coeff m ≠ 0 := by
    exact ⟨((swap f).coeff n).natDegree, hn.2.2.2, by aesop⟩
  have h_coeff_swap : ((swap f).coeff n).coeff m = (f.coeff m).coeff n := by
    convert ps_swap_coeff f m n using 1
  exact hm.2 (h_coeff_swap.symm ▸ by rw [coeff_eq_zero_of_natDegree_lt hm.1]; aesop)

private lemma ps_degree_x_swap_ge {F : Type} [CommRing F] (f : F[X][Y]) (hf : f ≠ 0) :
    natDegreeY f ≤ degreeX (swap f) := by
  obtain ⟨N, hN⟩ : ∃ N, N = f.natDegree ∧ f.coeff N ≠ 0 := by
    simp_all only [ne_eq, ↓existsAndEq, coeff_natDegree, leadingCoeff_eq_zero,
      not_false_eq_true, and_self]
  obtain ⟨n, hn⟩ : ∃ n, n = (f.coeff N).natDegree ∧ (f.coeff N).coeff n ≠ 0 := by
    contrapose! hN; aesop;
  have h_swap_coeff_nonzero : ((swap f).coeff n).coeff N ≠ 0 := by
    convert hn.2 using 1;
    convert ps_swap_coeff f N n using 1
  have h_swap_coeff_nonzero_natDegree : (swap f).coeff n ≠ 0 :=
    (ne_of_apply_ne Polynomial.coeff fun a ↦ h_swap_coeff_nonzero (congrFun a.symm N)).symm
  have h_swap_coeff_nonzero_natDegree_le : Nat.max (((swap f).coeff n).natDegree)
      (Nat.max (((swap f).coeff n).natDegree) N) ≤ degreeX (swap f) := by
    refine le_trans ?_ (Finset.le_sup <| show n ∈ ((swap f).support) from ?_) <;>
      simp_all only [ne_eq, ext_iff, coeff_zero, not_forall, coeff_natDegree, swap_apply,
        le_sup_left, sup_of_le_right, sup_le_iff, le_refl, true_and]
    · exact le_natDegree_of_ne_zero h_swap_coeff_nonzero |> le_trans (by aesop)
    · aesop
  have h_swap_coeff_nonzero_natDegree_le_natDegreeY : N ≤ Nat.max (((swap f).coeff n).natDegree)
      (Nat.max (((swap f).coeff n).natDegree) N) := le_max_of_le_right (le_max_right _ _)
  have h_final : f.natDegree ≤ degreeX (swap f) := by
    bv_omega
  exact h_final

lemma ps_degree_x_swap {F : Type} [CommRing F] (f : F[X][Y]) :
    degreeX (swap f) = natDegreeY f := by
  by_cases hf : f = 0
  · subst hf; simp [degreeX, natDegreeY]
  · exact le_antisymm (ps_degree_x_swap_le f) (ps_degree_x_swap_ge f hf)

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
  letI : Algebra F[X] F[X] := Polynomial.algebra (R := F) (A := F)
  convert aveal_eq_map_swap y f using 1
  · unfold evalY; simp [Polynomial.aeval_def]
  · -- By definition of `evalX`, we have `evalX y (swap f) = (swap f).map (evalRingHom y)`.
    rw [ps_eval_x_eq_map]
    rfl

lemma ps_exists_x_preserve_nat_degree_y {F : Type} [Field F]
    (B : F[X][Y]) (hB : B ≠ 0) (P_x : Finset F)
    (hcard : P_x.card > degreeX B) :
    ∃ x ∈ P_x, (evalX x B).natDegree = natDegreeY B := by
  obtain ⟨x, hx⟩ : ∃ x ∈ P_x, (B.coeff (natDegreeY B)).eval x ≠ 0 := by
    have h_p_ne_zero : natDegree (B.coeff (natDegreeY B)) < P_x.card := by
      exact lt_of_le_of_lt
        (Finset.le_sup (f := fun n ↦ (B.coeff n).natDegree)
          (natDegree_mem_support_of_nonzero hB))
        hcard
    by_contra h_contra; push Not at h_contra
    have h_poly_zero : leadingCoeffY B = 0 :=
      eq_zero_of_degree_lt_of_eval_finset_eq_zero P_x
        (degree_le_natDegree.trans_lt (by exact_mod_cast h_p_ne_zero))
        h_contra
    exact absurd h_poly_zero (leadingCoeffY_ne_zero _ |>.2 hB)
  refine ⟨x, hx.1, le_antisymm ?_ ?_⟩
  · rw [evalX]
    simp only [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt,
      coeff_ofFinsupp, Finsupp.mapRange_apply]
    intro m hm
    rw [toFinsupp_apply, coeff_eq_zero_of_natDegree_lt hm]
    simp
  · refine le_natDegree_of_ne_zero ?_
    convert hx.2 using 1

lemma ps_exists_y_preserve_degree_x {F : Type} [Field F]
    (B : F[X][Y]) (hB : B ≠ 0) (P_y : Finset F) (hcard : P_y.card > natDegreeY B) :
    ∃ y ∈ P_y, (evalY y B).natDegree = degreeX B := by
  revert B hB P_y hcard;
  intro B hB P_y hcard
  set d := degreeX B with hd
  set g := B.sum (fun j p ↦ Polynomial.monomial j (p.coeff d)) with hg
  have hg_ne_zero : g ≠ 0 := by
    obtain ⟨j0, hj0⟩ : ∃ j0 ∈ B.support, (B.coeff j0).natDegree = d := by
      have h_sup : ∃ j0 ∈ B.support, ∀ j ∈ B.support,
          (B.coeff j).natDegree ≤ (B.coeff j0).natDegree := by
        apply_rules [Finset.exists_max_image]; aesop
      generalize_proofs at *; (
      exact ⟨h_sup.choose, h_sup.choose_spec.1, le_antisymm
        (Finset.le_sup (f := fun j ↦ (B.coeff j).natDegree) h_sup.choose_spec.1)
        (Finset.sup_le fun j hj ↦ h_sup.choose_spec.2 j hj)⟩)
    have h_nonzero_term : (B.coeff j0).coeff d ≠ 0 := by
      rw [← hj0.2, coeff_natDegree]; aesop
    have h_g_nonzero : g.coeff j0 = (B.coeff j0).coeff d := by
      simp only [coeff_sum, coeff_monomial, hg, hd]
      rw [sum_def]
      aesop
    exact fun h ↦ h_nonzero_term (by rw [← h_g_nonzero, h, coeff_zero])
  have hg_natDegree : natDegree g ≤ natDegreeY B := by
    refine le_trans (natDegree_sum_le _ _) (Finset.sup_le ?_)
    intro j hj
    exact (natDegree_monomial_le _).trans (le_natDegree_of_mem_supp _ hj)
  have hg_eval_nonzero : ∃ y ∈ P_y, g.eval y ≠ 0 := by
    by_contra! hcard_contra
    exact hg_ne_zero (eq_zero_of_degree_lt_of_eval_finset_eq_zero P_y
      (degree_le_natDegree.trans_lt (by exact_mod_cast lt_of_le_of_lt hg_natDegree hcard))
      hcard_contra)
  obtain ⟨y, hy⟩ := hg_eval_nonzero
  use y, hy.left
  have h_deg_y : (evalY y B).natDegree ≤ d := by
    have h_deg_y : ∀ j ∈ B.support, natDegree (B.coeff j) ≤ d :=
      fun j hj ↦ Finset.le_sup (f := fun n ↦ (B.coeff n).natDegree) hj
    rw [evalY, eval_eq_sum, sum_def]
    exact le_trans
      (natDegree_sum_le _ _) (Finset.sup_le fun i hi ↦ le_trans (natDegree_mul_le ..) (by aesop))
  have h_deg_y_eq : (evalY y B).coeff d = g.eval y := by
    simp only [sum_def, eval_finset_sum, eval_monomial, g]
    unfold evalY
    simp only [eval_eq_sum, sum_def, finset_sum_coeff]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    induction i <;> simp_all [coeff_mul, coeff_C, pow_succ'] ; ring_nf
    rw [sum_eq_single (degreeX B, 0)] <;> simp only [mem_antidiagonal, ne_eq,
      Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one, sum_ite_eq', mem_range,
      Order.lt_add_one_iff, zero_le, ↓reduceIte, tsub_zero, mul_eq_zero, Prod.forall, Prod.mk.injEq,
      not_and]
    all_goals ring_nf
    · simp [coeff_zero_eq_eval_zero, eval_pow, eval_C]
    · intro a b hab h; rcases b with (_ | b) <;> simp_all [coeff_eq_zero_of_natDegree_lt]
    · aesop
  exact le_antisymm h_deg_y (le_natDegree_of_ne_zero (by aesop))

lemma ps_filter_nonzero_card_y {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P_y : Finset F) (bound : ℕ)
    (h_bound_ge : bound ≥ natDegreeY A)
    (h_card_gt : P_y.card > bound) :
    (P_y.filter (fun y ↦ evalY y A ≠ 0)).card > bound - natDegreeY A := by
  have := ps_card_eval_y_eq_zero_le_nat_degree_y A hA P_y;
  simp_all only [ne_eq, ge_iff_le, gt_iff_lt, Finset.filter_not, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)] ; omega

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
  by_contra h_contra
  obtain ⟨y, hy⟩ : ∃ y ∈ P_y, (evalY y P).natDegree = degreeX P ∧ evalY y A ≠ 0 := by
    have h_card_filter : (P_y.filter (fun y ↦ evalY y A ≠ 0)).card > natDegreeY P := by
      have h_filter_card : (P_y.filter (fun y ↦ evalY y A ≠ 0)).card > b_y - natDegreeY A := by
        apply_rules [ps_filter_nonzero_card_y]
        all_goals linarith
      grind +qlia
    have := ps_exists_y_preserve_degree_x P hP (P_y.filter (fun y ↦ evalY y A ≠ 0)) ?_ <;> aesop
  -- Since $B = P * A$, we have $evalY y B = evalY y P * evalY y A$.
  have h_eval_Y_B : evalY y B = evalY y P * evalY y A := by unfold evalY; aesop
  have := h_quot_x y hy.1
  simp_all
  linarith

lemma ps_degY_bound {F : Type} [Field F]
    {A B P : F[X][Y]} (hA : A ≠ 0) (hP : P ≠ 0) (hBA : B = P * A)
    (b_x b_y a_x a_y : ℕ) (n_x : ℕ+) (h_bx_ge_ax : b_x ≥ a_x)
    (h_f_degX : a_x ≥ degreeX A) (h_g_degY : b_y ≥ natDegreeY B)
    (P_x : Finset F) (h_card_Px : n_x ≤ P_x.card) (quot_y : F → F[X])
    (h_quot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ b_y - a_y ∧ evalX x B = (quot_y x) * (evalX x A))
    (h_bx_lt_nx : b_x < (n_x : ℕ)) (hdegX_P_le : degreeX P ≤ b_x - a_x) :
    natDegreeY P ≤ b_y - a_y := by
  classical
  obtain ⟨x, hx⟩ : ∃ x ∈ P_x, (evalX x A) ≠ 0 ∧ (evalX x P).natDegree = natDegreeY P := by
    have h_filter : (P_x.filter (fun x ↦ (evalX x A) ≠ 0)).card > (degreeX P) := by
      have := ps_filter_nonzero_card_x A hA P_x b_x (by linarith) (by linarith); simp_all; omega
    obtain ⟨x, hx⟩ : ∃ x ∈ P_x.filter (fun x ↦ (evalX x A) ≠ 0),
        (evalX x P).natDegree = (natDegreeY P) := by apply_rules [ps_exists_x_preserve_nat_degree_y]
    aesop
  -- Since $evalX x B = quot_y x * evalX x A$, we have $evalX x P = quot_y x$.
  have h_evalX_P : evalX x P = quot_y x := by
    have h_evalX_P : evalX x B = evalX x P * evalX x A := by rw [hBA, evalX_mul]
    exact mul_left_cancel₀ hx.2.1 <| by
      linear_combination h_evalX_P.symm.trans (h_quot_y x hx.1 |>.2)
  exact hx.2.2 ▸ h_evalX_P ▸ h_quot_y x hx.1 |>.1

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
  letI : DecidableEq F := Classical.decEq F
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
    h ((map_dvd_iff f).1 (by simpa [f] using hdA)) ((map_dvd_iff f).1 (by simpa [f] using hdB))
  have : IsUnit (f (f.symm d)) := f.toRingHom.isUnit_map hunit
  simpa [f] using this

lemma ps_nat_degree_y_swap {F : Type} [CommRing F]
    (f : F[X][Y]) : natDegreeY (swap f) = degreeX f := by
  have h := ps_degree_x_swap (swap f)
  have hs : swap (swap f) = f := swap.left_inv f
  rw [hs] at h
  exact h.symm
