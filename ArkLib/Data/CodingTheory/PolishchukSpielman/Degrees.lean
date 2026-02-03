/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleModule.Basic

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
- `ps_exists_x_preserve_nat_degree_y`, `ps_exists_y_preserve_degree_x`: Existence of evaluation points
  preserving the degree.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]

-/

open Polynomial.Bivariate Polynomial
open scoped BigOperators

lemma ps_bx_lt_nx {b_x b_y : ℕ} {n_x n_y : ℕ+}
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_x < (n_x : ℕ) := by
  have hby_nonneg : (0 : ℚ) ≤ (b_y : ℚ) / (n_y : ℚ) := by
    have hnum : (0 : ℚ) ≤ (b_y : ℚ) := by
      simp_all only [gt_iff_lt, Nat.cast_nonneg]
    have hden : (0 : ℚ) ≤ (n_y : ℚ) := by
      simp_all only [gt_iff_lt, Nat.cast_nonneg]
    exact div_nonneg hnum hden
  have hb : (b_x : ℚ) / (n_x : ℚ) < 1 := by
    grind only
  have hnx_pos : (0 : ℚ) < (n_x : ℚ) := by
    simp_all only [gt_iff_lt, Nat.cast_pos, PNat.pos]
  have hnx_ne : (n_x : ℚ) ≠ 0 := by
    exact ne_of_gt hnx_pos
  have hx : (b_x : ℚ) < (n_x : ℚ) := by
    have hmul := mul_lt_mul_of_pos_right hb hnx_pos
    simpa [div_mul_cancel₀, hnx_ne, one_mul] using hmul
  exact_mod_cast hx

lemma ps_by_lt_ny {b_x b_y : ℕ} {n_x n_y : ℕ+}
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_y < (n_y : ℕ) := by
  have hsum : (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) < 1 := by
    exact h_le_1
  have hx_nonneg : 0 ≤ (b_x : ℚ) / (n_x : ℚ) := by
    have hb : (0 : ℚ) ≤ (b_x : ℚ) := by
      simp_all only [gt_iff_lt, Nat.cast_nonneg]
    have hn : (0 : ℚ) ≤ (n_x : ℚ) := by
      simp_all only [gt_iff_lt, Nat.cast_nonneg]
    exact div_nonneg hb hn
  have hy_le : (b_y : ℚ) / (n_y : ℚ) ≤ (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) := by
    exact le_add_of_nonneg_left hx_nonneg
  have hy_lt_one : (b_y : ℚ) / (n_y : ℚ) < 1 := by
    exact lt_of_le_of_lt hy_le hsum
  have hn_y : (0 : ℚ) < (n_y : ℚ) := by
    simp_all only [gt_iff_lt, le_add_iff_nonneg_left, Nat.cast_pos, PNat.pos]
  have hn_y_ne : (n_y : ℚ) ≠ 0 := by
    exact ne_of_gt hn_y
  have hy_lt : (b_y : ℚ) < (n_y : ℚ) := by
    have hmul : (b_y : ℚ) / (n_y : ℚ) * (n_y : ℚ) < (1 : ℚ) * (n_y : ℚ) := by
      apply mul_lt_mul_of_pos_right hy_lt_one hn_y
    simpa [div_mul_cancel₀, hn_y_ne] using hmul
  simp only [gt_iff_lt]
  exact_mod_cast hy_lt

lemma ps_card_eval_x_eq_zero_le_degree_x {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun x => Polynomial.Bivariate.evalX x A = 0)).card
      ≤ Polynomial.Bivariate.degreeX A := by
  classical
  have hcoeff_test (x : F) (j : ℕ) :
    (Polynomial.Bivariate.evalX x A).coeff j = (A.coeff j).eval x := by
    simp [Polynomial.Bivariate.evalX, Polynomial.coeff]
  have hsupp : A.support.Nonempty := by
    exact support_nonempty.mpr hA
  obtain ⟨j0, hj0mem, hj0sup⟩ :=
    Finset.exists_mem_eq_sup A.support hsupp (fun n => (A.coeff n).natDegree)
  have hj0deg : (A.coeff j0).natDegree = Polynomial.Bivariate.degreeX A := by
    simpa [Polynomial.Bivariate.degreeX] using hj0sup.symm
  have hc0 : A.coeff j0 ≠ 0 := by
    exact mem_support_iff.mp hj0mem
  let S : Finset F := P.filter (fun x => Polynomial.Bivariate.evalX x A = 0)
  have hsub : S.val ⊆ (A.coeff j0).roots := by
    intro x hx
    have hxS : x ∈ S := by
      simpa [S] using hx
    have hxEval : Polynomial.Bivariate.evalX x A = 0 :=
      (Finset.mem_filter.1 hxS).2
    have hxcoeff : (A.coeff j0).eval x = 0 := by
      have := congrArg (fun q : Polynomial F => q.coeff j0) hxEval
      simpa [hcoeff_test, Polynomial.coeff_zero] using this
    have hxroot : Polynomial.IsRoot (A.coeff j0) x := by
      simpa [Polynomial.IsRoot] using hxcoeff
    exact (Polynomial.mem_roots hc0).2 hxroot
  have hcard : S.card ≤ (A.coeff j0).natDegree := by
    simpa using (Polynomial.card_le_degree_of_subset_roots (p := A.coeff j0) (Z := S) hsub)
  have : S.card ≤ Polynomial.Bivariate.degreeX A := by
    simpa [hj0deg] using hcard
  simpa [S] using this


lemma ps_card_eval_y_eq_zero_le_nat_degree_y {F : Type} [Field F] [DecidableEq F]
    (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun y => Polynomial.Bivariate.evalY y A = 0)).card
      ≤ Polynomial.Bivariate.natDegreeY A := by
  classical
  -- Let `bad` be the subset of `P` on which `A` vanishes after evaluating in `Y`.
  set bad : Finset F := P.filter (fun y => Polynomial.Bivariate.evalY y A = 0)
  -- Consider the corresponding set of constant polynomials `C y : F[X]`.
  set Z : Finset F[X] := bad.image (fun y : F => (Polynomial.C y : F[X]))

  have hcard : bad.card = Z.card := by
    -- `C` is injective, so taking images preserves cardinality.
    have h :=
      (Finset.card_image_of_injective (s := bad)
        (f := fun y : F => (Polynomial.C y : F[X]))
        (by
          intro a b hab
          exact Polynomial.C_injective hab))
    -- `h : Z.card = bad.card`
    simpa [Z] using h.symm

  -- Show `Z` is contained in the multiset of roots of `A` (viewed as a polynomial in `Y`).
  have hZ : (Z.1 : Multiset F[X]) ⊆ A.roots := by
    intro z hz
    -- unpack membership in the image
    have hz' : z ∈ Z := hz
    rcases Finset.mem_image.1 hz' with ⟨y, hybad, rfl⟩
    have hy : Polynomial.Bivariate.evalY y A = 0 := by
      -- membership in the filter gives the defining property
      exact (show y ∈ P ∧ Polynomial.Bivariate.evalY y A = 0 by
        simpa [bad] using hybad).2
    -- `hy` says `C y` is a root of `A`.
    have : IsRoot A (Polynomial.C y : F[X]) := by
      -- `evalY` is just `Polynomial.eval (C y)`.
      simpa [Polynomial.Bivariate.evalY, Polynomial.IsRoot] using hy
    -- therefore it lies in `A.roots`
    exact (Polynomial.mem_roots hA).2 this

  -- Apply the standard bound on the number of distinct roots.
  have hZcard : Z.card ≤ A.natDegree := by
    simpa using (Polynomial.card_le_degree_of_subset_roots (p := A) (Z := Z) hZ)

  -- Translate back to the original statement.
  -- `natDegreeY` is just `natDegree`.
  simpa [Polynomial.Bivariate.natDegreeY, bad, hcard] using hZcard

lemma ps_coeff_mul_monomial_ite {R : Type} [Semiring R]
    (A : R[X]) (j i : ℕ) (r : R) :
    (A * Polynomial.monomial j r).coeff i =
      if j ≤ i then A.coeff (i - j) * r else 0 := by
  classical
  simp [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow',
    Polynomial.coeff_mul_C]

lemma ps_coeff_mul_sum_monomial {R : Type} [CommRing R]
    (A : R[X]) (m n : ℕ) (hm : A.natDegree ≤ m)
    (c : Fin n → R) (i : ℕ) :
    (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j))).coeff i =
      ∑ j : Fin n,
        if (j : ℕ) ≤ i ∧ i ≤ (j : ℕ) + m
        then A.coeff (i - (j : ℕ)) * c j else 0 := by
  classical
  have hdeg : ∀ N : ℕ, m < N → A.coeff N = 0 :=
    (Polynomial.natDegree_le_iff_coeff_eq_zero (p := A) (n := m)).1 hm
  simp [Finset.mul_sum, Polynomial.finset_sum_coeff, ps_coeff_mul_monomial_ite]
  grind only [cases Or]

lemma ps_degree_x_swap {F : Type} [CommRing F]
    (f : F[X][Y]) :
    Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap f) =
      Polynomial.Bivariate.natDegreeY f := by
  classical
  -- A coefficient-level description of `swap`.
  have hcoeff :
      ∀ (g : F[X][Y]) (i j : ℕ),
        Polynomial.Bivariate.coeff (Polynomial.Bivariate.swap g) i j =
          Polynomial.Bivariate.coeff g j i := by
    intro g i j
    induction g using Polynomial.induction_on' with
    | add p q hp hq =>
        -- rewrite the IHs so they apply after unfolding `Bivariate.coeff`
        have hp' : ((Polynomial.Bivariate.swap p).coeff j).coeff i = (p.coeff i).coeff j := by
          exact hp
        have hq' : ((Polynomial.Bivariate.swap q).coeff j).coeff i = (q.coeff i).coeff j := by
          exact hq
        simp [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply, hp', hq']
    | monomial n a =>
        -- inner induction on the coefficient `a : F[X]`
        induction a using Polynomial.induction_on' with
        | add p q hp hq =>
            have hp' : ((Polynomial.Bivariate.swap ((monomial n) p)).coeff j).coeff i =
                (((monomial n) p).coeff i).coeff j := by exact hp
            have hq' : ((Polynomial.Bivariate.swap ((monomial n) q)).coeff j).coeff i =
                (((monomial n) q).coeff i).coeff j := by exact hq
            simp [Polynomial.Bivariate.coeff, Polynomial.monomial_add,
              -Polynomial.Bivariate.swap_apply, hp', hq']
        | monomial m r =>
            -- now `g = monomial n (monomial m r)`
            by_cases hi : n = i
            · subst hi
              by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  -Polynomial.Bivariate.swap_apply]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hj]
            · by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hi]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hi, hj]

  -- Unfold the ArkLib degree definitions.
  unfold Polynomial.Bivariate.degreeX Polynomial.Bivariate.natDegreeY

  by_cases hf : f = 0
  · subst hf
    simp
  · -- main (nonzero) case
    apply le_antisymm
    · -- `degreeX (swap f) ≤ natDegree f`
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have hfm : f.coeff m = 0 := by exact coeff_eq_zero_of_natDegree_lt hm
      have hmn : ((Polynomial.Bivariate.swap f).coeff n).coeff m = (f.coeff m).coeff n := by
        exact hcoeff f m n
      rw [hmn]
      simp [hfm]
    · -- `natDegree f ≤ degreeX (swap f)`
      have hNmem : natDegree f ∈ f.support :=
        Polynomial.natDegree_mem_support_of_nonzero hf
      have hcoeffN0 : f.coeff (natDegree f) ≠ 0 := by exact mem_support_iff.mp hNmem
      let n : ℕ := (f.coeff (natDegree f)).natDegree
      have hnmem : n ∈ (f.coeff (natDegree f)).support := by
        exact natDegree_mem_support_of_nonzero hcoeffN0
      have hcoeffn : (f.coeff (natDegree f)).coeff n ≠ 0 := by exact mem_support_iff.mp hnmem
      have hEq : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) =
          (f.coeff (natDegree f)).coeff n := by
          exact hcoeff f f.natDegree n
      have hswapCoeff : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) ≠ 0 := by
        simpa [hEq, -Polynomial.Bivariate.swap_apply] using hcoeffn
      have hNle_natDeg : natDegree f ≤ ((Polynomial.Bivariate.swap f).coeff n).natDegree := by
        exact le_natDegree_of_ne_zero hswapCoeff
      have hcoeff_nonzero : (Polynomial.Bivariate.swap f).coeff n ≠ 0 := by
        intro hzero
        apply hswapCoeff
        rw [hzero]
        simp
      have hn_support : n ∈ (Polynomial.Bivariate.swap f).support := by
        exact mem_support_iff.mpr hcoeff_nonzero
      have hn_le_degX :
          ((Polynomial.Bivariate.swap f).coeff n).natDegree ≤
            (Polynomial.Bivariate.swap f).support.sup
              (fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) :=
        Finset.le_sup (f := fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) hn_support
      exact le_trans hNle_natDeg hn_le_degX

lemma ps_descend_eval_x {F : Type} [Field F] [DecidableEq F]
    {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
    (x : F) (hx : Polynomial.Bivariate.evalX x G ≠ 0) (q : F[X])
    (h : Polynomial.Bivariate.evalX x B = q * Polynomial.Bivariate.evalX x A) :
    Polynomial.Bivariate.evalX x B1 = q * Polynomial.Bivariate.evalX x A1 := by
  classical
  -- First show that `evalX` is the same as the usual coefficient map.
  have evalX_eq_map (f : F[X][Y]) :
  Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
    ext n
    simp [Polynomial.Bivariate.evalX, Polynomial.toFinsupp_apply]
  -- use this lemma to rewrite the hypothesis and goal
  have hmap : (B.map (Polynomial.evalRingHom x)) = q * (A.map (Polynomial.evalRingHom x)) := by
    simpa [evalX_eq_map] using h
  -- now substitute the factorizations of `A` and `B`
  have hmap' :
  ((G * B1).map (Polynomial.evalRingHom x)) = q * ((G * A1).map (Polynomial.evalRingHom x)) := by
    simpa [hB, hA] using hmap
  -- expand the map over multiplication
  have hmap'' : (G.map (Polynomial.evalRingHom x)) * (B1.map (Polynomial.evalRingHom x))
      = q * ((G.map (Polynomial.evalRingHom x)) * (A1.map (Polynomial.evalRingHom x))) := by
    simpa [mul_assoc] using hmap'
  -- cancel the nonzero factor
  have hg' : (G.map (Polynomial.evalRingHom x)) ≠ 0 := by
    simpa [evalX_eq_map] using hx
  have hcancel : (B1.map (Polynomial.evalRingHom x)) = q * (A1.map (Polynomial.evalRingHom x)) := by
    apply mul_left_cancel₀ hg'
    -- rearrange `hmap''` so the common factor is on the left
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmap''
  -- rewrite back to `evalX`
  simpa [evalX_eq_map] using hcancel

lemma ps_descend_eval_y {F : Type} [Field F] [DecidableEq F]
    {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
    (y : F) (hy : Polynomial.Bivariate.evalY y G ≠ 0) (q : F[X])
    (h : Polynomial.Bivariate.evalY y B = q * Polynomial.Bivariate.evalY y A) :
    Polynomial.Bivariate.evalY y B1 = q * Polynomial.Bivariate.evalY y A1 := by
  have h' : Polynomial.Bivariate.evalY y (G * B1) = q * Polynomial.Bivariate.evalY y (G * A1) := by
    simpa [hB, hA] using h
  have h'' :
      Polynomial.Bivariate.evalY y G * Polynomial.Bivariate.evalY y B1 =
        q * (Polynomial.Bivariate.evalY y G * Polynomial.Bivariate.evalY y A1) := by
    simpa [Polynomial.Bivariate.evalY, Polynomial.eval_mul, mul_assoc] using h'
  apply mul_left_cancel₀ hy
  grind only

lemma ps_eval_x_eq_map {F : Type} [CommSemiring F]
    (x : F) (f : F[X][Y]) :
    Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
  classical
  ext n
  simp [Polynomial.Bivariate.evalX, Polynomial.toFinsupp_apply]

lemma ps_eval_y_eq_eval_x_swap {F : Type} [CommRing F]
    (y : F) (f : F[X][Y]) :
    Polynomial.Bivariate.evalY y f =
      Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
  classical
  -- Use the same `F[X]`-algebra structure on `F[X]` as in `Polynomial.Bivariate.aveal_eq_map_swap`.
  -- (This is *not* the default `Algebra.id` instance.)
  letI : Algebra F[X] F[X] := Polynomial.algebra (R := F) (A := F)
  -- `evalX` is coefficient-wise evaluation in the inner variable
  -- i.e. coefficient-map by `evalRingHom`.
  have evalX_eq_map (g : F[X][Y]) :
      Polynomial.Bivariate.evalX y g = g.map (Polynomial.evalRingHom y) := by
    ext n
    simp [Polynomial.Bivariate.evalX, Polynomial.coeff_map, Polynomial.toFinsupp_apply]
  -- Convert `aeval (C y)` (using the `Polynomial.algebra` instance above) into `eval (C y)`.
  have eval_eq_aeval : Polynomial.eval (Polynomial.C y) f = aeval (Polynomial.C y) f := by
    -- show the relevant `algebraMap F[X] F[X]` is the identity
    have halg : (algebraMap F[X] F[X]) = RingHom.id (F[X]) := by
      simp only [algebraMap_def, Algebra.algebraMap_self, mapRingHom_id]
    simp [Polynomial.eval, Polynomial.aeval_def, halg]
  -- Rewrite the RHS of `aveal_eq_map_swap` into a `map` by `evalRingHom`.
  have mapAlgHom_eq_map :
      Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f)
        = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
        exact rfl
  have hmain :
  Polynomial.Bivariate.evalY y f = Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
    calc
      Polynomial.Bivariate.evalY y f
          = Polynomial.eval (Polynomial.C y) f := by
              rfl
      _ = aeval (Polynomial.C y) f := by exact eval_eq_aeval
      _ = Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f) := by
        exact aveal_eq_map_swap y f
      _ = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
        exact mapAlgHom_eq_map
      _ = Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
        exact Eq.symm (ps_eval_x_eq_map y (swap f))
  exact hmain

lemma ps_exists_x_preserve_nat_degree_y {F : Type} [Field F] [DecidableEq F]
    (B : F[X][Y]) (hB : B ≠ 0) (P_x : Finset F)
    (hcard : P_x.card > Polynomial.Bivariate.degreeX B) :
    ∃ x ∈ P_x, (Polynomial.Bivariate.evalX x B).natDegree = Polynomial.Bivariate.natDegreeY B := by
  classical
  let d : ℕ := Polynomial.Bivariate.natDegreeY B
  let p : F[X] := Polynomial.Bivariate.leadingCoeffY B
  have hp0 : p ≠ 0 := by
    -- leading coefficient in Y is nonzero since B ≠ 0
    simpa [p] using (Polynomial.Bivariate.leadingCoeffY_ne_zero (f := B)).2 hB
  have hp_deg : p.natDegree ≤ Polynomial.Bivariate.degreeX B := by
    -- `degreeX` is the sup of the X-degrees of all Y-coefficients
    have hdmem : B.natDegree ∈ B.support := Polynomial.natDegree_mem_support_of_nonzero hB
    have : (B.coeff B.natDegree).natDegree ≤ B.support.sup (fun n => (B.coeff n).natDegree) :=
      Finset.le_sup (f := fun n => (B.coeff n).natDegree) hdmem
    simpa [p, Polynomial.Bivariate.leadingCoeffY, Polynomial.Bivariate.degreeX] using this
  have hlt : p.natDegree < P_x.card := lt_of_le_of_lt hp_deg hcard
  have hx : ∃ x ∈ P_x, p.eval x ≠ 0 := by
    by_contra h
    have hall : ∀ x ∈ P_x, p.eval x = 0 := by
      intro x hx
      by_contra hxne
      exact h ⟨x, hx, hxne⟩
    have hsub : P_x.val ⊆ p.roots := by
      intro x hxval
      have hxP : x ∈ P_x := by exact hxval
      have hxroot : Polynomial.IsRoot p x := by exact hall x hxval
      exact (Polynomial.mem_roots hp0).2 hxroot
    have hle : P_x.card ≤ p.natDegree := by
      simpa using (Polynomial.card_le_degree_of_subset_roots (p := p) (Z := P_x) hsub)
    exact (not_lt_of_ge hle) hlt
  rcases hx with ⟨x, hxPx, hxne⟩
  refine ⟨x, hxPx, ?_⟩
  have hnat_le :
  (Polynomial.Bivariate.evalX x B).natDegree ≤ Polynomial.Bivariate.natDegreeY B := by
    -- coefficients above `natDegreeY B` vanish
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hBN : B.coeff N = 0 := by exact coeff_eq_zero_of_natDegree_lt hN
    have hBN' : B.toFinsupp N = 0 := by exact hBN
    simp [Polynomial.Bivariate.evalX, hBN']
  have hcoeff : (Polynomial.Bivariate.evalX x B).coeff (Polynomial.Bivariate.natDegreeY B) ≠ 0 := by
    -- the top coefficient is `p.eval x`
    exact hxne
  exact natDegree_eq_of_le_of_coeff_ne_zero hnat_le hxne

lemma ps_exists_y_preserve_degree_x {F : Type} [Field F] [DecidableEq F]
    (B : F[X][Y]) (hB : B ≠ 0) (P_y : Finset F)
    (hcard : P_y.card > Polynomial.Bivariate.natDegreeY B) :
    ∃ y ∈ P_y, (Polynomial.Bivariate.evalY y B).natDegree = Polynomial.Bivariate.degreeX B := by
  classical
  -- Let `d` be the maximal `X`-degree of a coefficient of `B`.
  set d : ℕ := Polynomial.Bivariate.degreeX B with hd
  -- Let `g` be the coefficient of `X^d` viewed as a univariate polynomial in `Y`.
  set g : F[X] := B.sum (fun j p => Polynomial.monomial j (p.coeff d)) with hg

  -- Pick a `Y`-index where the `X`-degree of the coefficient polynomial reaches `d`.
  have hBsup_ne : B.support.Nonempty := by exact support_nonempty.mpr hB
  obtain ⟨j0, hj0_mem, hj0_deg⟩ :=
    Finset.exists_mem_eq_sup B.support hBsup_ne (fun n => (B.coeff n).natDegree)

  have hj0_deg' : (B.coeff j0).natDegree = d := by
    exact id (Eq.symm hj0_deg)

  have hj0_coeff_ne : (B.coeff j0).coeff d ≠ 0 := by
    have hj0_ne : B.coeff j0 ≠ 0 := by exact mem_support_iff.mp hj0_mem
    have hlead : (B.coeff j0).leadingCoeff ≠ 0 := by exact leadingCoeff_ne_zero.mpr hj0_ne
    simpa [Polynomial.leadingCoeff, hj0_deg'] using hlead

  -- Hence `g` is nonzero.
  have hg_ne : g ≠ 0 := by
    have hg_coeff : g.coeff j0 = (B.coeff j0).coeff d := by
      rw [hg]
      simp [Polynomial.sum_def, Polynomial.coeff_monomial, hj0_mem]
    intro hzero
    have : g.coeff j0 = 0 := by simp [hzero]
    exact hj0_coeff_ne (by simpa [hg_coeff] using this)

  -- Degree bound: `g.natDegree ≤ natDegreeY B`.
  have hg_natDegree_le : g.natDegree ≤ Polynomial.Bivariate.natDegreeY B := by
    simp [Polynomial.Bivariate.natDegreeY]
    rw [hg, Polynomial.sum_def]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := B.support)
        (f := fun j => Polynomial.monomial j ((B.coeff j).coeff d))
        (n := B.natDegree)
        ?_
    intro j hj
    exact le_trans
      (Polynomial.natDegree_monomial_le (a := (B.coeff j).coeff d) (m := j))
      (Polynomial.le_natDegree_of_mem_supp (p := B) j hj)

  -- Since `P_y.card > natDegreeY B`, we also have `g.natDegree < P_y.card`.
  have hcard_g : g.natDegree < P_y.card := lt_of_le_of_lt hg_natDegree_le hcard

  -- Choose `y ∈ P_y` with `g.eval y ≠ 0`.
  have hy_exists : ∃ y ∈ P_y, g.eval y ≠ 0 := by
    by_contra h
    have heval : ∀ y ∈ P_y, g.eval y = 0 := by
      intro y hy
      by_contra hne
      exact h ⟨y, hy, hne⟩
    have : g = 0 := by
      exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g P_y heval hcard_g
    exact hg_ne this

  rcases hy_exists with ⟨y, hyP, hgy_ne⟩
  refine ⟨y, hyP, ?_⟩

  -- First, show `natDegree (evalY y B) ≤ d`.
  have hdeg_le : (Polynomial.Bivariate.evalY y B).natDegree ≤ d := by
    have heval : Polynomial.Bivariate.evalY y B =
        ∑ j ∈ B.support, B.coeff j * (Polynomial.C y : F[X]) ^ j := by
      simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [heval]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := B.support)
        (f := fun j => B.coeff j * (Polynomial.C y : F[X]) ^ j)
        (n := d)
        ?_
    intro j hj
    have hj_le : (B.coeff j).natDegree ≤ d := by
      have : (B.coeff j).natDegree ≤ B.support.sup (fun n => (B.coeff n).natDegree) :=
        Finset.le_sup (s := B.support) (f := fun n => (B.coeff n).natDegree) hj
      simpa [Polynomial.Bivariate.degreeX, hd] using this
    have hmul : (B.coeff j * (Polynomial.C y : F[X]) ^ j).natDegree ≤ (B.coeff j).natDegree := by
      simpa using (Polynomial.natDegree_mul_C_le (f := B.coeff j) (a := y ^ j))
    exact le_trans hmul hj_le

  -- Compute the coefficient of `X^d` in `evalY y B`.
  have hcoeff_evalY :
      (Polynomial.Bivariate.evalY y B).coeff d =
        ∑ j ∈ B.support, (B.coeff j).coeff d * y ^ j := by
    have heval : Polynomial.Bivariate.evalY y B =
        ∑ j ∈ B.support, B.coeff j * (Polynomial.C y : F[X]) ^ j := by
      simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [heval]
    rw [Polynomial.finset_sum_coeff (s := B.support)
      (f := fun j => B.coeff j * (Polynomial.C y : F[X]) ^ j) (n := d)]
    refine Finset.sum_congr rfl ?_
    intro j hj
    -- Use `coeff_mul_C` after rewriting `C (y^j)` as `(C y)^j`.
    simpa [Polynomial.C_pow] using
      (Polynomial.coeff_mul_C (p := B.coeff j) (n := d) (a := y ^ j))

  -- Compute `g.eval y` as the same sum.
  have hcoeff_g : g.eval y = ∑ j ∈ B.support, (B.coeff j).coeff d * y ^ j := by
    rw [hg, Polynomial.sum_def]
    -- Evaluate termwise.
    rw [Polynomial.eval_finset_sum]
    simp [Polynomial.eval_monomial]

  have hcoeff_eq : (Polynomial.Bivariate.evalY y B).coeff d = g.eval y := by
    simp [hcoeff_evalY, hcoeff_g]

  have hcoeff_ne : (Polynomial.Bivariate.evalY y B).coeff d ≠ 0 := by
    simpa [hcoeff_eq] using hgy_ne

  have hnat : (Polynomial.Bivariate.evalY y B).natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg_le hcoeff_ne

  simpa [hd] using hnat

lemma ps_degree_bounds_of_mul {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    {A B P : F[X][Y]}
    (hA : A ≠ 0)
    (hBA : B = P * A)
    (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
    (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A)
    (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
    (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x : F → F[X]) (quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y,
      (quot_x y).natDegree ≤ (b_x - a_x) ∧
        Polynomial.Bivariate.evalY y B = (quot_x y) * (Polynomial.Bivariate.evalY y A))
    (h_quot_y : ∀ x ∈ P_x,
      (quot_y x).natDegree ≤ (b_y - a_y) ∧
        Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    Polynomial.Bivariate.degreeX P ≤ b_x - a_x ∧
      Polynomial.Bivariate.natDegreeY P ≤ b_y - a_y := by
  classical
  letI : DecidableEq F := Classical.decEq F

  by_cases hB0 : B = 0
  · have hPA : P * A = 0 := by
      calc
        P * A = B := by simp [hBA]
        _ = 0 := hB0
    have hP0 : P = 0 := by
      rcases mul_eq_zero.mp hPA with hP0 | hA0
      · exact hP0
      · exfalso
        exact hA hA0
    subst hP0
    constructor <;> simp [Polynomial.Bivariate.degreeX, Polynomial.Bivariate.natDegreeY]
  · have hB : B ≠ 0 := hB0
    have hP : P ≠ 0 := by
      intro hP0
      apply hB
      simp [hBA, hP0]

    -- helper: evalX multiplicativity via map
    have evalX_eq_map (a : F) (f : F[X][Y]) : Polynomial.Bivariate.evalX a f
    = f.map (Polynomial.evalRingHom a) := by
      ext n
      simp [Polynomial.Bivariate.evalX, Polynomial.coeff]
      simpa [Polynomial.coe_evalRingHom, Polynomial.coeff] using
        (Polynomial.coeff_map (p := f) (f := Polynomial.evalRingHom a) n).symm

    have evalX_mul (a : F) (f g : F[X][Y]) :
        Polynomial.Bivariate.evalX a (f * g)
        = Polynomial.Bivariate.evalX a f * Polynomial.Bivariate.evalX a g := by
      simp [evalX_eq_map, Polynomial.map_mul]

    -- filtered set in Y
    let py0 : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A = 0)
    let py' : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A ≠ 0)

    have h_py0_le : py0.card ≤ Polynomial.Bivariate.natDegreeY A := by
      simpa [py0] using
        ps_card_eval_y_eq_zero_le_nat_degree_y (A := A) (hA := hA) (P := P_y)

    have hcard_part : py0.card + py'.card = P_y.card := by
      simpa [py0, py'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_y)
          (p := fun y : F => Polynomial.Bivariate.evalY y A = 0))

    have h_py'_ge : P_y.card - Polynomial.Bivariate.natDegreeY A ≤ py'.card := by
      have hsub : P_y.card - Polynomial.Bivariate.natDegreeY A ≤ P_y.card - py0.card :=
        tsub_le_tsub_left h_py0_le P_y.card
      have h_py0_sub : py'.card = P_y.card - py0.card := by
        -- subtract py0.card from partition equation
        have htmp := congrArg (fun t => t - py0.card) hcard_part
        simpa [Nat.add_sub_cancel_left] using htmp
      -- rewrite
      simpa [h_py0_sub] using hsub

    have hby_lt_ny : b_y < (n_y : ℕ) :=
      ps_by_lt_ny (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
    have hby_lt_card : b_y < P_y.card := lt_of_lt_of_le hby_lt_ny h_card_Py

    have hdegA_le_by : Polynomial.Bivariate.natDegreeY A ≤ b_y := le_trans h_f_degY h_by_ge_ay

    have hdegY :
        Polynomial.Bivariate.natDegreeY B =
          Polynomial.Bivariate.natDegreeY P + Polynomial.Bivariate.natDegreeY A := by
      calc
        Polynomial.Bivariate.natDegreeY B = Polynomial.Bivariate.natDegreeY (P * A) := by
          simp [hBA]
        _ = Polynomial.Bivariate.natDegreeY P + Polynomial.Bivariate.natDegreeY A := by
          simpa using (Polynomial.Bivariate.degreeY_mul (F := F) P A hP hA)

    have hsumY :
        Polynomial.Bivariate.natDegreeY P + Polynomial.Bivariate.natDegreeY A ≤ b_y := by
      -- rewrite natDegreeY B in h_g_degY
      have hBN : Polynomial.Bivariate.natDegreeY B ≤ b_y := h_g_degY
      simpa [hdegY] using hBN

    have hnatDegY_P_le :
        Polynomial.Bivariate.natDegreeY P ≤ b_y - Polynomial.Bivariate.natDegreeY A :=
      le_tsub_of_add_le_right hsumY

    have hbsubY : b_y - Polynomial.Bivariate.natDegreeY A
    < P_y.card - Polynomial.Bivariate.natDegreeY A :=
      tsub_lt_tsub_right_of_le hdegA_le_by hby_lt_card

    have h_py'_card : py'.card > Polynomial.Bivariate.natDegreeY P := by
      have hlt : Polynomial.Bivariate.natDegreeY P < P_y.card - Polynomial.Bivariate.natDegreeY A :=
        lt_of_le_of_lt hnatDegY_P_le hbsubY
      have hlt' : Polynomial.Bivariate.natDegreeY P < py'.card := lt_of_lt_of_le hlt h_py'_ge
      exact hlt'

    -- choose y preserving degreeX
    rcases ps_exists_y_preserve_degree_x (F := F) (B := P) (hB := hP) (P_y := py') h_py'_card with
      ⟨y, hyPy', hydegX⟩

    have hyP_y : y ∈ P_y := (Finset.mem_filter.mp hyPy').1
    have hyA0 : Polynomial.Bivariate.evalY y A ≠ 0 := (Finset.mem_filter.mp hyPy').2

    have h_quot_x_deg : (quot_x y).natDegree ≤ b_x - a_x := (h_quot_x y hyP_y).1
    have h_quot_x_eq : Polynomial.Bivariate.evalY y B = (quot_x y) * Polynomial.Bivariate.evalY y A :=
      (h_quot_x y hyP_y).2

    have hBA_evalY :
        Polynomial.Bivariate.evalY y B =
          Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A := by
      calc
        Polynomial.Bivariate.evalY y B = Polynomial.Bivariate.evalY y (P * A) := by
          simp [hBA]
        _ = Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A := by
          -- evalY is Polynomial.eval
          simp [Polynomial.Bivariate.evalY, Polynomial.eval_mul]

    have hEvalY_P_eq_quot : Polynomial.Bivariate.evalY y P = quot_x y := by
      apply mul_right_cancel₀ hyA0
      -- cancel the common right factor
      calc
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A
        = Polynomial.Bivariate.evalY y B := by
          simp [hBA_evalY]
        _ = quot_x y * Polynomial.Bivariate.evalY y A := h_quot_x_eq

    have hdegX_P_le : Polynomial.Bivariate.degreeX P ≤ b_x - a_x := by
      -- hydegX : (evalY y P).natDegree = degreeX P
      have hdegX' : Polynomial.Bivariate.degreeX P
      = (Polynomial.Bivariate.evalY y P).natDegree := hydegX.symm
      rw [hdegX']
      simpa [hEvalY_P_eq_quot] using h_quot_x_deg

    -- Now the X-direction
    let px0 : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A = 0)
    let px' : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0)

    have h_px0_le : px0.card ≤ Polynomial.Bivariate.degreeX A := by
      simpa [px0] using ps_card_eval_x_eq_zero_le_degree_x (A := A) (hA := hA) (P := P_x)

    have hcard_partX : px0.card + px'.card = P_x.card := by
      simpa [px0, px'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_x)
          (p := fun x : F => Polynomial.Bivariate.evalX x A = 0))

    have h_px'_ge : P_x.card - Polynomial.Bivariate.degreeX A ≤ px'.card := by
      have hsub : P_x.card - Polynomial.Bivariate.degreeX A ≤ P_x.card - px0.card :=
        tsub_le_tsub_left h_px0_le P_x.card
      have h_px0_sub : px'.card = P_x.card - px0.card := by
        have htmp := congrArg (fun t => t - px0.card) hcard_partX
        simpa [Nat.add_sub_cancel_left] using htmp
      simpa [h_px0_sub] using hsub

    have hbx_lt_nx : b_x < (n_x : ℕ) :=
      ps_bx_lt_nx (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
    have hbx_lt_card : b_x < P_x.card := lt_of_lt_of_le hbx_lt_nx h_card_Px

    have hdegX_A_le_bx : Polynomial.Bivariate.degreeX A ≤ b_x := by
      -- degreeX A ≤ a_x ≤ b_x
      exact le_trans (show Polynomial.Bivariate.degreeX A ≤ a_x from h_f_degX) h_bx_ge_ax

    have hbsubX : b_x - Polynomial.Bivariate.degreeX A
    < P_x.card - Polynomial.Bivariate.degreeX A :=
      tsub_lt_tsub_right_of_le hdegX_A_le_bx hbx_lt_card

    have hdegX_P_le' : Polynomial.Bivariate.degreeX P ≤ b_x - Polynomial.Bivariate.degreeX A := by
      -- degreeX P ≤ b_x - a_x ≤ b_x - degreeX A
      have h1 : b_x - a_x ≤ b_x - Polynomial.Bivariate.degreeX A :=
        tsub_le_tsub_left (show Polynomial.Bivariate.degreeX A ≤ a_x from h_f_degX) b_x
      exact le_trans hdegX_P_le h1

    have h_px'_card : px'.card > Polynomial.Bivariate.degreeX P := by
      have hlt : Polynomial.Bivariate.degreeX P < P_x.card - Polynomial.Bivariate.degreeX A :=
        lt_of_le_of_lt hdegX_P_le' hbsubX
      have hlt' : Polynomial.Bivariate.degreeX P < px'.card := lt_of_lt_of_le hlt h_px'_ge
      exact hlt'

    rcases ps_exists_x_preserve_nat_degree_y (F := F) (B := P) (hB := hP) (P_x := px') h_px'_card with
      ⟨x, hxPx', hxdegY⟩

    have hxP_x : x ∈ P_x := (Finset.mem_filter.mp hxPx').1
    have hxA0 : Polynomial.Bivariate.evalX x A ≠ 0 := (Finset.mem_filter.mp hxPx').2

    have h_quot_y_deg : (quot_y x).natDegree ≤ b_y - a_y := (h_quot_y x hxP_x).1
    have h_quot_y_eq : Polynomial.Bivariate.evalX x B = (quot_y x) * Polynomial.Bivariate.evalX x A :=
      (h_quot_y x hxP_x).2

    have hBA_evalX :
        Polynomial.Bivariate.evalX x B =
          Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
      calc
        Polynomial.Bivariate.evalX x B = Polynomial.Bivariate.evalX x (P * A) := by
          simp [hBA]
        _ = Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
          simp [evalX_mul]

    have hEvalX_P_eq_quot : Polynomial.Bivariate.evalX x P = quot_y x := by
      apply mul_right_cancel₀ hxA0
      calc
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A
        = Polynomial.Bivariate.evalX x B := by
          simp [hBA_evalX]
        _ = quot_y x * Polynomial.Bivariate.evalX x A := h_quot_y_eq

    have hdegY_P_le : Polynomial.Bivariate.natDegreeY P ≤ b_y - a_y := by
      -- hxdegY : (evalX x P).natDegree = natDegreeY P
      have hdegY' : Polynomial.Bivariate.natDegreeY P
      = (Polynomial.Bivariate.evalX x P).natDegree := by exact id (Eq.symm hxdegY)
      rw [hdegY']
      simpa [hEvalX_P_eq_quot] using h_quot_y_deg

    exact ⟨hdegX_P_le, hdegY_P_le⟩

lemma ps_gcd_decompose {F : Type} [Field F]
    {A B : F[X][Y]} (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ G A1 B1 : F[X][Y],
      A = G * A1 ∧ B = G * B1 ∧ IsRelPrime A1 B1 ∧ A1 ≠ 0 ∧ B1 ≠ 0 := by
  classical
  let G : F[X][Y] := gcd A B
  have hGA : G ∣ A := by
    simpa [G] using (gcd_dvd_left A B)
  have hGB : G ∣ B := by
    simpa [G] using (gcd_dvd_right A B)
  rcases hGA with ⟨A1, hAfac⟩
  rcases hGB with ⟨B1, hBfac⟩
  refine ⟨G, A1, B1, ?_⟩
  have hG0 : G ≠ 0 := by exact gcd_ne_zero_of_right hB
  have hA1 : A1 ≠ 0 := by
    intro hA10
    apply hA
    simp [hAfac, hA10]
  have hB1 : B1 ≠ 0 := by
    intro hB10
    apply hB
    simp [hBfac, hB10]
  have hnorm : normalize G = G := by exact NormalizedGCDMonoid.normalize_gcd A B
  have hgcdAB : gcd A B = normalize G * gcd A1 B1 := by
    calc
      gcd A B = gcd (G * A1) (G * B1) := by
        simp [hAfac, hBfac]
      _ = normalize G * gcd A1 B1 := by
        simp
  have hEq : G = normalize G * gcd A1 B1 := by exact hgcdAB
  have hEq' : G = G * gcd A1 B1 := by simpa [hnorm] using hEq

  have hgcd_eq_one : gcd A1 B1 = 1 := by
    have hmul : G * 1 = G * gcd A1 B1 := by
      simpa [mul_one] using hEq'
    exact (mul_left_cancel₀ hG0 hmul).symm

  have hgcd_unit : IsUnit (gcd A1 B1) := by
    rw [hgcd_eq_one]
    exact isUnit_one

  have hrel : IsRelPrime A1 B1 := by exact gcd_isUnit_iff_isRelPrime.mp hgcd_unit
  exact ⟨hAfac, hBfac, hrel, hA1, hB1⟩

lemma ps_is_rel_prime_swap {F : Type} [CommRing F] {A B : F[X][Y]}
    (h : IsRelPrime A B) :
    IsRelPrime (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) := by
  classical
  let f : F[X][Y] ≃+* F[X][Y] := (Polynomial.Bivariate.swap (R := F)).toRingEquiv
  -- reduce to the definition and pull everything back along the equivalence
  refine fun d hdA hdB => ?_
  have hdA' : f.symm d ∣ A :=
    (map_dvd_iff (f := f)).1 (by simpa [f] using hdA)
  have hdB' : f.symm d ∣ B :=
    (map_dvd_iff (f := f)).1 (by simpa [f] using hdB)
  have hunit : IsUnit (f.symm d) := h hdA' hdB'
  have : IsUnit (f (f.symm d)) := (f.toRingHom).isUnit_map hunit
  simpa [f] using this

lemma ps_nat_degree_y_swap {F : Type} [CommRing F]
    (f : F[X][Y]) :
    Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
      Polynomial.Bivariate.degreeX f := by
  classical
  have h := ps_degree_x_swap (F := F) (f := Polynomial.Bivariate.swap f)
  have hs : Polynomial.Bivariate.swap (R := F) (Polynomial.Bivariate.swap f) = f := by
    simpa using (Polynomial.Bivariate.swap (R := F)).left_inv f
  have h' :
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
        Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) := by
    simpa using h.symm
  have hdeg :
      Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) =
        Polynomial.Bivariate.degreeX f := by
    simpa using congrArg Polynomial.Bivariate.degreeX hs
  exact h'.trans hdeg
