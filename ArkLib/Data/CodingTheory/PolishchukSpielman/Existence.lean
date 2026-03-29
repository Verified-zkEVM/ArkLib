/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.PolishchukSpielman.Resultant

/-!
# Existence of polynomials for Polishchuk-Spielman

This file contains the core existence proofs for the polynomials $P$ and $Q$
required by the Polishchuk-Spielman lemma [BCIKS20].

## Main results

- `ps_exists_p`: Existence of a polynomial `P` such that `B = P * A`.
- `ps_exists_qx_of_cancel`: Existence of `Q_x` after cancellation in the X direction.
- `ps_exists_qy_of_cancel`: Existence of `Q_y` after cancellation in the Y direction.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]

-/

open Polynomial.Bivariate Polynomial Matrix
open scoped BigOperators


/-- A bivariate polynomial of degree zero in both variables divides every polynomial. -/
lemma ps_exists_p_of_degree_x_eq_zero_nat_degree_y_eq_zero {F : Type} [Field F]
    {A B : F[X][Y]} (hA0 : A ≠ 0)
    (hdegX : degreeX A = 0) (hdegY : natDegreeY A = 0) :
    ∃ P : F[X][Y], B = P * A := by
  classical
  rcases natDegree_eq_zero.1 (by simpa [natDegreeY] using hdegY) with ⟨a0, ha0⟩
  subst ha0; simp_all only [ne_eq, C_eq_zero]
  rcases natDegree_eq_zero.1 (by simpa [degreeX, support_C hA0] using hdegX) with ⟨a, ha⟩
  subst ha; simp_all only [map_eq_zero]
  exact ⟨B * C (C a⁻¹), by ext n m : 2; simp [coeff_mul_C, inv_mul_cancel_right₀ hA0]⟩

/-- After cancellation in X, a large subset of evaluation points witnesses `P = quot_y`. -/
lemma ps_exists_qx_of_cancel {F : Type} [Field F]
    (a_x : ℕ) (n_x : ℕ+) {A B P : F[X][Y]} (hA : A ≠ 0) (hBA : B = P * A)
    (P_x : Finset F) (h_card_Px : n_x ≤ P_x.card) (quot_y : F → F[X])
    (h_quot_y : ∀ x ∈ P_x, evalX x B = (quot_y x) * (evalX x A))
    (h_f_degX : a_x ≥ degreeX A) :
    ∃ Q_x : Finset F, Q_x.card ≥ (n_x : ℕ) - a_x ∧ Q_x ⊆ P_x ∧
      ∀ x ∈ Q_x, evalX x P = quot_y x := by
  classical
  refine ⟨P_x.filter (fun x ↦ evalX x A ≠ 0), ?_, Finset.filter_subset _ _, ?_⟩
  · have := ps_card_eval_x_eq_zero_le_degree_x A hA P_x
    have := Finset.card_filter_add_card_filter_not (s := P_x) (fun x ↦ evalX x A = 0)
    have : {a ∈ P_x | ¬evalX a A = 0}.card = {x ∈ P_x | evalX x A ≠ 0}.card := rfl
    omega
  · intro x hx
    exact mul_right_cancel₀ (Finset.mem_filter.mp hx).2
      (by rw [← evalX_mul, ← hBA]; exact h_quot_y x (Finset.mem_of_mem_filter x hx))

/-- After cancellation in Y, a large subset of evaluation points witnesses `P = quot_x`. -/
lemma ps_exists_qy_of_cancel {F : Type} [Field F]
    (a_y : ℕ) (n_y : ℕ+) {A B P : F[X][Y]} (hA : A ≠ 0) (hBA : B = P * A)
    (P_y : Finset F) (h_card_Py : n_y ≤ P_y.card) (quot_x : F → F[X])
    (h_quot_x : ∀ y ∈ P_y, evalY y B = (quot_x y) * (evalY y A))
    (h_f_degY : a_y ≥ natDegreeY A) :
    ∃ Q_y : Finset F, Q_y.card ≥ (n_y : ℕ) - a_y ∧ Q_y ⊆ P_y ∧
      ∀ y ∈ Q_y, evalY y P = quot_x y := by
  classical
  refine ⟨P_y.filter (fun y ↦ evalY y A ≠ 0), ?_, Finset.filter_subset _ _, ?_⟩
  · have := ps_card_eval_y_eq_zero_le_nat_degree_y A hA P_y
    have := Finset.card_filter_add_card_filter_not (s := P_y) (fun y ↦ evalY y A = 0)
    have : {a ∈ P_y | ¬evalY a A = 0}.card = {y ∈ P_y | evalY y A ≠ 0}.card := rfl
    omega
  · intro y hy
    exact mul_right_cancel₀ (Finset.mem_filter.mp hy).2 (by
      rw [← show evalY y (P * A) = evalY y P * evalY y A from by simp [evalY], ← hBA]
      exact h_quot_x y (Finset.mem_filter.mp hy).1)

/-- If `A` and `B` are coprime and agree on sufficiently many lines, then `A` is constant. -/
lemma ps_coprime_case_constant {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y]) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hrel : IsRelPrime A B)
    (h_f_degX : a_x ≥ degreeX A) (h_g_degX : b_x ≥ degreeX B)
    (h_f_degY : a_y ≥ natDegreeY A) (h_g_degY : b_y ≥ natDegreeY B)
    (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y, (quot_x y).natDegree ≤ (b_x - a_x) ∧
      evalY y B = (quot_x y) * (evalY y A))
    (h_quot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ (b_y - a_y) ∧
      evalX x B = (quot_y x) * (evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    degreeX A = 0 ∧ natDegreeY A = 0 := by
  classical
  set mY := natDegreeY A with hmY; set mX := degreeX A with hmX
  set RY := resultant B A b_y mY with hRY
  set RX := resultant (swap B) (swap A) b_x mX with hRX
  have hA0' : swap A ≠ 0 := fun h ↦ hA0 (swap.injective (by simpa using h))
  have hB0' : swap B ≠ 0 := fun h ↦ hB0 (swap.injective (by simpa using h))
  have hRY0 : RY ≠ 0 := by
    simpa [RY, hRY, mY, hmY] using ps_resultant_ne_zero_of_is_rel_prime _ _ b_y
      (by simpa using h_g_degY) hA0 hrel
  have hRX0 : RX ≠ 0 := by
    rw [hRX, show mX = natDegreeY (swap A) from hmX.trans (ps_nat_degree_y_swap A).symm]
    simpa using ps_resultant_ne_zero_of_is_rel_prime _ _ b_x
      (by rw [ps_nat_degree_y_swap]; simpa using h_g_degX) hA0' (ps_is_rel_prime_swap hrel)
  have hcop : Pairwise fun x y : F ↦ IsCoprime (X - C x : F[X]) (X - C y) :=
    pairwise_coprime_X_sub_C fun _ _ h ↦ h
  have hprod_dvd_RY : (∏ x ∈ P_x, (X - C x) ^ mY) ∣ RY :=
    Finset.prod_dvd_of_coprime (fun _ _ _ _ hxy ↦ by simpa using (hcop hxy).pow) fun x hx ↦ by
      obtain ⟨hdegQ, hQ⟩ := h_quot_y x hx
      simpa [RY, hRY, mY, hmY] using ps_resultant_dvd_pow_eval_x _ _ _ _ b_y
        (by omega) (by simpa using h_g_degY) (by omega) hQ
  have hprod_dvd_RX : (∏ y ∈ P_y, (X - C y) ^ mX) ∣ RX :=
    Finset.prod_dvd_of_coprime (fun _ _ _ _ hyy' ↦ by simpa using (hcop hyy').pow) fun y hy ↦ by
      obtain ⟨hdegQ, hQ⟩ := h_quot_x y hy
      simpa [RX, hRX, mX, hmX] using ps_resultant_dvd_pow_eval_y A B y (quot_x y) b_x
        (by omega) (by simpa using h_g_degX) (by omega) hQ
  have hdeg_prod (S : Finset F) (m : ℕ) :
      (∏ x ∈ S, (X - C x) ^ m).natDegree = m * S.card := by
    rw [natDegree_prod _ _ (fun x _ ↦ pow_ne_zero _ (X_sub_C_ne_zero x))]
    simp [natDegree_pow, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- Upper bounds from resultant degree
  have hRY_le : RY.natDegree ≤ mY * b_x + mX * b_y := le_trans
    (by simpa [RY, hRY] using ps_nat_degree_resultant_le A B mY b_y)
    (Nat.add_le_add (Nat.mul_le_mul_left _ h_g_degX) (le_of_eq (Nat.mul_comm b_y (degreeX A))))
  have hRX_le : RX.natDegree ≤ mX * b_y + mY * b_x := by
    have hdeg' : RX.natDegree ≤ mX * degreeX (swap B) + b_x * degreeX (swap A) := by
      simpa [RX, hRX] using ps_nat_degree_resultant_le (swap A) (swap B) mX b_x
    apply le_trans hdeg' (Nat.add_le_add ?_ ?_)
    · rw [ps_degree_x_swap B]; exact Nat.mul_le_mul_left _ (by simpa using h_g_degY)
    · rw [ps_degree_x_swap A]; exact le_of_eq (Nat.mul_comm b_x (natDegreeY A))
  -- Show D := mX * b_y + mY * b_x = 0 via rational argument
  have hmy_le_D : mY * (n_x : ℕ) ≤ mX * b_y + mY * b_x :=
    le_trans (le_trans (Nat.mul_le_mul_left _ h_card_Px)
      ((hdeg_prod P_x mY).symm ▸ natDegree_le_of_dvd hprod_dvd_RY hRY0)) (by linarith)
  have hmx_le_D : mX * (n_y : ℕ) ≤ mX * b_y + mY * b_x :=
    le_trans (le_trans (Nat.mul_le_mul_left _ h_card_Py)
      ((hdeg_prod P_y mX).symm ▸ natDegree_le_of_dvd hprod_dvd_RX hRX0)) hRX_le
  suffices mX * b_y + mY * b_x = 0 by
    constructor
    · simpa [mX, hmX] using show mX = 0 from by
        have : mX * (n_y : ℕ) ≤ 0 := by omega
        exact (mul_eq_zero.mp (Nat.eq_zero_of_le_zero this)).resolve_right (Nat.ne_of_gt n_y.pos)
    · simpa [mY, hmY] using show mY = 0 from by
        have : mY * (n_x : ℕ) ≤ 0 := by omega
        exact (mul_eq_zero.mp (Nat.eq_zero_of_le_zero this)).resolve_right (Nat.ne_of_gt n_x.pos)
  set D : ℚ := ((mX * b_y + mY * b_x : ℕ) : ℚ)
  have hn_x0 : (0 : ℚ) < n_x := by exact_mod_cast n_x.pos
  have hn_y0 : (0 : ℚ) < n_y := by exact_mod_cast n_y.pos
  have hmyq : (mY : ℚ) * n_x ≤ ((mX * b_y + mY * b_x : ℕ) : ℚ) := by exact_mod_cast hmy_le_D
  have hmxq : (mX : ℚ) * n_y ≤ ((mX * b_y + mY * b_x : ℕ) : ℚ) := by exact_mod_cast hmx_le_D
  have hDle : D ≤ D * ((b_x : ℚ) / n_x + (b_y : ℚ) / n_y) := by
    linarith [mul_add D ((b_x : ℚ) / n_x) ((b_y : ℚ) / n_y),
      show D = (mX : ℚ) * b_y + (mY : ℚ) * b_x from by simp [D, Nat.cast_add, Nat.cast_mul],
      show (mY : ℚ) * b_x ≤ D * ((b_x : ℚ) / n_x) from by
        linarith [mul_le_mul_of_nonneg_right hmyq (div_nonneg (Nat.cast_nonneg b_x) hn_x0.le),
          show (mY : ℚ) * n_x * (b_x / n_x) = (mY : ℚ) * b_x from by field_simp],
      show (mX : ℚ) * b_y ≤ D * ((b_y : ℚ) / n_y) from by
        linarith [mul_le_mul_of_nonneg_right hmxq (div_nonneg (Nat.cast_nonneg b_y) hn_y0.le),
          show (mX : ℚ) * n_y * (b_y / n_y) = (mX : ℚ) * b_y from by field_simp]]
  by_contra hD0
  linarith [mul_lt_mul_of_pos_left (show (b_x : ℚ) / n_x + b_y / n_y < 1 by linarith)
    (show 0 < D by positivity)]

/-- Existence of `P` with `B = P * A` when both `A` and `B` are nonzero. -/
lemma ps_exists_p_nonzero {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y]) (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (h_f_degX : a_x ≥ degreeX A) (h_g_degX : b_x ≥ degreeX B)
    (h_f_degY : a_y ≥ natDegreeY A) (h_g_degY : b_y ≥ natDegreeY B)
    (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y, (quot_x y).natDegree ≤ (b_x - a_x) ∧
      evalY y B = (quot_x y) * (evalY y A))
    (h_quot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ (b_y - a_y) ∧
      evalX x B = (quot_y x) * (evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    ∃ P : F[X][Y], B = P * A := by
  classical
  rcases ps_gcd_decompose (A := A) (B := B) hA0 hB0 with ⟨G, A1, B1, hA, hB, hrel, hA1, hB1⟩
  have hG0 : G ≠ 0 := fun hG ↦ hA0 (by simp [hA, hG])
  set g_x := degreeX G; set g_y := natDegreeY G
  have hdegX_A : degreeX A = g_x + degreeX A1 := by
    rw [hA]; simpa [g_x] using degreeX_mul G A1 hG0 hA1
  have hdegY_A : natDegreeY A = g_y + natDegreeY A1 := by
    rw [hA]; simpa [g_y] using degreeY_mul G A1 hG0 hA1
  have hdegX_B : degreeX B = g_x + degreeX B1 := by
    rw [hB]; simpa [g_x] using degreeX_mul G B1 hG0 hB1
  have hdegY_B : natDegreeY B = g_y + natDegreeY B1 := by
    rw [hB]; simpa [g_y] using degreeY_mul G B1 hG0 hB1
  have hbxltnx := ps_bx_lt_nx h_le_1
  have hbyltny := ps_by_lt_ny h_le_1
  have hgx_le_ax : g_x ≤ a_x := le_trans (by simp [hdegX_A]) h_f_degX
  have hgy_le_ay : g_y ≤ a_y := le_trans (by simp [hdegY_A]) h_f_degY
  have hgx_le_bx : g_x ≤ b_x := le_trans hgx_le_ax h_bx_ge_ax
  have hgy_le_by : g_y ≤ b_y := le_trans hgy_le_ay h_by_ge_ay
  have hx_lt_nx : g_x < (n_x : ℕ) := lt_of_le_of_lt hgx_le_bx hbxltnx
  have hy_lt_ny : g_y < (n_y : ℕ) := lt_of_le_of_lt hgy_le_by hbyltny
  let Px' := P_x.filter (fun x ↦ evalX x G ≠ 0)
  let Py' := P_y.filter (fun y ↦ evalY y G ≠ 0)
  have hcard_Px' : (n_x : ℕ) - g_x ≤ Px'.card := by
    have := Finset.card_filter_add_card_filter_not (s := P_x) (fun x ↦ evalX x G = 0)
    have := by simpa [g_x] using ps_card_eval_x_eq_zero_le_degree_x (A := G) hG0 P_x
    have : {a ∈ P_x | ¬evalX a G = 0}.card = Px'.card := rfl
    omega
  have hcard_Py' : (n_y : ℕ) - g_y ≤ Py'.card := by
    have := Finset.card_filter_add_card_filter_not (s := P_y) (fun y ↦ evalY y G = 0)
    have := by simpa [g_y] using ps_card_eval_y_eq_zero_le_nat_degree_y G hG0 P_y
    have : {a ∈ P_y | ¬evalY a G = 0}.card = Py'.card := rfl
    omega
  haveI : Nonempty Px' := ⟨⟨_, (Finset.card_pos.mp (by omega)).choose_spec⟩⟩
  haveI : Nonempty Py' := ⟨⟨_, (Finset.card_pos.mp (by omega)).choose_spec⟩⟩
  let ax' := a_x - g_x; let ay' := a_y - g_y
  let bx' := b_x - g_x; let by' := b_y - g_y
  let nx' : ℕ+ := ⟨(n_x : ℕ) - g_x, Nat.sub_pos_of_lt hx_lt_nx⟩
  let ny' : ℕ+ := ⟨(n_y : ℕ) - g_y, Nat.sub_pos_of_lt hy_lt_ny⟩
  have hdiff_x : bx' - ax' = b_x - a_x := by
    simpa [bx', ax'] using tsub_tsub_tsub_cancel_right hgx_le_ax
  have hdiff_y : by' - ay' = b_y - a_y := by
    simpa [by', ay'] using tsub_tsub_tsub_cancel_right hgy_le_ay
  have hquotX' : ∀ y ∈ Py', (quot_x y).natDegree ≤ (bx' - ax') ∧
      evalY y B1 = (quot_x y) * evalY y A1 := fun y hy ↦
    ⟨hdiff_x ▸ (h_quot_x y (Finset.mem_filter.mp hy).1).1,
     ps_descend_eval_y hA hB y (Finset.mem_filter.mp hy).2 _
       (h_quot_x y (Finset.mem_filter.mp hy).1).2⟩
  have hquotY' : ∀ x ∈ Px', (quot_y x).natDegree ≤ (by' - ay') ∧
      evalX x B1 = (quot_y x) * evalX x A1 := fun x hx ↦
    ⟨hdiff_y ▸ (h_quot_y x (Finset.mem_filter.mp hx).1).1,
     ps_descend_eval_x hA hB x (Finset.mem_filter.mp hx).2 _
       (h_quot_y x (Finset.mem_filter.mp hx).1).2⟩
  have hxfrac : (bx' : ℚ) / (nx' : ℚ) ≤ (b_x : ℚ) / (n_x : ℚ) := by
    have hn2 : (0 : ℚ) < (nx' : ℚ) := by exact_mod_cast nx'.pos
    have hbx'cast : (bx' : ℚ) = (b_x : ℚ) - g_x := by simp [bx', Nat.cast_sub hgx_le_bx]
    have hnx'cast : (nx' : ℚ) = (n_x : ℚ) - g_x := by
      simp [nx', Nat.cast_sub (le_of_lt hx_lt_nx)]
    rw [hbx'cast, hnx'cast,
      div_le_div_iff₀ (by rw [hnx'cast] at hn2; exact hn2) (by exact_mod_cast n_x.pos)]
    nlinarith [show (b_x : ℚ) ≤ n_x from by exact_mod_cast le_of_lt hbxltnx,
      Nat.cast_nonneg (α := ℚ) g_x]
  have hyfrac : (by' : ℚ) / (ny' : ℚ) ≤ (b_y : ℚ) / (n_y : ℚ) := by
    have hn2 : (0 : ℚ) < (ny' : ℚ) := by exact_mod_cast ny'.pos
    have hby'cast : (by' : ℚ) = (b_y : ℚ) - g_y := by simp [by', Nat.cast_sub hgy_le_by]
    have hny'cast : (ny' : ℚ) = (n_y : ℚ) - g_y := by
      simp [ny', Nat.cast_sub (le_of_lt hy_lt_ny)]
    rw [hby'cast, hny'cast,
      div_le_div_iff₀ (by rw [hny'cast] at hn2; exact hn2) (by exact_mod_cast n_y.pos)]
    nlinarith [show (b_y : ℚ) ≤ n_y from by exact_mod_cast le_of_lt hbyltny,
      Nat.cast_nonneg (α := ℚ) g_y]
  have hconst := ps_coprime_case_constant ax' ay' bx' by' nx' ny'
    (by simpa [bx', ax'] using Nat.sub_le_sub_right h_bx_ge_ax g_x)
    (by simpa [by', ay'] using Nat.sub_le_sub_right h_by_ge_ay g_y)
    A1 B1 hA1 hB1 hrel
    (by simpa [ax', ge_iff_le] using
      le_tsub_of_add_le_left (show g_x + degreeX A1 ≤ a_x by simpa [hdegX_A] using h_f_degX))
    (by simpa [bx', ge_iff_le] using
      le_tsub_of_add_le_left (show g_x + degreeX B1 ≤ b_x by simpa [hdegX_B] using h_g_degX))
    (by simpa [ay', ge_iff_le] using
      le_tsub_of_add_le_left (show g_y + natDegreeY A1 ≤ a_y by simpa [hdegY_A] using h_f_degY))
    (by simpa [by', ge_iff_le] using
      le_tsub_of_add_le_left (show g_y + natDegreeY B1 ≤ b_y by simpa [hdegY_B] using h_g_degY))
    Px' Py' quot_x quot_y
    (by simpa [nx'] using hcard_Px') (by simpa [ny'] using hcard_Py')
    hquotX' hquotY' (lt_of_le_of_lt (add_le_add hxfrac hyfrac) h_le_1)
  rcases ps_exists_p_of_degree_x_eq_zero_nat_degree_y_eq_zero hA1 hconst.1 hconst.2 (B := B1)
    with ⟨P1, hB1fac⟩
  exact ⟨P1, by rw [hB, hB1fac, hA]; ring⟩

/-- Main existence: if `B/A` agrees with low-degree quotients on enough lines, then `A ∣ B`. -/
lemma ps_exists_p {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y])
    (h_f_degX : a_x ≥ degreeX A) (h_g_degX : b_x ≥ degreeX B)
    (h_f_degY : a_y ≥ natDegreeY A) (h_g_degY : b_y ≥ natDegreeY B)
    (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x : F → F[X]) (quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y, (quot_x y).natDegree ≤ (b_x - a_x) ∧
      evalY y B = (quot_x y) * (evalY y A))
    (h_quot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ (b_y - a_y) ∧
      evalX x B = (quot_y x) * (evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    ∃ P : F[X][Y], B = P * A := by
  classical
  letI : DecidableEq F := Classical.decEq F
  by_cases hB0 : B = 0
  · exact ⟨0, by simp [hB0]⟩
  by_cases hA0 : A = 0
  · exfalso
    have hBx_lt_card : b_x < P_x.card := lt_of_lt_of_le (ps_bx_lt_nx h_le_1) h_card_Px
    have h_all_zero : ∀ x ∈ P_x, evalX x B = 0 := fun x hx ↦ by
      simpa [hA0, ps_eval_x_eq_map] using (h_quot_y x hx).2
    have := ps_card_eval_x_eq_zero_le_degree_x B hB0 P_x
    rw [Finset.filter_true_of_mem h_all_zero] at this; omega
  · exact ps_exists_p_nonzero a_x a_y b_x b_y n_x n_y h_bx_ge_ax h_by_ge_ay A B hA0 hB0
      h_f_degX h_g_degX h_f_degY h_g_degY P_x P_y quot_x quot_y h_card_Px h_card_Py
      h_quot_x h_quot_y h_le_1
