/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.PolishchukSpielman.Degrees
import ArkLib.Data.CodingTheory.PolishchukSpielman.Resultant
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

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

lemma ps_exists_p_of_degree_x_eq_zero_nat_degree_y_eq_zero {F : Type} [Field F]
    {A B : F[X][Y]} (hA0 : A ≠ 0)
    (hdegX : Polynomial.Bivariate.degreeX A = 0)
    (hdegY : Polynomial.Bivariate.natDegreeY A = 0) :
    ∃ P : F[X][Y], B = P * A := by
  classical
  have hdegY' : A.natDegree = 0 := by
    simpa [Polynomial.Bivariate.natDegreeY] using hdegY
  rcases (Polynomial.natDegree_eq_zero).1 hdegY' with ⟨a0, ha0⟩
  subst ha0
  simp_all only [ne_eq, C_eq_zero, natDegree_C]
  have ha0ne : a0 ≠ 0 := by
    exact hA0
  have hdegX' : Polynomial.Bivariate.degreeX (C a0 : F[X][Y]) = 0 := by
    exact hdegX
  have ha0_natdeg : a0.natDegree = 0 := by
    simpa [Polynomial.Bivariate.degreeX, Polynomial.support_C ha0ne] using hdegX'
  rcases (Polynomial.natDegree_eq_zero).1 ha0_natdeg with ⟨a, ha⟩
  subst ha
  simp_all only [not_false_eq_true, ne_eq, map_eq_zero, natDegree_C]
  have ha_ne : a ≠ 0 := by
    exact ha0ne
  have hinner : (C a⁻¹ : F[X]) * (C a : F[X]) = C (a⁻¹ * a) := by
    exact Eq.symm C_mul
  have hCa : (C (C a⁻¹) : F[X][Y]) * C (C a) = 1 := by
    calc
      (C (C a⁻¹) : F[X][Y]) * C (C a) = C ((C a⁻¹ : F[X]) * (C a : F[X])) := by exact Eq.symm C_mul
      _ = C (C (a⁻¹ * a)) := by rw [hinner]
      _ = 1 := by simp [ha_ne]

  refine ⟨B * C (C a⁻¹), ?_⟩
  simp_all only [not_false_eq_true, ne_eq, inv_mul_cancel₀, map_one]
  ext n n_1 : 2
  simp_all only [coeff_mul_C, ne_eq, not_false_eq_true, inv_mul_cancel_right₀]


lemma ps_exists_qx_of_cancel {F : Type} [Field F] [DecidableEq F]
    (a_x : ℕ) (n_x : ℕ+)
    {A B P : F[X][Y]}
    (hA : A ≠ 0)
    (hBA : B = P * A)
    (P_x : Finset F) (h_card_Px : n_x ≤ P_x.card)
    (quot_y : F → F[X])
    (h_quot_y : ∀ x ∈ P_x,
      Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A))
    (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A) :
    ∃ Q_x : Finset F,
      Q_x.card ≥ (n_x : ℕ) - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Polynomial.Bivariate.evalX x P = quot_y x := by
  classical
  let Q_x : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0)
  refine ⟨Q_x, ?_, ?_, ?_⟩
  · -- cardinality bound
    let Z_x : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A = 0)
    have hZdeg : Z_x.card ≤ Polynomial.Bivariate.degreeX A := by
      exact ps_card_eval_x_eq_zero_le_degree_x A hA P_x
    have hsplit : Z_x.card + Q_x.card = P_x.card := by
      exact Finset.filter_card_add_filter_neg_card_eq_card fun x ↦ evalX x A = 0
    have hPsub : P_x.card - a_x ≤ Q_x.card := by
      grind only [= degreeX_as_weighted_deg, ← Bivariate.mul_ne_zero, quotient_nezero, cases Or]
    grind only
  · -- subset
    simp_all only [ne_eq, Finset.filter_subset, Q_x]
  · -- agreement by cancellation
    intro x hx
    have hx' : x ∈ P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0) := by
      simpa [Q_x] using hx
    have hxP : x ∈ P_x := by
      exact Finset.mem_of_mem_filter x hx
    have hxA : Polynomial.Bivariate.evalX x A ≠ 0 := by
      simp_all only [ne_eq, Finset.mem_filter, true_and, not_false_eq_true, Q_x]
    -- relate evalX to `Polynomial.map` so we can use `map_mul`
    have evalX_eq_map (x : F) (f : F[X][Y]) :
        Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
      ext n
      simp [Polynomial.Bivariate.evalX, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
        Polynomial.toFinsupp_apply]
    have evalX_mul (x : F) (f g : F[X][Y]) :
        Polynomial.Bivariate.evalX x (f * g) =
          Polynomial.Bivariate.evalX x f * Polynomial.Bivariate.evalX x g := by
      simp [evalX_eq_map, Polynomial.map_mul]
    have hBAx : Polynomial.Bivariate.evalX x B =
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
      grind only [= Finset.mem_filter, = degreeX_as_weighted_deg, ← Bivariate.mul_ne_zero,
        quotient_nezero]
    have hquot : Polynomial.Bivariate.evalX x B =
        (quot_y x) * Polynomial.Bivariate.evalX x A := by
      exact h_quot_y x hxP
    have hcancel_eq :
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A =
          (quot_y x) * Polynomial.Bivariate.evalX x A := by
      grind only
    exact mul_right_cancel₀ hxA hcancel_eq

lemma ps_exists_qy_of_cancel {F : Type} [Field F] [DecidableEq F]
    (a_y : ℕ) (n_y : ℕ+)
    {A B P : F[X][Y]}
    (hA : A ≠ 0)
    (hBA : B = P * A)
    (P_y : Finset F) (h_card_Py : n_y ≤ P_y.card)
    (quot_x : F → F[X])
    (h_quot_x : ∀ y ∈ P_y,
      Polynomial.Bivariate.evalY y B = (quot_x y) * (Polynomial.Bivariate.evalY y A))
    (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A) :
    ∃ Q_y : Finset F,
      Q_y.card ≥ (n_y : ℕ) - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Polynomial.Bivariate.evalY y P = quot_x y := by
  classical
  let Q_y : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A ≠ 0)
  refine ⟨Q_y, ?_, ?_, ?_⟩
  · -- cardinality bound
    let bad : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A = 0)
    have hsum : bad.card + Q_y.card = P_y.card := by
      exact Finset.filter_card_add_filter_neg_card_eq_card fun y ↦ evalY y A = 0
    have hbad : bad.card ≤ a_y := by
      have h1 : bad.card ≤ Polynomial.Bivariate.natDegreeY A := by
        exact ps_card_eval_y_eq_zero_le_nat_degree_y A hA P_y
      exact le_trans h1 h_f_degY
    have hny : (n_y : ℕ) ≤ P_y.card := by
      exact h_card_Py
    have h1 : (n_y : ℕ) - a_y ≤ P_y.card - a_y := by
      exact Nat.sub_le_sub_right hny a_y
    have h2 : P_y.card - a_y ≤ P_y.card - bad.card := by
      exact Nat.sub_le_sub_left hbad P_y.card
    have hsub : P_y.card - bad.card = Q_y.card := by
      exact Eq.symm (Nat.eq_sub_of_add_eq' hsum)
      -- (bad + Q) - bad = Q
    have h12 : (n_y : ℕ) - a_y ≤ P_y.card - bad.card := by
      exact le_trans h1 h2
    have : (n_y : ℕ) - a_y ≤ Q_y.card := by
      exact le_of_le_of_eq h12 hsub
    exact this
  · -- subset
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  · -- evaluation property
    intro y hy
    have hyP : y ∈ P_y := (Finset.mem_filter.mp hy).1
    have hyA : Polynomial.Bivariate.evalY y A ≠ 0 := (Finset.mem_filter.mp hy).2
    have hquot : Polynomial.Bivariate.evalY y B = (quot_x y) * Polynomial.Bivariate.evalY y A :=
      h_quot_x y hyP
    have hquot' :
    Polynomial.Bivariate.evalY y (P * A) = (quot_x y) * Polynomial.Bivariate.evalY y A := by
      simpa [hBA] using hquot
    have hmul : Polynomial.Bivariate.evalY y (P * A) =
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A := by
      simp [Polynomial.Bivariate.evalY]
    have hcancel :
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A =
          (quot_x y) * Polynomial.Bivariate.evalY y A := by
      calc
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A =
            Polynomial.Bivariate.evalY y (P * A) := by simpa using hmul.symm
        _ = (quot_x y) * Polynomial.Bivariate.evalY y A := hquot'
    exact mul_right_cancel₀ hyA hcancel





lemma ps_coprime_case_constant {F : Type} [Field F] [DecidableEq F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y])
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hrel : IsRelPrime A B)
    (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
    (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
    (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A)
    (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
    (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y,
      (quot_x y).natDegree ≤ (b_x - a_x) ∧
        Polynomial.Bivariate.evalY y B = (quot_x y) * (Polynomial.Bivariate.evalY y A))
    (h_quot_y : ∀ x ∈ P_x,
      (quot_y x).natDegree ≤ (b_y - a_y) ∧
        Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    Polynomial.Bivariate.degreeX A = 0 ∧ Polynomial.Bivariate.natDegreeY A = 0 := by
  classical
  -- abbreviations for degrees
  set mY : ℕ := Polynomial.Bivariate.natDegreeY A with hmY
  set mX : ℕ := Polynomial.Bivariate.degreeX A with hmX
  -- resultant in the Y-direction
  set RY : F[X] := Polynomial.resultant A B mY b_y with hRY
  -- for the X-direction we use the swapped polynomials
  set RX : F[X] :=
      Polynomial.resultant (Polynomial.Bivariate.swap A)
        (Polynomial.Bivariate.swap B) mX b_x with hRX

  -- convenient bounds coming from the new hypotheses
  have hmY_le_ay : mY ≤ a_y := by
    simpa [hmY.symm] using h_f_degY
  have hmX_le_ax : mX ≤ a_x := by
    simpa [hmX.symm] using h_f_degX
  have hax_le_bx : a_x ≤ b_x := by
    simpa using h_bx_ge_ax
  have hay_le_by : a_y ≤ b_y := by
    simpa using h_by_ge_ay
  have hmY_le_by : mY ≤ b_y := le_trans hmY_le_ay hay_le_by
  have hmX_le_bx : mX ≤ b_x := le_trans hmX_le_ax hax_le_bx

  -- nonvanishing of the two resultants from coprimality
  have hRY0 : RY ≠ 0 := by
    have h :=
      ps_resultant_ne_zero_of_is_rel_prime (A := A) (B := B) (n := b_y) (hn := by
        -- natDegreeY B ≤ b_y
        simpa using h_g_degY)
        (hA0 := hA0) (hrel := hrel)
    simpa [RY, hRY, mY, hmY] using h

  have hA0' : Polynomial.Bivariate.swap A ≠ 0 := by
    intro h
    apply hA0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simpa using h)

  have hB0' : Polynomial.Bivariate.swap B ≠ 0 := by
    intro h
    apply hB0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simpa using h)

  have hrel' : IsRelPrime (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) :=
    ps_is_rel_prime_swap (A := A) (B := B) hrel

  have hnX : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap B) ≤ b_x := by
    rw [ps_nat_degree_y_swap (f := B)]
    simpa using h_g_degX

  have hRX0 : RX ≠ 0 := by
    have h :=
      ps_resultant_ne_zero_of_is_rel_prime
        (A := Polynomial.Bivariate.swap A) (B := Polynomial.Bivariate.swap B) (n := b_x) (hn := hnX)
        (hA0 := hA0') (hrel := hrel')
    -- unfold RX and rewrite the exponent to match the lemma
    rw [hRX]
    have hnat : mX = Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) := by
      -- mX = degreeX A = natDegreeY (swap A)
      exact hmX.trans (ps_nat_degree_y_swap (f := A)).symm
    -- replace mX by natDegreeY (swap A)
    rw [hnat]
    simpa using h

  -- divisibility of RY by the product over x∈P_x of (X - C x)^mY
  have hprod_dvd_RY : (∏ x ∈ P_x, (X - C x) ^ mY) ∣ RY := by
    have hpair_all : Pairwise (fun x y : F => IsCoprime (X - C x : F[X]) (X - C y : F[X])) := by
      simpa using
        (Polynomial.pairwise_coprime_X_sub_C (K := F) (s := fun x : F => x)
          (by
            intro a b h
            exact h))
    have hpair : (P_x : Set F).Pairwise
        (fun x y : F => IsCoprime ((X - C x : F[X]) ^ mY) ((X - C y : F[X]) ^ mY)) := by
      intro x hx y hy hxy
      have hcop : IsCoprime (X - C x : F[X]) (X - C y : F[X]) := hpair_all hxy
      simpa using (hcop.pow (m := mY) (n := mY))
    have hdiv : ∀ x ∈ P_x, (X - C x) ^ mY ∣ RY := by
      intro x hx
      rcases h_quot_y x hx with ⟨hdegQ, hQ⟩
      have h :=
        ps_resultant_dvd_pow_eval_x (A := A) (B := B) (x := x) (Q := quot_y x) (n := b_y)
          (hmn := by
            -- natDegreeY A ≤ b_y
            simpa [hmY.symm] using hmY_le_by)
          (hn := by
            simpa using h_g_degY)
          (hQdeg := by
            have h1 : (quot_y x).natDegree ≤ b_y - a_y := hdegQ
            have h2 : b_y - a_y ≤ b_y - mY := by
              exact Nat.sub_le_sub_left hmY_le_ay b_y
            exact le_trans h1 h2)
          (hQ := hQ)
      simpa [RY, hRY, mY, hmY] using h
    exact
      Finset.prod_dvd_of_coprime (t := P_x) (s := fun x : F => (X - C x : F[X]) ^ mY) (z := RY)
        hpair hdiv

  -- analogous divisibility for RX over y∈P_y
  have hprod_dvd_RX : (∏ y ∈ P_y, (X - C y) ^ mX) ∣ RX := by
    have hpair_all : Pairwise (fun y y' : F => IsCoprime (X - C y : F[X]) (X - C y' : F[X])) := by
      simpa using
        (Polynomial.pairwise_coprime_X_sub_C (K := F) (s := fun y : F => y)
          (by
            intro a b h
            exact h))
    have hpair : (P_y : Set F).Pairwise
        (fun y y' : F => IsCoprime ((X - C y : F[X]) ^ mX) ((X - C y' : F[X]) ^ mX)) := by
      intro y hy y' hy' hyy'
      have hcop : IsCoprime (X - C y : F[X]) (X - C y' : F[X]) := hpair_all hyy'
      simpa using (hcop.pow (m := mX) (n := mX))
    have hdiv : ∀ y ∈ P_y, (X - C y) ^ mX ∣ RX := by
      intro y hy
      rcases h_quot_x y hy with ⟨hdegQ, hQ⟩
      have h :=
        ps_resultant_dvd_pow_eval_y (A := A) (B := B) (y := y) (Q := quot_x y) (n := b_x)
          (hmn := by
            -- degreeX A ≤ b_x
            simpa [hmX.symm] using hmX_le_bx)
          (hn := by
            simpa using h_g_degX)
          (hQdeg := by
            have h1 : (quot_x y).natDegree ≤ b_x - a_x := hdegQ
            have h2 : b_x - a_x ≤ b_x - mX := by
              exact Nat.sub_le_sub_left hmX_le_ax b_x
            exact le_trans h1 h2)
          (hQ := hQ)
      have h' : (X - C y) ^ mX ∣
          Polynomial.resultant (Polynomial.Bivariate.swap A)
            (Polynomial.Bivariate.swap B) mX b_x := by
        simpa [mX, hmX] using h
      simpa [RX, hRX] using h'
    exact
      Finset.prod_dvd_of_coprime (t := P_y) (s := fun y : F => (X - C y : F[X]) ^ mX) (z := RX)
        hpair hdiv

  -- lower bounds on natDegrees from divisibility
  have hdeg_prod_RY : (∏ x ∈ P_x, (X - C x) ^ mY).natDegree = mY * P_x.card := by
    have hne : ∀ x ∈ P_x, (X - C x : F[X]) ^ mY ≠ 0 := by
      intro x hx
      exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
    calc
      (∏ x ∈ P_x, (X - C x : F[X]) ^ mY).natDegree
          = ∑ x ∈ P_x, ((X - C x : F[X]) ^ mY).natDegree := by
              simpa using
                (Polynomial.natDegree_prod (s := P_x) (f := fun x : F => (X - C x : F[X]) ^ mY) hne)
      _ = ∑ x ∈ P_x, mY := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have := (Polynomial.natDegree_pow (p := (X - C x : F[X])) (n := mY))
            simp [Polynomial.natDegree_X_sub_C, Nat.mul_one]
      _ = mY * P_x.card := by
            simp only [Finset.sum_const, smul_eq_mul]
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  have hdeg_prod_RX : (∏ y ∈ P_y, (X - C y) ^ mX).natDegree = mX * P_y.card := by
    have hne : ∀ y ∈ P_y, (X - C y : F[X]) ^ mX ≠ 0 := by
      intro y hy
      exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero y)
    calc
      (∏ y ∈ P_y, (X - C y : F[X]) ^ mX).natDegree
          = ∑ y ∈ P_y, ((X - C y : F[X]) ^ mX).natDegree := by
              simpa using
                (Polynomial.natDegree_prod (s := P_y) (f := fun y : F => (X - C y : F[X]) ^ mX) hne)
      _ = ∑ y ∈ P_y, mX := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            have := (Polynomial.natDegree_pow (p := (X - C y : F[X])) (n := mX))
            simp only [natDegree_pow, natDegree_sub_C, natDegree_X, mul_one]
      _ = mX * P_y.card := by
            simp [Nat.mul_comm]

  have hmy_card_le : mY * (n_x : ℕ) ≤ RY.natDegree := by
    have h1 : (∏ x ∈ P_x, (X - C x) ^ mY).natDegree ≤ RY.natDegree :=
      Polynomial.natDegree_le_of_dvd hprod_dvd_RY hRY0
    have hnx : (n_x : ℕ) ≤ P_x.card := h_card_Px
    have h2 : mY * (n_x : ℕ) ≤ mY * P_x.card := Nat.mul_le_mul_left _ hnx
    calc
      mY * (n_x : ℕ) ≤ mY * P_x.card := h2
      _ = (∏ x ∈ P_x, (X - C x) ^ mY).natDegree := by
            simp [hdeg_prod_RY]
      _ ≤ RY.natDegree := h1

  have hmx_card_le : mX * (n_y : ℕ) ≤ RX.natDegree := by
    have h1 : (∏ y ∈ P_y, (X - C y) ^ mX).natDegree ≤ RX.natDegree :=
      Polynomial.natDegree_le_of_dvd hprod_dvd_RX hRX0
    have hny : (n_y : ℕ) ≤ P_y.card := h_card_Py
    have h2 : mX * (n_y : ℕ) ≤ mX * P_y.card := Nat.mul_le_mul_left _ hny
    calc
      mX * (n_y : ℕ) ≤ mX * P_y.card := h2
      _ = (∏ y ∈ P_y, (X - C y) ^ mX).natDegree := by
            simp [hdeg_prod_RX]
      _ ≤ RX.natDegree := h1

  -- upper bounds on natDegrees from the given resultant degree lemma
  have hRY_le : RY.natDegree ≤ mY * b_x + mX * b_y := by
    have hdeg :=
      ps_nat_degree_resultant_le (A := A) (B := B) (m := mY) (n := b_y)
    have hdeg' :
        RY.natDegree ≤ mY * Polynomial.Bivariate.degreeX B + b_y * Polynomial.Bivariate.degreeX A := by
      simpa [RY, hRY] using hdeg
    have hBx : Polynomial.Bivariate.degreeX B ≤ b_x := by
      simpa using h_g_degX
    have h1 : mY * Polynomial.Bivariate.degreeX B ≤ mY * b_x := Nat.mul_le_mul_left _ hBx
    have h2 : b_y * Polynomial.Bivariate.degreeX A ≤ mX * b_y := by
      -- rewrite degreeX A as mX
      have : b_y * Polynomial.Bivariate.degreeX A = mX * b_y := by
        -- commutativity of Nat multiplication
        -- simp [mX]
        exact Nat.mul_comm b_y (degreeX A)
      exact le_of_eq this
    have hsum :
        mY * Polynomial.Bivariate.degreeX B + b_y * Polynomial.Bivariate.degreeX A ≤ mY * b_x + mX * b_y :=
      Nat.add_le_add h1 h2
    exact le_trans hdeg' hsum

  have hRX_le : RX.natDegree ≤ mX * b_y + mY * b_x := by
    have hm_swap : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) ≤ mX := by
      simpa [hmX.symm] using (le_of_eq (ps_nat_degree_y_swap (f := A)))
    have hdeg :=
      ps_nat_degree_resultant_le (A := Polynomial.Bivariate.swap A)
        (B := Polynomial.Bivariate.swap B) (m := mX) (n := b_x)
    have hdeg' :
        RX.natDegree ≤
          mX * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap B) +
            b_x * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap A) := by
      simpa [RX, hRX] using hdeg
    have h1 : mX * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap B) ≤ mX * b_y := by
      -- degreeX (swap B) = natDegreeY B ≤ b_y
      rw [ps_degree_x_swap (f := B)]
      have : Polynomial.Bivariate.natDegreeY B ≤ b_y := by
        simpa using h_g_degY
      exact Nat.mul_le_mul_left _ this
    have h2 : b_x * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap A) ≤ mY * b_x := by
      -- degreeX (swap A) = natDegreeY A = mY
      rw [ps_degree_x_swap (f := A)]
      -- now both sides are equal by commutativity
      have : b_x * Polynomial.Bivariate.natDegreeY A = mY * b_x := by
        -- rewrite natDegreeY A as mY
        simp [hmY.symm, Nat.mul_comm]
      exact le_of_eq this
    have hsum :
        mX * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap B) +
            b_x * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap A)
          ≤ mX * b_y + mY * b_x :=
      Nat.add_le_add h1 h2
    exact le_trans hdeg' hsum

  -- combine bounds to get the key inequalities
  have hmy_le_D : mY * (n_x : ℕ) ≤ mX * b_y + mY * b_x := by
    -- align terms using commutativity
    have hRY_le' : RY.natDegree ≤ mX * b_y + mY * b_x := by
      have : mY * b_x + mX * b_y = mX * b_y + mY * b_x := by ac_rfl
      exact le_trans hRY_le (by simp [this])
    exact le_trans hmy_card_le hRY_le'

  have hmx_le_D : mX * (n_y : ℕ) ≤ mX * b_y + mY * b_x := by
    exact le_trans hmx_card_le hRX_le

  -- Now use the rational inequality to show the common bound must be 0.
  have hD0 : mX * b_y + mY * b_x = 0 := by
    have hn_x0 : (0 : ℚ) < (n_x : ℚ) := by
      exact_mod_cast (show (0 : ℕ) < (n_x : ℕ) from n_x.pos)
    have hn_y0 : (0 : ℚ) < (n_y : ℚ) := by
      exact_mod_cast (show (0 : ℕ) < (n_y : ℕ) from n_y.pos)
    -- cast the inequalities
    have hmyq : (mY : ℚ) * (n_x : ℚ) ≤ ((mX * b_y + mY * b_x : ℕ) : ℚ) := by
      exact_mod_cast hmy_le_D
    have hmxq : (mX : ℚ) * (n_y : ℚ) ≤ ((mX * b_y + mY * b_x : ℕ) : ℚ) := by
      exact_mod_cast hmx_le_D
    set D : ℚ := ((mX * b_y + mY * b_x : ℕ) : ℚ) with hD
    have hD_nonneg : 0 ≤ D := by
      simpa [D] using (Nat.cast_nonneg (mX * b_y + mY * b_x : ℕ))
    have hn_x0' : (n_x : ℚ) ≠ 0 := ne_of_gt hn_x0
    have hn_y0' : (n_y : ℚ) ≠ 0 := ne_of_gt hn_y0
    have h1 : (mY : ℚ) * (b_x : ℚ) ≤ D * ((b_x : ℚ) / (n_x : ℚ)) := by
      have hb : (mY : ℚ) * (n_x : ℚ) ≤ D := by
        simpa [D] using hmyq
      have hnonneg : 0 ≤ (b_x : ℚ) / (n_x : ℚ) := by
        exact div_nonneg (by exact_mod_cast (Nat.zero_le b_x)) (le_of_lt hn_x0)
      have hb' := mul_le_mul_of_nonneg_right hb hnonneg
      have : (mY : ℚ) * (n_x : ℚ) * ((b_x : ℚ) / (n_x : ℚ)) = (mY : ℚ) * (b_x : ℚ) := by
        field_simp [hn_x0']
        ring
      simpa [mul_assoc, this] using hb'
    have h2 : (mX : ℚ) * (b_y : ℚ) ≤ D * ((b_y : ℚ) / (n_y : ℚ)) := by
      have hb : (mX : ℚ) * (n_y : ℚ) ≤ D := by
        simpa [D] using hmxq
      have hnonneg : 0 ≤ (b_y : ℚ) / (n_y : ℚ) := by
        exact div_nonneg (by exact_mod_cast (Nat.zero_le b_y)) (le_of_lt hn_y0)
      have hb' := mul_le_mul_of_nonneg_right hb hnonneg
      have : (mX : ℚ) * (n_y : ℕ) * ((b_y : ℚ) / (n_y : ℚ)) = (mX : ℚ) * (b_y : ℚ) := by
        field_simp [hn_y0']
        ring
      simpa [mul_assoc, this] using hb'
    have hDexpr : D = (mX : ℚ) * (b_y : ℚ) + (mY : ℚ) * (b_x : ℚ) := by
      simp [D, Nat.cast_add, Nat.cast_mul]
    have hDle : D ≤ D * ((b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) := by
      have : (mX : ℚ) * (b_y : ℚ) + (mY : ℚ) * (b_x : ℚ) ≤
          D * ((b_y : ℚ) / (n_y : ℚ)) + D * ((b_x : ℚ) / (n_x : ℚ)) := by
        exact add_le_add h2 h1
      have : D ≤ D * ((b_y : ℚ) / (n_y : ℚ)) + D * ((b_x : ℚ) / (n_x : ℚ)) := by
        simpa [hDexpr] using this
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using this
    have hlt : (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) < 1 := by
      linarith
    have : D = 0 := by
      by_contra hD0
      have hDpos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
      have hmul_lt : D * ((b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) < D := by
        have := mul_lt_mul_of_pos_left hlt hDpos
        simpa [mul_one] using this
      have := lt_of_le_of_lt hDle hmul_lt
      exact lt_irrefl _ this
    have : ((mX * b_y + mY * b_x : ℕ) : ℚ) = 0 := by
      simpa [D] using this
    exact (Nat.cast_inj (R := ℚ)).1 (by simpa using this)

  -- finally deduce mX = 0 and mY = 0 from the inequalities with n_x,n_y > 0
  have hmX0 : mX = 0 := by
    have hle : mX * (n_y : ℕ) ≤ 0 := by
      simpa [hD0] using hmx_le_D
    have hmul : mX * (n_y : ℕ) = 0 := Nat.eq_zero_of_le_zero hle
    have hny0 : (n_y : ℕ) ≠ 0 := Nat.ne_of_gt n_y.pos
    have : mX = 0 ∨ (n_y : ℕ) = 0 := by
      simpa using (mul_eq_zero.mp hmul)
    exact this.resolve_right hny0

  have hmY0 : mY = 0 := by
    have hle : mY * (n_x : ℕ) ≤ 0 := by
      simpa [hD0] using hmy_le_D
    have hmul : mY * (n_x : ℕ) = 0 := Nat.eq_zero_of_le_zero hle
    have hnx0 : (n_x : ℕ) ≠ 0 := Nat.ne_of_gt n_x.pos
    have : mY = 0 ∨ (n_x : ℕ) = 0 := by
      simpa using (mul_eq_zero.mp hmul)
    exact this.resolve_right hnx0

  refine ⟨?_, ?_⟩
  · simpa [mX, hmX] using hmX0
  · simpa [mY, hmY] using hmY0


lemma ps_exists_p_nonzero {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y])
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
    (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
    (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A)
    (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
    (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
    (quot_x quot_y : F → F[X])
    (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
    (h_quot_x : ∀ y ∈ P_y,
      (quot_x y).natDegree ≤ (b_x - a_x) ∧
        Polynomial.Bivariate.evalY y B = (quot_x y) * (Polynomial.Bivariate.evalY y A))
    (h_quot_y : ∀ x ∈ P_x,
      (quot_y x).natDegree ≤ (b_y - a_y) ∧
        Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A))
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    ∃ P : F[X][Y], B = P * A := by
  classical
  rcases ps_gcd_decompose (A := A) (B := B) hA0 hB0 with ⟨G, A1, B1, hA, hB, hrel, hA1, hB1⟩
  have hG0 : G ≠ 0 := by
    intro hG
    apply hA0
    simp [hA, hG]
    -- degrees of the gcd factor
  set g_x : ℕ := Polynomial.Bivariate.degreeX G
  set g_y : ℕ := Polynomial.Bivariate.natDegreeY G
  have hdegX_A : Polynomial.Bivariate.degreeX A = g_x + Polynomial.Bivariate.degreeX A1 := by
    rw [hA]
    simpa [g_x] using
      (Polynomial.Bivariate.degreeX_mul (F := F) (f := G) (g := A1) hG0 hA1)
  have hdegY_A : Polynomial.Bivariate.natDegreeY A = g_y + Polynomial.Bivariate.natDegreeY A1 := by
    rw [hA]
    simpa [g_y] using
      (Polynomial.Bivariate.degreeY_mul (F := F) (f := G) (g := A1) hG0 hA1)
  have hdegX_B : Polynomial.Bivariate.degreeX B = g_x + Polynomial.Bivariate.degreeX B1 := by
    rw [hB]
    simpa [g_x] using
      (Polynomial.Bivariate.degreeX_mul (F := F) (f := G) (g := B1) hG0 hB1)
  have hdegY_B : Polynomial.Bivariate.natDegreeY B = g_y + Polynomial.Bivariate.natDegreeY B1 := by
    rw [hB]
    simpa [g_y] using
      (Polynomial.Bivariate.degreeY_mul (F := F) (f := G) (g := B1) hG0 hB1)
    -- inequalities gx < n_x and gy < n_y
  have hbxltnx : b_x < (n_x : ℕ) :=
    ps_bx_lt_nx (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
  have hbyltny : b_y < (n_y : ℕ) :=
    ps_by_lt_ny (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
  have hgx_le_degA : g_x ≤ Polynomial.Bivariate.degreeX A := by
    simp [hdegX_A]
  have hgy_le_degYA : g_y ≤ Polynomial.Bivariate.natDegreeY A := by
    simp [hdegY_A]
  have hgx_le_ax : g_x ≤ a_x := le_trans hgx_le_degA h_f_degX
  have hgy_le_ay : g_y ≤ a_y := le_trans hgy_le_degYA h_f_degY
  have hgx_le_bx : g_x ≤ b_x := le_trans hgx_le_ax h_bx_ge_ax
  have hgy_le_by : g_y ≤ b_y := le_trans hgy_le_ay h_by_ge_ay
  have hx_lt_nx : g_x < (n_x : ℕ) := lt_of_le_of_lt hgx_le_bx hbxltnx
  have hy_lt_ny : g_y < (n_y : ℕ) := lt_of_le_of_lt hgy_le_by hbyltny
  -- filtered sets
  let Px' : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x G ≠ 0)
  let Py' : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y G ≠ 0)
  -- card bounds on zeros
  have hcard_zero_x : (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card ≤ g_x := by
    simpa [g_x] using ps_card_eval_x_eq_zero_le_degree_x (A := G) hG0 P_x
  have hcard_zero_y : (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card ≤ g_y := by
    simpa [g_y] using ps_card_eval_y_eq_zero_le_nat_degree_y (A := G) hG0 P_y
    -- card lower bounds on filtered sets
  have hcard_Px' : (n_x : ℕ) - g_x ≤ Px'.card := by
    have hpart : (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card + Px'.card = P_x.card := by
      simpa [Px'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_x)
          (p := fun x => Polynomial.Bivariate.evalX x G = 0))
    have hPx'_eq : Px'.card = P_x.card - (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card := by
      have := congrArg (fun t => t - (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card) hpart
      simpa [Nat.add_sub_cancel_left] using this
    have h1 : (n_x : ℕ) - g_x ≤ P_x.card - g_x := Nat.sub_le_sub_right h_card_Px g_x
    have h2 : P_x.card - g_x ≤ Px'.card := by
      simpa [hPx'_eq] using (Nat.sub_le_sub_left hcard_zero_x P_x.card)
    exact le_trans h1 h2
  have hcard_Py' : (n_y : ℕ) - g_y ≤ Py'.card := by
    have hpart : (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card + Py'.card = P_y.card := by
      simpa [Py'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_y)
          (p := fun y => Polynomial.Bivariate.evalY y G = 0))
    have hPy'_eq : Py'.card = P_y.card - (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card := by
      have := congrArg (fun t => t - (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card) hpart
      simpa [Nat.add_sub_cancel_left] using this
    have h1 : (n_y : ℕ) - g_y ≤ P_y.card - g_y := Nat.sub_le_sub_right h_card_Py g_y
    have h2 : P_y.card - g_y ≤ Py'.card := by
      simpa [hPy'_eq] using (Nat.sub_le_sub_left hcard_zero_y P_y.card)
    exact le_trans h1 h2
    -- Nonempty instances for filtered sets
  have hxpos : 0 < Px'.card := lt_of_lt_of_le (Nat.sub_pos_of_lt hx_lt_nx) hcard_Px'
  have hypos : 0 < Py'.card := lt_of_lt_of_le (Nat.sub_pos_of_lt hy_lt_ny) hcard_Py'
  haveI : Nonempty Px' := by
    classical
    rcases Finset.card_pos.mp hxpos with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  haveI : Nonempty Py' := by
    classical
    rcases Finset.card_pos.mp hypos with ⟨y, hy⟩
    exact ⟨⟨y, hy⟩⟩
  -- adjusted parameters
  let ax' : ℕ := a_x - g_x
  let ay' : ℕ := a_y - g_y
  let bx' : ℕ := b_x - g_x
  let by' : ℕ := b_y - g_y
  let nx' : ℕ+ := ⟨(n_x : ℕ) - g_x, Nat.sub_pos_of_lt hx_lt_nx⟩
  let ny' : ℕ+ := ⟨(n_y : ℕ) - g_y, Nat.sub_pos_of_lt hy_lt_ny⟩
  have hbxax' : bx' ≥ ax' := by
    -- bx' ≥ ax' ↔ ax' ≤ bx'
    simpa [bx', ax'] using (Nat.sub_le_sub_right h_bx_ge_ax g_x)
  have hbyay' : by' ≥ ay' := by
    simpa [by', ay'] using (Nat.sub_le_sub_right h_by_ge_ay g_y)
  -- simplify differences bx' - ax' and by' - ay'
  have hdiff_x : bx' - ax' = b_x - a_x := by
    simpa [bx', ax'] using
      (tsub_tsub_tsub_cancel_right (a := b_x) (b := a_x) (c := g_x) hgx_le_ax)
  have hdiff_y : by' - ay' = b_y - a_y := by
    simpa [by', ay'] using
      (tsub_tsub_tsub_cancel_right (a := b_y) (b := a_y) (c := g_y) hgy_le_ay)
  -- descend quotient hypotheses to A1,B1
  have hquotX' : ∀ y ∈ Py', (quot_x y).natDegree ≤ (bx' - ax') ∧
      Polynomial.Bivariate.evalY y B1 = (quot_x y) * Polynomial.Bivariate.evalY y A1 := by
    intro y hy
    have hyP : y ∈ P_y := (Finset.mem_filter.mp hy).1
    have hyG : Polynomial.Bivariate.evalY y G ≠ 0 := (Finset.mem_filter.mp hy).2
    have hq := h_quot_x y hyP
    refine ⟨?_, ?_⟩
    · simpa [hdiff_x] using hq.1
    · exact ps_descend_eval_y (hA := hA) (hB := hB) y hyG (quot_x y) hq.2
  have hquotY' : ∀ x ∈ Px', (quot_y x).natDegree ≤ (by' - ay') ∧
      Polynomial.Bivariate.evalX x B1 = (quot_y x) * Polynomial.Bivariate.evalX x A1 := by
    intro x hx
    have hxP : x ∈ P_x := (Finset.mem_filter.mp hx).1
    have hxG : Polynomial.Bivariate.evalX x G ≠ 0 := (Finset.mem_filter.mp hx).2
    have hq := h_quot_y x hxP
    refine ⟨?_, ?_⟩
    · simpa [hdiff_y] using hq.1
    · exact ps_descend_eval_x (hA := hA) (hB := hB) x hxG (quot_y x) hq.2
  -- degree bounds for A1,B1 under adjusted parameters
  have h_ax' : ax' ≥ Polynomial.Bivariate.degreeX A1 := by
    have hsum : g_x + Polynomial.Bivariate.degreeX A1 ≤ a_x := by
      simpa [hdegX_A] using h_f_degX
    have : Polynomial.Bivariate.degreeX A1 ≤ a_x - g_x := le_tsub_of_add_le_left hsum
    simpa [ax', ge_iff_le] using this
  have h_ay' : ay' ≥ Polynomial.Bivariate.natDegreeY A1 := by
    have hsum : g_y + Polynomial.Bivariate.natDegreeY A1 ≤ a_y := by
      simpa [hdegY_A] using h_f_degY
    have : Polynomial.Bivariate.natDegreeY A1 ≤ a_y - g_y := le_tsub_of_add_le_left hsum
    simpa [ay', ge_iff_le] using this
  have h_bx' : bx' ≥ Polynomial.Bivariate.degreeX B1 := by
    have hsum : g_x + Polynomial.Bivariate.degreeX B1 ≤ b_x := by
      simpa [hdegX_B] using h_g_degX
    have : Polynomial.Bivariate.degreeX B1 ≤ b_x - g_x := le_tsub_of_add_le_left hsum
    simpa [bx', ge_iff_le] using this
  have h_by' : by' ≥ Polynomial.Bivariate.natDegreeY B1 := by
    have hsum : g_y + Polynomial.Bivariate.natDegreeY B1 ≤ b_y := by
      simpa [hdegY_B] using h_g_degY
    have : Polynomial.Bivariate.natDegreeY B1 ≤ b_y - g_y := le_tsub_of_add_le_left hsum
    simpa [by', ge_iff_le] using this
  -- card bounds in the form needed (using nx',ny')
  have hcard_Px'' : nx' ≤ Px'.card := by
    simpa [nx'] using hcard_Px'
  have hcard_Py'' : ny' ≤ Py'.card := by
    simpa [ny'] using hcard_Py'
  -- inequality for adjusted ratios
  have hxfrac : (bx' : ℚ) / (nx' : ℚ) ≤ (b_x : ℚ) / (n_x : ℚ) := by
    have hn1 : (0 : ℚ) < (n_x : ℚ) := by
      exact_mod_cast n_x.pos
    have hn2 : (0 : ℚ) < (nx' : ℚ) := by
      exact_mod_cast nx'.pos
    -- use div_le_div_iff₀
    refine (div_le_div_iff₀ hn2 hn1).2 ?_
    -- show (bx')*n_x ≤ b_x*nx'
    have hbx'cast : (bx' : ℚ) = (b_x : ℚ) - (g_x : ℚ) := by
      -- bx' = b_x - gx, and gx ≤ b_x
      have : g_x ≤ b_x := hgx_le_bx
      simp [bx', Nat.cast_sub this]
    have hnx'cast : (nx' : ℚ) = (n_x : ℚ) - (g_x : ℚ) := by
      have : g_x ≤ (n_x : ℕ) := le_of_lt hx_lt_nx
      simp [nx', Nat.cast_sub this]
    -- start from gx*b_x ≤ gx*n_x
    have hbn : (b_x : ℚ) ≤ (n_x : ℚ) := by
      exact_mod_cast (le_of_lt hbxltnx)
    have hgx_nonneg : (0 : ℚ) ≤ (g_x : ℚ) := by
      exact_mod_cast (Nat.zero_le g_x)
    have hmul : (g_x : ℚ) * (b_x : ℚ) ≤ (g_x : ℚ) * (n_x : ℚ) :=
      mul_le_mul_of_nonneg_left hbn hgx_nonneg
    have hsub : (b_x : ℚ) * (n_x : ℚ) - (g_x : ℚ) * (n_x : ℚ) ≤
        (b_x : ℚ) * (n_x : ℚ) - (g_x : ℚ) * (b_x : ℚ) := by
      -- subtract the inequality from (b_x*n_x)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (sub_le_sub_left hmul ((b_x : ℚ) * (n_x : ℚ)))
    -- rewrite into the desired form
    rw [hbx'cast, hnx'cast]
    simpa [sub_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hsub
  have hyfrac : (by' : ℚ) / (ny' : ℚ) ≤ (b_y : ℚ) / (n_y : ℚ) := by
    have hn1 : (0 : ℚ) < (n_y : ℚ) := by
      exact_mod_cast n_y.pos
    have hn2 : (0 : ℚ) < (ny' : ℚ) := by
      exact_mod_cast ny'.pos
    refine (div_le_div_iff₀ hn2 hn1).2 ?_
    have hby'cast : (by' : ℚ) = (b_y : ℚ) - (g_y : ℚ) := by
      have : g_y ≤ b_y := hgy_le_by
      simp [by', Nat.cast_sub this]
    have hny'cast : (ny' : ℚ) = (n_y : ℚ) - (g_y : ℚ) := by
      have : g_y ≤ (n_y : ℕ) := le_of_lt hy_lt_ny
      simp [ny', Nat.cast_sub this]
    have hbn : (b_y : ℚ) ≤ (n_y : ℚ) := by
      exact_mod_cast (le_of_lt hbyltny)
    have hgy_nonneg : (0 : ℚ) ≤ (g_y : ℚ) := by
      exact_mod_cast (Nat.zero_le g_y)
    have hmul : (g_y : ℚ) * (b_y : ℚ) ≤ (g_y : ℚ) * (n_y : ℚ) :=
      mul_le_mul_of_nonneg_left hbn hgy_nonneg
    have hsub : (b_y : ℚ) * (n_y : ℚ) - (g_y : ℚ) * (n_y : ℚ) ≤
        (b_y : ℚ) * (n_y : ℚ) - (g_y : ℚ) * (b_y : ℚ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (sub_le_sub_left hmul ((b_y : ℚ) * (n_y : ℚ)))
    rw [hby'cast, hny'cast]
    simpa [sub_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hsub

  have h_le_1' : (1 : ℚ) > (bx' : ℚ) / (nx' : ℚ) + (by' : ℚ) / (ny' : ℚ) := by
    have hsum_le : (bx' : ℚ) / (nx' : ℚ) + (by' : ℚ) / (ny' : ℚ) ≤
      (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) := by
      exact add_le_add hxfrac hyfrac
    exact lt_of_le_of_lt hsum_le h_le_1
-- apply coprime-case lemma to A1,B1
  have hconst : Polynomial.Bivariate.degreeX A1 = 0 ∧ Polynomial.Bivariate.natDegreeY A1 = 0 := by
    classical
    simpa [ax', ay', bx', by', nx', ny'] using
          (ps_coprime_case_constant (F := F) ax' ay' bx' by' nx' ny' hbxax' hbyay' A1 B1
            hA1 hB1 hrel h_ax' h_bx' h_ay' h_by'
            Px' Py' quot_x quot_y hcard_Px'' hcard_Py''
            hquotX' hquotY' h_le_1')
-- get B1 = P1 * A1
  rcases ps_exists_p_of_degree_x_eq_zero_nat_degree_y_eq_zero (A := A1) (B := B1) hA1 hconst.1 hconst.2 with
    ⟨P1, hB1fac⟩
  refine ⟨P1, ?_⟩
-- assemble
  calc
  B = G * B1 := by
    simp [hB]
  _ = G * (P1 * A1) := by
    simp [hB1fac]
  _ = P1 * (G * A1) := by
    simp [mul_left_comm, mul_comm]
  _ = P1 * A := by
    simp [hA]


lemma ps_exists_p {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y])
    (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
    (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
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
    ∃ P : F[X][Y], B = P * A := by
  classical
  letI : DecidableEq F := Classical.decEq F

  by_cases hB0 : B = 0
  · refine ⟨0, ?_⟩
    simp [hB0]
  · have hB : B ≠ 0 := hB0
    by_cases hA0 : A = 0
    · have hA : A = 0 := hA0

      have hBx_lt : b_x < (n_x : ℕ) :=
        ps_bx_lt_nx (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
      have hBx_lt_card : b_x < P_x.card := lt_of_lt_of_le hBx_lt h_card_Px

      have h_evalX_B_zero : ∀ x ∈ P_x, Polynomial.Bivariate.evalX x B = 0 := by
        intro x hx
        have hEq :
            Polynomial.Bivariate.evalX x B =
              (quot_y x) * (Polynomial.Bivariate.evalX x A) :=
          (h_quot_y x hx).2
        simpa [hA, ps_eval_x_eq_map] using hEq

      have hB_eq : B = 0 := by
        by_contra hB_ne

        have hcard_le :
            (P_x.filter (fun x => Polynomial.Bivariate.evalX x B = 0)).card ≤
              Polynomial.Bivariate.degreeX B :=
          ps_card_eval_x_eq_zero_le_degree_x (A := B) hB_ne P_x

        have hfilter_eq :
            P_x.filter (fun x => Polynomial.Bivariate.evalX x B = 0) = P_x := by
          ext x
          by_cases hx : x ∈ P_x
          · simp [Finset.mem_filter, hx, h_evalX_B_zero x hx]
          · simp [Finset.mem_filter, hx]

        have hPx_card_le : P_x.card ≤ Polynomial.Bivariate.degreeX B := by
          simpa [hfilter_eq] using hcard_le

        have hdegX_le : Polynomial.Bivariate.degreeX B ≤ b_x := by
          exact h_g_degX
        have hdegX_lt : Polynomial.Bivariate.degreeX B < P_x.card :=
          lt_of_le_of_lt hdegX_le hBx_lt_card

        exact (not_lt_of_ge hPx_card_le) hdegX_lt

      refine ⟨0, ?_⟩
      simp [hB_eq, hA]

    · have hA : A ≠ 0 := by exact hA0
      exact
        ps_exists_p_nonzero (a_x := a_x) (a_y := a_y) (b_x := b_x) (b_y := b_y)
          (n_x := n_x) (n_y := n_y) (h_bx_ge_ax := h_bx_ge_ax) (h_by_ge_ay := h_by_ge_ay)
          (A := A) (B := B) (hA0 := hA) (hB0 := hB) (h_f_degX := h_f_degX)
          (h_g_degX := h_g_degX) (h_f_degY := h_f_degY) (h_g_degY := h_g_degY)
          (P_x := P_x) (P_y := P_y) (quot_x := quot_x) (quot_y := quot_y)
          (h_card_Px := h_card_Px) (h_card_Py := h_card_Py) (h_quot_x := h_quot_x)
          (h_quot_y := h_quot_y) (h_le_1 := h_le_1)
