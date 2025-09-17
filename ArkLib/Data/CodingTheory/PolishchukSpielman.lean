/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.Polynomial.Bivariate

open Polynomial.Bivariate Polynomial

/--
Polishchuk-Spielman Lemma variant from Ben-Sasson et Al. Proximity Gaps for Reed-Solomon Codes
-/
lemma Polishchuk_Spielman {F : Type} [Semiring F] [Field F]
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (f g : F[X][Y]) (a_x a_y b_x b_y n_x n_y : ℕ)
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (h_f_degX : a_x ≥ Bivariate.degreeX f) (h_g_degX : b_x ≥ Bivariate.degreeX g)
  (h_f_degY : a_y ≥ natDegreeY f) (h_g_degY : b_y ≥ natDegreeY g)
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧ Bivariate.evalY y g = (quot_X y) * (Bivariate.evalY y f))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧ Bivariate.evalX x g = (quot_Y x) * (Bivariate.evalX x f))
  : ∃ q : F[X][Y], g = q * f
    ∧ Bivariate.degreeX q ≤ b_x - a_x ∧ natDegreeY q ≤ b_y - a_y
    ∧ (∃ Q_x : Finset F, Q_x.card ≥ n_x - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Bivariate.evalX x q = quot_Y x)
    ∧ (∃ Q_y : Finset F, Q_y.card ≥ n_y - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Bivariate.evalX y q = quot_X y)
    := sorry
