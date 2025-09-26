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
lemma Polishchuk_Spielman {F : Type} [Field F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (A B : F[X][Y])
  (h_f_degX : a_x ≥ Bivariate.degreeX A) (h_g_degX : b_x ≥ Bivariate.degreeX B)
  (h_f_degY : a_y ≥ natDegreeY A) (h_g_degY : b_y ≥ natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧ Bivariate.evalY y B = (quot_X y) * (Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧ Bivariate.evalX x B = (quot_Y x) * (Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  : ∃ P : F[X][Y], B = P * A
    ∧ Bivariate.degreeX P ≤ b_x - a_x ∧ natDegreeY P ≤ b_y - a_y
    ∧ (∃ Q_x : Finset F, Q_x.card ≥ n_x - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Bivariate.evalX x P = quot_Y x)
    ∧ (∃ Q_y : Finset F, Q_y.card ≥ n_y - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Bivariate.evalX y P = quot_X y)
    := sorry
