/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for the division-free Schwartz–Zippel count

* The bound is attained: `X₀` in two variables over `ZMod 2` has `2 = 1 * 2 ^ 1` zeros.
* `p ≠ 0` is needed: `0` vanishes at all `4` points of `(ZMod 2)²` and has total degree `0`.
* The source statement `card_jet_zeros_le` at ArkLib revision
  a5aa2677fee4e3a79d6bb05136631cce4a08587d, over a finite field with the full grid, is the case
  `S = univ`.
-/

open Finset MvPolynomial

/-- `X₀` attains the bound on `(ZMod 2)²`: its zeros are `(0, 0)` and `(0, 1)`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 2)) |
      eval x (X 0 : MvPolynomial (Fin 2) (ZMod 2)) = 0} = 2 ∧
    (X 0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree * #(univ : Finset (ZMod 2)) ^ 1 = 2 := by
  refine ⟨?_, by rw [totalDegree_X, card_univ, ZMod.card]; rfl⟩
  simp only [eval_X]
  decide

/-- `p ≠ 0` is needed: the zero polynomial vanishes at all `4` points of `(ZMod 2)²`. -/
example : ¬#{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 2)) |
      eval x (0 : MvPolynomial (Fin 2) (ZMod 2)) = 0} ≤
    (0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree * #(univ : Finset (ZMod 2)) ^ 1 := by
  simp only [map_zero, filter_true, totalDegree_zero, zero_mul]
  decide

/-- Source shape: `card_jet_zeros_le`, over a finite field with the full grid. -/
example {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (Q : MvPolynomial (Fin (d + 1)) F) (hQ : Q ≠ 0) :
    #{jet | eval jet Q = 0} ≤ Q.totalDegree * Fintype.card F ^ d := by
  simpa [Fintype.piFinset_univ] using card_filter_eval_eq_zero_le hQ univ
