/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.MvPolynomial.SchwartzZippelInjective
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Schwartz–Zippel over pairwise-distinct points: acceptance tests

On `(ZMod 3)²` there are `3 * 2 = 6` pairs with distinct coordinates. `X 0 - X 1` vanishes at three
grid points but at none of them, and `X 0 - X 1 - 1` vanishes at three of them, which attains
`card_filter_injective_eval_eq_zero_le`: `3 * (3 - 2 + 1) = 1 * 6`.
-/

open Finset MvPolynomial

/-- The pairs with distinct coordinates number `(#univ).descFactorial 2 = 6`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x} = 6 ∧ (#(univ : Finset (ZMod 3))).descFactorial 2 = 6 := by
  refine ⟨by decide, ?_⟩
  rw [card_univ, ZMod.card]
  rfl

/-- `X 0 - X 1` has three zeros on the grid `(ZMod 3)²` and none with distinct coordinates. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      eval x (X 0 - X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} = 3 ∧
    #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ eval x (X 0 - X 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} = 0 := by
  simp only [map_sub, eval_X]
  decide

/-- `X 0 - X 1 - 1` has total degree `1` and three zeros with distinct coordinates, so it attains
the bound: `3 * (3 - 2 + 1) = 1 * 6`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ eval x (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} *
        (#(univ : Finset (ZMod 3)) - 2 + 1) =
      (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)).totalDegree *
        (#(univ : Finset (ZMod 3))).descFactorial 2 := by
  have hcount : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 3)) |
      Function.Injective x ∧ eval x (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)) = 0} = 3 := by
    simp only [map_sub, map_one, eval_X]
    decide
  have hle : (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans <| max_le ((totalDegree_sub _ _).trans (by simp)) (by simp)
  have hge : 1 ≤ (X 0 - X 1 - 1 : MvPolynomial (Fin 2) (ZMod 3)).totalDegree := by
    refine le_of_eq_of_le ?_ (le_totalDegree (s := Finsupp.single 0 1) ?_)
    · simp
    · rw [mem_support_iff]
      simp [coeff_X, coeff_one, Finsupp.single_eq_single_iff,
        (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
  rw [hcount, le_antisymm hle hge, card_univ, ZMod.card]
  rfl
