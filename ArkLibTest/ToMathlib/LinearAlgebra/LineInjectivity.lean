/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.LineInjectivity
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for line injectivity

The lines `z ↦ 1 + 2 z` and `z ↦ 3 + z` over `ℚ` meet exactly at `z = 2`. The torsion-free
hypothesis is needed: in the `ℤ`-module `ZMod 2`, two different lines agree at the parameters `0`
and `2`. The hypothesis that the field is infinite is needed: over `ZMod 2`, no parameter separates
the four pairs `(a, b)`.
-/

namespace LineInjectivityTest

/-- The collision set of two distinct lines over `ℚ` is the single parameter `2`. -/
example : {z : ℚ | (1 : ℚ) + z • (2 : ℚ) = 3 + z • 1} = {2} := by
  have hsub := subsingleton_setOf_add_smul_eq_add_smul (K := ℚ) (a := (1 : ℚ)) (b := 2) (c := 3)
    (d := 1) (by simp)
  exact hsub.eq_singleton_of_mem (by norm_num)

/-- Two agreements recover the line over `ℚ`. -/
example (a b : ℚ) (h0 : a + (0 : ℚ) • b = 5 + (0 : ℚ) • 7)
    (h1 : a + (1 : ℚ) • b = 5 + (1 : ℚ) • 7) : a = 5 ∧ b = 7 :=
  eq_and_eq_of_add_smul_eq_add_smul_of_ne zero_ne_one h0 h1

/-- Torsion is a counterexample: over `ℤ`, the lines `z ↦ z • 1` and `z ↦ z • 0` in `ZMod 2`
agree at the distinct parameters `0` and `2`, but `1 ≠ 0`. -/
example : ∃ (x y : ℤ) (a b c d : ZMod 2), x ≠ y ∧ a + x • b = c + x • d ∧
    a + y • b = c + y • d ∧ b ≠ d :=
  ⟨0, 2, 0, 1, 0, 0, by decide, by simp, by decide, by decide⟩

/-- Over the finite field `ZMod 2`, no parameter makes `(a, b) ↦ a + z • b` injective on all four
pairs: `(0, 1)` and `(z, 0)` have the same image `z`. -/
example : ¬ ∃ z : ZMod 2, Set.InjOn (fun p : ZMod 2 × ZMod 2 ↦ p.1 + z • p.2) Set.univ := by
  rintro ⟨z, hz⟩
  have h := hz (Set.mem_univ ((0 : ZMod 2), (1 : ZMod 2))) (Set.mem_univ (z, 0))
    (by simp only [smul_eq_mul, mul_one, mul_zero, zero_add, add_zero])
  exact one_ne_zero (congrArg Prod.snd h)

/-- Over `ℚ` the four pairs `(a, b)` with `a, b ∈ {0, 1}` are separated by a parameter that
avoids `{0, 1, -1}`. -/
example : ∃ z ∉ ({0, 1, -1} : Set ℚ), Set.InjOn (fun p : ℚ × ℚ ↦ p.1 + z • p.2)
    ({(0, 0), (0, 1), (1, 0), (1, 1)} : Set (ℚ × ℚ)) :=
  Set.Finite.exists_notMem_injOn_add_smul (by simp) Prod.fst Prod.snd
    (fun _ _ _ _ h ↦ h) (by simp)

end LineInjectivityTest
