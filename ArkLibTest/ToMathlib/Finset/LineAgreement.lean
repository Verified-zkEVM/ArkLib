/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Finset.LineAgreement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Acceptance client for `ArkLib.ToMathlib.Finset.LineAgreement`

The examples show that the bound `#{i ∈ s | b i ≠ d i}` is attained over `ℚ`, that indices with
equal slopes contribute no exceptional parameter, and that the field hypothesis is needed: over
`ZMod 4` the line `z ↦ 2 * z` meets `0` at two parameters.
-/

open Finset

namespace LineAgreementTest

/-- The bound is attained: the lines `z` and `1`, `z` and `2` at the two indices meet at `z = 1`
and `z = 2`, so every admissible exceptional set contains both. The theorem's bound here is
`#{i ∈ univ | 1 ≠ 0} = 2`. -/
example (exceptional : Finset ℚ)
    (h : ∀ z ∉ exceptional, ∀ i ∈ (univ : Finset (Fin 2)),
      (0 : ℚ) + z * 1 = ![1, 2] i + z * 0 ↔ (0 : ℚ) = ![1, 2] i ∧ (1 : ℚ) = 0) :
    2 ≤ exceptional.card := by
  have h1 : (1 : ℚ) ∈ exceptional := by
    by_contra hz
    have := (h 1 hz 0 (mem_univ _)).mp (by simp)
    norm_num at this
  have h2 : (2 : ℚ) ∈ exceptional := by
    by_contra hz
    have := (h 2 hz 1 (mem_univ _)).mp (by simp)
    norm_num at this
  calc 2 = ({1, 2} : Finset ℚ).card := by norm_num
    _ ≤ exceptional.card := card_le_card (by simp [insert_subset_iff, h1, h2])

/-- Equal slopes contribute nothing: with `b = d` the exceptional set is empty, so the lines agree
for one parameter exactly when they agree for all. -/
example (a c b : Fin 3 → ℚ) (z : ℚ) (i : Fin 3) :
    a i + z * b i = c i + z * b i ↔ a i = c i ∧ b i = b i := by
  obtain ⟨exceptional, hcard, hiff⟩ :=
    exists_card_le_forall_add_mul_eq_add_mul_iff univ a b c b
  have hempty : exceptional = ∅ := by simpa using hcard
  exact hiff z (by simp [hempty]) i (mem_univ i)

/-- The field hypothesis is needed: in `ZMod 4` the line `z ↦ 0 + z * 2` meets the line `0` at
`z = 0` and `z = 2`, so one index with different slopes needs two exceptional parameters. -/
example : ¬∃ exceptional : Finset (ZMod 4), exceptional.card ≤ 1 ∧
    ∀ z ∉ exceptional, ∀ i ∈ (univ : Finset (Fin 1)),
      (0 : ZMod 4) + z * 2 = 0 + z * 0 ↔ (0 : ZMod 4) = 0 ∧ (2 : ZMod 4) = 0 := by
  rintro ⟨exceptional, hcard, h⟩
  have hmem : ∀ z : ZMod 4, z * 2 = 0 → z ∈ exceptional := by
    intro z hz
    by_contra hnot
    have := ((h z hnot 0 (mem_univ _)).mp (by simpa using hz)).2
    exact absurd this (by decide)
  have h0 := hmem 0 (by decide)
  have h2 := hmem 2 (by decide)
  have : ({0, 2} : Finset (ZMod 4)).card ≤ exceptional.card :=
    card_le_card (by simp [insert_subset_iff, h0, h2])
  have hpair : ({0, 2} : Finset (ZMod 4)).card = 2 := by decide
  omega

end LineAgreementTest
