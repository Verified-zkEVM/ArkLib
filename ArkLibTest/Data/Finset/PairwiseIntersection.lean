/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Data.Fin.VecNotation

/-! # Acceptance cases for the pairwise-intersection Johnson counts -/

open Finset

/-- Three `2`-subsets of `Fin 4`: the halves `{0, 1}` and `{2, 3}`, with `{0, 1}` repeated. -/
private def halves : Fin 3 → Finset (Fin 4) := ![{0, 1}, {2, 3}, {0, 1}]

/-- The first and third members share a label, since they carry the same set. -/
private def halfLabel : Fin 3 → Fin 2 := ![0, 1, 0]

-- Two disjoint `2`-subsets of `Fin 4` (`n = 4`, `A = 2`, `D = 0`) meet the bound with equality:
-- `|T| (A² - nD) = 2 · 4 = 8 = n (A - D)`.
example : ({0, 1} : Finset (Fin 3)).card * (2 * 2 - Fintype.card (Fin 4) * 0) ≤
    Fintype.card (Fin 4) * (2 - 0) :=
  card_mul_sq_sub_card_mul_le_of_inter_card_le {0, 1} halves 2 0 (by decide) (by decide)

-- With `n = 4`, `A = 2`, `D = 0` the Johnson factor is `n (A - D) / (A² - nD) = 2`.
-- Each label has at most `M = 2` members, so the three members obey `3 ≤ 2 · 2`.
example : ((univ : Finset (Fin 3)).card : ℝ) ≤
    Fintype.card (Fin 4) * ((2 : ℝ) - (0 : ℕ)) / ((2 : ℝ) * 2 - Fintype.card (Fin 4) * (0 : ℕ)) *
      (2 : ℕ) :=
  card_le_of_fiber_card_le_of_inter_card_le univ halfLabel halves (A := 2) (D := 0) (M := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- The count above is not vacuous: the family has three members and the bound evaluates to `4`.
example : Fintype.card (Fin 4) * ((2 : ℝ) - (0 : ℕ)) /
    ((2 : ℝ) * 2 - Fintype.card (Fin 4) * (0 : ℕ)) * (2 : ℕ) = 4 := by
  norm_num

/-- info: 'Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le

/-- info: 'Finset.card_le_of_fiber_card_le_of_inter_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_le_of_fiber_card_le_of_inter_card_le
