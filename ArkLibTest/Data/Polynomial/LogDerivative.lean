/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import ArkLib.Data.Polynomial.LogDerivative
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Logarithmic-derivative lookup acceptance tests

The seven elements of ZMod 7 each occur once among seven queries.

The largest count is 1, so equal sums give set inclusion.

The number of queries is 7, which vanishes in ZMod 7, so the length bound does not apply.
-/

namespace ArkLibTest.LogDerivative

open RatFunc

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The seven distinct elements of ZMod 7. -/
private def queries : List (ZMod 7) := [0, 1, 2, 3, 4, 5, 6]

example : queries.maxCount = 1 := by decide

/-- The largest-count bound holds. -/
example : NatCastNeZeroUpTo (ZMod 7) queries.maxCount :=
  .of_lt _ 7 (by decide)

/-- The length bound fails: 7 queries, and 7 vanishes in ZMod 7. -/
example : ¬ NatCastNeZeroUpTo (ZMod 7) queries.length :=
  fun h => h 7 (by decide) le_rfl (by decide)

/-- Equal sums give inclusion under the largest-count bound alone. -/
example (t m : List (ZMod 7)) (hm : m.length = t.length)
    (h : logDerivSum (queries.map (·, 1)) = logDerivSum (t.zip m)) : queries ⊆ t :=
  subset_of_logDerivSum_eq (.of_lt _ 7 (by decide)) hm h

/-- Seven equal queries cancel in ZMod 7 against an empty table. -/
example : logDerivSum ((List.replicate 7 (3 : ZMod 7)).map (·, 1)) =
      logDerivSum (([] : List (ZMod 7)).zip []) ∧
    ¬ List.replicate 7 (3 : ZMod 7) ⊆ [] :=
  logDerivSum_replicate_eq_nil_and_not_subset 7 (by decide) 3

end ArkLibTest.LogDerivative
