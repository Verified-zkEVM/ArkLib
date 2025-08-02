/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad

variable {α : Type*}

instance [IsEmpty α] : IsEmpty (PMF α) := by
  refine Subtype.isEmpty_of_false ?_
  intro f h
  have : Fintype α := Fintype.ofIsEmpty
  obtain h' := hasSum_fintype f ; simp at h'
  have one_eq_zero := HasSum.unique h h'
  simp_all only [one_ne_zero]

-- @[simp]
-- theorem PMF.eq_pure_iff_ge_one {α : Type*} {p : PMF α} {a : α} : p = pure a ↔ p a ≥ 1 := by
--   constructor <;> intro h
--   · sorry
--   · ext b
--     simp only [pure, PMF.pure_apply]
--     by_cases hb : b = a
--     · simp [hb]; exact le_antisymm (PMF.coe_le_one p a) h
--     · simp [hb]; sorry
