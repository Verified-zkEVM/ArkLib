/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.NestedStages
import Mathlib.Algebra.Field.ZMod

/-!
# Nested stages: concrete tests

Two stages. The first has two coordinates over `ZMod 5` with two values needed at each; the second
has one coordinate over `ZMod 7` with three values needed. The tests compute the error and size,
apply the finder theorem and the interpolation on a challenge tree, and show that the strict degree
bound of the interpolation is load-bearing.
-/

open MvPolynomial OracleComp OracleSpec
open scoped ENNReal NNReal NNRat

namespace NestedStagesTest

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The alphabet of a stage: `ZMod 5` for the first, `ZMod 7` for the second. -/
def alph : Fin 2 → Type
  | 0 => ZMod 5
  | 1 => ZMod 7

instance : ∀ r, Fintype (alph r)
  | 0 => inferInstanceAs (Fintype (ZMod 5))
  | 1 => inferInstanceAs (Fintype (ZMod 7))

instance : ∀ r, DecidableEq (alph r)
  | 0 => inferInstanceAs (DecidableEq (ZMod 5))
  | 1 => inferInstanceAs (DecidableEq (ZMod 7))

instance : ∀ r, SampleableType (alph r)
  | 0 => inferInstanceAs (SampleableType (ZMod 5))
  | 1 => inferInstanceAs (SampleableType (ZMod 7))

/-- Two coordinates with arity `2` in stage `0`, one coordinate with arity `3` in stage `1`. -/
abbrev D : NestedStages 2 where
  coords := ![2, 1]
  alphabet := fun r _ => alph r
  arity := fun r _ => ![2, 3] r

example : D.stageSize 0 = 4 := by decide

example : D.size = 12 := by decide

#eval D.error

/-- The error is `2/5 + 2/7 = 24/35`, which is below one. -/
example : D.error = 24 / 35 := by
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h7 : Fintype.card (alph 1) = 7 := by decide
  simp only [NestedStages.error, NestedStages.stageError, Fin.sum_univ_two, h5, h7]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num [D]

example : D.error < 1 := by
  have h : D.error = 24 / 35 := by
    have h5 : Fintype.card (alph 0) = 5 := by decide
    have h7 : Fintype.card (alph 1) = 7 := by decide
    simp only [NestedStages.error, NestedStages.stageError, Fin.sum_univ_two, h5, h7]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num [D]
  rw [h]
  norm_num

/-- The finder theorem applies to this design, for the acceptance function that accepts every
challenge vector. -/
example :=
  D.finder_bounds (fun r u => by fin_cases r <;> fin_cases u <;> decide) (fun _ => true)

end NestedStagesTest

/--
info: 'NestedStages.finder_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NestedStages.finder_bounds

/--
info: 'Rewinding.thresholdError_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Rewinding.thresholdError_le_sum
