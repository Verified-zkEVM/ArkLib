/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import Mathlib.Algebra.Field.ZMod

/-!
# Injective specialization of polynomial tuples

Two distinct tuples can collide at a challenge, so some challenges must be excluded; over `ℚ` one
challenge separates them while avoiding a prescribed value. The infinite-field hypothesis of the
avoidance statement is needed: over `ZMod 2` the nonzero polynomial `X ^ 2 - X` vanishes
everywhere.
-/

open Polynomial ReedSolomon

namespace TupleSpecializationTest

/-- The tuple `(1, 0)`, batched to the constant `1`. -/
noncomputable def tupleOne : Fin 2 → ℚ[X] := ![1, 0]

/-- The tuple `(0, 1)`, batched to the constant `z`. -/
noncomputable def tupleChallenge : Fin 2 → ℚ[X] := ![0, 1]

theorem tupleOne_ne_tupleChallenge : tupleOne ≠ tupleChallenge := fun h ↦ by
  simpa [tupleOne, tupleChallenge] using congrFun h 0

-- The two tuples collide at the challenge `1`: both batch to the constant `1`.
example : powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) 1 =
    powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) 1 := by
  simp [powerBatchedPolynomial, tupleOne, tupleChallenge, Fin.sum_univ_two]

-- They collide at only finitely many challenges.
example : {z : ℚ | powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) z =
    powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) z}.Finite :=
  finite_polynomialTuple_collisions _ tupleOne_ne_tupleChallenge

-- Over `ℚ`, one challenge other than `1` separates them and is not a root of `X`.
example : ∃ z : ℚ, z ≠ 1 ∧ z ≠ 0 ∧
    powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) z ≠
      powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) z := by
  classical
  obtain ⟨z, hz, hinj, hroot⟩ := exists_polynomialTuple_specialization_injective_avoiding_roots
    (RingHom.id ℚ) {tupleOne, tupleChallenge} {1} {X} (by simp [X_ne_zero])
  refine ⟨z, by simpa using hz, by simpa using hroot X (by simp), fun heq ↦ ?_⟩
  exact tupleOne_ne_tupleChallenge (hinj (by simp) (by simp) heq)

-- The infinite-field hypothesis is needed: over `ZMod 2`, the nonzero `X ^ 2 - X` has every
-- point as a root, so no challenge avoids its roots.
example : ¬ ∃ z : ZMod 2, (X ^ 2 - X : (ZMod 2)[X]).eval z ≠ 0 := by
  rintro ⟨z, hz⟩
  simp only [eval_sub, eval_pow, eval_X] at hz
  revert z hz
  decide

example : (X ^ 2 - X : (ZMod 2)[X]) ≠ 0 := fun h ↦ by
  simpa [coeff_X] using congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 2) h

end TupleSpecializationTest
