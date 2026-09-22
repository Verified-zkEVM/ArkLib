/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.ExactCharacteristicBudget
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.ZMod.Basic

/-!
# Exact characteristic budget acceptance tests

* Concrete coordinate floors at `D = 3`, `A = 5`, `m = 2`, `d = 2`: the floors at `j = 0, 1, 2`
  are `3, 4, 9`, and the global floor is `9`.
* When `d = D` the weight `D - d` of the top jet is `0`, and the coordinate floor there is `0`
  by division by zero; the comparison with the global floor then needs `d < D` to be meaningful.
* The characteristic bound over `ZMod 11`, where the global floor `9` is below `11`, together
  with `D < ringChar F`.
* Over `ℚ` the characteristic is `0`, so the characteristic hypothesis cannot hold.
-/

open PolynomialDifferential ReedSolomon.HiddenDerivative

example : exactInterpolationJetDegreeFloorAt (d := 2) 3 5 2 0 = 3 := by decide
example : exactInterpolationJetDegreeFloorAt (d := 2) 3 5 2 1 = 4 := by decide
example : exactInterpolationJetDegreeFloorAt (d := 2) 3 5 2 2 = 9 := by decide
example : exactInterpolationJetDegreeFloor 3 5 2 2 = 9 := by decide

/-- The comparison instance at `j = 0`: `3 ≤ 9`. -/
example : exactInterpolationJetDegreeFloorAt (d := 2) 3 5 2 0 ≤
    exactInterpolationJetDegreeFloor 3 5 2 2 :=
  exactInterpolationJetDegreeFloorAt_le (by norm_num) 0

/-- A jet-degree bound computed by the theorem: every member of the exact space at
`D = 3`, `A = 5`, `m = 2`, `d = 2` has degree at most `3` in `Y₀`. -/
example {F : Type*} [CommSemiring F] {M W : ℕ} (Q : DifferentialPolynomial F 2)
    (hQ : Q ∈ exactInterpolationSpace F 3 5 2 2 M W (by norm_num)) :
    jetDegree Q 0 ≤ 3 :=
  jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace Q hQ 0

/-- For `m * A = 0` the floor is `0`, so every member of the space has jet degree `0`. -/
example {F : Type*} [CommSemiring F] {M W : ℕ} (Q : DifferentialPolynomial F 1)
    (hQ : Q ∈ exactInterpolationSpace F 2 0 1 7 M W (by norm_num)) (j : Fin 2) :
    jetDegree Q j = 0 :=
  Nat.le_zero.mp
    ((jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace Q hQ j).trans
      (by simp [exactInterpolationJetDegreeFloorAt]))

/-- Boundary: at `d = D` the weight of the top jet is `0`, and the coordinate floor there is `0`
by division by zero, which is not a bound on the jet degree. This is why the theorems require
`d < D`. -/
example : exactInterpolationJetDegreeFloorAt (d := 2) 2 5 2 2 = 0 := by decide

/-- Over `ZMod 11`, `D < ringChar F` together with the bound on every jet degree: each jet degree
is below `11` because the global floor `9` is. -/
example {M W : ℕ} (Q : DifferentialPolynomial (ZMod 11) 2)
    (hQ : Q ∈ exactInterpolationSpace (ZMod 11) 3 5 2 2 M W (by norm_num)) :
    3 < ringChar (ZMod 11) ∧ ∀ j, jetDegree Q j < ringChar (ZMod 11) := by
  have h : ringChar (ZMod 11) = 11 := ZMod.ringChar_zmod_n 11
  refine ⟨by rw [h]; norm_num, fun j => ?_⟩
  exact jetDegree_lt_ringChar_of_mem_exactInterpolationSpace Q hQ (by rw [h]; decide) j

/-- In characteristic zero the hypothesis `floor < ringChar F` is false. -/
example (D A d m : ℕ) : ¬ exactInterpolationJetDegreeFloor D A d m < ringChar ℚ := by
  rw [ringChar.eq_zero]
  exact Nat.not_lt_zero _
