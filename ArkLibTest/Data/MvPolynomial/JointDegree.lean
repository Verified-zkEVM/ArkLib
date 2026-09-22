/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.JointDegree

/-!
# Joint degree acceptance tests

For one variable `X₀` of weight one, `Z² X₀` has joint degree `3` and `(Z X₀)³` has joint degree
`6`. `X₀` has no joint degree bound `0`, so the weight counts. With the zero weight the joint
bound is the coefficientwise challenge-degree bound.
-/

open scoped Polynomial

namespace JointDegreeTest

/-- `Z² X₀` has joint degree `2 + 1` when `X₀` has weight one. -/
example : MvPolynomial.C (Polynomial.X ^ 2 : ℚ[X]) * MvPolynomial.X (0 : Fin 1) ∈
    MvPolynomial.restrictJointDegree (R := ℚ) (fun _ => 1) (2 + 1) :=
  MvPolynomial.mul_mem_restrictJointDegree
    (MvPolynomial.C_mem_restrictJointDegree _ (by simp))
    (MvPolynomial.X_mem_restrictJointDegree _ 0 le_rfl)

/-- `(Z X₀)³` has joint degree `3 * 2`. -/
example : (MvPolynomial.C (Polynomial.X : ℚ[X]) * MvPolynomial.X (0 : Fin 1)) ^ 3 ∈
    MvPolynomial.restrictJointDegree (R := ℚ) (fun _ => 1) (3 * (1 + 1)) :=
  MvPolynomial.pow_mem_restrictJointDegree
    (MvPolynomial.mul_mem_restrictJointDegree
      (MvPolynomial.C_mem_restrictJointDegree _ (by simp))
      (MvPolynomial.X_mem_restrictJointDegree _ 0 le_rfl)) 3

/-- The weight counts: `X₀` of weight one has no joint degree bound `0`. -/
example : MvPolynomial.X (0 : Fin 1) ∉
    MvPolynomial.restrictJointDegree (R := ℚ) (fun _ => 1) 0 := by
  intro h
  have := MvPolynomial.coeff_eq_zero_of_mem_restrictJointDegree h
    (e := Finsupp.single 0 1) (by simp [Finsupp.weight_single])
  simp at this

/-- With the zero weight, a joint bound `2` bounds the challenge degree of every coefficient by
`2`. -/
example (e : Fin 1 →₀ ℕ) :
    ((MvPolynomial.C (Polynomial.X ^ 2 : ℚ[X]) * MvPolynomial.X (0 : Fin 1)).coeff e).natDegree ≤
      2 :=
  MvPolynomial.mem_restrictJointDegree_zero_iff.mp
    (MvPolynomial.mul_mem_restrictJointDegree (B := 0)
      (MvPolynomial.C_mem_restrictJointDegree _ (by simp))
      (MvPolynomial.X_mem_restrictJointDegree _ 0 le_rfl)) e

/-- Substitution: `X₀ ↦ Z X₁ + X₂` sends a polynomial of joint degree `B` for weight one on `X₀`
to one of joint degree `B` for weight one on `X₁, X₂`. -/
example {B : ℕ} {P : MvPolynomial (Fin 1) ℚ[X]}
    (hP : P ∈ MvPolynomial.restrictJointDegree (R := ℚ) (fun _ => 2) B) :
    MvPolynomial.bind₁ (fun _ => MvPolynomial.C Polynomial.X * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.X 1) P ∈ MvPolynomial.restrictJointDegree (R := ℚ) (fun _ => 1) B :=
  MvPolynomial.bind₁_mem_restrictJointDegree
    (fun _ => add_mem
      (MvPolynomial.mul_mem_restrictJointDegree (A := 1) (B := 1)
        (MvPolynomial.C_mem_restrictJointDegree _ (by simp))
        (MvPolynomial.X_mem_restrictJointDegree _ 0 le_rfl))
      (MvPolynomial.X_mem_restrictJointDegree _ 1 (by norm_num))) hP

end JointDegreeTest
