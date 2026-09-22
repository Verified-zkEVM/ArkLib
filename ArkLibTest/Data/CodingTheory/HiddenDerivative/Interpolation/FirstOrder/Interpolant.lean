/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Interpolant

/-!
# First-order interpolant acceptance tests

Nonvacuous interpolation certificates checked through the dimension count, at `D = 2` and at
`D = 1`, and the form of the root-multiplicity statement for one polynomial that agrees with every
received value.
-/

open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- With `m = 1` and `M = 0` each point imposes at most `certifiedEnlargedRankBound 1 1 0 0 = 1`
condition. -/
example : certifiedEnlargedRankBound 1 1 0 0 = 1 := by decide

/-- Three received points impose at most three conditions on the four-dimensional first-order
space at `D = 2`, `A = 3`, `m = 1`, `M = 0`, `μ = 1`. -/
example {F : Type*} [Field F] (centers received : Fin 3 → F) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧ Q ∈ firstOrderSpace F 2 3 1 0 1 ∧
      ∀ i, SatisfiesLocalConstraints 1 (centers i) (received i) Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount (by norm_num) centers received
  decide

/-- With `m = 1` and `M = 1` each point imposes at most `certifiedEnlargedRankBound 1 1 1 0 = 2`
conditions. -/
example : certifiedEnlargedRankBound 1 1 1 0 = 2 := by decide

/-- At `D = 1`, `A = 3`, `m = 1`, `M = 1`, `μ = 1`, three points impose at most six conditions on
the eight-dimensional first-order space. -/
example {F : Type*} [Field F] (centers received : Fin 3 → F) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧ Q ∈ firstOrderSpace F 1 3 1 1 1 ∧
      ∀ i, SatisfiesLocalConstraints 1 (centers i) (received i) Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount (by norm_num) centers received
  decide

/-- The local and global rank bounds at `D = 1`. -/
example {F : Type*} [Field F] (centers received : Fin 3 → F) :
    Module.finrank F (LinearMap.range
      (firstOrderGlobalConstraintMap (D := 1) (A := 3) (m := 1) (M := 1) (μ := 1) centers
        received)) ≤ 6 := by
  simpa using (finrank_firstOrderGlobalConstraintMap_le centers received).trans_eq
    (by decide : Fintype.card (Fin 3) * certifiedEnlargedRankBound 1 1 1 0 = 6)

/-- The form with one polynomial `P` agreeing with every received value, fixed before the
interpolant is chosen. -/
example {F : Type*} [Field F] {ι : Type*} [Fintype ι] {D A m M μ : ℕ}
    (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card)
    (P : Polynomial F) (hagree : ∀ i, P.eval (centers i) = received i) :
    ∃ Q : DifferentialPolynomial F 1, Q ≠ 0 ∧ Q ∈ firstOrderSpace F D A m M μ ∧
      ∀ i, (Polynomial.X - Polynomial.C (centers i)) ^ m ∣ differentialSpecialization Q P := by
  obtain ⟨Q, hQ0, hQ, hdvd⟩ :=
    exists_nonzero_firstOrder_interpolant_X_sub_C_pow_dvd centers received hdim
  exact ⟨Q, hQ0, hQ, fun i => hdvd P i (hagree i)⟩
