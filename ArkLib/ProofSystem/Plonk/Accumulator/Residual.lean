/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Accumulator.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Polynomial residuals of Plonk accumulators

The boundary and recurrence conditions are equivalent to vanishing of two polynomials on the
evaluation domain. For wire, permutation and accumulator polynomials of degree `< n`, their
degrees are at most `2(n - 1)` and, when `n ≥ 2`, `4(n - 1)`, respectively.
-/

@[expose] public section

namespace Plonk

open Polynomial
open scoped BigOperators

variable {F : Type} [Field F] {n : ℕ}

/-- The normalized boundary condition, using noncomputable Lagrange interpolation and polynomial
arithmetic. -/
noncomputable def boundaryResidual (D : EvaluationDomain F n) (hn : 0 < n) (Z : F[X]) : F[X] :=
  (D.lagrange ⟨0, hn⟩).val * (Z - 1)

/-- The cyclic recurrence residual, using noncomputable Mathlib polynomial arithmetic. -/
noncomputable def recurrenceResidual (ω : F) (N Q Z : F[X]) : F[X] :=
  Z.comp (C ω * X) * Q - Z * N

/-- The boundary residual vanishes precisely when the first row is normalized. -/
theorem vanishes_boundaryResidual_iff (D : EvaluationDomain F n) (hn : 0 < n) (Z : F[X]) :
    D.Vanishes (boundaryResidual D hn Z) ↔ Z.eval (D.node ⟨0, hn⟩) = 1 := by
  constructor
  · intro h
    have hzero := h ⟨0, hn⟩
    simpa [boundaryResidual, sub_eq_zero] using hzero
  · intro h i
    by_cases hi : i = ⟨0, hn⟩
    · subst i
      simp [boundaryResidual, h]
    · simp [boundaryResidual, hi]

/-- Evaluating the recurrence residual gives the multiplication-form row equation. -/
@[simp]
theorem eval_recurrenceResidual (ω x : F) (N Q Z : F[X]) :
    (recurrenceResidual ω N Q Z).eval x = Z.eval (ω * x) * Q.eval x - Z.eval x * N.eval x := by
  simp [recurrenceResidual, eval_comp]

/-- The recurrence residual vanishes precisely when every row satisfies the recurrence. -/
theorem vanishes_recurrenceResidual_iff (D : EvaluationDomain F n) (ω : F) (N Q Z : F[X]) :
    D.Vanishes (recurrenceResidual ω N Q Z) ↔
      ∀ i, Z.eval (ω * D.node i) * Q.eval (D.node i) =
        Z.eval (D.node i) * N.eval (D.node i) := by
  simp [EvaluationDomain.Vanishes, sub_eq_zero]

/-- On a primitive-root domain, the normalized accumulator relation is exactly the two zero
conditions. -/
theorem accumulatorRelation_iff_vanishes (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (N Q Z : F[X]) :
    AccumulatorRelation (EvaluationDomain.primitiveRoot ω hω) ω N Q Z ↔
      (EvaluationDomain.primitiveRoot ω hω).Vanishes
        (boundaryResidual (EvaluationDomain.primitiveRoot ω hω) hn Z) ∧
      (EvaluationDomain.primitiveRoot ω hω).Vanishes (recurrenceResidual ω N Q Z) := by
  rw [vanishes_boundaryResidual_iff, vanishes_recurrenceResidual_iff]
  simp [AccumulatorRelation]

private theorem natDegree_degreeLT_le (p : degreeLT F n) : p.val.natDegree ≤ n - 1 := by
  by_cases hp : p.val = 0
  · simp [hp]
  · have hlt := (natDegree_lt_iff_degree_lt hp).mpr (mem_degreeLT.mp p.property)
    omega

/-- The boundary residual has degree at most `2(n - 1)`. -/
theorem degree_boundaryResidual_le (D : EvaluationDomain F n) (hn : 0 < n)
    (Z : degreeLT F n) :
    (boundaryResidual D hn Z.val).degree ≤ (2 * (n - 1) : ℕ) := by
  apply degree_le_of_natDegree_le
  unfold boundaryResidual
  apply natDegree_mul_le.trans
  have hL := natDegree_degreeLT_le (D.lagrange ⟨0, hn⟩)
  have hZ := natDegree_degreeLT_le Z
  have hsub : (Z.val - 1).natDegree = Z.val.natDegree := by
    simpa using (natDegree_sub_C (p := Z.val) (a := (1 : F)))
  rw [hsub]
  omega

/-- For `n ≥ 2`, the numerator product has degree at most `3(n - 1)`. -/
theorem degree_accumulatorNumerator_le (hn : 2 ≤ n) (a : Fin 3 → degreeLT F n)
    (k : Fin 3 → F) (β γ : F) :
    (accumulatorNumerator a k β γ).degree ≤ (3 * (n - 1) : ℕ) := by
  have hf (c : Fin 3) : ((a c).val + C (β * k c) * X + C γ).natDegree ≤ n - 1 := by
    rw [natDegree_add_C]
    apply natDegree_add_le_of_degree_le (natDegree_degreeLT_le (a c))
    exact (natDegree_C_mul_le _ X).trans (by simp; omega)
  apply degree_le_of_natDegree_le
  unfold accumulatorNumerator
  refine (natDegree_prod_le _ _).trans ?_
  calc
    (∑ c : Fin 3, ((a c).val + C (β * k c) * X + C γ).natDegree) ≤
        (∑ _c : Fin 3, (n - 1)) := by
          apply Finset.sum_le_sum
          intro c _
          exact hf c
    _ = 3 * (n - 1) := by simp

/-- The denominator product has degree at most `3(n - 1)`. -/
theorem degree_accumulatorDenominator_le (a s : Fin 3 → degreeLT F n) (β γ : F) :
    (accumulatorDenominator a s β γ).degree ≤ (3 * (n - 1) : ℕ) := by
  have hf (c : Fin 3) : ((a c).val + C β * (s c).val + C γ).natDegree ≤ n - 1 := by
    rw [natDegree_add_C]
    exact natDegree_add_le_of_degree_le (natDegree_degreeLT_le (a c))
      ((natDegree_C_mul_le _ _).trans (natDegree_degreeLT_le (s c)))
  apply degree_le_of_natDegree_le
  unfold accumulatorDenominator
  refine (natDegree_prod_le _ _).trans ?_
  calc
    (∑ c : Fin 3, ((a c).val + C β * (s c).val + C γ).natDegree) ≤
        (∑ _c : Fin 3, (n - 1)) := by
          apply Finset.sum_le_sum
          intro c _
          exact hf c
    _ = 3 * (n - 1) := by simp

/-- Three degree-bounded wire columns and an accumulator give recurrence degree at most
`4(n - 1)` when `n ≥ 2`. -/
theorem degree_accumulatorRecurrenceResidual_le (hn : 2 ≤ n)
    (a s : Fin 3 → degreeLT F n) (k : Fin 3 → F) (β γ ω : F) (Z : degreeLT F n) :
    (recurrenceResidual ω (accumulatorNumerator a k β γ)
      (accumulatorDenominator a s β γ) Z.val).degree ≤ (4 * (n - 1) : ℕ) := by
  have hN := natDegree_le_of_degree_le (degree_accumulatorNumerator_le hn a k β γ)
  have hQ := natDegree_le_of_degree_le (degree_accumulatorDenominator_le a s β γ)
  have hZ := natDegree_degreeLT_le Z
  have hcomp : (Z.val.comp (C ω * X)).natDegree ≤ Z.val.natDegree := by
    apply natDegree_comp_le.trans
    have hlin : (C ω * X).natDegree ≤ 1 := (natDegree_C_mul_le _ X).trans (by simp)
    exact (Nat.mul_le_mul_left _ hlin).trans_eq (Nat.mul_one _)
  apply degree_le_of_natDegree_le
  unfold recurrenceResidual
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by omega)
  · exact natDegree_mul_le.trans (by omega)

end Plonk
