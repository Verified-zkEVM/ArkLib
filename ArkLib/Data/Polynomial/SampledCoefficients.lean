/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Recovering bounded polynomial coefficients from scalar samples

For strict degree bound `<L`, exactly `L` distinct samples determine the coefficient vector.
Any correct solver for the corresponding Vandermonde system therefore recovers the actual
coefficients. Testing all sampled values for zero also tests the whole polynomial for zero.

These are mathematical refinement interfaces for a future costed sampling implementation.
The theorems do not implement sampling, matrix construction, or linear-system solving, and
attach no cost bound to an abstract solver.
-/

@[expose] public section

namespace Polynomial

open scoped Matrix

variable {F : Type*} [Field F] {L : ℕ}

/-- The actual bounded coefficient vector satisfies the scalar sample equations. -/
theorem vandermonde_coefficients_eq_samples (points : Fin L → F) (P : F[X])
    (hdegree : P.natDegree < L) :
    Matrix.vandermonde points *ᵥ (fun j : Fin L ↦ P.coeff j) =
      fun i ↦ P.eval (points i) := by
  funext i
  rw [eval_eq_sum_range' hdegree]
  change (∑ j : Fin L, points i ^ (j : ℕ) * P.coeff j) = _
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ P.coeff j * points i ^ j) L]
  exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)

/-- A correct Vandermonde solve returns the true coefficients, not just an agreeing polynomial. -/
theorem coefficients_eq_of_vandermonde_solve (points : Fin L ↪ F) (P : F[X])
    (hdegree : P.natDegree < L) (coefficients : Fin L → F)
    (hsolve : Matrix.vandermonde (fun i ↦ points i) *ᵥ coefficients =
      fun i ↦ P.eval (points i)) :
    coefficients = fun j : Fin L ↦ P.coeff j := by
  apply Matrix.mulVec_injective_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr points.injective)
  exact hsolve.trans (vandermonde_coefficients_eq_samples (fun i ↦ points i) P hdegree).symm

/-- The bounded sample system has exactly one solution, represented by the actual coefficients. -/
theorem existsUnique_vandermonde_coefficients (points : Fin L ↪ F) (P : F[X])
    (hdegree : P.natDegree < L) :
    ∃! coefficients : Fin L → F,
      Matrix.vandermonde (fun i ↦ points i) *ᵥ coefficients =
        fun i ↦ P.eval (points i) := by
  refine ⟨fun j : Fin L ↦ P.coeff j, vandermonde_coefficients_eq_samples _ P hdegree, ?_⟩
  intro coefficients hsolve
  exact coefficients_eq_of_vandermonde_solve points P hdegree coefficients hsolve

/-- The full zero-polynomial check reduces to scalar zero checks at the distinct samples.
The strict degree bound is essential; it is not replaced by a non-strict bound. -/
theorem eq_zero_iff_samples_eq_zero (points : Fin L ↪ F) (P : F[X])
    (hdegree : P.natDegree < L) : P = 0 ↔ ∀ i, P.eval (points i) = 0 := by
  constructor
  · rintro rfl i
    simp
  · intro hzero
    apply eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
      (v := fun i : Fin L ↦ points i) points.injective.injOn
    · have hdeg : P.degree < (L : WithBot ℕ) := by
        by_cases hp : P = 0
        · simp [hp]
        · exact (natDegree_lt_iff_degree_lt hp).mp hdegree
      simpa only [Finset.card_univ, Fintype.card_fin] using hdeg
    · intro i _
      exact hzero i

end Polynomial
