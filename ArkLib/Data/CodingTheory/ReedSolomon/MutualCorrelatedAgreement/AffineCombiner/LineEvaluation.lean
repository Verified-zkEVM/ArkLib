/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Trivariate polynomials along an affine challenge line

The proof interpolates a polynomial `Q(X, Y, Z)` and evaluates it along a challenge line.

The evaluation sends `Y` to `α + β X` and `Z` to a candidate `P(X)`.

## Weights

The `(Y, Z)`-weight ignores `X`, so it measures the joint degree in `Y` and `Z`.

The line weight `(1, 1, d)` bounds the degree after the evaluation, when `deg P ≤ d`.

## Main definitions

* `ReedSolomon.AffineVar`: the variables `X`, `Y`, `Z`.
* `ReedSolomon.affineYZWeight` and `ReedSolomon.affineLineWeight`: the two weights.
* `ReedSolomon.affineLineEval`: the evaluation `Q ↦ Q(X, α + β X, P(X))`.

## Main statements

* `ReedSolomon.natDegree_affineLineEval_le`: the degree of the line evaluation.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

/-- The variables of the trivariate interpolant: `none` is the root variable `Z`, `some 0` is
`X` and `some 1` is the challenge variable `Y`. -/
abbrev AffineVar : Type := Option (Fin 2)

/-- The `(Y, Z)`-weight: `X` has weight `0`, `Y` and `Z` have weight `1`. -/
def affineYZWeight : AffineVar → ℕ := fun v ↦ v.elim 1 ![0, 1]

/-- The line weight `(1, 1, d)`: `X` and `Y` have weight `1`, `Z` has weight `d`. -/
def affineLineWeight (d : ℕ) : AffineVar → ℕ := fun v ↦ v.elim d ![1, 1]

@[simp] theorem affineYZWeight_none : affineYZWeight none = 1 := rfl
@[simp] theorem affineYZWeight_x : affineYZWeight (some 0) = 0 := rfl
@[simp] theorem affineYZWeight_y : affineYZWeight (some 1) = 1 := rfl
@[simp] theorem affineLineWeight_none (d : ℕ) : affineLineWeight d none = d := rfl
@[simp] theorem affineLineWeight_x (d : ℕ) : affineLineWeight d (some 0) = 1 := rfl
@[simp] theorem affineLineWeight_y (d : ℕ) : affineLineWeight d (some 1) = 1 := rfl

variable {K : Type*} [Field K]

/-- The evaluation `Q ↦ Q(X, α + β X, P(X))` along the challenge line. -/
noncomputable def affineLineEval (α β : K) (P : K[X]) : MvPolynomial AffineVar K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun v ↦ v.elim P ![X, affineMultiplier α β]

@[simp] theorem affineLineEval_X_none (α β : K) (P : K[X]) :
    affineLineEval α β P (MvPolynomial.X none) = P := by
  simp [affineLineEval]

@[simp] theorem affineLineEval_X_x (α β : K) (P : K[X]) :
    affineLineEval α β P (MvPolynomial.X (some 0)) = X := by
  simp [affineLineEval]

@[simp] theorem affineLineEval_X_y (α β : K) (P : K[X]) :
    affineLineEval α β P (MvPolynomial.X (some 1)) = affineMultiplier α β := by
  simp [affineLineEval]

/-- If `deg P ≤ d`, the line evaluation has degree at most the line-weighted degree of `Q`. -/
theorem natDegree_affineLineEval_le (α β : K) {P : K[X]} {d : ℕ} (hP : P.natDegree ≤ d)
    (Q : MvPolynomial AffineVar K) :
    (affineLineEval α β P Q).natDegree ≤ Q.weightedTotalDegree (affineLineWeight d) := by
  classical
  conv_lhs => rw [Q.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  rw [affineLineEval, MvPolynomial.aeval_monomial]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_weightedTotalDegree _ hm)
  rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
  refine (natDegree_pow_le).trans ?_
  rw [smul_eq_mul]
  gcongr
  rcases v with _ | ⟨i⟩
  · simpa [affineLineWeight] using hP
  · fin_cases i
    · simp [affineLineWeight]
    · simp only [affineLineWeight]
      exact natDegree_le_of_degree_le (degree_affineMultiplier_le α β) |>.trans le_rfl

end ReedSolomon
