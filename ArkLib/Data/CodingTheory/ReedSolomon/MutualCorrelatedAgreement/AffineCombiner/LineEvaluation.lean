/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Trivariate polynomials along a multiplier curve

The proof interpolates a polynomial `Q(X, Y, Z)` and evaluates it along a curve.
The evaluation sends `Y` to a multiplier `M(X)` and `Z` to a candidate `P(X)`.
For Reed–Solomon codes the multiplier is the affine line `α + β X`.

## Weights

The `(Y, Z)`-weight ignores `X`, so it measures the joint degree in `Y` and `Z`.
The line weight `(1, e, d)` bounds the degree after the evaluation, when `deg M ≤ e`
and `deg P ≤ d`.
Reed–Solomon codes use `e = 1`; Reed–Muller codes use `e = n / q₀`.

## Main definitions

* `ReedSolomon.AffineVar`: the variables `X`, `Y`, `Z`.
* `ReedSolomon.affineYZWeight` and `ReedSolomon.lineWeight`: the two weights.
* `ReedSolomon.multiplierEval`: the evaluation `Q ↦ Q(X, M(X), P(X))`.

## Main statements

* `ReedSolomon.natDegree_multiplierEval_le`: the degree of the evaluation.
* `ReedSolomon.eval_multiplierEval`: evaluating the result at a point.
* `ReedSolomon.map_multiplierEval`: the evaluation commutes with a field embedding.

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

/-- The line weight `(1, e, d)`: `X` has weight `1`, `Y` has weight `e`, `Z` has weight `d`. -/
def lineWeight (e d : ℕ) : AffineVar → ℕ := fun v ↦ v.elim d ![1, e]

@[simp] theorem affineYZWeight_none : affineYZWeight none = 1 := rfl
@[simp] theorem affineYZWeight_X : affineYZWeight (some 0) = 0 := rfl
@[simp] theorem affineYZWeight_Y : affineYZWeight (some 1) = 1 := rfl
@[simp] theorem lineWeight_none (e d : ℕ) : lineWeight e d none = d := rfl
@[simp] theorem lineWeight_X (e d : ℕ) : lineWeight e d (some 0) = 1 := rfl
@[simp] theorem lineWeight_Y (e d : ℕ) : lineWeight e d (some 1) = e := rfl

/-- The weight of an exponent in the three variables. -/
theorem weight_affineVar (w : AffineVar → ℕ) (e : AffineVar →₀ ℕ) :
    Finsupp.weight w e = e none * w none + e (some 0) * w (some 0) + e (some 1) * w (some 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_option, Fin.sum_univ_two, add_assoc]

/-- The `(Y, Z)`-weight of a monomial is its `Y`-exponent plus its `Z`-exponent. -/
theorem weight_affineYZWeight (m : AffineVar →₀ ℕ) :
    Finsupp.weight affineYZWeight m = m none + m (some 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_option, Fin.sum_univ_two]

variable {K : Type*} [Field K]

/-- The evaluation `Q ↦ Q(X, M(X), P(X))` along the multiplier `M`. -/
noncomputable def multiplierEval (M P : K[X]) : MvPolynomial AffineVar K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun v ↦ v.elim P ![X, M]

@[simp] theorem multiplierEval_X_none (M P : K[X]) :
    multiplierEval M P (MvPolynomial.X none) = P := by
  simp [multiplierEval]

@[simp] theorem multiplierEval_X_X (M P : K[X]) :
    multiplierEval M P (MvPolynomial.X (some 0)) = X := by
  simp [multiplierEval]

@[simp] theorem multiplierEval_X_Y (M P : K[X]) :
    multiplierEval M P (MvPolynomial.X (some 1)) = M := by
  simp [multiplierEval]

/-- If `deg M ≤ e` and `deg P ≤ d`, the evaluation has degree at most `wdeg_{(1, e, d)} Q`. -/
theorem natDegree_multiplierEval_le {M P : K[X]} {e d : ℕ} (hM : M.natDegree ≤ e)
    (hP : P.natDegree ≤ d) (Q : MvPolynomial AffineVar K) :
    (multiplierEval M P Q).natDegree ≤ Q.weightedTotalDegree (lineWeight e d) := by
  classical
  conv_lhs => rw [Q.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  rw [multiplierEval, MvPolynomial.aeval_monomial]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_weightedTotalDegree _ hm)
  rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
  refine (natDegree_pow_le).trans ?_
  rw [smul_eq_mul]
  gcongr
  rcases v with _ | ⟨i⟩
  · simpa [lineWeight] using hP
  · fin_cases i
    · simp [lineWeight]
    · simpa [lineWeight] using hM

/-- Evaluating the result at `c` evaluates `Q` at `(c, M(c), P(c))`. -/
theorem eval_multiplierEval (c : K) (M P : K[X]) (Q : MvPolynomial AffineVar K) :
    (multiplierEval M P Q).eval c =
      MvPolynomial.aeval (fun v ↦ v.elim (P.eval c) ![c, M.eval c]) Q := by
  rw [← Polynomial.coe_aeval_eq_eval, multiplierEval, ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i <;> simp

/-- The evaluation commutes with a field embedding. -/
theorem map_multiplierEval {L : Type*} [Field L] (φ : K →+* L) (M P : K[X])
    (Q : MvPolynomial AffineVar K) :
    (multiplierEval M P Q).map φ = multiplierEval (M.map φ) (P.map φ) (MvPolynomial.map φ Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [multiplierEval]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Polynomial.map_mul, hp, MvPolynomial.map_X]
    congr 1
    rcases v with _ | ⟨i⟩
    · simp
    · fin_cases i <;> simp

end ReedSolomon
