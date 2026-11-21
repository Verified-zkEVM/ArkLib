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
The evaluation sends `Y` to a multiplier `L(X)` and `Z` to a candidate `P(X)`.
For Reed–Solomon codes the multiplier is the affine line `α + β X`.
A family of polynomials `θⱼ` gives the multipliers `∑ⱼ aⱼ θⱼ`, linear in the coefficients `aⱼ`.
The lines `α + β X` come from the family `(1, X)`.

## Weights

The `(Y, Z)`-weight ignores `X`, so it measures the joint degree in `Y` and `Z`.
The multiplier weight `(1, e, d)` bounds the degree after the evaluation.
It applies when `deg L ≤ e` and `deg P ≤ d`.
Reed–Solomon codes use `e = 1`.
On the grid `𝔽_{q₀}^k` of `n = q₀^k` points, Reed–Muller codes use `e = n / q₀ = q₀^(k-1)`.

## Main definitions

* `ReedSolomon.AffineVar`: the variables `X`, `Y`, `Z`.
* `ReedSolomon.affineYZWeight` and `ReedSolomon.multiplierWeight`: the two weights.
* `ReedSolomon.multiplierEval`: the evaluation `Q ↦ Q(X, L(X), P(X))`.
* `ReedSolomon.familyMultiplier`: the multiplier `∑ⱼ aⱼ θⱼ` of a linear family `θ`, as a
  Mathlib linear combination, so it is linear in the coefficients.
* `ReedSolomon.affineFamily`: the Reed–Solomon family `(1, X)`.

## Main statements

* `ReedSolomon.natDegree_multiplierEval_le`: the degree of the evaluation.
* `ReedSolomon.eval_multiplierEval`: evaluating the result at a point.
* `ReedSolomon.map_multiplierEval`: the evaluation commutes with a field embedding.
* `ReedSolomon.familyMultiplier_apply`: the multiplier as the sum `∑ⱼ C(aⱼ) θⱼ`.
* `ReedSolomon.familyMultiplier_affineFamily`: the family `(1, X)` gives the lines `a + b X`.

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

/-- The multiplier weight `(1, e, d)`: `X`, `Y` and `Z` have weights `1`, `e` and `d`. -/
def multiplierWeight (e d : ℕ) : AffineVar → ℕ := fun v ↦ v.elim d ![1, e]

@[simp] theorem affineYZWeight_none : affineYZWeight none = 1 := rfl
@[simp] theorem affineYZWeight_X : affineYZWeight (some 0) = 0 := rfl
@[simp] theorem affineYZWeight_Y : affineYZWeight (some 1) = 1 := rfl
@[simp] theorem multiplierWeight_none (e d : ℕ) : multiplierWeight e d none = d := rfl
@[simp] theorem multiplierWeight_X (e d : ℕ) : multiplierWeight e d (some 0) = 1 := rfl
@[simp] theorem multiplierWeight_Y (e d : ℕ) : multiplierWeight e d (some 1) = e := rfl

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

/-- The evaluation `Q ↦ Q(X, L(X), P(X))` along the multiplier `L`. -/
noncomputable def multiplierEval (L P : K[X]) : MvPolynomial AffineVar K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun v ↦ v.elim P ![X, L]

@[simp] theorem multiplierEval_X_none (L P : K[X]) :
    multiplierEval L P (MvPolynomial.X none) = P := by
  simp [multiplierEval]

@[simp] theorem multiplierEval_X_X (L P : K[X]) :
    multiplierEval L P (MvPolynomial.X (some 0)) = X := by
  simp [multiplierEval]

@[simp] theorem multiplierEval_X_Y (L P : K[X]) :
    multiplierEval L P (MvPolynomial.X (some 1)) = L := by
  simp [multiplierEval]

/-- If `deg L ≤ e` and `deg P ≤ d`, the evaluation has degree at most `wdeg_{(1, e, d)} Q`. -/
theorem natDegree_multiplierEval_le {L P : K[X]} {e d : ℕ} (hL : L.natDegree ≤ e)
    (hP : P.natDegree ≤ d) (Q : MvPolynomial AffineVar K) :
    (multiplierEval L P Q).natDegree ≤ Q.weightedTotalDegree (multiplierWeight e d) := by
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
  · simpa [multiplierWeight] using hP
  · fin_cases i
    · simp [multiplierWeight]
    · simpa [multiplierWeight] using hL

/-- Evaluating the result at `c` evaluates `Q` at `(c, L(c), P(c))`. -/
theorem eval_multiplierEval (c : K) (L P : K[X]) (Q : MvPolynomial AffineVar K) :
    (multiplierEval L P Q).eval c =
      MvPolynomial.aeval (fun v ↦ v.elim (P.eval c) ![c, L.eval c]) Q := by
  rw [← Polynomial.coe_aeval_eq_eval, multiplierEval, ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i <;> simp

/-- The multiplier `∑ⱼ aⱼ θⱼ` of the family `θ` at the coefficient vector `a`. -/
noncomputable def familyMultiplier {κ : Type*} [Fintype κ] (θ : κ → K[X]) (a : κ → K) : K[X] :=
  Fintype.linearCombination K θ a

/-- The multiplier of `θ` at `a` is `∑ⱼ C(aⱼ) θⱼ`. -/
theorem familyMultiplier_apply {κ : Type*} [Fintype κ] (θ : κ → K[X]) (a : κ → K) :
    familyMultiplier θ a = ∑ j, C (a j) * θ j := by
  simp [familyMultiplier, Fintype.linearCombination_apply, smul_eq_C_mul]

/-- The Reed–Solomon family `(1, X)`, whose multipliers are the lines `a + b X`. -/
noncomputable def affineFamily : Fin 2 → K[X] := ![1, X]

/-- The multiplier of the family `(1, X)` at `(a, b)` is the line `a + b X`. -/
@[simp] theorem familyMultiplier_affineFamily (a b : K) :
    familyMultiplier affineFamily ![a, b] = affineMultiplier a b := by
  simp [familyMultiplier_apply, affineFamily, affineMultiplier, Fin.sum_univ_two]

/-- The evaluation commutes with a field embedding. -/
theorem map_multiplierEval {K' : Type*} [Field K'] (φ : K →+* K') (L P : K[X])
    (Q : MvPolynomial AffineVar K) :
    (multiplierEval L P Q).map φ = multiplierEval (L.map φ) (P.map φ) (MvPolynomial.map φ Q) := by
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
