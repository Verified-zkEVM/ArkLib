/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MlPoly.Basic
import ArkLib.Data.MvPolynomial.Notation
-- import Mathlib.RingTheory.MvPolynomial.Basic

/-!
  # Equivalence between `MlPoly` and multilinear polynomials in `MvPolynomial`

  This file establishes the mathematical foundations for `MlPoly` by proving:
  1. Basis properties for the coefficient representation
  2. Change-of-basis matrices between different representations
  3. Equivalences with mathlib's `MvPolynomial.restrictDegree`
  4. Arithmetic operation compatibilities
-/

open MvPolynomial

#check MvPolynomial.restrictDegree

variable {R : Type*} [CommRing R] {n : ℕ}

-- def MlPolynomial R n := MvPolynomial.restrictDegree (Fin n) R 1

noncomputable section

namespace MlPoly

/-! ### Basis Properties -/

-- /-- The coefficient basis for `MlPoly R n` -/
-- def coefficientBasis : Basis (Fin (2^n)) R (MlPoly R n) :=
--   Basis.ofEquiv (Vector.equivFin _) (by infer_instance)

-- /-- The evaluation basis for `MlPoly R n` (evaluations at Boolean hypercube points) -/
-- def evaluationBasis : Basis (Fin (2^n)) R (MlPolyEval R n) :=
--   Basis.ofEquiv (Vector.equivFin _) (by infer_instance)

/-! ### Change-of-Basis Matrices -/

/-- Change-of-basis matrix from coefficient basis to evaluation basis -/
noncomputable def coeffToEvalMatrix : Matrix (Fin (2^n)) (Fin (2^n)) R :=
  fun i j => (lagrangeBasis (Vector.ofFn (fun k => if k < n then if (BitVec.ofFin i).getLsb k then 1 else 0 else 0)))[j]

/-- Change-of-basis matrix from evaluation basis to coefficient basis -/
noncomputable def evalToCoeffMatrix : Matrix (Fin (2^n)) (Fin (2^n)) R :=
  fun i j => (evalToCoeff n (Vector.ofFn (fun k => if (BitVec.ofFin i).getLsb ⟨k.val % n, by sorry⟩ then 1 else 0)))[j]

/-- The change-of-basis matrices are inverses of each other -/
theorem coeffToEvalMatrix_inv_evalToCoeffMatrix :
  coeffToEvalMatrix * evalToCoeffMatrix = (1 : Matrix (Fin (2^n)) (Fin (2^n)) R) ∧
  evalToCoeffMatrix * coeffToEvalMatrix = (1 : Matrix (Fin (2^n)) (Fin (2^n)) R) := by
  sorry

/-- The change-of-basis matrix is invertible -/
theorem coeffToEvalMatrix_invertible (n : ℕ) :
  IsUnit (Matrix.det (coeffToEvalMatrix : Matrix (Fin (2^n)) (Fin (2^n)) R) : R) := by
  sorry

/-! ### Equivalence with Mathlib MvPolynomial -/

def toSpec (p : MlPoly R n) : R⦃≤ 1⦄[X Fin n] :=
  ⟨∑ i : Fin (2 ^ n), (C p[i]) * ∏ j : Fin n, if (BitVec.ofFin i).getLsb' j then X j else C 1 - X j,
  by
    sorry⟩

def ofSpec (p : R⦃≤ 1⦄[X Fin n]) : MlPoly R n :=
  Vector.ofFn (fun i : Fin (2 ^ n) =>
    p.val.coeff (Finsupp.onFinset Finset.univ (fun j => finFunctionFinEquiv.invFun i j) (by simp)))

def equivSpec : MlPoly R n ≃ R⦃≤ 1⦄[X Fin n] where
  toFun := toSpec
  invFun := ofSpec
  left_inv := sorry
  right_inv := sorry

/-- Linear equivalence between `MlPoly` and `MvPolynomial.restrictDegree` -/
noncomputable def linearEquivMvPolynomial : MlPoly R n ≃ₗ[R] R⦃≤ 1⦄[X Fin n] :=
  sorry

#check MvPolynomial.eval₂

variable {S : Type*} [CommRing S]

/-! ### Arithmetic Operation Equivalences -/

theorem equivSpec_add (p q : MlPoly R n) :
  (p + q).toSpec = p.toSpec + q.toSpec :=
  sorry

theorem equivSpec_smul (r : R) (p : MlPoly R n) :
  (r • p).toSpec = r • p.toSpec :=
  sorry

theorem equivSpec_eval₂ (f : R →+* S) (p : MlPoly R n) (x : Vector S n) :
    p.eval₂ f x = p.toSpec.val.eval₂ f x.get :=
  sorry

/-! ### Evaluation Equivalences -/

/-- Evaluation at Boolean hypercube points is equivalent to coefficient access -/
theorem eval_at_boolean_hypercube_equiv (p : MlPoly R n) (i : Fin (2^n)) :
  p.eval (Vector.ofFn (fun j => if (BitVec.ofFin i).getLsb j then 1 else 0)) = p[i] := by
  sorry

/-- Evaluation at arbitrary points via Lagrange interpolation -/
theorem eval_equiv_mvPolynomial_eval (p : MlPoly R n) (x : Vector R n) :
  p.eval x = p.toSpec.val.eval₂ (RingHom.id R) x.get := by
  sorry

/-! ### Transform Equivalences -/

/-- The zeta transform preserves polynomial evaluation -/
theorem coeffToEval_preserves_eval (p : MlPoly R n) (x : Vector R n) :
  MlPoly.eval (MlPoly.coeffToEval n p) x = p.eval x := by
  sorry

/-- The inverse zeta transform preserves polynomial evaluation -/
theorem evalToCoeff_preserves_eval (p : MlPolyEval R n) (x : Vector R n) :
  MlPoly.eval (MlPoly.evalToCoeff n p) x = MlPoly.eval p x := by
  sorry

-- TODO: fill in these theorems and more

end MlPoly

namespace MlPolyEval

-- TODO: state the equivalence between `MlPolyEval` and
-- `MlPoly`, via going from the coefficients to
-- the monomial basis

/-! ### Equivalence between MlPolyEval and MlPoly -/

/-- Convert from evaluation representation to coefficient representation -/
def toCoeff (p : MlPolyEval R n) : MlPoly R n := MlPoly.evalToCoeff n p

/-- Convert from coefficient representation to evaluation representation -/
def ofCoeff (p : MlPoly R n) : MlPolyEval R n := MlPoly.coeffToEval n p

/-- Equivalence between evaluation and coefficient representations -/
def equivCoeff : MlPolyEval R n ≃ MlPoly R n where
  toFun := toCoeff
  invFun := ofCoeff
  left_inv := sorry
  right_inv := sorry

/-- Linear equivalence between evaluation and coefficient representations -/
noncomputable def linearEquivCoeff : MlPolyEval R n ≃ₗ[R] MlPoly R n :=
  sorry

/-- Evaluation is preserved under the equivalence -/
theorem eval_preserved_under_equiv (p : MlPolyEval R n) (x : Vector R n) :
  MlPoly.eval p x = MlPoly.eval p.toCoeff x := by
  sorry

end MlPolyEval

end
