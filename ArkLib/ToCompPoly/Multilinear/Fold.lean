/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Multilinear.Affine
public import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Formal polynomial semantics of Boolean table folding

Folding adjacent entries eliminates the least significant coordinate. Its canonical multilinear
extension is exactly formal substitution of the head variable. The fast equality-weight cache
represents the equality polynomial, also with an arbitrary scalar factor, including zero.

These identities hold over every commutative ring. The proofs use degree-one Boolean uniqueness;
they do not infer equality of unrestricted polynomials from their values in a finite field.
No new table algorithm or resource bound is introduced. Execution remains the existing
`evalMleLayer`, with its actual `(1-r)*a+r*b` expression, and the already certified fast basis.
-/

@[expose] public section

namespace CompPoly.CMlPolynomialEval
open MvPolynomial
variable {R : Type*} [CommRing R] {n : Nat}

/-- A table head-fold is formal partial evaluation of its canonical multilinear extension. -/
theorem MLE_evalMleLayer (table : CMlPolynomialEval R (n + 1)) (r : R) :
    MLE (fun u => (evalMleLayer table r).get (finFunctionFinEquiv u)) =
      Polynomial.eval (C r) (MvPolynomial.finSuccEquiv R n
        (MLE (fun u => table.get (finFunctionFinEquiv u)))) := by
  symm
  apply MvPolynomial.eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
  · intro i
    exact (MvPolynomial.degreeOf_eval_C_finSuccEquiv _ i r).trans
      (MvPolynomial.MLE_degreeOf _ i.succ)
  · intro u
    rw [MvPolynomial.eval_polynomial_eval_finSuccEquiv]
    simp only [MvPolynomial.eval_C]
    change MvPolynomial.eval (Fin.cons r (fun i => (u i : R))) _ = _
    rw [MvPolynomial.eval_eq_eval_mv_eval']
    have hrow := affineRow_toPoly table (finFunctionFinEquiv u)
    simp only [Equiv.symm_apply_apply] at hrow
    rw [← hrow, affineRow, CPolynomial.Raw.toPoly_affine, evalMleLayer_get]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    ring

/-- The fast little-endian equality-weight cache represents the formal equality polynomial. -/
theorem MLE_lagrangeBasisFast (z : Vector R n) :
    MLE (fun u => (lagrangeBasisFast z).get (finFunctionFinEquiv u)) =
      MvPolynomial.eqPolynomial z.get := by
  rw [lagrangeBasisFast_eq]
  symm
  apply MvPolynomial.eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
  · exact MvPolynomial.eqPolynomial_degreeOf _
  · intro u
    have ht : evalMle (lagrangeBasis z) (Vector.ofFn (fun i => (u i : R))) =
        (lagrangeBasis z).get (finFunctionFinEquiv u) := by
      simpa [eval₂Mle, map, MvPolynomial.MLE_eval_zeroOne] using
        eval₂Mle_eq_MvPolynomial_MLE (lagrangeBasis z) (RingHom.id R)
          (fun i => (u i : R))
    have hk : evalMle (lagrangeBasis z) (Vector.ofFn (fun i => (u i : R))) =
        MvPolynomial.eval (fun i => (u i : R)) (MvPolynomial.eqPolynomial z.get) := by
      rw [eval_mle_eq_eval]
      change CompPoly.CMlPolynomialEval.eqTilde z _ = _
      rw [CompPoly.CMlPolynomialEval.eqTilde_eq_prod, ← MvPolynomial.eqTilde_eq_eval,
        MvPolynomial.eqTilde_eq_prod]
      simp [Vector.get_eq_getElem]
    exact hk.symm.trans ht

/-- A scaled equality cache represents the scaled equality polynomial, even at zero factors. -/
theorem MLE_smul_lagrangeBasisFast (kappa : R) (z : Vector R n) :
    MLE (fun u => (kappa • lagrangeBasisFast z).get (finFunctionFinEquiv u)) =
      C kappa * MvPolynomial.eqPolynomial z.get := by
  rw [← MLE_lagrangeBasisFast]
  simp only [MLE, Finset.mul_sum, Vector.get_eq_getElem, Vector.getElem_smul,
    smul_eq_mul, map_mul]
  apply Finset.sum_congr rfl
  intro u _
  ring

end CompPoly.CMlPolynomialEval
