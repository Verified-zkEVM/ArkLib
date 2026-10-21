/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import CompPoly.Multilinear.Basic
public import CompPoly.Multilinear.Equiv

/-!
  # Evaluation semantics of CompPoly's multilinear representations

  Additions to `CompPoly.Multilinear` not yet upstreamed to CompPoly.

  CompPoly bridges its representations to Mathlib: `CompPoly.Multilinear.Equiv` transports a
  monomial-coefficient vector `CMlPolynomial R n` to `MvPolynomial (Fin n) R` (`toMvPolynomial`,
  `toMvPolynomialDeg1`, `equivMvPolynomialDeg1`), and a hypercube evaluation table
  `CMlPolynomialEval R n` through `lagrangeToMono`. What it does not yet record is how the
  computable evaluators relate to `MvPolynomial.eval`. This file supplies both halves.

  * Monomial side: `CMlPolynomial.eval`, a dot product against the little-endian monomial basis,
    is `MvPolynomial.eval` of `toMvPolynomial` (`CMlPolynomial.eval_eq_eval_toMvPolynomial`).
  * Lagrange side: `CMlPolynomialEval.eval`, a dot product against the Lagrange basis, is
    `MvPolynomial.eval` of the multilinear extension `MvPolynomial.MLE` of
    `ArkLib/Data/MvPolynomial/Multilinear.lean` (`CMlPolynomialEval.eval_eq_MvPolynomial_MLE`).

  The bit-index reconciliation is the whole content: CompPoly indexes coefficients and hypercube
  points by `Fin (2 ^ n)` through little-endian bits, while Mathlib uses exponent functions
  (`CMlPolynomial.monomialOfNat`) and `Fin n → Fin 2` (matched by `finFunctionFinEquiv`).

  The Hachi zero-check (`ZeroCheck/Constraints.lean`) crosses the Lagrange-side boundary: its
  relations use `CMlPolynomialEval.eval`, while the nested-tree zero test behind the corrected
  Lemma 10 reasons in `MvPolynomial`. The Hachi trace head (`TraceHead/Coefficients.lean`)
  crosses the monomial-side boundary to state its packing through the shared `MvPolynomial`
  packing layer.
-/

@[expose] public section

namespace CompPoly.CMlPolynomial

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- Entry `i` of the monomial basis at `x` is the evaluation at `x` of the monomial whose
exponents are the little-endian bits of `i`. -/
theorem monomialBasis_get_eq_eval_monomial (x : Vector R n) (i : Fin (2 ^ n)) :
    (monomialBasis x).get i =
      MvPolynomial.eval x.get (MvPolynomial.monomial (monomialOfNat i) 1) := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun j => pow_zero _)]
  change (monomialBasis x)[i] = _
  rw [monomialBasis_getElem]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [monomialOfNat, Finsupp.onFinset_apply, Nat.getBit_eq_testBit,
    BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin, Fin.getElem_fin, Vector.get_eq_getElem]
  split_ifs <;> simp

/-- Direct evaluation of a monomial-coefficient vector agrees with evaluating the transported
Mathlib polynomial. -/
theorem eval_eq_eval_toMvPolynomial (p : CMlPolynomial R n) (x : Vector R n) :
    p.eval x = MvPolynomial.eval x.get (toMvPolynomial p) := by
  rw [toMvPolynomial, map_sum, eval, Vector.dotProduct_eq_root_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [monomialBasis_get_eq_eval_monomial, MvPolynomial.eval_monomial,
    MvPolynomial.eval_monomial, one_mul]
  rfl

end CompPoly.CMlPolynomial

namespace CompPoly.CMlPolynomialEval

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The identically-zero evaluation table vanishes at every point.

This is what makes an identity `H ≡ 0` usable at an *arbitrary* challenge point, hence the
honest-direction step in protocols that reduce a polynomial identity to evaluation claims (the
Hachi zero-check, `ZeroCheck/Completeness.lean`). -/
@[simp]
theorem eval_zero (x : Vector R n) : eval (0 : CMlPolynomialEval R n) x = 0 := by
  change Vector.dotProduct (0 : CMlPolynomialEval R n) (lagrangeBasis x) = 0
  rw [Vector.dotProduct_eq_root_dotProduct]
  have hget : (0 : CMlPolynomialEval R n).get = 0 := by
    funext i
    simp [Vector.get]
  rw [hget, zero_dotProduct]

/-- Direct evaluation of a Boolean-value vector agrees with evaluating Mathlib's multilinear
extension of the same table. This is the boundary used when a computational relation is stated
with `CMlPolynomialEval.eval` but an algebraic proof consumes `MvPolynomial.MLE`. -/
theorem eval_eq_MvPolynomial_MLE (evals : (Fin n → Fin 2) → R) (x : Fin n → R) :
    eval
        (Vector.ofFn fun i => evals (finFunctionFinEquiv.symm i))
        (Vector.ofFn x) =
      MvPolynomial.eval x (MvPolynomial.MLE evals) := by
  rw [MvPolynomial.MLE, map_sum]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval,
    Vector.dotProduct_eq_root_dotProduct, _root_.dotProduct]
  apply Fintype.sum_equiv finFunctionFinEquiv.symm
  intro i
  simp only [Vector.get_ofFn]
  rw [mul_comm]
  congr 1
  unfold lagrangeBasis
  simp only [Vector.get_ofFn]
  simp only [MvPolynomial.eqPolynomial, map_prod, map_add, map_mul, map_sub, map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.prod_congr rfl
  intro j _
  have hbit :
      (BitVec.ofFin i).getLsb j = ((finFunctionFinEquiv.symm i) j == 1) := by
    simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [finFunctionFinEquiv]
    have hr : i.val / 2 ^ j.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hq : i.val / 2 ^ j.val % 2 <;> simp [hq]
  rw [hbit]
  have hv := ((finFunctionFinEquiv.symm i) j).isLt
  interval_cases hval : ((finFunctionFinEquiv.symm i) j).val <;>
    simp [Fin.ext_iff, hval]

end CompPoly.CMlPolynomialEval
