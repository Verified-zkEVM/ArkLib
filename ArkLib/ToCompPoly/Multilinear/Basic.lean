/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Data.MvPolynomial.Multilinear
import CompPoly.Multilinear.Basic

/-!
  # Evaluation semantics of CompPoly's multilinear evaluation tables

  Addition to `CompPoly.Multilinear` not yet upstreamed to CompPoly.

  CompPoly bridges the two *representations*: `CompPoly.Multilinear.Equiv` transports a hypercube
  evaluation table `CMlPolynomialEval R n` to `MvPolynomial (Fin n) R` (via `toMvPolynomial`,
  `toMvPolynomialDeg1`, `equivMvPolynomialDeg1`). What it does not yet record is how the computable
  evaluator `CMlPolynomialEval.eval` — a dot product against the Lagrange basis — relates to
  `MvPolynomial.eval` of the transported polynomial. This file supplies that missing half, stated
  against the multilinear extension `MvPolynomial.MLE` of
  `ArkLib/Data/MvPolynomial/Multilinear.lean`.

  The bit-index reconciliation is the whole content: `CMlPolynomialEval` indexes the hypercube by
  `Fin (2 ^ n)` through little-endian `BitVec` bits, while `MvPolynomial.MLE` indexes it by
  `Fin n → Fin 2`, and the two are matched by `finFunctionFinEquiv`.

  This is the boundary the Hachi zero-check crosses (`ZeroCheck/Constraints.lean`): the protocol
  relations are stated with the computable `CMlPolynomialEval.eval`, while the nested-tree zero
  test behind the corrected Lemma 10 reasons in `MvPolynomial`.
-/

namespace CompPoly.CMlPolynomialEval

variable {R : Type*} [CommRing R] {n : ℕ}

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
