/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import CompPoly.Multilinear.Basic

/-!
# Evaluating a computable table as a multilinear extension

CompPoly indexes Boolean evaluation tables by `Fin (2 ^ n)`, while ArkLib's `MvPolynomial.MLE`
indexes its input by `Fin n → Fin 2`. The equivalence `finFunctionFinEquiv` identifies the two
little-endian indexings. Evaluating a `CMlPolynomialEval` at any point therefore agrees with
evaluating ArkLib's multilinear extension of the same table there.

Hachi's zero-check uses this identity to apply a nested-tree zero test to its computable tables.
-/

@[expose] public section

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
