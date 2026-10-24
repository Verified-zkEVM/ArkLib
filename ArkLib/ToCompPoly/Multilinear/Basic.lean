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
  # Evaluation and table construction for CompPoly's multilinear representations

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

  The shared recursive `CMlPolynomialEval.lagrangeBasisFast` constructs the Lagrange table
  with a linear number of field operations in its output size. Its monadic construction also
  supports a measured arithmetic interpretation. The even/odd factorization proofs adapt
  the corresponding private lemmas from `CompPoly.Multilinear.Basic`.

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

universe u v

/-- Build a Boolean Lagrange table using supplied complement and multiplication operations.
The coordinate head is the least significant bit: each tail entry produces its even entry
with the complemented head and its odd entry with the head. -/
def lagrangeBasisWith {R : Type u} {m : Type u → Type v} [Monad m]
    (one : R) (complement : R → m R) (multiply : R → R → m R) :
    {n : ℕ} → Vector R n → m (CMlPolynomialEval R n)
  | 0, _ => pure #v[one]
  | n + 1, w => do
      let tailBasis ← lagrangeBasisWith one complement multiply w.tail
      let c ← complement w.head
      Vector.ofFnM fun i : Fin (2 ^ (n + 1)) =>
        let j : Fin (2 ^ n) := ⟨i.val / 2, by
          have hi : i.val < 2 ^ n * 2 := by
            simpa only [pow_succ] using i.isLt
          omega⟩
        multiply (if i.val % 2 = 0 then c else w.head) tailBasis[j]

/-- Construct the Boolean Lagrange table by sharing each tail table and each coordinate
complement. Each output entry requires one multiplication, independently of the dimension. -/
def lagrangeBasisFast {R : Type*} {n : ℕ} [CommRing R]
    (w : Vector R n) : CMlPolynomialEval R n :=
  lagrangeBasisWith (m := Id) 1 (fun x => 1 - x) (fun x y => x * y) w

/-- The zero-dimensional Lagrange table has the single entry one. -/
@[simp]
theorem lagrangeBasisFast_zero {R : Type*} [CommRing R] (w : Vector R 0) :
    lagrangeBasisFast w = #v[1] := rfl

/-- The least significant bit selects the head factor multiplying its shared tail entry. -/
theorem lagrangeBasisFast_succ {R : Type*} [CommRing R] {n : ℕ}
    (w : Vector R (n + 1)) :
    lagrangeBasisFast w = Vector.ofFn (fun i : Fin (2 ^ (n + 1)) =>
      (if i.val % 2 = 0 then 1 - w.head else w.head) *
        (lagrangeBasisFast w.tail).get ⟨i.val / 2, by
          simp only [Nat.add_sub_cancel]
          have hi : i.val < 2 ^ n * 2 := by
            simpa only [pow_succ] using i.isLt
          omega⟩) := by
  unfold lagrangeBasisFast
  rw [lagrangeBasisWith]
  change Id.run (Vector.ofFnM _) = _
  exact Vector.idRun_ofFnM

/-- An even Boolean-table index has zero as its head coordinate. -/
theorem lagrangeBasis_get_even {R : Type*} [CommRing R]
    {n : ℕ} (x : Vector R (n + 1)) (j : Fin (2 ^ n)) :
    (lagrangeBasis x).get ⟨2 * j.val, by omega⟩ =
      (1 - x.head) * (lagrangeBasis x.tail).get j := by
  unfold lagrangeBasis
  simp only [Vector.get_ofFn]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [← Nat.bit_false_apply j.val]
  simp only [Nat.testBit_bit_zero, Bool.false_eq_true, ite_false]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Nat.testBit_bit_succ]
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

/-- An odd Boolean-table index has one as its head coordinate. -/
theorem lagrangeBasis_get_odd {R : Type*} [CommRing R]
    {n : ℕ} (x : Vector R (n + 1)) (j : Fin (2 ^ n)) :
    (lagrangeBasis x).get ⟨2 * j.val + 1, by omega⟩ =
      x.head * (lagrangeBasis x.tail).get j := by
  unfold lagrangeBasis
  simp only [Vector.get_ofFn]
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [← Nat.bit_true_apply j.val]
  simp only [Nat.testBit_bit_zero, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Nat.testBit_bit_succ]
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

/-- The shared recursive construction equals the coordinate-product Lagrange table. -/
theorem lagrangeBasisFast_eq {R : Type*} [CommRing R]
    {n : ℕ} (w : Vector R n) : lagrangeBasisFast w = lagrangeBasis w := by
  induction n with
  | zero => rw [lagrangeBasisFast_zero, lagrangeBasis_zero]
  | succ n ih =>
    ext i hi
    have hj : i / 2 < 2 ^ n := by
      rw [pow_succ] at hi
      omega
    by_cases he : i % 2 = 0
    · have hi' : i = 2 * (i / 2) := by omega
      have h := lagrangeBasis_get_even w ⟨i / 2, hj⟩
      simpa only [lagrangeBasisFast_succ, Vector.getElem_ofFn, he, ite_true, ih,
        Vector.get_eq_getElem, Fin.getElem_fin, ← hi'] using h.symm
    · have hi' : i = 2 * (i / 2) + 1 := by omega
      have h := lagrangeBasis_get_odd w ⟨i / 2, hj⟩
      simpa only [lagrangeBasisFast_succ, Vector.getElem_ofFn, he, ite_false, ih,
        Vector.get_eq_getElem, Fin.getElem_fin, ← hi'] using h.symm

/-- Callers compiled with this extension use the shared recursive table construction. -/
@[csimp]
theorem lagrangeBasis_eq_lagrangeBasisFast : @lagrangeBasis = @lagrangeBasisFast := by
  funext R n _ w
  exact (lagrangeBasisFast_eq w).symm

end CompPoly.CMlPolynomialEval
