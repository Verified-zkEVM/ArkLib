/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToCompPoly.Multilinear.Basic
public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomialCost
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Affine rows of Boolean evaluation tables

Adjacent entries fix all remaining Boolean coordinates and leave the least significant
coordinate free. Their two dense coefficients represent that restriction as a formal
univariate polynomial in every characteristic. Only the already proved degree-one bound is
used to identify coefficients; no finite-field uniqueness principle is used.
-/

@[expose] public section

namespace CompPoly.CMlPolynomialEval

open MvPolynomial OracleComp OracleSpec

/-- The padded coefficients of the next-variable affine row at one Boolean suffix index. -/
def affineRow {R : Type*} [Sub R] {n : ℕ}
    (table : CMlPolynomialEval R (n + 1)) (j : Fin (2 ^ n)) : CPolynomial.Raw R :=
  CPolynomial.Raw.affine (table.get ⟨2 * j.val, by omega⟩)
    (table.get ⟨2 * j.val + 1, by omega⟩)

/-- Every affine row retains both coefficients, including a zero slope. -/
@[simp]
theorem size_affineRow {R : Type*} [Sub R] {n : ℕ}
    (table : CMlPolynomialEval R (n + 1)) (j : Fin (2 ^ n)) :
    (affineRow table j).size = 2 := rfl

private theorem finFunctionFinEquiv_cons_val {m n : ℕ}
    (a : Fin m) (u : Fin n → Fin m) :
    (finFunctionFinEquiv (Fin.cons a u)).val = a.val +
      m * (finFunctionFinEquiv u).val := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_succ, finFunctionFinEquiv_apply]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one, Fin.cons_succ, Fin.val_succ,
    pow_succ]
  congr 1
  simp_rw [mul_comm (m ^ _), ← mul_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem eq_affine_of_natDegree_le_one {R : Type*} [CommRing R]
    (p : Polynomial R) (hp : p.natDegree ≤ 1) :
    p = Polynomial.C (p.eval 0) + Polynomial.C (p.eval 1 - p.eval 0) * Polynomial.X := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hp]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, mul_zero, zero_add, mul_one]
  rw [add_sub_cancel_right]
  exact add_comm _ _

/-- The dense affine row equals formal restriction of the table's multilinear extension.
The suffix is Boolean and the head remains the polynomial variable. -/
theorem affineRow_toPoly {R : Type*} [CommRing R] {n : ℕ}
    (table : CMlPolynomialEval R (n + 1)) (j : Fin (2 ^ n)) :
    (affineRow table j).toPoly =
      Polynomial.map (MvPolynomial.eval (fun i => (finFunctionFinEquiv.symm j i : R)))
        (MvPolynomial.finSuccEquiv R n
          (MLE (fun x => table.get (finFunctionFinEquiv x)))) := by
  rw [affineRow, CPolynomial.Raw.toPoly_affine]
  symm
  classical
  let u := finFunctionFinEquiv.symm j
  let p := Polynomial.map (MvPolynomial.eval (fun i => (u i : R)))
    (MvPolynomial.finSuccEquiv R n
      (MLE (fun x => table.get (finFunctionFinEquiv x))))
  change p = _
  have hd : p.natDegree ≤ 1 := by
    apply Polynomial.natDegree_map_le.trans
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.MLE_degreeOf _ 0
  have hb (a : Fin 2) :
      p.eval (a : R) = table.get ⟨2 * j.val + a.val, by omega⟩ := by
    rw [show p = Polynomial.map (MvPolynomial.eval (fun i => (u i : R)))
      (MvPolynomial.finSuccEquiv R n
        (MLE (fun x => table.get (finFunctionFinEquiv x)))) from rfl]
    rw [← MvPolynomial.eval_eq_eval_mv_eval']
    have heq : Fin.cons (a : R) (fun i => (u i : R)) =
        (fun i => ((Fin.cons a u : Fin (n + 1) → Fin 2) i : R)) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> rfl
    rw [heq, MvPolynomial.MLE_eval_zeroOne]
    congr 1
    apply Fin.ext
    rw [finFunctionFinEquiv_cons_val]
    have hu : finFunctionFinEquiv u = j := Equiv.apply_symm_apply _ _
    rw [hu]
    change a.val + 2 * j.val = 2 * j.val + a.val
    omega
  have h := eq_affine_of_natDegree_le_one p hd
  rw [show p.eval (0 : R) = table.get ⟨2 * j.val, by omega⟩ from by simpa using hb 0,
    show p.eval (1 : R) = table.get ⟨2 * j.val + 1, by omega⟩ from by simpa using hb 1] at h
  exact h

section Arithmetic

variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Read each endpoint once and construct the padded affine row by a certified subtraction. -/
def affineRowProgram {n : ℕ} (table : CMlPolynomialEval F (n + 1)) (j : Fin (2 ^ n)) :
    OracleComp (ArithmeticSpec F) {p : CPolynomial.Raw F // p = affineRow table j} := do
  let a ← Arithmetic.valueRead table.toArray (2 * j.val)
  let b ← Arithmetic.valueRead table.toArray (2 * j.val + 1)
  let p ← Arithmetic.affineRaw a.val b.val
  pure ⟨p.val, by
    rw [p.property, a.property, b.property]
    have heven : 2 * j.val < 2 ^ (n + 1) := by omega
    have hodd : 2 * j.val + 1 < 2 ^ (n + 1) := by omega
    simp [affineRow, heven, hodd, Vector.get_eq_getElem]⟩

/-- An affine row requests two endpoint reads and one subtraction, with no other instructions. -/
theorem profileArithmetic_affineRowProgram {n : ℕ}
    (table : CMlPolynomialEval F (n + 1)) (j : Fin (2 ^ n)) :
    (profileArithmetic (affineRowProgram table j)).2 = fun kind =>
      if kind = .valueRead then 2 else if kind = .sub then 1 else 0 := by
  funext kind
  cases kind <;> simp [affineRowProgram, Arithmetic.profileArithmetic_affineRaw,
    arithmeticCost, ArithmeticOp.costKind]

end Arithmetic

end CompPoly.CMlPolynomialEval
