/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import CompPoly.Univariate.ToPoly
public import ArkLib.ToCompPoly.Univariate.Raw.Horner
import Mathlib.Algebra.Polynomial.OfFn

import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Padded coefficient arithmetic and affine rows

Raw arrays retain trailing zero coefficients. The explicit operations below preserve this
padding; their polynomial interpretations are used only in proofs. No algebraic instances
are installed on arrays with distinct representations of the same polynomial.
-/

@[expose] public section

namespace CompPoly.CPolynomial.Raw

/-- Seeded evaluation is the sum of all stored coefficient powers, including trailing zeros. -/
theorem evalHornerSeeded_eq_sum {R : Type*} [Semiring R] (x : R) (p : Array R) :
    evalHornerSeeded x p = ∑ i : Fin p.size, p[i.val] * x ^ i.val := by
  classical
  have hpoly : toPoly p = Polynomial.ofFn p.size (fun i => p[i.val]) := by
    ext j
    rw [coeff_toPoly]
    by_cases hj : j < p.size
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj, Trim.coeff_eq_getElem hj]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      simp only [coeff, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (Nat.le_of_not_gt hj), Option.getD_none]
  rw [evalHornerSeeded_eq_evalHorner, evalHorner_eq_eval, ← eval_toPoly_eq_eval,
    hpoly, Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- A typed coefficient vector has the same stored-coordinate sum as its seeded array view. -/
theorem evalHornerSeeded_toArray_eq_sum {R : Type*} [Semiring R] {L : Nat}
    (x : R) (p : Vector R L) :
    evalHornerSeeded x p.toArray = ∑ i : Fin L, p[i.val] * x ^ i.val := by
  rcases p with ⟨p, rfl⟩
  exact evalHornerSeeded_eq_sum x p

/-- The two stored coefficients of the affine function with values `a` at zero and `b` at one. -/
def affine {R : Type*} [Sub R] (a b : R) : Raw R := #[a, b - a]

/-- An affine row always stores both coefficients, including a zero slope. -/
@[simp]
theorem size_affine {R : Type*} [Sub R] (a b : R) : (affine a b).size = 2 := rfl

/-- The two stored coefficients give the formal affine polynomial. -/
theorem toPoly_affine {R : Type*} [Ring R] (a b : R) :
    (affine a b).toPoly = Polynomial.C a + Polynomial.C (b - a) * Polynomial.X := by
  ext i
  rcases i with _ | i
  · simp [coeff_toPoly, affine, coeff]
  · rcases i with _ | i
    · simp [coeff_toPoly, affine, coeff]
    · simp [coeff_toPoly, affine, coeff, Polynomial.coeff_mul_X]

/-- Padded convolution represents formal polynomial multiplication without intermediate trimming. -/
theorem toPoly_mulRaw {R : Type*} [Semiring R] (p q : Raw R) :
    (mulRaw p q).toPoly = p.toPoly * q.toPoly := by
  classical
  have h := toPoly_mul p q
  change (mulRaw p q).trim.toPoly = p.toPoly * q.toPoly at h
  rwa [toPoly_trim] at h

/-- Coefficient-wise left scaling represents left multiplication by a constant polynomial. -/
theorem toPoly_smul {R : Type*} [Semiring R] (r : R) (p : Raw R) :
    (smul r p).toPoly = Polynomial.C r * p.toPoly := by
  ext i
  rw [Polynomial.coeff_C_mul, coeff_toPoly, coeff_toPoly]
  simp only [smul, coeff, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p[i]? <;> simp

/-- Subtract coefficient arrays while retaining padding to the larger input size. -/
def subRaw {R : Type*} [Zero R] [Add R] [Neg R] (p q : Raw R) : Raw R :=
  addRaw p (neg q)

/-- Padded subtraction stores exactly the larger input size. -/
theorem size_subRaw {R : Type*} [Zero R] [Add R] [Neg R] (p q : Raw R) :
    (subRaw p q).size = max p.size q.size := by
  simp [subRaw, addRaw, Array.size_rightpad, max_comm, neg]

/-- Padded subtraction represents formal polynomial subtraction. -/
theorem toPoly_subRaw {R : Type*} [Ring R] (p q : Raw R) :
    (subRaw p q).toPoly = p.toPoly - q.toPoly := by
  classical
  rw [subRaw, toPoly_addRaw]
  have h : (neg q).toPoly = -q.toPoly := toPoly_neg q
  rw [h, sub_eq_add_neg]

end CompPoly.CPolynomial.Raw
