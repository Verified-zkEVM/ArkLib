/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Data.MvPolynomial.Multilinear
import CompPoly.Multilinear.Basic
import CompPoly.Multivariate.Operations

/-!
  # Computable multilinear extensions over `CMvPolynomial`

  Additions to `CompPoly.Multivariate` not yet upstreamed to CompPoly.

  `ArkLib/Data/MvPolynomial/Multilinear.lean` builds the multilinear extension `MvPolynomial.MLE`
  of a hypercube evaluation table on top of Mathlib's `MvPolynomial`, which is noncomputable:
  its carrier is a `Finsupp`, so nothing about it reduces. This file mirrors that construction on
  CompPoly's computable `CMvPolynomial` — a tree-map of monomials — and establishes that the two
  agree under the `fromCMvPolynomial` bridge.

  ## Main definitions

  * `CMvPolynomial.singleEqPolynomial`, `CMvPolynomial.eqPolynomial` — the computable `eq̃` factors
    and their product.
  * `CMvPolynomial.MLE` — the computable multilinear extension of a table
    `(Fin n → Fin 2) → R`.
  * `CMlPolynomialEval.eval_eq_MvPolynomial_MLE` — direct value-vector evaluation agrees with
    Mathlib's multilinear extension.

  ## The correspondence

  `fromCMvPolynomial_MLE` is the load-bearing theorem: `fromCMvPolynomial (MLE evals)` is
  *definitionally the same polynomial* as `MvPolynomial.MLE evals`. Every property of the
  computable side is then obtained by transporting the Mathlib-side proof rather than reproving
  it — `MLE_eval_zeroOne`, `MLE_degreeOf`, `MLE_eq_zero_iff`, and membership in the multilinear
  submodule `MvPolynomial.restrictDegree`.

  This is the pattern the Hachi zero-check uses (`ZeroCheck/Constraints.lean`): the constraint
  polynomials `H₀`/`H_α` are *defined* computably and their Mathlib images are what the soundness
  argument reasons about.
-/

namespace CPoly

namespace CMvPolynomial

open CPoly BigOperators

variable {n : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-! ## `fromCMvPolynomial` commutes with big operators

`fromCMvPolynomial` is the forward direction of the ring equivalence `CPoly.polyRingEquiv`, so
Mathlib's `map_sum`/`map_prod` apply to it once it is seen through that bundling. -/

theorem fromCMvPolynomial_sum {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    fromCMvPolynomial (∑ i ∈ s, f i) = ∑ i ∈ s, fromCMvPolynomial (f i) :=
  map_sum (polyRingEquiv (n := n) (R := R)) f s

theorem fromCMvPolynomial_prod {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    fromCMvPolynomial (∏ i ∈ s, f i) = ∏ i ∈ s, fromCMvPolynomial (f i) :=
  map_prod (polyRingEquiv (n := n) (R := R)) f s

/-- `CPoly.map_sub` restated with an `HSub.hSub` head.

CompPoly states it as `fromCMvPolynomial (Sub.sub a b) = …`, whose head symbol is `Sub.sub`
rather than the `HSub.hSub` that `a - b` elaborates to, so `rw`'s keyed matching never fires on
it. The two sides are reducibly defeq (`Lawful.sub p₁ p₂ = p₁ + (-p₂)`), so restating is enough. -/
theorem fromCMvPolynomial_sub (a b : CMvPolynomial n R) :
    fromCMvPolynomial (a - b) = fromCMvPolynomial a - fromCMvPolynomial b :=
  CPoly.map_sub a b

/-! ## The computable `eq̃` polynomial -/

/-- The computable per-variable equality factor `(1 - r)·(1 - x) + r·x`, mirroring
`MvPolynomial.singleEqPolynomial`. -/
def singleEqPolynomial (r : R) (x : CMvPolynomial n R) : CMvPolynomial n R :=
  (1 - C r) * (1 - x) + C r * x

/-- The computable equality polynomial `eq̃(r, ·) = ∏ᵢ ((1 - rᵢ)(1 - Xᵢ) + rᵢ·Xᵢ)`, mirroring
`MvPolynomial.eqPolynomial`. -/
def eqPolynomial (r : Fin n → R) : CMvPolynomial n R :=
  ∏ i : Fin n, singleEqPolynomial (r i) (X i)

/-- The computable multilinear extension of a hypercube evaluation table, mirroring
`MvPolynomial.MLE`: `MLE evals = ∑_{x ∈ {0,1}ⁿ} eq̃(x, ·)·evals(x)`. -/
def MLE (evals : (Fin n → Fin 2) → R) : CMvPolynomial n R :=
  ∑ x : Fin n → Fin 2, eqPolynomial (x : Fin n → R) * C (evals x)

/-! ## Correspondence with `MvPolynomial.MLE` -/

@[simp]
theorem fromCMvPolynomial_singleEqPolynomial (r : R) (x : CMvPolynomial n R) :
    fromCMvPolynomial (singleEqPolynomial r x)
      = MvPolynomial.singleEqPolynomial r (fromCMvPolynomial x) := by
  unfold singleEqPolynomial MvPolynomial.singleEqPolynomial
  rw [CPoly.map_add, CPoly.map_mul, CPoly.map_mul, fromCMvPolynomial_sub, fromCMvPolynomial_sub,
    CPoly.map_one, fromCMvPolynomial_C]

@[simp]
theorem fromCMvPolynomial_eqPolynomial (r : Fin n → R) :
    fromCMvPolynomial (eqPolynomial r) = MvPolynomial.eqPolynomial r := by
  unfold eqPolynomial MvPolynomial.eqPolynomial
  rw [fromCMvPolynomial_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [fromCMvPolynomial_singleEqPolynomial, fromCMvPolynomial_X]

/-- **The bridge.** The computable multilinear extension maps onto Mathlib's under
`fromCMvPolynomial`. Every downstream fact about `CMvPolynomial.MLE` is transported along this
equation. -/
@[simp]
theorem fromCMvPolynomial_MLE (evals : (Fin n → Fin 2) → R) :
    fromCMvPolynomial (MLE evals) = MvPolynomial.MLE evals := by
  unfold MLE MvPolynomial.MLE
  rw [fromCMvPolynomial_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [CPoly.map_mul, fromCMvPolynomial_eqPolynomial, fromCMvPolynomial_C]

/-! ## Transported properties -/

/-- The computable MLE reproduces the table at every Boolean point. -/
@[simp]
theorem MLE_eval_zeroOne (x : Fin n → Fin 2) (evals : (Fin n → Fin 2) → R) :
    (MLE evals).eval (x : Fin n → R) = evals x := by
  rw [eval_equiv, fromCMvPolynomial_MLE]
  exact MvPolynomial.MLE_eval_zeroOne x evals

/-- The computable MLE is multilinear: degree at most `1` in every variable. -/
theorem MLE_degreeOf (evals : (Fin n → Fin 2) → R) (i : Fin n) :
    (MLE evals).degreeOf i ≤ 1 := by
  rw [congrFun (degreeOf_equiv (S := R) (p := MLE evals)) i, fromCMvPolynomial_MLE]
  exact MvPolynomial.MLE_degreeOf evals i

/-- The Mathlib image of a computable MLE lies in the multilinear submodule
`MvPolynomial.restrictDegree _ _ 1`, the form the Hachi zero-check's root-counting argument
consumes. -/
theorem fromCMvPolynomial_MLE_mem_restrictDegree (evals : (Fin n → Fin 2) → R) :
    fromCMvPolynomial (MLE evals) ∈ MvPolynomial.restrictDegree (Fin n) R 1 := by
  rw [fromCMvPolynomial_MLE]
  exact MvPolynomial.MLE_mem_restrictDegree evals

/-- Nondegeneracy: a computable MLE is the zero polynomial iff its table vanishes identically.
The computable counterpart of `MvPolynomial.MLE_eq_zero_iff`. -/
theorem MLE_eq_zero_iff (evals : (Fin n → Fin 2) → R) :
    MLE evals = 0 ↔ ∀ x, evals x = 0 := by
  rw [eq_iff_fromCMvPolynomial, fromCMvPolynomial_MLE, CPoly.map_zero]
  exact MvPolynomial.MLE_eq_zero_iff evals

end CMvPolynomial

end CPoly

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
