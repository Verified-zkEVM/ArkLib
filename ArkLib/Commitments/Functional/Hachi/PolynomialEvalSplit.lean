/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.Vectors
import CompPoly.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Multilinear Evaluation as a Matrix–Vector Product

The matrix split underlying the Greyhound [NS24] / Hachi [NOZ26] evaluation argument, formalized
over the computable multilinear polynomials `CompPoly.CMlPolynomial` and the lattice-layer
matrix/vector notion (`PolyVec` / `PolyMatrix` with `matVecMul` / `dot`, i.e. `*ᵥ` / `⬝ᵥ`).

As outlined at the beginning of [NOZ26, §4], the evaluation of a multilinear polynomial is split
into a **vector–matrix–vector product**. Concretely, fix a split of the `nl + nh` variables into
`nl` *low* (first) variables and `nh` *high* (last) variables. The `2 ^ (nl + nh)` monomial
coefficients of a polynomial `p` are reshaped into a `2 ^ nl × 2 ^ nh` matrix `M` (`toMatrix`), with
rows indexed by the low (first) variables and columns by the high (last) variables. This matches
Hachi's `b`/`a` split: the outer vector `b` ranges over the first variables (the matrix rows) and
the inner vector `a` over the last variables (the matrix columns). Evaluating `p` at a point that
splits as low part `xl` and high part `xh` then factors as
```
  eval p (xl ++ xh) = mb(xl) ⬝ᵥ (M *ᵥ mb(xh)),
```
where `mb(·)` is the monomial tensor basis (`CMlPolynomial.monomialBasis`). This is `evalSplit`,
proved equal to `eval` by `evalSplit_eq_eval`. The analogous statement for the Lagrange / hypercube
evaluation representation (`CMlPolynomialEval`, with `mb(·)` the multilinear equality kernel
`lagrangeBasis`) is `evalSplitEval_eq_eval`.

The point of phrasing the split with the lattice-layer `matVecMul` / `dot` (rather than ad-hoc
sums) is **composability**: instantiating `R := Rq Φ`, the matrix `toMatrix p : PolyMatrix (Rq Φ) _
_` and the basis vectors `PolyVec (Rq Φ) _` slot directly into the Ajtai commitment
`ArkLib.Lattices.Ajtai.Simple.commit` (which is itself a `matVecMul`) and the inner-outer
construction.

## Index convention

The coefficient/value vectors are indexed **little-endian** (bit `0` is the least significant), as
in `CompPoly.CMlPolynomial`. The split index equivalence `splitEquiv` sends `(x, y)` to
`y + 2 ^ nl * x`: the low `nl` bits (`y`) carry the first `nl` variables (the matrix **row** index)
and the high `nh` bits (`x`) carry the last `nh` variables (the matrix **column** index).

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly

namespace ArkLib.Lattices.Hachi

variable {R : Type*} {nl nh : Nat}

/-! ## The split index equivalence -/

/-- The little-endian split of a `(nl + nh)`-bit index into a high `nh`-bit part `x`
(column index) and a low `nl`-bit part `y` (row index): `(x, y) ↦ y + 2 ^ nl * x`. -/
def splitEquiv (nl nh : Nat) : Fin (2 ^ nh) × Fin (2 ^ nl) ≃ Fin (2 ^ (nl + nh)) :=
  finProdFinEquiv.trans (finCongr (by rw [Nat.mul_comm, ← pow_add]))

@[simp] theorem splitEquiv_val (x : Fin (2 ^ nh)) (y : Fin (2 ^ nl)) :
    (splitEquiv nl nh (x, y)).val = y.val + 2 ^ nl * x.val := rfl

/-! ## The tensor split of a factorized basis vector

Both the monomial basis `CMlPolynomial.monomialBasis` and the Lagrange basis
`CMlPolynomialEval.lagrangeBasis` have the form `i ↦ ∏ⱼ g (bitⱼ i) w[j]` for a per-coordinate
factor `g`. The following lemma is the combinatorial heart of the split: along `splitEquiv`, this
product factors as the product over the low variables times the product over the high variables. -/

/-- Tensor split of a factorized basis vector along `splitEquiv`. -/
private theorem basisProd_split [CommSemiring R] (g : Bool → R → R)
    (xl : Vector R nl) (xh : Vector R nh) (x : Fin (2 ^ nh)) (y : Fin (2 ^ nl)) :
    (∏ j : Fin (nl + nh),
        g ((BitVec.ofFin (splitEquiv nl nh (x, y))).getLsb j) ((xl ++ xh).get j))
      = (∏ j : Fin nl, g ((BitVec.ofFin y).getLsb j) (xl.get j))
        * (∏ k : Fin nh, g ((BitVec.ofFin x).getLsb k) (xh.get k)) := by
  rw [Fin.prod_univ_add]
  congr 1
  · -- low variables: bit `j < nl` of `y + 2 ^ nl * x` is bit `j` of `y`
    apply Finset.prod_congr rfl
    intro j _
    have hbit : (BitVec.ofFin (splitEquiv nl nh (x, y))).getLsb (Fin.castAdd nh j)
        = (BitVec.ofFin y).getLsb j := by
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin,
        Fin.val_castAdd, splitEquiv_val]
      rw [Nat.add_comm y.val (2 ^ nl * x.val), Nat.testBit_two_pow_mul_add x.val y.isLt,
        if_pos j.isLt]
    have hval : (xl ++ xh).get (Fin.castAdd nh j) = xl.get j := by
      simp only [Vector.get_eq_getElem, Fin.val_castAdd]
      rw [Vector.getElem_append_left j.isLt]
    rw [hbit, hval]
  · -- high variables: bit `nl + k` of `y + 2 ^ nl * x` is bit `k` of `x`
    apply Finset.prod_congr rfl
    intro k _
    have hk := k.isLt
    have hbit : (BitVec.ofFin (splitEquiv nl nh (x, y))).getLsb (Fin.natAdd nl k)
        = (BitVec.ofFin x).getLsb k := by
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin,
        Fin.val_natAdd, splitEquiv_val]
      rw [Nat.add_comm y.val (2 ^ nl * x.val), Nat.testBit_two_pow_mul_add x.val y.isLt,
        if_neg (by omega), Nat.add_sub_cancel_left]
    have hval : (xl ++ xh).get (Fin.natAdd nl k) = xh.get k := by
      simp only [Vector.get_eq_getElem, Fin.val_natAdd]
      rw [Vector.getElem_append_right (by omega) (Nat.le_add_right nl k.val)]
      congr 1
      omega
    rw [hbit, hval]

/-! ## Monomial representation -/

section Monomial

variable [CommSemiring R]

open CMlPolynomial

/-- Evaluation as a `Finset.sum` against the monomial basis. -/
theorem eval_eq_sum (p : CMlPolynomial R (nl + nh)) (v : Vector R (nl + nh)) :
    eval p v = ∑ i : Fin (2 ^ (nl + nh)), p.get i * (monomialBasis v).get i := by
  rw [eval, Vector.dotProduct_eq_root_dotProduct]; rfl

/-- `.get`-form of `monomialBasis_getElem`. -/
theorem monomialBasis_get {n : Nat} (w : Vector R n) (i : Fin (2 ^ n)) :
    (monomialBasis w).get i
      = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w.get j else 1 := by
  change (monomialBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1
  exact monomialBasis_getElem i

/-- Reshape the monomial coefficient vector of a multilinear polynomial in `nl + nh` variables into
a `2 ^ nl × 2 ^ nh` matrix: row `i` (low/first variables) and column `j` (high/last variables) hold
the coefficient at the split index `splitEquiv (j, i)`. Rows are the outer/fold index `b` and
columns the inner index `a` of Hachi [NOZ26, §4] eq. (12). -/
def toMatrix (p : CMlPolynomial R (nl + nh)) : PolyMatrix R (2 ^ nl) (2 ^ nh) :=
  fun i j => p.get (splitEquiv nl nh (j, i))

/-- The monomial tensor basis factors along `splitEquiv` into low- and high-variable bases. -/
theorem monomialBasis_split (xl : Vector R nl) (xh : Vector R nh)
    (x : Fin (2 ^ nh)) (y : Fin (2 ^ nl)) :
    (monomialBasis (xl ++ xh)).get (splitEquiv nl nh (x, y))
      = (monomialBasis xl).get y * (monomialBasis xh).get x := by
  rw [monomialBasis_get, monomialBasis_get, monomialBasis_get]
  exact basisProd_split (fun b v => if b then v else 1) xl xh x y

/-- Multilinear evaluation as the split bilinear form `splitForm` (monomial representation): the
outer/`b` basis `mb(xl)` over the first variables, the reshaped coefficient matrix `toMatrix p`,
and the inner/`a` basis `mb(xh)` over the last variables. Phrasing it through `splitForm` keeps the
matrix and the two bases independent, so the gadget-decomposition step (Hachi eq. 15) can move a
matrix factor between them via `splitForm_comp` / `splitForm_transpose`. -/
def evalSplit (p : CMlPolynomial R (nl + nh)) (xl : Vector R nl) (xh : Vector R nh) : R :=
  splitForm (toMatrix p) (monomialBasis xl).get (monomialBasis xh).get

/-- **The split.** Evaluating a multilinear polynomial equals the vector–matrix–vector product of
its reshaped coefficient matrix with the monomial bases of the low and high evaluation points
(Hachi [NOZ26, §4]). -/
theorem evalSplit_eq_eval (p : CMlPolynomial R (nl + nh)) (xl : Vector R nl) (xh : Vector R nh) :
    evalSplit p xl xh = eval p (xl ++ xh) := by
  simp only [evalSplit, splitForm]
  rw [eval_eq_sum,
    ← Equiv.sum_comp (splitEquiv nl nh) (fun i => p.get i * (monomialBasis (xl ++ xh)).get i),
    Fintype.sum_prod_type, dot_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [matVecMul_apply, dot_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [monomialBasis_split]
  change (monomialBasis xl).get y * (toMatrix p y x * (monomialBasis xh).get x)
    = toMatrix p y x * ((monomialBasis xl).get y * (monomialBasis xh).get x)
  ring

/-- Coefficientwise additivity of `CMlPolynomial` (the `+` is `Vector.zipWith (·+·)`). -/
private theorem coeff_add (p q : CMlPolynomial R (nl + nh)) (k : Fin (2 ^ (nl + nh))) :
    (p + q).get k = p.get k + q.get k := by
  change (Vector.zipWith (· + ·) p q).get k = p.get k + q.get k
  simp only [Vector.get_eq_getElem, Vector.getElem_zipWith]

/-- Coefficientwise scalar multiplication of `CMlPolynomial` (the `•` is `Vector.map (r * ·)`). -/
private theorem coeff_smul (r : R) (p : CMlPolynomial R (nl + nh)) (k : Fin (2 ^ (nl + nh))) :
    (r • p).get k = r * p.get k := by
  change (Vector.map (fun a => r * a) p).get k = r * p.get k
  simp only [Vector.get_eq_getElem, Vector.getElem_map]

/-- The reshape `toMatrix` is additive in the coefficient vector. -/
theorem toMatrix_add (p q : CMlPolynomial R (nl + nh)) :
    toMatrix (p + q) = toMatrix p + toMatrix q := by
  funext i j; simp only [toMatrix, Matrix.add_apply]; exact coeff_add p q _

/-- The reshape `toMatrix` pulls out a scalar from the coefficient vector. -/
theorem toMatrix_smul (r : R) (p : CMlPolynomial R (nl + nh)) :
    toMatrix (r • p) = r • toMatrix p := by
  funext i j; simp only [toMatrix, Matrix.smul_apply, smul_eq_mul]; exact coeff_smul r p _

/-- **Coefficient `R`-linearity (additive).** A corollary of `splitForm_matrix_add` and
`toMatrix_add`: useful for the random-linear-combination/batching steps. -/
theorem evalSplit_add (p q : CMlPolynomial R (nl + nh)) (xl : Vector R nl) (xh : Vector R nh) :
    evalSplit (p + q) xl xh = evalSplit p xl xh + evalSplit q xl xh := by
  simp only [evalSplit, toMatrix_add, splitForm_matrix_add]

/-- **Coefficient `R`-linearity (scalar).** A corollary of `splitForm_matrix_smul` and
`toMatrix_smul`. -/
theorem evalSplit_smul (r : R) (p : CMlPolynomial R (nl + nh)) (xl : Vector R nl)
    (xh : Vector R nh) : evalSplit (r • p) xl xh = r * evalSplit p xl xh := by
  simp only [evalSplit, toMatrix_smul, splitForm_matrix_smul]

end Monomial

/-! ## Lagrange / hypercube-evaluation representation -/

section Lagrange

variable [CommRing R]

open CMlPolynomialEval

/-- Evaluation as a `Finset.sum` against the Lagrange basis. -/
theorem evalEval_eq_sum (p : CMlPolynomialEval R (nl + nh)) (v : Vector R (nl + nh)) :
    eval p v = ∑ i : Fin (2 ^ (nl + nh)), p.get i * (lagrangeBasis v).get i := by
  rw [eval, Vector.dotProduct_eq_root_dotProduct]; rfl

/-- `.get`-form of `lagrangeBasis_getElem`. -/
theorem lagrangeBasis_get {n : Nat} (w : Vector R n) (i : Fin (2 ^ n)) :
    (lagrangeBasis w).get i
      = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w.get j else 1 - w.get j := by
  change (lagrangeBasis w)[i] = ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j]
  exact lagrangeBasis_getElem i

/-- Reshape the hypercube-evaluation vector of a multilinear polynomial in `nl + nh` variables into
a `2 ^ nl × 2 ^ nh` matrix: row `i` (low/first variables) and column `j` (high/last variables) hold
the value at the split index `splitEquiv (j, i)`. -/
def toMatrixEval (p : CMlPolynomialEval R (nl + nh)) : PolyMatrix R (2 ^ nl) (2 ^ nh) :=
  fun i j => p.get (splitEquiv nl nh (j, i))

/-- The Lagrange tensor basis factors along `splitEquiv` into low- and high-variable bases. -/
theorem lagrangeBasis_split (xl : Vector R nl) (xh : Vector R nh)
    (x : Fin (2 ^ nh)) (y : Fin (2 ^ nl)) :
    (lagrangeBasis (xl ++ xh)).get (splitEquiv nl nh (x, y))
      = (lagrangeBasis xl).get y * (lagrangeBasis xh).get x := by
  rw [lagrangeBasis_get, lagrangeBasis_get, lagrangeBasis_get]
  exact basisProd_split (fun b v => if b then v else 1 - v) xl xh x y

/-- Multilinear evaluation as the split bilinear form `splitForm` (Lagrange / evaluation
representation): the outer basis `lagrangeBasis xl` over the first variables, the reshaped value
matrix `toMatrixEval p`, and the inner basis `lagrangeBasis xh` over the last variables. -/
def evalSplitEval (p : CMlPolynomialEval R (nl + nh))
    (xl : Vector R nl) (xh : Vector R nh) : R :=
  splitForm (toMatrixEval p) (lagrangeBasis xl).get (lagrangeBasis xh).get

/-- **The split (Lagrange representation).** Evaluating a multilinear polynomial given by its
hypercube values equals the vector–matrix–vector product of its reshaped value matrix with the
Lagrange bases of the low and high evaluation points. -/
theorem evalSplitEval_eq_eval (p : CMlPolynomialEval R (nl + nh))
    (xl : Vector R nl) (xh : Vector R nh) :
    evalSplitEval p xl xh = eval p (xl ++ xh) := by
  simp only [evalSplitEval, splitForm]
  rw [evalEval_eq_sum,
    ← Equiv.sum_comp (splitEquiv nl nh) (fun i => p.get i * (lagrangeBasis (xl ++ xh)).get i),
    Fintype.sum_prod_type, dot_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [matVecMul_apply, dot_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [lagrangeBasis_split]
  change (lagrangeBasis xl).get y * (toMatrixEval p y x * (lagrangeBasis xh).get x)
    = toMatrixEval p y x * ((lagrangeBasis xl).get y * (lagrangeBasis xh).get x)
  ring

end Lagrange

end ArkLib.Lattices.Hachi
