/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Vectors And Matrices For The Lattice Layer

The lattice commitment layer uses **Mathlib function-vectors** `Fin k → P` and
`Matrix (Fin rows) (Fin cols) P` as containers, instantiated at the cyclotomic ring
`CyclotomicModulus.Rq Φ`. Using the canonical `Pi`/`Matrix` instance set avoids the
`Vector`-instance clash between Lean-core and `VCVio`, so the `0`/`-`/`+` used in the
Module-SIS relation are unambiguous.

To keep commitments **computable**, `dot`/`matVecMul`/`scalarVecMul` are defined over the
bare `Mul`/`Add`/`Zero` instances (via `List.sum ∘ List.ofFn`) rather than Mathlib's
`Matrix.mulVec` — the latter would route the ring product through the *noncomputable*
`Rq.commRing` instance. The linearity lemmas are proved over a `CommRing` carrier and
relate `dot` to `Finset.sum`.

## Main definitions

* `PolyVec` / `PolyMatrix` — `Fin`-indexed function-vector / matrix.
* `dot` / `matVecMul` / `scalarVecMul` — computable `⟨u,v⟩`, `M *ᵥ v`, `c • v`.
* `PolyVec.flattenBlocks` — flatten `blocks` equal-width blocks into one vector.
-/

open scoped BigOperators

universe u

namespace ArkLib.Lattices

/-- A length-`k` vector over `P`, as a Mathlib function-vector. -/
abbrev PolyVec (P : Type u) (k : Nat) := Fin k → P

/-- A `rows × cols` matrix over `P`, as a Mathlib `Matrix`. -/
abbrev PolyMatrix (P : Type u) (rows cols : Nat) := Matrix (Fin rows) (Fin cols) P

namespace PolyVec

variable {P : Type u}

/-- Flatten `blocks` equal-width blocks into one row-major vector. -/
def flattenBlocks {blocks width : Nat} (xs : PolyVec (PolyVec P width) blocks) :
    PolyVec P (blocks * width) :=
  fun j => xs (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

@[simp] theorem flattenBlocks_apply {blocks width : Nat}
    (xs : PolyVec (PolyVec P width) blocks) (i : Fin blocks) (j : Fin width) :
    flattenBlocks xs (finProdFinEquiv (i, j)) = xs i j := by
  simp [flattenBlocks]

/-- Equal flattenings agree blockwise. -/
theorem block_eq_of_flattenBlocks_eq {blocks width : Nat}
    {xs ys : PolyVec (PolyVec P width) blocks}
    (h : flattenBlocks xs = flattenBlocks ys) (i : Fin blocks) :
    xs i = ys i := by
  funext j
  have := congrArg (fun v => v (finProdFinEquiv (i, j))) h
  simpa using this

end PolyVec

/-! ## Computable vector / matrix arithmetic -/

section Defs

variable {P : Type u} [Mul P] [Add P] [Zero P]

/-- Dot product `Σᵢ uᵢ · vᵢ`, computed by `List.sum` over the coordinatewise products
(so it stays computable on `Rq Φ`, whose `CommRing` instance is noncomputable). -/
def dot {k : Nat} (u v : PolyVec P k) : P :=
  (List.ofFn fun i : Fin k => u i * v i).sum

/-- Matrix–vector product: each output entry is the dot product of a row with `v`. -/
def matVecMul {rows cols : Nat} (A : PolyMatrix P rows cols) (v : PolyVec P cols) :
    PolyVec P rows :=
  fun i => dot (A i) v

/-- Matrix–matrix product, computed via `dot` (so it stays computable on `Rq Φ`, like `matVecMul`,
rather than routing through Mathlib's noncomputable `Matrix.mul`). -/
def matMul {a b c : Nat} (M : PolyMatrix P a b) (N : PolyMatrix P b c) : PolyMatrix P a c :=
  fun i k => dot (M i) (fun j => N j k)

/-- Left scalar multiplication of a vector by a ring element. -/
def scalarVecMul {cols : Nat} (c : P) (v : PolyVec P cols) : PolyVec P cols :=
  fun i => c * v i

@[inherit_doc matVecMul] scoped infixr:73 " *ᵥ " => matVecMul
@[inherit_doc dot] scoped infixl:72 " ⬝ᵥ " => dot
@[inherit_doc scalarVecMul] scoped infixr:73 " •ᵥ " => scalarVecMul

@[simp] theorem matVecMul_apply {rows cols : Nat} (A : PolyMatrix P rows cols)
    (v : PolyVec P cols) (i : Fin rows) : (A *ᵥ v) i = (A i) ⬝ᵥ v := rfl

omit [Add P] [Zero P] in
@[simp] theorem scalarVecMul_apply {cols : Nat} (c : P) (v : PolyVec P cols) (i : Fin cols) :
    (c •ᵥ v) i = c * v i := rfl

end Defs

section Algebra

variable {P : Type u} [CommSemiring P]

/-- `dot` as a `Finset.sum` of coordinatewise products. -/
theorem dot_eq_sum {k : ℕ} (u v : PolyVec P k) : u ⬝ᵥ v = ∑ i : Fin k, u i * v i := by
  rw [dot, List.sum_ofFn]

/-- `dot` is symmetric. -/
theorem dot_comm {k : ℕ} (u v : PolyVec P k) : u ⬝ᵥ v = v ⬝ᵥ u := by
  simp only [dot_eq_sum]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- `dot` distributes over addition in the first argument. -/
theorem dot_add_left {k : ℕ} (u v w : PolyVec P k) : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp only [dot_eq_sum, ← Finset.sum_add_distrib, Pi.add_apply, add_mul]

/-- `dot` distributes over addition in the second argument. -/
theorem dot_add_right {k : ℕ} (u v w : PolyVec P k) : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp only [dot_eq_sum, ← Finset.sum_add_distrib, Pi.add_apply, mul_add]

/-- `dot` pulls out a left scalar from the second argument. -/
theorem dot_scalarVecMul {k : ℕ} (c : P) (u v : PolyVec P k) :
    u ⬝ᵥ (c •ᵥ v) = c * (u ⬝ᵥ v) := by
  simp only [dot_eq_sum, Finset.mul_sum, scalarVecMul_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_left_comm _ _ _)

/-- Matrix–vector multiplication distributes over addition of vectors. -/
theorem matVecMul_add {rows cols : ℕ} (A : PolyMatrix P rows cols) (v w : PolyVec P cols) :
    A *ᵥ (v + w) = A *ᵥ v + A *ᵥ w := by
  funext i; simp only [matVecMul_apply, Pi.add_apply, dot_add_right]

/-- Matrix–vector multiplication distributes over addition of matrices. -/
theorem matVecMul_matrix_add {rows cols : ℕ} (A B : PolyMatrix P rows cols) (v : PolyVec P cols) :
    (A + B) *ᵥ v = A *ᵥ v + B *ᵥ v := by
  funext i
  simp only [matVecMul_apply, Pi.add_apply, dot_eq_sum, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]

/-- Matrix–vector multiplication pulls out a scalar from the matrix. -/
theorem matVecMul_matrix_smul {rows cols : ℕ} (c : P) (A : PolyMatrix P rows cols)
    (v : PolyVec P cols) : (c • A) *ᵥ v = scalarVecMul c (A *ᵥ v) := by
  funext i
  simp only [matVecMul_apply, scalarVecMul_apply, dot_eq_sum, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- Matrix–vector multiplication commutes with left scalar multiplication. -/
theorem matVecMul_scalarVecMul {rows cols : ℕ} (A : PolyMatrix P rows cols) (c : P)
    (v : PolyVec P cols) : A *ᵥ (c •ᵥ v) = c •ᵥ (A *ᵥ v) := by
  funext i; simp only [matVecMul_apply, scalarVecMul_apply, dot_scalarVecMul]

/-- `matMul` entrywise: `(matMul M N) i k = ∑ⱼ Mᵢⱼ Nⱼₖ`. -/
theorem matMul_apply {a b c : ℕ} (M : PolyMatrix P a b) (N : PolyMatrix P b c)
    (i : Fin a) (k : Fin c) : matMul M N i k = ∑ j : Fin b, M i j * N j k := by
  simp only [matMul, dot_eq_sum]

/-- Associativity of matrix–vector multiplication with the matrix product: applying `matMul M N`
to `v` is applying `M` to `N *ᵥ v`. This is the algebraic core of folding a gadget matrix into the
witness (Hachi [NOZ26] eq. 15). -/
theorem matVecMul_matMul {a b c : ℕ} (M : PolyMatrix P a b) (N : PolyMatrix P b c)
    (v : PolyVec P c) : matMul M N *ᵥ v = M *ᵥ (N *ᵥ v) := by
  funext i
  simp only [matVecMul_apply, matMul_apply, dot_eq_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-! ### The split bilinear form -/

/-- The **split bilinear form** `⟨u, M *ᵥ v⟩` (`uᵀ M v`) underlying the Greyhound/Hachi evaluation
equation. Keeping the matrix `M` and the two basis vectors `u`, `v` as independent arguments lets a
gadget/decomposition matrix be moved between `M` and the basis side (`splitForm_comp`,
`splitForm_transpose`), which is how a raw-coefficient evaluation claim is reduced to one over the
decomposed witness (Hachi [NOZ26] eq. 12 → eq. 15). -/
def splitForm {a b : ℕ} (M : PolyMatrix P a b) (u : PolyVec P a) (v : PolyVec P b) : P :=
  u ⬝ᵥ (M *ᵥ v)

/-- `splitForm` is additive in the inner (right) basis vector. -/
theorem splitForm_add_right {a b : ℕ} (M : PolyMatrix P a b) (u : PolyVec P a)
    (v w : PolyVec P b) : splitForm M u (v + w) = splitForm M u v + splitForm M u w := by
  simp only [splitForm, matVecMul_add, dot_add_right]

/-- `splitForm` pulls a scalar out of the inner (right) basis vector. -/
theorem splitForm_smul_right {a b : ℕ} (M : PolyMatrix P a b) (u : PolyVec P a) (c : P)
    (v : PolyVec P b) : splitForm M u (scalarVecMul c v) = c * splitForm M u v := by
  simp only [splitForm, matVecMul_scalarVecMul, dot_scalarVecMul]

/-- `splitForm` is additive in the outer (left) basis vector. -/
theorem splitForm_add_left {a b : ℕ} (M : PolyMatrix P a b) (u u' : PolyVec P a)
    (v : PolyVec P b) : splitForm M (u + u') v = splitForm M u v + splitForm M u' v := by
  simp only [splitForm, dot_add_left]

/-- `splitForm` pulls a scalar out of the outer (left) basis vector. -/
theorem splitForm_smul_left {a b : ℕ} (M : PolyMatrix P a b) (c : P) (u : PolyVec P a)
    (v : PolyVec P b) : splitForm M (scalarVecMul c u) v = c * splitForm M u v := by
  simp only [splitForm]
  rw [dot_comm (scalarVecMul c u), dot_scalarVecMul, dot_comm]

/-- `splitForm` is additive in the matrix. -/
theorem splitForm_matrix_add {a b : ℕ} (M N : PolyMatrix P a b) (u : PolyVec P a)
    (v : PolyVec P b) : splitForm (M + N) u v = splitForm M u v + splitForm N u v := by
  simp only [splitForm, matVecMul_matrix_add, dot_add_right]

/-- `splitForm` pulls a scalar out of the matrix. -/
theorem splitForm_matrix_smul {a b : ℕ} (c : P) (M : PolyMatrix P a b) (u : PolyVec P a)
    (v : PolyVec P b) : splitForm (c • M) u v = c * splitForm M u v := by
  simp only [splitForm, matVecMul_matrix_smul, dot_scalarVecMul]

/-- **Transpose adjunction.** Moving the matrix across the form swaps the two basis vectors and
transposes `M`: `uᵀ M v = vᵀ Mᵀ u`. This is what pushes a gadget factor from the witness side onto
the (public) basis side. -/
theorem splitForm_transpose {a b : ℕ} (M : PolyMatrix P a b) (u : PolyVec P a) (v : PolyVec P b) :
    splitForm M u v = splitForm M.transpose v u := by
  simp only [splitForm, dot_eq_sum, matVecMul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

/-- **Gadget composition.** A matrix factor on the inner basis side is absorbed into the form's
matrix: `splitForm (matMul M N) u v = splitForm M u (N *ᵥ v)`. With `splitForm_transpose` this is
exactly the move that folds the gadget matrix `G` of Hachi eq. (15) between witness and basis. -/
theorem splitForm_comp {a b c : ℕ} (M : PolyMatrix P a b) (N : PolyMatrix P b c)
    (u : PolyVec P a) (v : PolyVec P c) : splitForm (matMul M N) u v = splitForm M u (N *ᵥ v) := by
  simp only [splitForm, matVecMul_matMul]

end Algebra

section AlgebraRing

variable {P : Type u} [CommRing P]

/-- `dot` distributes over subtraction in the second argument. -/
theorem dot_sub {k : ℕ} (u v w : PolyVec P k) : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by
  simp only [dot_eq_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, mul_sub]

/-- Matrix–vector multiplication preserves subtraction. -/
theorem matVecMul_sub {rows cols : ℕ} (A : PolyMatrix P rows cols) (v w : PolyVec P cols) :
    A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w := by
  funext i; simp only [matVecMul_apply, Pi.sub_apply, dot_sub]

/-- Left scalar multiplication by a unit is injective. -/
theorem scalarVecMul_injective_of_isUnit {cols : ℕ} {c : P} (hc : IsUnit c) :
    Function.Injective (scalarVecMul (cols := cols) c) := by
  intro v w h
  funext i
  have : scalarVecMul c v i = scalarVecMul c w i := by rw [h]
  simp only [scalarVecMul_apply] at this
  exact hc.mul_right_injective this

/-- Scaling by a product of two units preserves vector inequality. -/
theorem scalarVecMul_mul_ne_of_ne {cols : ℕ} {c d : P} {v w : PolyVec P cols}
    (hc : IsUnit c) (hd : IsUnit d) (hvw : v ≠ w) :
    (c * d) •ᵥ v ≠ (d * c) •ᵥ w := by
  intro h; apply hvw
  rw [mul_comm d c] at h
  exact scalarVecMul_injective_of_isUnit (hc.mul hd) h

/-- Equality of matrix products is preserved by scaling with a product of two scalars. -/
theorem matVecMul_scalarVecMul_mul_eq_of_eq {rows cols : ℕ} (A : PolyMatrix P rows cols)
    (c d : P) {v w : PolyVec P cols} (h : A *ᵥ v = A *ᵥ w) :
    A *ᵥ ((c * d) •ᵥ v) = A *ᵥ ((d * c) •ᵥ w) := by
  rw [matVecMul_scalarVecMul A (c * d) v, matVecMul_scalarVecMul A (d * c) w, mul_comm d c, h]

end AlgebraRing

end ArkLib.Lattices
