/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Fin

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

/-- Left scalar multiplication of a vector by a ring element. -/
def scalarVecMul {cols : Nat} (c : P) (v : PolyVec P cols) : PolyVec P cols :=
  fun i => c * v i

@[inherit_doc matVecMul] scoped infixr:73 " *ᵥ " => matVecMul
@[inherit_doc dot] scoped infixl:72 " ⬝ᵥ " => dot

@[simp] theorem matVecMul_apply {rows cols : Nat} (A : PolyMatrix P rows cols)
    (v : PolyVec P cols) (i : Fin rows) : (A *ᵥ v) i = (A i) ⬝ᵥ v := rfl

omit [Add P] [Zero P] in
@[simp] theorem scalarVecMul_apply {cols : Nat} (c : P) (v : PolyVec P cols) (i : Fin cols) :
    scalarVecMul c v i = c * v i := rfl

end Defs

section Algebra

variable {P : Type u} [CommRing P]

/-- `dot` as a `Finset.sum` of coordinatewise products. -/
theorem dot_eq_sum {k : ℕ} (u v : PolyVec P k) : u ⬝ᵥ v = ∑ i : Fin k, u i * v i := by
  rw [dot, List.sum_ofFn]

/-- `dot` distributes over subtraction in the second argument. -/
theorem dot_sub {k : ℕ} (u v w : PolyVec P k) : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by
  simp only [dot_eq_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, mul_sub]

/-- `dot` pulls out a left scalar from the second argument. -/
theorem dot_scalarVecMul {k : ℕ} (c : P) (u v : PolyVec P k) :
    u ⬝ᵥ scalarVecMul c v = c * (u ⬝ᵥ v) := by
  simp only [dot_eq_sum, Finset.mul_sum, scalarVecMul_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_left_comm _ _ _)

/-- Matrix–vector multiplication preserves subtraction. -/
theorem matVecMul_sub {rows cols : ℕ} (A : PolyMatrix P rows cols) (v w : PolyVec P cols) :
    A *ᵥ (v - w) = A *ᵥ v - A *ᵥ w := by
  funext i; simp only [matVecMul_apply, Pi.sub_apply, dot_sub]

/-- Matrix–vector multiplication commutes with left scalar multiplication. -/
theorem matVecMul_scalarVecMul {rows cols : ℕ} (A : PolyMatrix P rows cols) (c : P)
    (v : PolyVec P cols) : A *ᵥ scalarVecMul c v = scalarVecMul c (A *ᵥ v) := by
  funext i; simp only [matVecMul_apply, scalarVecMul_apply, dot_scalarVecMul]

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
    scalarVecMul (c * d) v ≠ scalarVecMul (d * c) w := by
  intro h; apply hvw
  rw [mul_comm d c] at h
  exact scalarVecMul_injective_of_isUnit (hc.mul hd) h

/-- Equality of matrix products is preserved by scaling with a product of two scalars. -/
theorem matVecMul_scalarVecMul_mul_eq_of_eq {rows cols : ℕ} (A : PolyMatrix P rows cols)
    (c d : P) {v w : PolyVec P cols} (h : A *ᵥ v = A *ᵥ w) :
    A *ᵥ scalarVecMul (c * d) v = A *ᵥ scalarVecMul (d * c) w := by
  rw [matVecMul_scalarVecMul A (c * d) v, matVecMul_scalarVecMul A (d * c) w, mul_comm d c, h]

end Algebra

end ArkLib.Lattices
