/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Recovering a family from invertible linear combinations

Let `A` be a square matrix over a commutative ring `R` with invertible determinant, `M` an
`R`-module, `p` a submodule of `M` and `x : ι → M` a finite family. If every combination
`∑ j, A i j • x j` lies in `p`, then so does every `x j`, because `x j` is the combination of
these elements with the coefficients of the row `j` of `A⁻¹`.

The Vandermonde case is the interpolation step for polynomials: if the values
`∑ j, α i ^ j • x j` of a polynomial with coefficients `x j` at `c` distinct points `α i` of a
field lie in `p`, then so do its coefficients. Applied to a subalgebra, it shows that an algebra
containing the values of a polynomial of degree less than `c` at `c` distinct points contains its
coefficients.

## Main statements

* `Submodule.mem_of_forall_sum_smul_mem`: the recovery for an invertible matrix.
* `Submodule.mem_of_forall_sum_pow_smul_mem`: the recovery for a Vandermonde matrix at distinct
  points of a field.
-/

@[expose] public section

namespace Submodule

variable {R M ι : Type*} [CommRing R] [AddCommMonoid M] [Module R M] [Fintype ι]
  [DecidableEq ι]

/-- If `A` has invertible determinant and every combination `∑ j, A i j • x j` lies in a
submodule `p`, then every `x j` lies in `p`. -/
theorem mem_of_forall_sum_smul_mem {p : Submodule R M} (A : Matrix ι ι R) (hA : IsUnit A.det)
    {x : ι → M} (hx : ∀ i, ∑ j, A i j • x j ∈ p) (j : ι) : x j ∈ p := by
  have hrecover : x j = ∑ i, A⁻¹ j i • ∑ l, A i l • x l := by
    have hinv := congrFun (congrFun (Matrix.nonsing_inv_mul A hA) j)
    simp only [Matrix.mul_apply] at hinv
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hrecover]
  exact p.sum_mem fun i _ ↦ p.smul_mem _ (hx i)

/-- Interpolation in a module: if the values `∑ j, α i ^ j • x j` at `c` distinct points `α i` of
a field lie in a submodule `p`, then every coefficient `x j` lies in `p`. -/
theorem mem_of_forall_sum_pow_smul_mem {K : Type*} [Field K] [Module K M] {p : Submodule K M}
    {c : ℕ} {α : Fin c → K} (hα : Function.Injective α) {x : Fin c → M}
    (hx : ∀ i, ∑ j : Fin c, α i ^ (j : ℕ) • x j ∈ p) (j : Fin c) : x j ∈ p :=
  mem_of_forall_sum_smul_mem (Matrix.vandermonde α)
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hα))
    (fun i ↦ by simpa only [Matrix.vandermonde_apply] using hx i) j

end Submodule
