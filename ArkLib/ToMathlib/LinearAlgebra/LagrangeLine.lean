/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.SparseContraction
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange interpolation along a line and under field homomorphisms

Let `s` be a finite set of nodes `v i` over a field `F`, injective on `s`, and let `φ : F →+* E`
be a homomorphism into another field. Lagrange interpolation commutes with `φ`: mapping the
interpolant of the values `r` gives the interpolant of `φ ∘ r` at the nodes `φ ∘ v`. Since
interpolation is linear in the values, a polynomial `P` over `E` of degree below `#s` whose
values at the nodes `φ (v i)` are `φ (r i) + y * φ (r' i)` is the combination
`(interpolate s v r).map φ + C y * (interpolate s v r').map φ` of two polynomials over `F` that do
not depend on `E`, `φ`, `y` or `P`.

The same conclusion holds for a polynomial of degree below `p ^ e * #s` that is a Frobenius
pullback: if the Taylor coefficients of `P` at some center vanish outside the multiples of
`p ^ e` in exponential characteristic `p`, and `P` takes the values above at `p ^ e`-th roots of
the nodes, then `P` is `expand E (p ^ e)` of that combination. Only `#s` nodes are used, although
`P` can have degree up to `p ^ e * #s - 1`.

## Main statements

* `Lagrange.map_basisDivisor`, `Lagrange.map_basis`, `Lagrange.map_interpolate`: interpolation
  commutes with field homomorphisms. No injectivity of `v` is needed.
* `Lagrange.eq_map_interpolate_add_C_mul_of_eval_eq`: recognition of a polynomial on the line
  spanned by two interpolants.
* `Lagrange.eq_expand_map_interpolate_add_C_mul_of_eval_eq`: the same recognition for a
  Frobenius pullback with sparse Taylor coefficients.
-/

@[expose] public section

open Polynomial Finset

namespace Lagrange

variable {F E ι : Type*} [Field F] [Field E]

/-- `basisDivisor` commutes with field homomorphisms. -/
theorem map_basisDivisor (φ : F →+* E) (x y : F) :
    (basisDivisor x y).map φ = basisDivisor (φ x) (φ y) := by
  simp [basisDivisor, Polynomial.map_mul, map_inv₀, map_sub]

variable [DecidableEq ι]

/-- Lagrange basis polynomials commute with field homomorphisms. No injectivity of `v` on `s`
is needed: both sides are the same product of basis divisors. -/
theorem map_basis (φ : F →+* E) (s : Finset ι) (v : ι → F) (i : ι) :
    (Lagrange.basis s v i).map φ = Lagrange.basis s (φ ∘ v) i := by
  simp [Lagrange.basis, Polynomial.map_prod, map_basisDivisor]

/-- Lagrange interpolation commutes with field homomorphisms: mapping the interpolant of `r` at
the nodes `v` gives the interpolant of `φ ∘ r` at the nodes `φ ∘ v`. No injectivity of `v` on
`s` is needed. -/
theorem map_interpolate (φ : F →+* E) (s : Finset ι) (v r : ι → F) :
    (interpolate s v r).map φ = interpolate s (φ ∘ v) (φ ∘ r) := by
  simp [interpolate_apply, Polynomial.map_sum, map_basis]

/-- A polynomial `P` over `E` of degree below `#s` whose value at every node `φ (v i)`, `i ∈ s`,
is `φ (r i) + y * φ (r' i)` equals `(interpolate s v r).map φ + C y * (interpolate s v r').map φ`.
The two interpolants are over `F` and depend only on `s`, `v`, `r` and `r'`, so the same pair
explains every such `P` for every field `E`, homomorphism `φ` and challenge `y`.

Injectivity of `v` on `s` is needed: with two equal nodes, the prescribed values at them can
disagree while `P` can only take one value. The degree bound is needed because a polynomial of
degree `#s` can vanish at all nodes. -/
theorem eq_map_interpolate_add_C_mul_of_eval_eq (φ : F →+* E) {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (r r' : ι → F) (y : E) {P : E[X]} (hP : P.degree < #s)
    (heval : ∀ i ∈ s, P.eval (φ (v i)) = φ (r i) + y * φ (r' i)) :
    P = (interpolate s v r).map φ + C y * (interpolate s v r').map φ := by
  have hφvs : Set.InjOn (φ ∘ v) s := φ.injective.comp_injOn hvs
  rw [eq_interpolate_of_eval_eq (fun i ↦ φ (r i) + y * φ (r' i)) hφvs hP heval,
    map_interpolate, map_interpolate, ← smul_eq_C_mul, ← map_smul, ← map_add]
  rfl

/-- A Frobenius pullback is recognized from `#s` values. Let `E` have exponential
characteristic `p`, let `P` have degree below `p ^ e * #s` with Taylor coefficients at `t`
vanishing outside the multiples of `p ^ e`, and let `P` take the value `φ (r i) + y * φ (r' i)`
at a `p ^ e`-th root `roots i` of each node `φ (v i)`, `i ∈ s`. Then `P` is `expand E (p ^ e)` of
`(interpolate s v r).map φ + C y * (interpolate s v r').map φ`.

The sparsity hypothesis is needed: without it, `P` need not be a pullback at all. The degree bound
makes the contraction of `P` have degree below `#s`, so that it is determined by `#s` values. -/
theorem eq_expand_map_interpolate_add_C_mul_of_eval_eq (φ : F →+* E) {s : Finset ι}
    {v : ι → F} (hvs : Set.InjOn v s) (r r' : ι → F) (y : E) (p e : ℕ) [ExpChar E p]
    (roots : ι → E) (hroots : ∀ i ∈ s, roots i ^ p ^ e = φ (v i)) (t : E) {P : E[X]}
    (hP : P.degree < ↑(p ^ e * #s))
    (hsparse : ∀ j : ℕ, ¬p ^ e ∣ j → (taylor t P).coeff j = 0)
    (heval : ∀ i ∈ s, P.eval (roots i) = φ (r i) + y * φ (r' i)) :
    P = expand E (p ^ e) ((interpolate s v r).map φ + C y * (interpolate s v r').map φ) := by
  obtain ⟨Q, ⟨hQ, rfl⟩, -⟩ := existsUnique_expand_of_sparse_taylor p e #s P t hsparse hP
  congr 1
  refine eq_map_interpolate_add_C_mul_of_eval_eq φ hvs r r' y hQ fun i hi ↦ ?_
  rw [← hroots i hi, ← expand_eval]
  exact heval i hi

end Lagrange
