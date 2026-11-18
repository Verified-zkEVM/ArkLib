/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Trace polynomials and trace coordinates

Let `L` be an extension of degree `k` of a finite field `K` with `q` elements.
For `c ∈ L`, the trace polynomial `T_c = ∑_{j < k} c^{qʲ} X^{qʲ}` has degree at most `qᵏ⁻¹`.
It evaluates to the trace of `c x` at every `x ∈ L`.
Its degree is exactly `qᵏ⁻¹` when `c ≠ 0`.
It is additive in `c`, and it is additive as a function on every `L`-algebra.
Both facts hold because `x ↦ x^q` is additive on every algebra over `K`.

A family `c` of elements of `L` gives the `K`-linear map `x ↦ (Tr(cᵢ x))ᵢ`.
For a basis `c`, this map is a bijection onto `K^ι`.
Its coordinates are those in the trace-dual basis.
That basis exists since the trace form is nondegenerate.

The exponent `k - 1` uses subtraction in `ℕ`.
The trace polynomial is noncomputable, as polynomial arithmetic over a field is.
The coordinate map and equivalence are noncomputable, as `Algebra.trace` is.

## Main definitions

* `FiniteField.tracePolynomial`: the polynomial `∑_{j < k} c^{qʲ} X^{qʲ}`.
* `FiniteField.traceCoordinateMap`: the `K`-linear map `x ↦ (Tr(cᵢ x))ᵢ`.
* `FiniteField.traceCoordinateEquiv`: the same map for a basis, as a linear equivalence.

## Main statements

* `FiniteField.add_pow_card_pow`: `x ↦ x^{qʲ}` is additive on every algebra over `K`.
* `FiniteField.eval_tracePolynomial`: `T_c(x) = Tr(c x)`.
* `FiniteField.tracePolynomial_add`: `T_{c + c'} = T_c + T_{c'}`.
* `FiniteField.aeval_tracePolynomial_add` and `FiniteField.eval_tracePolynomial_add`:
  `T_c(x + y) = T_c(x) + T_c(y)`.
* `FiniteField.coeff_tracePolynomial`: the coefficient of `X^{qʲ}` is `c^{qʲ}`.
* `FiniteField.natDegree_tracePolynomial_le` and `FiniteField.natDegree_tracePolynomial`:
  the degree is at most `qᵏ⁻¹`, with equality for `c ≠ 0`.
* `FiniteField.traceCoordinateMap_apply` and `FiniteField.traceCoordinateEquiv_apply`:
  the coordinates are traces.
* `FiniteField.traceCoordinateMap_bijective`: a basis gives a bijection.
* `FiniteField.exists_bijective_traceCoordinateMap`: such a bijection exists with `k`
  coordinates.
-/

@[expose] public section

open Polynomial Finset

namespace FiniteField

section TracePolynomial

variable (K : Type*) {L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]

/-- The trace polynomial `∑_{j < k} c^{qʲ} X^{qʲ}`, where `q = |K|` and `k = [L : K]`. -/
noncomputable def tracePolynomial (c : L) : L[X] :=
  ∑ j ∈ range (Module.finrank K L), C (c ^ Fintype.card K ^ j) * X ^ Fintype.card K ^ j

/-- On a commutative ring `A` that is an algebra over `K`, the power `x ↦ x^{qʲ}` is additive.
Here `q = |K|`. -/
theorem add_pow_card_pow {A : Type*} [CommRing A] [Algebra K A] (x y : A) (j : ℕ) :
    (x + y) ^ Fintype.card K ^ j = x ^ Fintype.card K ^ j + y ^ Fintype.card K ^ j := by
  have h (z : A) : (frobeniusAlgHom K A ^ j) z = z ^ Fintype.card K ^ j := by
    rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate]
  rw [← h, ← h, ← h, map_add]

variable {K}

/-- The trace polynomial of `c + c'` is the sum of the trace polynomials of `c` and `c'`. -/
theorem tracePolynomial_add (c c' : L) :
    tracePolynomial K (c + c') = tracePolynomial K c + tracePolynomial K c' := by
  simp only [tracePolynomial, add_pow_card_pow K, map_add, add_mul, sum_add_distrib]

/-- Let `A` be a commutative ring that is an algebra over `L`, and let `c ∈ L`.
The trace polynomial of `c` is additive as a function on `A`. -/
theorem aeval_tracePolynomial_add {A : Type*} [CommRing A] [Algebra L A] (c : L) (x y : A) :
    aeval (x + y) (tracePolynomial K c) =
      aeval x (tracePolynomial K c) + aeval y (tracePolynomial K c) := by
  let _ : Algebra K A := ((algebraMap L A).comp (algebraMap K L)).toAlgebra
  simp only [tracePolynomial, map_sum, map_mul, aeval_C, map_pow, aeval_X, add_pow_card_pow K,
    mul_add, sum_add_distrib]

/-- The trace polynomial of `c` is additive as a function on `L`. -/
theorem eval_tracePolynomial_add (c x y : L) :
    (tracePolynomial K c).eval (x + y) =
      (tracePolynomial K c).eval x + (tracePolynomial K c).eval y := by
  simpa using aeval_tracePolynomial_add (A := L) c x y

/-- Let `L` be a finite extension of a finite field `K`, and let `c ∈ L`.
At every `x ∈ L`, the trace polynomial of `c` evaluates to the trace of `c x`. -/
theorem eval_tracePolynomial [Finite L] (c x : L) :
    (tracePolynomial K c).eval x = algebraMap K L (Algebra.trace K L (c * x)) := by
  rw [algebraMap_trace_eq_sum_pow, tracePolynomial, eval_finsetSum, Nat.card_eq_fintype_card]
  simp [mul_pow]

/-- For `j < k`, the coefficient of `X^{qʲ}` in the trace polynomial of `c` is `c^{qʲ}`.
Here `q = |K|` and `k = [L : K]`. -/
theorem coeff_tracePolynomial (c : L) {j : ℕ} (hj : j < Module.finrank K L) :
    (tracePolynomial K c).coeff (Fintype.card K ^ j) = c ^ Fintype.card K ^ j := by
  rw [tracePolynomial, finsetSum_coeff, sum_eq_single j]
  · rw [coeff_C_mul_X_pow]
    simp
  · intro i _ hi
    rw [coeff_C_mul_X_pow, ite_eq_right]
    exact fun h ↦ (hi (Nat.pow_right_injective Fintype.one_lt_card h).symm).elim
  · simp [hj]

/-- The trace polynomial has degree at most `qᵏ⁻¹`, where `q = |K|` and `k = [L : K]`. -/
theorem natDegree_tracePolynomial_le (c : L) :
    (tracePolynomial K c).natDegree ≤ Fintype.card K ^ (Module.finrank K L - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.pow_le_pow_right Fintype.card_pos (by simp at hj; omega)

/-- Let `L` be a finite-dimensional extension of `K`, and let `c ∈ L` be nonzero.
The trace polynomial of `c` has degree exactly `qᵏ⁻¹`, where `q = |K|` and `k = [L : K]`. -/
theorem natDegree_tracePolynomial [FiniteDimensional K L] {c : L} (hc : c ≠ 0) :
    (tracePolynomial K c).natDegree = Fintype.card K ^ (Module.finrank K L - 1) := by
  refine (natDegree_tracePolynomial_le c).antisymm (le_natDegree_of_ne_zero ?_)
  rw [coeff_tracePolynomial c (Nat.sub_lt Module.finrank_pos one_pos)]
  exact pow_ne_zero _ hc

end TracePolynomial

section Coordinates

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- The `K`-linear map `x ↦ (Tr(cᵢ x))ᵢ` from `L` to `K^ι`. -/
noncomputable def traceCoordinateMap (c : ι → L) : L →ₗ[K] (ι → K) :=
  LinearMap.pi fun i ↦ (Algebra.trace K L).comp (LinearMap.mulLeft K (c i))

variable {K}

/-- The `i`-th trace coordinate of `x` is the trace of `cᵢ x`. -/
@[simp]
theorem traceCoordinateMap_apply (c : ι → L) (x : L) (i : ι) :
    traceCoordinateMap K c x i = Algebra.trace K L (c i * x) :=
  rfl

/-- Let `b` be a finite basis of `L` over a finite field `K`, so `L` is a finite field.
The map `x ↦ (Tr(bᵢ x))ᵢ` is a bijection from `L` onto `K^ι`.
Its coordinates are the coordinates in the trace-dual basis. -/
theorem traceCoordinateMap_bijective [Finite K] [Finite ι] (b : Module.Basis ι K L) :
    Function.Bijective (traceCoordinateMap K b) := by
  classical
  have := Fintype.ofFinite ι
  have := Module.Finite.of_basis b
  have : Finite L := Module.finite_of_finite K
  have h : ⇑(traceCoordinateMap K b) =
      ((Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b).equivFun := by
    funext x i
    simp [LinearMap.BilinForm.dualBasis_repr_apply, mul_comm]
  rw [h]
  exact LinearEquiv.bijective _

variable (K) in
/-- The linear equivalence `x ↦ (Tr(bᵢ x))ᵢ` between `L` and `K^ι`.
Here `b` is a finite basis of `L` over a finite field `K`. -/
noncomputable def traceCoordinateEquiv [Finite K] [Finite ι] (b : Module.Basis ι K L) :
    L ≃ₗ[K] (ι → K) :=
  LinearEquiv.ofBijective (traceCoordinateMap K b) (traceCoordinateMap_bijective b)

/-- The `i`-th coordinate of `x` is the trace of `bᵢ x`. -/
@[simp]
theorem traceCoordinateEquiv_apply [Finite K] [Finite ι] (b : Module.Basis ι K L) (x : L)
    (i : ι) : traceCoordinateEquiv K b x i = Algebra.trace K L (b i * x) :=
  rfl

variable (K L) in
/-- Let `L` be a finite field of degree `k` over `K`.
Some `k` elements `cᵢ ∈ L` make `x ↦ (Tr(cᵢ x))ᵢ` a bijection from `L` onto `Kᵏ`. -/
theorem exists_bijective_traceCoordinateMap [Finite L] :
    ∃ c : Fin (Module.finrank K L) → L, Function.Bijective (traceCoordinateMap K c) :=
  have : Finite K := .of_injective _ (algebraMap K L).injective
  ⟨_, traceCoordinateMap_bijective (Module.finBasis K L)⟩

end Coordinates

end FiniteField
