/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.FieldTheory.Finite.Extension

/-!
# Packing tuples of polynomials into one polynomial over an extension

Let `E` be an algebra over `K` and let `ζ` be a finite family in `E`.
A tuple `P` of polynomials over `K` packs to the polynomial `∑ r, ζ r · P r` over `E`.
Its coefficients are the packed coefficient tuples.

Packing is additive and commutes with multiplication by polynomials over `K`.
At a point of `K` it evaluates to the packed tuple of values.
For a linearly independent family it is injective and preserves and reflects degree bounds.
For a basis every polynomial over `E` is a packed tuple.

Every finite field has a finite extension of each positive degree, so it has a basis of any
positive size over the base field.

## Main definitions

* `Polynomial.pack`: the packed polynomial `∑ r, ζ r · P r`.

## Main statements

* `Polynomial.coeff_pack` and `Polynomial.eval_pack`: coefficients and values of a packing.
* `Polynomial.pack_add` and `Polynomial.pack_mul_left`: packing is additive and commutes with
  multiplication by polynomials over `K`.
* `Polynomial.pack_injective`: packing along a linearly independent family is injective.
* `Polynomial.degree_pack_le_iff` and `Polynomial.degree_pack_lt_iff`: packing along a linearly
  independent family preserves and reflects degree bounds.
* `Polynomial.exists_pack_eq`: along a basis, every polynomial over `E` is a packed tuple.
* `FiniteField.exists_basis_fin`: a finite field has a finite extension with a basis of any
  positive size.
-/

@[expose] public section

namespace Polynomial

open Finset

variable {K E κ : Type*} [Fintype κ]

section CommRing

variable [CommRing K] [CommRing E] [Algebra K E]

/-- The polynomial `∑ r, ζ r · P r` over `E` packing a tuple `P` of polynomials over `K`. -/
noncomputable def pack (ζ : κ → E) (P : κ → K[X]) : E[X] :=
  ∑ r, C (ζ r) * (P r).map (algebraMap K E)

/-- The coefficients of a packed polynomial are the packed coefficient tuples. -/
theorem coeff_pack (ζ : κ → E) (P : κ → K[X]) (k : ℕ) :
    (pack ζ P).coeff k = ∑ r, (P r).coeff k • ζ r := by
  simp [pack, Algebra.smul_def, mul_comm]

/-- At a point of `K`, a packed polynomial evaluates to the packed tuple of values. -/
theorem eval_pack (ζ : κ → E) (P : κ → K[X]) (x : K) :
    (pack ζ P).eval (algebraMap K E x) = ∑ r, (P r).eval x • ζ r := by
  simp [pack, eval_finsetSum, eval_map, eval₂_at_apply, Algebra.smul_def, mul_comm]

/-- Packing is additive. -/
theorem pack_add (ζ : κ → E) (P Q : κ → K[X]) : pack ζ (P + Q) = pack ζ P + pack ζ Q := by
  simp [pack, Polynomial.map_add, mul_add, sum_add_distrib]

/-- Packing commutes with multiplication by a polynomial over `K`. -/
theorem pack_mul_left (ζ : κ → E) (L : K[X]) (P : κ → K[X]) :
    pack ζ (fun r ↦ L * P r) = L.map (algebraMap K E) * pack ζ P := by
  simp only [pack, Polynomial.map_mul, mul_sum]
  exact sum_congr rfl fun r _ ↦ by ring

/-- A coefficient of a packing along a linearly independent family vanishes exactly when that
coefficient vanishes in every row. -/
theorem coeff_pack_eq_zero_iff {ζ : κ → E} (hζ : LinearIndependent K ζ) (P : κ → K[X]) (k : ℕ) :
    (pack ζ P).coeff k = 0 ↔ ∀ r, (P r).coeff k = 0 := by
  rw [coeff_pack]
  refine ⟨Fintype.linearIndependent_iff.mp hζ (fun r ↦ (P r).coeff k), fun h ↦ ?_⟩
  simp [h]

/-- Packing along a linearly independent family is injective. -/
theorem pack_injective {ζ : κ → E} (hζ : LinearIndependent K ζ) :
    Function.Injective (pack (K := K) ζ) := by
  intro P Q h
  have hsub : pack ζ (P - Q) = 0 := by
    rw [← add_right_cancel_iff (a := pack ζ Q), ← pack_add, sub_add_cancel, zero_add, h]
  funext r
  ext k
  rw [← sub_eq_zero, ← coeff_sub]
  exact (coeff_pack_eq_zero_iff hζ (P - Q) k).mp (by rw [hsub, coeff_zero]) r

/-- Packing along a linearly independent family preserves and reflects the bound
`degree ≤ n`. -/
theorem degree_pack_le_iff {ζ : κ → E} (hζ : LinearIndependent K ζ) (P : κ → K[X])
    (n : WithBot ℕ) : (pack ζ P).degree ≤ n ↔ ∀ r, (P r).degree ≤ n := by
  simp only [degree_le_iff_coeff_zero, coeff_pack_eq_zero_iff hζ]
  exact ⟨fun h r m hm ↦ h m hm r, fun h m hm r ↦ h r m hm⟩

/-- Packing along a linearly independent family preserves and reflects the bound
`degree < n`. -/
theorem degree_pack_lt_iff {ζ : κ → E} (hζ : LinearIndependent K ζ) (P : κ → K[X]) (n : ℕ) :
    (pack ζ P).degree < n ↔ ∀ r, (P r).degree < n := by
  simp only [degree_lt_iff_coeff_zero, coeff_pack_eq_zero_iff hζ]
  exact ⟨fun h r m hm ↦ h m hm r, fun h m hm r ↦ h r m hm⟩

/-- Along a basis of `E` over `K`, every polynomial over `E` is a packed tuple. -/
theorem exists_pack_eq (b : Module.Basis κ K E) (Q : E[X]) : ∃ P : κ → K[X], pack b P = Q := by
  induction Q using Polynomial.induction_on' with
  | add Q Q' hQ hQ' =>
    obtain ⟨P, rfl⟩ := hQ
    obtain ⟨P', rfl⟩ := hQ'
    exact ⟨P + P', pack_add _ _ _⟩
  | monomial k a =>
    refine ⟨fun r ↦ monomial k (b.repr a r), ?_⟩
    simp only [pack, map_monomial, C_mul_monomial, ← map_sum]
    congr 1
    conv_rhs => rw [← b.sum_repr a]
    exact sum_congr rfl fun r _ ↦ by rw [Algebra.smul_def, mul_comm]

end CommRing

end Polynomial

namespace FiniteField

/-- A finite field `K` has a finite extension with a basis of size `t`, for every `t ≠ 0`. -/
theorem exists_basis_fin (K : Type*) [Field K] [Finite K] {t : ℕ} (ht : t ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra K E),
      Nonempty (Module.Basis (Fin t) K E) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : NeZero t := ⟨ht⟩
  exact ⟨Extension K p t, inferInstance, inferInstance, inferInstance,
    ⟨Module.finBasisOfFinrankEq K _ (finrank_extension K p t)⟩⟩

end FiniteField
