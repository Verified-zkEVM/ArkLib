/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Point counts from finite coordinate quotients

A point of the zero locus of an ideal `I : Ideal (MvPolynomial σ k)` determines a
`k`-algebra homomorphism from the actual coordinate quotient `MvPolynomial σ k ⧸ I` to the
coordinate field. Distinct points determine distinct homomorphisms because their values on the
coordinate variables differ.

When the coordinate quotient is finite-dimensional, Mathlib's linear independence of algebra
homomorphisms supplies both finiteness of the homomorphism type and the sharp bound by the
quotient's `k`-dimension. Consequently the zero locus is finite and its `Set.ncard` is at most the
quotient's `k`-finrank.

No finiteness hypothesis on `σ`, properness or radicality hypothesis on `I`, or algebraic-closure
hypothesis on the coordinate field is needed. In particular the results include `I = ⊤`: both the
zero locus and the algebra-homomorphism type are empty, while the quotient has finrank zero.

## Main statements

* `MvPolynomial.zeroLocusPointHom`: evaluation of the coordinate quotient at a zero.
* `MvPolynomial.zeroLocusPointHom_injective`: distinct zeros induce distinct algebra homomorphisms.
* `MvPolynomial.finite_zeroLocus_of_finite_quotient`: a finite-dimensional coordinate quotient has
  finitely many points over every field extension.
* `MvPolynomial.ncard_zeroLocus_le_finrank_quotient`: the point count is bounded by the
  base-field dimension of the actual coordinate quotient.

## Ownership

The generic algebra result is already owned by Mathlib:
`Finite.algHom` and `card_algHom_le_finrank` in
`Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`. This module adds only the multivariate-polynomial
zero-locus adapter and does not duplicate that generic API. Hilbert-polynomial and Krull-dimension
interpretations belong to later geometry layers.

## References

These declarations are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/ZeroLocus/ZeroDimensional.lean`. Their statements are unchanged
apart from renaming the fields to `k` and `K` to match `Mathlib.RingTheory.Nullstellensatz`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

/-- Evaluate the coordinate quotient at one of its zeros. -/
def zeroLocusPointHom (I : Ideal (MvPolynomial σ k)) (x : zeroLocus K I) :
    (MvPolynomial σ k ⧸ I) →ₐ[k] K :=
  Ideal.Quotient.liftₐ I (aeval x.val) x.property

/-- A point is determined by its homomorphism on the coordinate quotient. -/
theorem zeroLocusPointHom_injective (I : Ideal (MvPolynomial σ k)) :
    Function.Injective (zeroLocusPointHom (K := K) I) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h (Ideal.Quotient.mk I (X i))
  change aeval x.val (X i) = aeval y.val (X i) at hi
  simpa only [aeval_X] using hi

/-- A finite-dimensional coordinate quotient has finitely many extension-field zeros. -/
theorem finite_zeroLocus_of_finite_quotient (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] : (zeroLocus K I).Finite := by
  have : Finite (zeroLocus K I) := Finite.of_injective
    (zeroLocusPointHom I) (zeroLocusPointHom_injective I)
  exact Set.toFinite _

/-- The number of distinct zeros is at most the dimension of the actual coordinate quotient.

The finite-dimensional hypothesis already implies finiteness by
`finite_zeroLocus_of_finite_quotient`, so the left side is the genuine finite cardinality rather
than the default value of `Set.ncard` for an infinite set. -/
theorem ncard_zeroLocus_le_finrank_quotient (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    (zeroLocus K I).ncard ≤ Module.finrank k (MvPolynomial σ k ⧸ I) := by
  have h := Nat.card_le_card_of_injective (zeroLocusPointHom (K := K) I)
    (zeroLocusPointHom_injective I)
  exact h.trans (card_algHom_le_finrank k (MvPolynomial σ k ⧸ I) K)

end MvPolynomial

end
