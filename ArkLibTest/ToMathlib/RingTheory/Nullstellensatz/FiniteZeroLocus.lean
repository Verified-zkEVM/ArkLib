/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteZeroLocus
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance tests for finite zero loci

These examples use the public API through an ordinary import, with `K` the algebraic closure of
`ℚ`. The ideal `(x ^ 2)` of `ℚ[x]` shows that evaluation on the zero locus is not injective
without radicality. Over `K`, the non-radical ideal `(x ^ 2)` has a finite zero locus, so its
Hilbert polynomial has natural degree zero, while the zero locus of `⊥` is infinite because its
Hilbert polynomial has natural degree one. The last examples derive the source statements, which
assumed radicality and took the points in the coefficient field.
-/

open MvPolynomial

namespace FiniteZeroLocusTest

local notation "K" => AlgebraicClosure ℚ

/-- `x` is not a multiple of `x ^ 2`, since `x` is not a unit. -/
theorem X_notMem_span_X_sq {k : Type*} [Field k] :
    (X 0 : MvPolynomial (Fin 1) k) ∉ Ideal.span {X 0 ^ 2} := by
  rw [Ideal.mem_span_singleton]
  rintro ⟨q, hq⟩
  have h1 : (X 0 : MvPolynomial (Fin 1) k) * (X 0 * q) = X 0 * 1 := by
    rw [← mul_assoc, ← pow_two, ← hq, mul_one]
  have h2 : (X 0 : MvPolynomial (Fin 1) k) * q = 1 := mul_left_cancel₀ (X_ne_zero 0) h1
  exact X_prime.not_isUnit (IsUnit.of_mul_eq_one q h2)

/-- The only zero of `(x ^ 2)`, over any field extension, is `0`. -/
theorem eq_zero_of_mem_zeroLocus_span_X_sq {k L : Type*} [Field k] [Field L] [Algebra k L]
    {x : Fin 1 → L} (hx : x ∈ zeroLocus L (Ideal.span {(X 0 : MvPolynomial (Fin 1) k) ^ 2})) :
    x = 0 := by
  have h := hx _ (Ideal.mem_span_singleton_self _)
  rw [map_pow, aeval_X] at h
  funext i
  rw [Subsingleton.elim i 0]
  exact (pow_eq_zero_iff two_ne_zero).mp h

/-- Radicality is needed in `zeroLocusEvaluation_injective`: for `I = (x ^ 2)` in `ℚ[x]`, the class
of `x` is nonzero but vanishes at every zero of `I` in `K`. -/
example : ¬ Function.Injective (LinearMap.pi fun x : zeroLocus K
    (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ) ^ 2}) ↦ (zeroLocusPointHom _ x).toLinearMap) := by
  intro hinj
  refine X_notMem_span_X_sq (Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_))
  rw [map_zero]
  funext x
  change aeval x.1 (X 0) = 0
  rw [aeval_X, eq_zero_of_mem_zeroLocus_span_X_sq x.2, Pi.zero_apply]

/-- A finite zero locus without radicality: over `K`, the zero locus of `(x ^ 2)` is `{0}`, so the
Hilbert polynomial of the non-radical ideal `(x ^ 2)` has natural degree zero. -/
example : (affineHilbertPolynomial
    (Ideal.span {(X 0 : MvPolynomial (Fin 1) K) ^ 2})).natDegree = 0 := by
  refine (finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero _).mp
    ((Set.finite_singleton 0).subset fun x hx ↦ ?_)
  exact eq_zero_of_mem_zeroLocus_span_X_sq hx

/-- The zero locus of `⊥` in `K ^ 1` is infinite, because the Hilbert polynomial of `⊥` has
natural degree one. -/
example : (zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) K))).Infinite := by
  rw [Set.Infinite, finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero,
    natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

/-- The source's `zeroLocusEvaluation_injective`, with the points in the coefficient field. -/
example {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ] (I : Ideal (MvPolynomial σ F))
    (hI : I.IsRadical) :
    Function.Injective (LinearMap.pi fun x : zeroLocus F I ↦
      (zeroLocusPointHom I x).toLinearMap) :=
  zeroLocusEvaluation_injective I hI

/-- The source's `moduleFinite_of_finite_zeroLocus`, with its radical hypothesis unused. -/
example {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ] (I : Ideal (MvPolynomial σ F))
    (_hI : I.IsRadical) (hV : (zeroLocus F I).Finite) :
    Module.Finite F (MvPolynomial σ F ⧸ I) :=
  moduleFinite_of_finite_zeroLocus I hV

/-- The source's `finite_zeroLocus_iff_hilbertPolynomial_natDegree_zero`, with its radical
hypothesis unused. -/
example {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ] (I : Ideal (MvPolynomial σ F))
    (_hI : I.IsRadical) :
    (zeroLocus F I).Finite ↔ (affineHilbertPolynomial I).natDegree = 0 :=
  finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero I

end FiniteZeroLocusTest
