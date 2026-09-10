/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Point counts for zero-dimensional affine quotients

Each zero defines an algebra homomorphism from the actual coordinate quotient. Distinct
zeros give distinct homomorphisms. Linear independence of algebra homomorphisms therefore
bounds the number of points by the quotient's vector-space dimension, over every extension
field. Krull dimension zero supplies finiteness of the coordinate algebra in finite variables.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {F E σ : Type*} [Field F] [Field E] [Algebra F E]

/-- Evaluate the coordinate quotient at one of its zeros. -/
def zeroLocusPointHom (I : Ideal (MvPolynomial σ F)) (x : zeroLocus E I) :
    (MvPolynomial σ F ⧸ I) →ₐ[F] E :=
  Ideal.Quotient.liftₐ I (aeval x.val) x.property

/-- A point is determined by its homomorphism on the coordinate quotient. -/
theorem zeroLocusPointHom_injective (I : Ideal (MvPolynomial σ F)) :
    Function.Injective (zeroLocusPointHom (E := E) I) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h (Ideal.Quotient.mk I (X i))
  change aeval x.val (X i) = aeval y.val (X i) at hi
  simpa only [aeval_X] using hi

/-- A finite-dimensional coordinate quotient has finitely many extension-field zeros. -/
theorem finite_zeroLocus_of_finite_quotient (I : Ideal (MvPolynomial σ F))
    [Module.Finite F (MvPolynomial σ F ⧸ I)] : (zeroLocus E I).Finite := by
  have : Finite (zeroLocus E I) := Finite.of_injective
    (zeroLocusPointHom I) (zeroLocusPointHom_injective I)
  exact Set.toFinite _

/-- The number of distinct zeros is at most the dimension of the actual coordinate quotient.
Finiteness is proved separately, so this is never a default `ncard` value for an infinite set. -/
theorem ncard_zeroLocus_le_finrank_quotient (I : Ideal (MvPolynomial σ F))
    [Module.Finite F (MvPolynomial σ F ⧸ I)] :
    (zeroLocus E I).ncard ≤ Module.finrank F (MvPolynomial σ F ⧸ I) := by
  have h := Nat.card_le_card_of_injective (zeroLocusPointHom (E := E) I)
    (zeroLocusPointHom_injective I)
  exact h.trans (card_algHom_le_finrank F (MvPolynomial σ F ⧸ I) E)

/-- A zero-dimensional affine quotient in finitely many variables has a finite zero locus
and its point count is bounded by its actual algebra dimension. -/
theorem finite_zeroLocus_and_ncard_le_of_krullDimLE_zero [Finite σ]
    (I : Ideal (MvPolynomial σ F)) [Ring.KrullDimLE 0 (MvPolynomial σ F ⧸ I)] :
    (zeroLocus E I).Finite ∧
      (zeroLocus E I).ncard ≤ Module.finrank F (MvPolynomial σ F ⧸ I) := by
  have : Module.Finite F (MvPolynomial σ F ⧸ I) :=
    (Module.finite_iff_krullDimLE_zero F (MvPolynomial σ F ⧸ I)).mpr inferInstance
  exact ⟨finite_zeroLocus_of_finite_quotient I, ncard_zeroLocus_le_finrank_quotient I⟩

end MvPolynomial

end
