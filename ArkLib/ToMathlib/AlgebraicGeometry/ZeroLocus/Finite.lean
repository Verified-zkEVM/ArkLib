/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Polynomial

/-!
# Finite zero loci and finite reduced coordinate quotients

Over an algebraically closed base, evaluation embeds a reduced coordinate quotient
into the functions on its zero locus. A finite zero locus therefore forces the
actual quotient to be finite-dimensional and its Hilbert polynomial to be constant.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial

variable {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]

/-- Evaluation on all rational points is injective for a reduced affine quotient
over an algebraically closed field. -/
theorem zeroLocusEvaluation_injective (I : Ideal (MvPolynomial σ F)) (hI : I.IsRadical) :
    Function.Injective (LinearMap.pi fun x : zeroLocus F I ↦
      (zeroLocusPointHom I x).toLinearMap) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  rw [← hI.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := F)]
  intro z hz
  have he := congrArg (fun v : zeroLocus F I → F ↦ v ⟨z, hz⟩) hxy
  change aeval z p = aeval z q at he
  rw [map_sub, he, sub_self]

/-- A finite zero locus forces a reduced affine quotient to be finite-dimensional. -/
theorem moduleFinite_of_finite_zeroLocus (I : Ideal (MvPolynomial σ F)) (hI : I.IsRadical)
    (hV : (zeroLocus F I).Finite) : Module.Finite F (MvPolynomial σ F ⧸ I) := by
  let _ : Fintype (zeroLocus F I) := hV.fintype
  exact Module.Finite.of_injective
    (LinearMap.pi fun x : zeroLocus F I ↦ (zeroLocusPointHom I x).toLinearMap)
    (zeroLocusEvaluation_injective I hI)

/-- Finiteness of the zero locus is exactly degree zero of the actual Hilbert
polynomial for a reduced affine quotient over an algebraically closed field. -/
theorem finite_zeroLocus_iff_hilbertPolynomial_natDegree_zero
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsRadical) :
    (zeroLocus F I).Finite ↔ (hilbertPolynomial I).natDegree = 0 := by
  constructor
  · intro hV
    have := moduleFinite_of_finite_zeroLocus I hI hV
    rw [hilbertPolynomial_eq_constant, Polynomial.natDegree_C]
  · intro hdeg
    have := moduleFinite_of_hilbertPolynomial_natDegree_zero I hdeg
    exact finite_zeroLocus_of_finite_quotient I

end AffineHilbert
