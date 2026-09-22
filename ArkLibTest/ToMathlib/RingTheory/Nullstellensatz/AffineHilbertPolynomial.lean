/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for the zero-locus bound by the affine Hilbert polynomial

In one variable over `ℚ`, the affine Hilbert polynomial of `span {f}` for nonzero `f` of total
degree `d > 0` is the constant `d`, so the bound says that `f` has at most `d` roots in every
extension field. Over `ZMod 2` the zero ideal in one variable has two zeros while its affine
Hilbert polynomial `X + 1` has constant coefficient `1`, so the finite-dimensional hypothesis is
needed. The forms for a quotient of Krull dimension zero and for a Hilbert polynomial of natural
degree zero are derived from the general one.

The same root count follows from the affine degree: `span {f}` has affine degree
`totalDegree f`. The zero ideal over `ZMod 2` has affine degree `1` and two zeros, so the
finite-dimensional hypothesis of `ncard_zeroLocus_le_affineDegree` is needed. The form
`finite_zeroLocus_and_ncard_le_affineDegree`, for natural degree zero, is also checked.
-/

open MvPolynomial Polynomial

namespace ZeroLocusAffineHilbertPolynomialTest

/-- In one variable, `span {f}` for nonzero `f` of total degree `d > 0` has constant affine Hilbert
polynomial `d`. -/
theorem affineHilbertPolynomial_span_singleton_fin_one {f : MvPolynomial (Fin 1) ℚ}
    (hf : f ≠ 0) (hd : 0 < f.totalDegree) :
    (affineHilbertPolynomial (Ideal.span {f})).natDegree = 0 ∧
      (affineHilbertPolynomial (Ideal.span {f})).coeff 0 = f.totalDegree := by
  have hP : (preHilbertPoly ℚ 1 0).natDegree = 1 := natDegree_preHilbertPoly ℚ 1 0
  have hlc : (preHilbertPoly ℚ 1 0).leadingCoeff = 1 := by
    rw [leadingCoeff_preHilbertPoly]
    simp
  rw [affineHilbertPolynomial_span_singleton hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h := natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (Nat.cast_ne_zero.mpr hd.ne') (by rw [hP]; exact Nat.one_pos)
  rw [hP, Nat.sub_self] at h
  refine ⟨h.1, ?_⟩
  have hc := coeff_natDegree (p := backwardDifference (f.totalDegree : ℚ) (preHilbertPoly ℚ 1 0))
  rw [h.1, h.2, hlc] at hc
  rw [hc]
  simp

/-- A nonzero polynomial of total degree `d > 0` in one variable over `ℚ` has at most `d` zeros in
every extension field. -/
example {K : Type*} [Field K] [Algebra ℚ K] {f : MvPolynomial (Fin 1) ℚ} (hf : f ≠ 0)
    (hd : 0 < f.totalDegree) : (zeroLocus K (Ideal.span {f})).ncard ≤ f.totalDegree := by
  obtain ⟨hdeg, hcoeff⟩ := affineHilbertPolynomial_span_singleton_fin_one hf hd
  have : Module.Finite ℚ (MvPolynomial (Fin 1) ℚ ⧸ Ideal.span {f}) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp hdeg
  have h := ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial (K := K) (Ideal.span {f})
  rw [hcoeff] at h
  exact_mod_cast h

/-- The affine Hilbert polynomial of the zero ideal in one variable over `ZMod 2` is `X + 1`. -/
theorem affineHilbertPolynomial_bot_fin_one :
    affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2))) = Polynomial.X + 1 :=
  (eq_affineHilbertPolynomial_of_eval_eq (N₀ := 0) fun N _ ↦ by
    simp [affineHilbertFunction_bot]).symm

/-- The finite-dimensional hypothesis is needed: over `ZMod 2`, the zero ideal in one variable has
the two zeros `0` and `1`, but the constant coefficient of its affine Hilbert polynomial is `1`. -/
example : (zeroLocus (ZMod 2) (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2)))).ncard = 2 ∧
    (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2)))).coeff 0 = 1 := by
  refine ⟨?_, by simp [affineHilbertPolynomial_bot_fin_one]⟩
  have huniv : zeroLocus (ZMod 2) (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2))) = Set.univ := by
    ext x
    simp
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
  rfl

/-- The bound for a quotient of Krull dimension zero. -/
example {F E σ : Type*} [Field F] [Finite σ] [Field E] [Algebra F E] (I : Ideal (MvPolynomial σ F))
    [Ring.KrullDimLE 0 (MvPolynomial σ F ⧸ I)] :
    (zeroLocus E I).Finite ∧
      ((zeroLocus E I).ncard : ℚ) ≤ (affineHilbertPolynomial I).coeff 0 :=
  finite_zeroLocus_and_ncard_le_affineHilbertPolynomial I

/-- The bound when the affine Hilbert polynomial is constant. -/
example {F E σ : Type*} [Field F] [Finite σ] [Field E] [Algebra F E] (I : Ideal (MvPolynomial σ F))
    (hdeg : (affineHilbertPolynomial I).natDegree = 0) :
    ((zeroLocus E I).ncard : ℚ) ≤ (affineHilbertPolynomial I).coeff 0 :=
  have := natDegree_affineHilbertPolynomial_eq_zero_iff.mp hdeg
  ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial I

/-- A nonzero polynomial of positive total degree `d` in one variable over `ℚ` has at most `d`
zeros in every extension field, by the affine-degree bound: `span {f}` has affine degree `d`. -/
example {K : Type*} [Field K] [Algebra ℚ K] {f : MvPolynomial (Fin 1) ℚ} (hf : f ≠ 0)
    (hd : 0 < f.totalDegree) :
    (zeroLocus K (Ideal.span {f})).Finite ∧
      (zeroLocus K (Ideal.span {f})).ncard ≤ f.totalDegree := by
  have h := finite_zeroLocus_and_ncard_le_affineDegree (K := K) (Ideal.span {f})
    (affineHilbertPolynomial_span_singleton_fin_one hf hd).1
  rw [affineDegree_span_singleton hf] at h
  exact ⟨h.1, by exact_mod_cast h.2⟩

/-- The finite-dimensional hypothesis of `ncard_zeroLocus_le_affineDegree` is needed: over
`ZMod 2`, the zero ideal in one variable has two zeros and affine degree `1`. -/
example : (zeroLocus (ZMod 2) (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2)))).ncard = 2 ∧
    affineDegree (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2))) = 1 := by
  refine ⟨?_, affineDegree_bot⟩
  have huniv : zeroLocus (ZMod 2) (⊥ : Ideal (MvPolynomial (Fin 1) (ZMod 2))) = Set.univ := by
    ext x
    simp
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
  rfl

/-- The affine-degree bound when the Hilbert polynomial has natural degree zero. -/
example {F E σ : Type*} [Field F] [Finite σ] [Field E] [Algebra F E] (I : Ideal (MvPolynomial σ F))
    (hdeg : (affineHilbertPolynomial I).natDegree = 0) :
    (zeroLocus E I).Finite ∧ ((zeroLocus E I).ncard : ℚ) ≤ affineDegree I :=
  finite_zeroLocus_and_ncard_le_affineDegree I hdeg

end ZeroLocusAffineHilbertPolynomialTest
