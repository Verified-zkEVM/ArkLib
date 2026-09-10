/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.NoetherNormalizationHeightOne
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.FiniteExtensionDegree
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Polynomial

/-!
# Hilbert-polynomial purity of principal cuts

A minimal prime over a proper principal cut of an affine prime has Hilbert-polynomial degree
exactly one below that of the parent prime.  The proof uses Noether normalization and preservation
of Hilbert-polynomial degree under finite injective affine algebra maps.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

/-- Every minimal component of a proper principal cut of an affine prime has
Hilbert-polynomial degree exactly one below the parent. -/
theorem principalCut_component_hilbertPolynomial_natDegree_add_one
    {F σ : Type*} [Field F] [Finite σ]
    {P J : Ideal (MvPolynomial σ F)} (hP : P.IsPrime) {f : MvPolynomial σ F}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (hilbertPolynomial J).natDegree + 1 = (hilbertPolynomial P).natDegree := by
  let _ : P.IsPrime := hP
  let _ : J.IsPrime := hJ.isPrime
  let A := MvPolynomial σ F ⧸ P
  let Q : Ideal A := J.map (Ideal.Quotient.mk P)
  let hPJ : P ≤ J := le_sup_left.trans hJ.le
  obtain ⟨d, g, a, ha, hg_inj, hg_fin, ha0, haproper,
      hbot_inj, hbot_fin, hchild_inj, hchild_fin, hdata⟩ :=
    principalCut_component_exists_coordinate_normalization hP hf hJ
  have hPproper : P ≠ ⊤ := hP.ne_top
  have hJproper : J ≠ ⊤ := hJ.isPrime.ne_top
  have hparent :
      (hilbertPolynomial P).natDegree =
        (hilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin d) F))).natDegree := by
    apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
      (normalizationBotMap g) hbot_inj hPproper
    simpa [RingHom.Finite] using hbot_fin
  have hchild :
      (hilbertPolynomial J).natDegree =
        (hilbertPolynomial (Ideal.span {a})).natDegree := by
    apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
      (normalizationChildMap hPJ g a ha) hchild_inj hJproper
    simpa [RingHom.Finite] using hchild_fin
  rw [hchild, hparent, hilbertPolynomial_bot_natDegree]
  exact hilbertPolynomial_span_singleton_natDegree_add_one ha0 haproper

end AffineHilbert
