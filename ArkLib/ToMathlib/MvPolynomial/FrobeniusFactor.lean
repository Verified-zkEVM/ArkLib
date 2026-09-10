/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullbackDerivative
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
public import ArkLib.ToMathlib.Polynomial.FrobeniusContractionFractionRing

/-!
# Frobenius factorization in one multivariate coordinate

An irreducible multivariate polynomial of positive degree in a distinguished root coordinate can
be contracted along that coordinate until its partial derivative is nonzero.  The contraction
stays over the original multivariate coefficient ring, preserves irreducibility, divides the root
degree exactly, and does not increase any other coordinate degree.  Under the standard
polynomial presentation, the terminal factor is primitive and becomes irreducible and separable
over the fraction field of the coefficient ring.

This file proves only this algebraic factorization.  It does not provide geometric reconstruction
or an agreement bound.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {K σ L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial σ K) L] [IsFractionRing (MvPolynomial σ K) L]
  (p : ℕ) [CharP K p] [Fact p.Prime]

/-- Contract all Frobenius powers from the distinguished `none` coordinate of an irreducible
multivariate polynomial.  The terminal factor has nonzero root partial derivative, exact root
degree, controlled coefficient-coordinate degrees, and a separable irreducible image over the
fraction field of the coefficient ring. -/
theorem exists_frobeniusFactor {F : MvPolynomial (Option σ) K}
    (hFpos : 0 < F.degreeOf none) (hFirr : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) K,
      rootExpansion (p ^ e) G = F ∧
      pderiv none G ≠ 0 ∧
      G.degreeOf none * (p ^ e) = F.degreeOf none ∧
      Irreducible G ∧
      (∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j)) ∧
      (optionEquivLeft K σ G).IsPrimitive ∧
      Irreducible ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ∧
      Polynomial.derivative ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ≠ 0 ∧
      ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)).Separable ∧
      ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)).natDegree = G.degreeOf none := by
  let P : Polynomial (MvPolynomial σ K) := optionEquivLeft K σ F
  let _ : CharP (MvPolynomial σ K) p :=
    charP_of_injective_ringHom (C_injective σ K) p
  have hPpos : 0 < P.natDegree := by
    simpa only [P, natDegree_optionEquivLeft] using hFpos
  have hPirr : Irreducible P := by
    change Irreducible (optionEquivLeft K σ F)
    exact hFirr.map (optionEquivLeft K σ)
  obtain ⟨e, H, hHder, hHP, hHdeg, _hHpos, hHprimitive, hHmapirr, hHmapder,
      hHmapsep, hHmapdeg⟩ :=
    Polynomial.exists_frobeniusContraction_fractionRing
      (R := MvPolynomial σ K) (K := L) p hPpos hPirr
  let G : MvPolynomial (Option σ) K := (optionEquivLeft K σ).symm H
  have hs : p ^ e ≠ 0 := pow_ne_zero e (Fact.out : p.Prime).ne_zero
  have hroot : rootExpansion (p ^ e) G = F := by
    apply (optionEquivLeft K σ).injective
    simpa only [rootExpansion, G, P, AlgEquiv.apply_symm_apply] using hHP
  have hGder_eq : optionEquivLeft K σ (pderiv none G) = Polynomial.derivative H := by
    rw [optionEquivLeft_pderiv_none]
    simp only [G, AlgEquiv.apply_symm_apply]
  have hGder : pderiv none G ≠ 0 := by
    intro hzero
    apply hHder
    rw [← hGder_eq, hzero, map_zero]
  have hGdeg : G.degreeOf none * (p ^ e) = F.degreeOf none := by
    rw [← natDegree_optionEquivLeft K, ← natDegree_optionEquivLeft K]
    simpa only [G, P, AlgEquiv.apply_symm_apply] using hHdeg
  have hGirr : Irreducible G := by
    have hHirr : Irreducible H :=
      (hHprimitive.irreducible_iff_irreducible_map_fraction_map (K := L)).mpr hHmapirr
    simpa only [G] using hHirr.map (optionEquivLeft K σ).symm
  have hGcontract : G = rootContraction (p ^ e) F := by
    apply (optionEquivLeft K σ).injective
    simp only [G, rootContraction, AlgEquiv.apply_symm_apply]
    change H = Polynomial.contract (p ^ e) P
    rw [← hHP, Polynomial.contract_expand (p ^ e) hs]
  have hGother : ∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j) := by
    intro j
    rw [hGcontract]
    exact degreeOf_rootContraction_some_le hs F j
  have hHG : optionEquivLeft K σ G = H := by
    simp only [G, AlgEquiv.apply_symm_apply]
  have hHdegree : H.natDegree = G.degreeOf none := by
    rw [← hHG, natDegree_optionEquivLeft]
  refine ⟨e, G, hroot, hGder, hGdeg, hGirr, hGother, ?_⟩
  exact ⟨by simpa only [hHG] using hHprimitive,
    by simpa only [hHG] using hHmapirr,
    by simpa only [hHG] using hHmapder,
    by simpa only [hHG] using hHmapsep,
    by simpa only [hHG] using hHmapdeg.trans hHdegree⟩

section ExponentialCharacteristic

variable {K σ L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial σ K) L] [IsFractionRing (MvPolynomial σ K) L]
  (p : ℕ) [ExpChar K p]

/-- Uniform Frobenius factorization in exponential characteristic `p`.  In characteristic zero,
`p = 1` and the input itself is the terminal factor; in prime characteristic this is
`exists_frobeniusFactor`. -/
theorem exists_frobeniusFactor_expChar {F : MvPolynomial (Option σ) K}
    (hFpos : 0 < F.degreeOf none) (hFirr : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) K,
      rootExpansion (p ^ e) G = F ∧
      pderiv none G ≠ 0 ∧
      G.degreeOf none * (p ^ e) = F.degreeOf none ∧
      Irreducible G ∧
      (∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j)) ∧
      (optionEquivLeft K σ G).IsPrimitive ∧
      Irreducible ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ∧
      Polynomial.derivative ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ≠ 0 ∧
      ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)).Separable ∧
      ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)).natDegree = G.degreeOf none := by
  rcases ‹ExpChar K p› with _ | hp
  · let _ : CharZero K := charZero_of_expChar_one' K
    let _ : CharZero (MvPolynomial σ K) :=
      charZero_of_injective_ringHom (C_injective σ K)
    let _ : CharZero L :=
      charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial σ K) L)
    let P : Polynomial (MvPolynomial σ K) := optionEquivLeft K σ F
    have hPpos : 0 < P.natDegree := by
      simpa only [P, natDegree_optionEquivLeft] using hFpos
    have hPirr : Irreducible P := by
      change Irreducible (optionEquivLeft K σ F)
      exact hFirr.map (optionEquivLeft K σ)
    have hPprimitive : P.IsPrimitive := hPirr.isPrimitive (Nat.ne_of_gt hPpos)
    have hPmapirr : Irreducible (P.map (algebraMap (MvPolynomial σ K) L)) :=
      (hPprimitive.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hPirr
    have hPmapsep : (P.map (algebraMap (MvPolynomial σ K) L)).Separable :=
      hPmapirr.separable
    have hPmapder :
        Polynomial.derivative (P.map (algebraMap (MvPolynomial σ K) L)) ≠ 0 :=
      (Polynomial.separable_iff_derivative_ne_zero hPmapirr).mp hPmapsep
    have hPder : Polynomial.derivative P ≠ 0 := by
      intro hzero
      apply hPmapder
      rw [Polynomial.derivative_map, hzero, Polynomial.map_zero]
    have hFder : pderiv none F ≠ 0 := by
      intro hzero
      apply hPder
      have h := congrArg (optionEquivLeft K σ) hzero
      simpa only [optionEquivLeft_pderiv_none, map_zero, P] using h
    refine ⟨0, F, ?_, hFder, ?_, hFirr, ?_, hPprimitive, ?_, ?_, ?_, ?_⟩
    · simp only [pow_zero, rootExpansion, Polynomial.expand_one,
        AlgEquiv.symm_apply_apply]
    · simp
    · intro j
      exact le_rfl
    · simpa only [P] using hPmapirr
    · simpa only [P] using hPmapder
    · simpa only [P] using hPmapsep
    · rw [Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective (MvPolynomial σ K) L), natDegree_optionEquivLeft]
  · let _ : Fact p.Prime := ⟨hp⟩
    exact exists_frobeniusFactor (K := K) (L := L) p hFpos hFirr

end ExponentialCharacteristic

section PerfectExponentialCharacteristic

variable {K σ : Type*} [Field K] [PerfectField K] (p : ℕ) [ExpChar K p]

/-- Exponential-characteristic form of coefficient-twist preservation for a terminal factor. -/
theorem inverseFrobeniusTwist_preserves_factor_expChar (e : ℕ)
    {G : MvPolynomial (Option σ) K} (hGirr : Irreducible G) (hGder : pderiv none G ≠ 0) :
    Irreducible (inverseFrobeniusTwist p e G) ∧
      pderiv none (inverseFrobeniusTwist p e G) ≠ 0 ∧
      ∀ i : Option σ,
        (inverseFrobeniusTwist p e G).degreeOf i = G.degreeOf i := by
  exact ⟨MvPolynomial.Irreducible.map_inverseFrobeniusTwist p e hGirr,
    pderiv_inverseFrobeniusTwist_ne_zero p e hGder,
    degreeOf_inverseFrobeniusTwist p e G⟩

end PerfectExponentialCharacteristic

section PerfectField

variable [PerfectField K]

/-- The inverse Frobenius coefficient twist preserves the three terminal-factor properties used
by the pullback: irreducibility, a nonzero root partial derivative, and every coordinate degree.
-/
theorem inverseFrobeniusTwist_preserves_factor (e : ℕ)
    {G : MvPolynomial (Option σ) K} (hGirr : Irreducible G) (hGder : pderiv none G ≠ 0) :
    Irreducible (inverseFrobeniusTwist p e G) ∧
      pderiv none (inverseFrobeniusTwist p e G) ≠ 0 ∧
      ∀ i : Option σ,
        (inverseFrobeniusTwist p e G).degreeOf i = G.degreeOf i := by
  exact ⟨MvPolynomial.Irreducible.map_inverseFrobeniusTwist p e hGirr,
    pderiv_inverseFrobeniusTwist_ne_zero p e hGder,
    degreeOf_inverseFrobeniusTwist p e G⟩

end PerfectField

/-- A nonconstant coefficient-coordinate canary for `exists_frobeniusFactor`.  The equation
`Y + X_j` is linear in the root coordinate and carries the nonconstant coefficient `X_j`; its
terminal factor maps to a separable polynomial over the coefficient fraction field. -/
theorem frobeniusFactor_coefficient_canary (j : σ) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) K,
      rootExpansion (p ^ e) G = X none + X (some j) ∧
      pderiv none G ≠ 0 ∧
      G.degreeOf none * (p ^ e) = 1 ∧
      Irreducible G ∧
      G.degreeOf (some j) ≤ (X none + X (some j) :
        MvPolynomial (Option σ) K).degreeOf (some j) ∧
      ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)).Separable := by
  let F : MvPolynomial (Option σ) K := X none + X (some j)
  have hFmap : optionEquivLeft K σ F =
      Polynomial.X + Polynomial.C (X j) := by
    simp only [F, map_add, optionEquivLeft_X_none, optionEquivLeft_X_some]
  have hPirr : Irreducible (Polynomial.X + Polynomial.C (X j) :
      Polynomial (MvPolynomial σ K)) := by
    simpa only [map_neg, sub_neg_eq_add] using
      Polynomial.irreducible_X_sub_C (-(X j : MvPolynomial σ K))
  have hFirr : Irreducible F := by
    have h := hPirr.map (optionEquivLeft K σ).symm
    rw [← hFmap] at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  have hFrootdeg : F.degreeOf none = 1 := by
    rw [← natDegree_optionEquivLeft K, hFmap]
    simp
  obtain ⟨e, G, hroot, hGder, hGdeg, hGirr, hGother, _hprimitive, _hmapirr,
      _hmapder, hmapsep, _hmapdeg⟩ :=
    exists_frobeniusFactor (K := K) (L := L) p (by rw [hFrootdeg]; exact Nat.zero_lt_one) hFirr
  refine ⟨e, G, ?_, hGder, ?_, hGirr, ?_, hmapsep⟩
  · simpa only [F] using hroot
  · simpa only [F, hFrootdeg] using hGdeg
  · simpa only [F] using hGother j

end

end MvPolynomial
