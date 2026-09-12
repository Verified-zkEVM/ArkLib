/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import Mathlib.RingTheory.AdjoinRoot

/-! # Algebraic laws for canonical tower reduction -/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerRepresentation

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Every coefficient is reduced, including coefficients beyond the stored array. -/
theorem coeff_reduceBase {G : CPolynomial F} (hG : G.monic)
    (p : CPolynomial (CPolynomial F)) (i : ℕ) :
    (reduceBase G p).coeff i = (p.coeff i).modByMonic G := by
  rw [reduceBase, FirstOrderNormDecoder.D5.coeff_reduceFiberCoefficients]
  split_ifs with hi
  · rfl
  · have hz : p.coeff i = 0 := by
      by_contra hn
      have := CPolynomial.le_natDegree_of_ne_zero hn
      omega
    rw [hz]
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG, CPolynomial.toPoly_zero]

/-- Coefficient reduction fixes representatives below the base degree. -/
theorem reduceBase_eq_self {G : CPolynomial F} (hG : G.monic)
    {p : CPolynomial (CPolynomial F)} (hp : BaseReduced G p) : reduceBase G p = p := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  rw [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly, coeff_reduceBase hG]
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG]
  exact (Polynomial.modByMonic_eq_self_iff ((CPolynomial.monic_toPoly_iff _).mp hG)).mpr (hp i)

/-- Canonical tower reduction fixes every bounded representative. -/
theorem reduceElement_eq_self {G : CPolynomial F} (hG : G.monic)
    {h p : CPolynomial (CPolynomial F)} (hh : h.monic)
    (hp : ElementReduced G h p) : reduceElement G h p = p := by
  have hm : p.modByMonic h = p := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hh]
    exact (Polynomial.modByMonic_eq_self_iff ((CPolynomial.monic_toPoly_iff _).mp hh)).mpr hp.1
  rw [reduceElement, hm, reduceBase_eq_self hG hp.2]

/-- Repeated canonical reduction has no further effect. -/
theorem reduceElement_reduceElement {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (p : CPolynomial (CPolynomial F)) :
    reduceElement G h (reduceElement G h p) = reduceElement G h p :=
  reduceElement_eq_self hG hh (elementReduced_reduceElement hG hh hhpos p)

/-- Base reduction is additive. -/
theorem reduceBase_add {G : CPolynomial F} (hG : G.monic)
    (p q : CPolynomial (CPolynomial F)) :
    reduceBase G (p + q) = reduceBase G p + reduceBase G q := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  simp only [CPolynomial.toPoly_add, Polynomial.coeff_add, ← CPolynomial.coeff_toPoly,
    coeff_reduceBase hG]
  apply CPolynomial.toPoly_injective
  simp [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG,
    CPolynomial.coeff_add, CPolynomial.toPoly_add, Polynomial.add_modByMonic]

/-- Tower reduction is additive. -/
theorem reduceElement_add {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (p q : CPolynomial (CPolynomial F)) :
    reduceElement G h (p + q) = reduceElement G h p + reduceElement G h q := by
  have hm : (p + q).modByMonic h = p.modByMonic h + q.modByMonic h := by
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hh,
      CPolynomial.toPoly_add, Polynomial.add_modByMonic]
  rw [reduceElement, hm, reduceBase_add hG]
  rfl

/-- The coefficient quotient map used only to prove normalization laws. -/
noncomputable def baseQuotientMap (G : CPolynomial F) :
    CPolynomial F →+* AdjoinRoot G.toPoly :=
  (AdjoinRoot.mk G.toPoly).comp CPolynomial.ringEquiv.toRingHom

/-- Interpret an outer polynomial over the base quotient ring. -/
noncomputable def quotientPolynomial (G : CPolynomial F)
    (p : CPolynomial (CPolynomial F)) : Polynomial (AdjoinRoot G.toPoly) :=
  p.toPoly.map (baseQuotientMap G)

/-- Quotient interpretation is unchanged by base normalization. -/
theorem quotientPolynomial_reduceBase {G : CPolynomial F} (hG : G.monic)
    (p : CPolynomial (CPolynomial F)) :
    quotientPolynomial G (reduceBase G p) = quotientPolynomial G p := by
  apply Polynomial.ext
  intro i
  simp only [quotientPolynomial, Polynomial.coeff_map, ← CPolynomial.coeff_toPoly,
    coeff_reduceBase hG]
  simp only [baseQuotientMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, CPolynomial.ringEquiv_apply]
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG]
  simpa only [AdjoinRoot.modByMonicHom_mk] using
    AdjoinRoot.mk_leftInverse ((CPolynomial.monic_toPoly_iff _).mp hG)
      (AdjoinRoot.mk G.toPoly (p.coeff i).toPoly)

/-- Base-reduced representatives are determined by their coefficient quotient image. -/
theorem reduceBase_eq_of_quotientPolynomial_eq {G : CPolynomial F} (hG : G.monic)
    {p q : CPolynomial (CPolynomial F)}
    (he : quotientPolynomial G p = quotientPolynomial G q) : reduceBase G p = reduceBase G q := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  rw [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
    coeff_reduceBase hG, coeff_reduceBase hG]
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG,
    CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG]
  have hc := congrArg (fun p => p.coeff i) he
  simpa [quotientPolynomial, baseQuotientMap, ← CPolynomial.coeff_toPoly] using
    congrArg (AdjoinRoot.modByMonicHom ((CPolynomial.monic_toPoly_iff _).mp hG)) hc

/-- Tower normalization agrees with monic remainder in the coefficient quotient. -/
theorem quotientPolynomial_reduceElement {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (p : CPolynomial (CPolynomial F)) :
    quotientPolynomial G (reduceElement G h p) =
      quotientPolynomial G p %ₘ quotientPolynomial G h := by
  rw [reduceElement, quotientPolynomial_reduceBase hG]
  simp only [quotientPolynomial, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hh,
    Polynomial.map_modByMonic _ ((CPolynomial.monic_toPoly_iff _).mp hh)]

/-- Multiplication can normalize both inputs before reducing the product. -/
theorem reduceElement_mul_reduce {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (p q : CPolynomial (CPolynomial F)) :
    reduceElement G h (p * q) =
      reduceElement G h (reduceElement G h p * reduceElement G h q) := by
  apply reduceBase_eq_of_quotientPolynomial_eq hG
  simp only [quotientPolynomial, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hh,
    Polynomial.map_modByMonic _ ((CPolynomial.monic_toPoly_iff _).mp hh),
    CPolynomial.toPoly_mul, Polynomial.map_mul]
  change (quotientPolynomial G p * quotientPolynomial G q) %ₘ quotientPolynomial G h =
    (quotientPolynomial G (reduceElement G h p) *
      quotientPolynomial G (reduceElement G h q)) %ₘ quotientPolynomial G h
  rw [quotientPolynomial_reduceElement hG hh, quotientPolynomial_reduceElement hG hh]
  exact Polynomial.mul_modByMonic _ _ _

/-- Base normalization commutes with multiplication by a field scalar. -/
theorem reduceBase_C_mul {G : CPolynomial F} (hG : G.monic)
    (a : F) (p : CPolynomial (CPolynomial F)) :
    reduceBase G (CPolynomial.C (CPolynomial.C a) * p) =
      CPolynomial.C (CPolynomial.C a) * reduceBase G p := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  simp only [← CPolynomial.coeff_toPoly, coeff_reduceBase hG, CPolynomial.coeff_C_mul]
  apply CPolynomial.toPoly_injective
  simp only [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG,
    CPolynomial.toPoly_mul, CPolynomial.toPoly_C, ← Polynomial.smul_eq_C_mul,
    Polynomial.smul_modByMonic]

/-- Tower normalization commutes with multiplication by a field scalar. -/
theorem reduceElement_C_mul {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (a : F) (p : CPolynomial (CPolynomial F)) :
    reduceElement G h (CPolynomial.C (CPolynomial.C a) * p) =
      CPolynomial.C (CPolynomial.C a) * reduceElement G h p := by
  have hm : (CPolynomial.C (CPolynomial.C a) * p).modByMonic h =
      CPolynomial.C (CPolynomial.C a) * p.modByMonic h := by
    apply CPolynomial.toPoly_injective
    simp only [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hh,
      CPolynomial.toPoly_mul, CPolynomial.toPoly_C, ← Polynomial.smul_eq_C_mul,
      Polynomial.smul_modByMonic]
  rw [reduceElement, hm, reduceBase_C_mul hG]
  rfl

end ReedSolomon.ListDecoding.TowerRepresentation
