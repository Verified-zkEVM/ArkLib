/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FractionFieldResultant
public import ArkLib.ToMathlib.MvPolynomial.PDeriv
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Separability of a radical primitive part

The product of the distinct irreducible factors of positive degree in a distinguished variable
is separable over the fraction field of the remaining polynomial variables when the characteristic
is zero or exceeds the degree of the original polynomial in that variable. This holds over a UFD
of coefficients. The ordinary-root polynomial is the presentation at `none` through
`MvPolynomial.optionEquivLeft`, and its derivative resultant is nonzero.

## Main statements

* `MvPolynomial.ordinaryRootPolynomial` and `MvPolynomial.natDegree_ordinaryRootPolynomial`:
  the positive-degree factor product as a polynomial in the distinguished variable.
* `MvPolynomial.radicalPrimPart_map_optionEquivLeft_fractionRing_separable`: separability of the
  radical primitive part over the fraction field.
* `MvPolynomial.ordinaryRootPolynomial_map_fractionRing_separable`: the ordinary-root instance.
* `Polynomial.resultant_derivative_ne_zero_ordinaryRootPolynomial`: nonvanishing of its padded
  derivative resultant.

## References

* [DKT26]
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R σ : Type*} [CommRing R] [UniqueFactorizationMonoid R]

/-- The positive-`none`-degree factor product, written as a univariate polynomial in `X none`. -/
def ordinaryRootPolynomial (Q : MvPolynomial (Option σ) R) :
    Polynomial (MvPolynomial σ R) :=
  optionEquivLeft R σ (radicalPrimPart none Q)

/-- The univariate degree of the ordinary-root polynomial is its degree in `X none`. -/
theorem natDegree_ordinaryRootPolynomial (Q : MvPolynomial (Option σ) R) :
    (ordinaryRootPolynomial Q).natDegree = degreeOf none (radicalPrimPart none Q) := by
  rw [ordinaryRootPolynomial, natDegree_optionEquivLeft]

variable {L : Type*} [IsDomain R] [Field L] [Algebra (MvPolynomial σ R) L]
  [IsFractionRing (MvPolynomial σ R) L]

open Polynomial

/-- The product of the distinct positive-`none`-degree factors of `Q` is separable over the
fraction field of the coefficient polynomials when the characteristic is zero or exceeds the
`none`-degree of `Q`. -/
theorem radicalPrimPart_map_optionEquivLeft_fractionRing_separable
    (Q : MvPolynomial (Option σ) R)
    (hchar : ringChar R = 0 ∨ degreeOf none Q < ringChar R) :
    ((optionEquivLeft R σ (radicalPrimPart none Q)).map
      (algebraMap (MvPolynomial σ R) L)).Separable := by
  classical
  let s := positiveDegreeFactorClasses none Q
  let A : Associates (MvPolynomial (Option σ) R) → Polynomial (MvPolynomial σ R) :=
    fun a ↦ optionEquivLeft R σ a.rep
  let f : Associates (MvPolynomial (Option σ) R) → Polynomial L :=
    fun a ↦ (A a).map (algebraMap (MvPolynomial σ R) L)
  have hAirr (a) (ha : a ∈ s) : Irreducible (A a) := by
    exact (irreducible_rep_of_mem_positiveDegreeFactorClasses ha).map
      (optionEquivLeft R σ)
  have hAdegree (a) (ha : a ∈ s) : 0 < (A a).natDegree := by
    simpa only [A, natDegree_optionEquivLeft] using
      (mem_positiveDegreeFactorClasses.mp ha).2
  have hAprimitive (a) (ha : a ∈ s) : (A a).IsPrimitive :=
    (hAirr a ha).isPrimitive (Nat.ne_of_gt (hAdegree a ha))
  have hfirr (a) (ha : a ∈ s) : Irreducible (f a) := by
    exact (hAprimitive a ha).irreducible_iff_irreducible_map_fraction_map.mp
      (hAirr a ha)
  have hfactorDegree (a) (ha : a ∈ s) : degreeOf none a.rep ≤ degreeOf none Q := by
    have hsum := sum_degreeOf_positiveDegreeFactorClasses_le none Q
    exact (Finset.single_le_sum
      (fun b _hb ↦ Nat.zero_le (degreeOf none b.rep)) ha).trans hsum
  have hfactorCast (a) (ha : a ∈ s) : (degreeOf none a.rep : R) ≠ 0 := by
    exact natCast_ne_zero_of_ringChar_eq_zero_or_lt hchar
      (mem_positiveDegreeFactorClasses.mp ha).2 (hfactorDegree a ha)
  have hfseparable (a) (ha : a ∈ s) : (f a).Separable := by
    rw [separable_iff_derivative_ne_zero (hfirr a ha)]
    change ((A a).map (algebraMap (MvPolynomial σ R) L)).derivative ≠ 0
    rw [derivative_map]
    apply (Polynomial.map_ne_zero_iff
      (IsFractionRing.injective (MvPolynomial σ R) L)).mpr
    change (optionEquivLeft R σ a.rep).derivative ≠ 0
    rw [← optionEquivLeft_pderiv_none]
    exact (map_ne_zero_iff (optionEquivLeft R σ)
      (optionEquivLeft R σ).injective).mpr
        (pderiv_ne_zero_of_natCast_ne_zero none a.rep (hfactorCast a ha))
  have hfpairwise (a) (ha : a ∈ s) (b) (hb : b ∈ s) (hab : a ≠ b) :
      IsCoprime (f a) (f b) := by
    rw [(hfirr a ha).coprime_iff_not_dvd]
    intro hdvd
    have hAdvd : A a ∣ A b :=
      ((hAprimitive a ha).dvd_iff_fraction_map_dvd_fraction_map L).mpr hdvd
    have hassocA : Associated (A a) (A b) :=
      (hAirr a ha).associated_of_dvd (hAirr b hb) hAdvd
    have hassocP : Associated a.rep b.rep := by
      simpa only [A, AlgEquiv.symm_apply_apply] using
        hassocA.map (optionEquivLeft R σ).symm
    have hclass : a = b := by
      calc
        a = Associates.mk a.rep := (Associates.mk_rep a).symm
        _ = Associates.mk b.rep :=
          Associates.mk_eq_mk_iff_associated.mpr hassocP
        _ = b := Associates.mk_rep b
    exact hab hclass
  have hsep : (∏ a ∈ s, f a).Separable := separable_prod' hfpairwise hfseparable
  have hoption : optionEquivLeft R σ (∏ a ∈ s, a.rep) = ∏ a ∈ s, A a := by
    simpa only [A] using map_prod (optionEquivLeft R σ) (fun a ↦ a.rep) s
  change (Polynomial.map (algebraMap (MvPolynomial σ R) L)
    (optionEquivLeft R σ (∏ a ∈ s, a.rep))).Separable
  rw [hoption]
  have hmap : Polynomial.map (algebraMap (MvPolynomial σ R) L) (∏ a ∈ s, A a) =
      ∏ a ∈ s, Polynomial.map (algebraMap (MvPolynomial σ R) L) (A a) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.map_mul, ih]
  rw [hmap]
  simpa only [f] using hsep

/-- The ordinary-root polynomial is separable over the fraction field when the characteristic is
zero or exceeds the degree of its defining polynomial in `X none`. -/
theorem ordinaryRootPolynomial_map_fractionRing_separable
    (Q : MvPolynomial (Option σ) R)
    (hchar : ringChar R = 0 ∨ degreeOf none Q < ringChar R) :
    ((ordinaryRootPolynomial Q).map
      (algebraMap (MvPolynomial σ R) L)).Separable := by
  simpa only [ordinaryRootPolynomial] using
    radicalPrimPart_map_optionEquivLeft_fractionRing_separable Q hchar

end

end MvPolynomial

namespace Polynomial

variable {R σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- The original-degree derivative resultant of the ordinary-root polynomial is nonzero. -/
theorem resultant_derivative_ne_zero_ordinaryRootPolynomial
    (Q : MvPolynomial (Option σ) R)
    (hchar : ringChar R = 0 ∨ MvPolynomial.degreeOf none Q < ringChar R) :
    resultant (MvPolynomial.ordinaryRootPolynomial Q)
      (MvPolynomial.ordinaryRootPolynomial Q).derivative
      (MvPolynomial.ordinaryRootPolynomial Q).natDegree
      ((MvPolynomial.ordinaryRootPolynomial Q).natDegree - 1) ≠ 0 :=
  resultant_derivative_ne_zero_of_separable_map_fractionField
    (K := FractionRing (MvPolynomial σ R))
    (MvPolynomial.ordinaryRootPolynomial Q)
    (MvPolynomial.ordinaryRootPolynomial_map_fractionRing_separable
      (L := FractionRing (MvPolynomial σ R)) Q hchar)

end Polynomial
