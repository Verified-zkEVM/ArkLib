/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.RadicalSplit.Separable
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Acceptance tests for radical primitive-part separability

The zero polynomial has an empty positive-degree factor product, so its ordinary-root polynomial
is `1`. In characteristic two, a linear root polynomial meets the strict degree guard and is
separable over the coefficient fraction field. The polynomial `X^2` in characteristic two marks
the guard boundary: its derivative vanishes. The final example recovers the derivative-first
resultant form from the general resultant theorem.
-/

open MvPolynomial Polynomial UniqueFactorizationMonoid

namespace RadicalSplitSeparableTest

section CharacteristicTwo

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The zero polynomial has no positive-degree factors, so the root polynomial is `1`. -/
example : ordinaryRootPolynomial (0 : MvPolynomial (Option Unit) ℚ) = 1 := by
  simp [ordinaryRootPolynomial, radicalPrimPart]

/-- A linear root polynomial is separable in characteristic two. -/
example : ((ordinaryRootPolynomial
    (X none : MvPolynomial (Option Unit) (ZMod 2))).map
      (algebraMap (MvPolynomial Unit (ZMod 2))
        (FractionRing (MvPolynomial Unit (ZMod 2))))).Separable := by
  apply ordinaryRootPolynomial_map_fractionRing_separable
  norm_num [degreeOf_X, ZMod.ringChar_zmod_n]

/-- In characteristic two, the derivative of a degree-two monomial vanishes at the guard
boundary. -/
example : pderiv none (X none ^ 2 : MvPolynomial (Option Unit) (ZMod 2)) = 0 := by
  rw [pderiv_pow, pderiv_X_self]
  simp only [Nat.reduceSub, pow_one, mul_one]
  have htwoCoeff : (2 : ZMod 2) = 0 := by decide
  change MvPolynomial.C (2 : ZMod 2) * X none = 0
  rw [htwoCoeff, MvPolynomial.C_0, zero_mul]

/-- The strict characteristic guard fails at that degree-two boundary. -/
example : ¬ (ringChar (ZMod 2) = 0 ∨
    degreeOf none (X none ^ 2 : MvPolynomial (Option Unit) (ZMod 2)) < ringChar (ZMod 2)) := by
  norm_num [degreeOf_X, ZMod.ringChar_zmod_n]

/-- At the guard boundary, `X none ^ 2 + X (some ())` is irreducible and inseparable over the
coefficient fraction field, so its distinct positive-root product is not separable either. -/
example :
    ¬ ((ordinaryRootPolynomial
      (X (some ()) + X none ^ 2 : MvPolynomial (Option Unit) (ZMod 2))).map
        (algebraMap (MvPolynomial Unit (ZMod 2))
          (FractionRing (MvPolynomial Unit (ZMod 2))))).Separable := by
  let Q : MvPolynomial (Option Unit) (ZMod 2) := X (some ()) + X none ^ 2
  have hQirr : Irreducible Q := by
    simpa [Q] using MvPolynomial.irreducible_mul_X_add
      (1 : MvPolynomial (Option Unit) (ZMod 2)) (X none ^ 2) (some ()) one_ne_zero
      (by simp)
      (by
        intro hi
        have hi' : some () ∈ (X none : MvPolynomial (Option Unit) (ZMod 2)).vars :=
          vars_pow _ _ hi
        rw [vars_X] at hi'
        simp at hi')
      isRelPrime_one_left
  have hQ : Q ≠ 0 := hQirr.ne_zero
  have hdegQ : degreeOf none Q = 2 := by
    rw [← natDegree_optionEquivLeft (ZMod 2)]
    simp [Q]
  have hrepAssoc : Associated (Associates.mk Q).rep Q := by
    rw [← Associates.mk_eq_mk_iff_associated, Associates.mk_rep]
  have hrepDegree : degreeOf none (Associates.mk Q).rep = 2 := by
    have hadd : ∀ x y : MvPolynomial (Option Unit) (ZMod 2), x ≠ 0 → y ≠ 0 →
        degreeOf none (x * y) = degreeOf none x + degreeOf none y :=
      fun _ _ hx hy => degreeOf_mul_eq hx hy
    rw [map_eq_of_associated hadd hQ hrepAssoc, hdegQ]
  have hclasses : positiveDegreeFactorClasses none Q = {Associates.mk Q} := by
    rw [positiveDegreeFactorClasses, ← pow_one Q,
      primeFactors_mk_pow_of_prime hQirr.prime one_ne_zero]
    simp [hrepDegree]
  have hpart : radicalPrimPart none Q = (Associates.mk Q).rep := by
    rw [radicalPrimPart, hclasses, Finset.prod_singleton]
  have hpartAssoc : Associated (radicalPrimPart none Q) Q := by
    rw [hpart]
    exact hrepAssoc
  have hder : pderiv none Q = 0 := by
    dsimp [Q]
    rw [map_add, pderiv_X_of_ne (show (some () : Option Unit) ≠ none by decide),
      pderiv_pow, pderiv_X_self]
    simp only [Nat.reduceSub, pow_one, mul_one, zero_add]
    change MvPolynomial.C (2 : ZMod 2) * X none = 0
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, MvPolynomial.C_0, zero_mul]
  let f := algebraMap (MvPolynomial Unit (ZMod 2))
    (FractionRing (MvPolynomial Unit (ZMod 2)))
  let B := (optionEquivLeft (ZMod 2) Unit Q).map f
  have hBirr : Irreducible B := by
    have hA : Irreducible (optionEquivLeft (ZMod 2) Unit Q) :=
      hQirr.map (optionEquivLeft (ZMod 2) Unit)
    have hApos : 0 < (optionEquivLeft (ZMod 2) Unit Q).natDegree := by
      rw [natDegree_optionEquivLeft, hdegQ]
      omega
    exact (hA.isPrimitive hApos.ne').irreducible_iff_irreducible_map_fraction_map.mp hA
  have hBder : B.derivative = 0 := by
    dsimp [B, f]
    rw [derivative_map, ← optionEquivLeft_pderiv_none, hder]
    simp
  have hBnotsep : ¬ B.Separable := by
    rw [separable_iff_derivative_ne_zero hBirr, hBder]
    simp
  have hmapAssoc : Associated
      ((ordinaryRootPolynomial Q).map f) B := by
    change Associated
      ((Polynomial.map f (optionEquivLeft (ZMod 2) Unit (radicalPrimPart none Q)))) B
    exact Associated.map (Polynomial.mapRingHom f)
      (Associated.map (optionEquivLeft (ZMod 2) Unit) hpartAssoc)
  exact fun hsep => hBnotsep (hmapAssoc.separable_iff.mp hsep)

end CharacteristicTwo

/-- The derivative-first padded order follows by swapping resultant arguments and degrees. -/
example {F σ : Type*} [Field F] (Q : MvPolynomial (Option σ) F) (_hQ : Q ≠ 0)
    (hchar : ringChar F = 0 ∨ degreeOf none Q < ringChar F) :
    resultant (ordinaryRootPolynomial Q).derivative (ordinaryRootPolynomial Q)
      ((ordinaryRootPolynomial Q).natDegree - 1) (ordinaryRootPolynomial Q).natDegree ≠ 0 := by
  rw [resultant_comm_sub_one]
  exact resultant_derivative_ne_zero_ordinaryRootPolynomial Q hchar

end RadicalSplitSeparableTest
