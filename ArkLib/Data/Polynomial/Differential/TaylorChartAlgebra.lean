/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorChart

/-!
# Rational Taylor chart equations over coefficient algebras

The rational Taylor chart can be written over a coefficient algebra whose parameters are later
specialized into a field. This file defines the symbolic agreement equation and relates its zeros,
the high coefficient cuts, and the cleared numerators to the reconstructed polynomial after
specialization.

## Main statements

* `PolynomialDifferential.taylorAgreementEquationOver` and
  `aeval_map_taylorAgreementEquationOver_eq_zero_iff`: symbolic agreement equations and their
  specialized meaning.
* `degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts`: symbolic high cuts bound the
  degree of the specialized reconstruction.
* `aeval_map_commonTaylorNumeratorOver_reconstruction`: each symbolic common numerator gives
  the corresponding coefficient of the reconstruction.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] {r : ℕ}

/-- The agreement equation over a coefficient algebra, with exponent `τ` and default `2 * K`.
Its coefficients retain the parameters in `A` until a later algebra map specializes them. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (x y : A) (τ : ℕ := 2 * K) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumeratorOver F center Q τ l.val) - C y * initialJetSeparant center Q ^ τ

/-- Coefficient algebra maps commute with symbolic agreement equations. -/
theorem map_taylorAgreementEquationOver [Algebra F B] (φ : A →ₐ[F] B) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A) (τ : ℕ := 2 * K) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y τ) =
      taylorAgreementEquationOver (F := F) (φ center) (map φ.toRingHom Q) K
        (φ x) (φ y) τ := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_C, map_pow,
    map_commonTaylorNumeratorOver, map_initialJetSeparant]
  rfl

/-- Over a field extension, a symbolic common numerator specializes to the field-level numerator. -/
theorem map_commonTaylorNumeratorOver_eq {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (τ l : ℕ) :
    map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l) =
      commonTaylorNumerator (φ center) (map φ.toRingHom Q) τ l := by
  rw [map_commonTaylorNumeratorOver]
  simp [commonTaylorNumeratorOver, commonTaylorNumerator, rationalTaylorNumeratorOver_eq]

/-- Over a field extension, the symbolic agreement equation specializes to the field equation. -/
theorem map_taylorAgreementEquationOver_eq {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K τ : ℕ) (x y : A) :
    map φ.toRingHom
        (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquation (φ center) (map φ.toRingHom Q) K τ (φ x) (φ y) := by
  rw [map_taylorAgreementEquationOver (φ := φ) (center := center) (Q := Q) (K := K)
    (x := x) (y := y) (τ := τ)]
  simp [taylorAgreementEquationOver, taylorAgreementEquation, commonTaylorNumeratorOver,
    commonTaylorNumerator, rationalTaylorNumeratorOver_eq]

/-- For a sufficient exponent and a nonzero separant, a symbolic agreement equation vanishes
exactly when the specialized reconstruction takes the prescribed value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
    {E : Type*} [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) = 0 ↔
      (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) = φ y := by
  have hS' : aeval jet (initialJetSeparant (φ center) (map φ.toRingHom Q)) ≠ 0 := by
    simpa only [map_initialJetSeparant, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hS
  rw [map_taylorAgreementEquationOver_eq]
  exact taylorAgreementEquation_eq_zero_iff (φ center) (map φ.toRingHom Q) hτ jet hS' (φ x)
    (φ y)

/-- With the default exponent `2 * K`, a symbolic agreement equation vanishes exactly when the
specialized reconstruction takes the prescribed value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff
    {E : Type*} [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y)) = 0 ↔
      (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) = φ y := by
  exact aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ center Q K (2 * K)
    (taylorExponentSufficient_two_mul r K) jet hS x y

/-- Symbolic high cuts with sufficient exponent bound the degree of the specialized
reconstruction. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
    {E : Type*} [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).degree < k := by
  have hS' : aeval jet (initialJetSeparant (φ center) (map φ.toRingHom Q)) ≠ 0 := by
    simpa only [map_initialJetSeparant, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hS
  apply degree_rationalTaylorPolynomial_lt (φ center) (map φ.toRingHom Q) hτ k jet hS'
  intro l hkl hlK
  simpa only [map_commonTaylorNumeratorOver_eq] using hhigh ⟨l, hlK⟩ hkl

/-- With the default exponent `2 * K`, symbolic high cuts bound the degree of the specialized
reconstruction. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts
    {E : Type*} [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K k : ℕ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q (2 * K) l.val)) = 0) :
    (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).degree < k := by
  exact degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent φ center Q K k
    (2 * K) (taylorExponentSufficient_two_mul r K) jet hS hhigh

/-- A symbolic common numerator evaluates to the corresponding Taylor coefficient of the
specialized reconstruction after clearing its denominator. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction
    {E : Type*} [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (l : Fin K) :
    aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q (2 * K) l.val)) =
      aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ (2 * K) *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff l.val := by
  have hS' : aeval jet (initialJetSeparant (φ center) (map φ.toRingHom Q)) ≠ 0 := by
    simpa only [map_initialJetSeparant, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hS
  rw [map_commonTaylorNumeratorOver_eq, map_initialJetSeparant]
  rw [aeval_commonTaylorNumerator (φ center) (map φ.toRingHom Q) jet
    (taylorExponentSufficient_two_mul r K l) hS']
  rw [coeff_taylor_rationalTaylorPolynomial]
  simp [l.isLt]

end

end PolynomialDifferential
