/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorChart

/-!
# Symbolic equations on the rational Taylor chart

The initial equation and separant specialize along coefficient maps. Agreement equations can
also be formed over an algebra, then mapped to a field where they describe the reconstructed
polynomial. Vanishing symbolic high cuts bounds the degree of that reconstruction, and each
symbolic common numerator evaluates to its corresponding Taylor coefficient after clearing the
separant denominator.

## Main statements

* `map_initialJetEquation` and `aeval_map_initialJetEquation` describe coefficient maps and
  evaluation of the initial equation.
* `taylorAgreementEquationOver` and its map theorem define symbolic agreement equations over an
  algebra and specialize them to field-valued cuts.
* `commonTaylorNumeratorOver_eq` and `map_commonTaylorNumeratorOver_eq` bridge algebra-valued
  numerators to their field-valued counterparts.
* `aeval_map_taylorAgreementEquationOver` characterizes regular agreement cuts, while
  `degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts` bounds the reconstruction degree.
* `aeval_map_commonTaylorNumeratorOver_reconstruction` identifies symbolic common numerators
  with coefficients of the reconstructed polynomial.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {r : ℕ}

variable {F : Type*} [Field F] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

/-- The agreement equation over an `F`-algebra, with every common numerator using the same
separant exponent. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (x y : A) (τ : ℕ := 2 * K) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumeratorOver F center Q τ l.val) - C y * initialJetSeparant center Q ^ τ

/-- Coefficient specialization maps an algebra-valued agreement equation to the corresponding
agreement equation. -/
theorem map_taylorAgreementEquationOver (φ : A →ₐ[F] B) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A) (τ : ℕ := 2 * K) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquationOver (F := F) (φ center) (map φ.toRingHom Q) K
        (φ x) (φ y) (τ := τ) := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_C, map_pow,
    map_commonTaylorNumeratorOver, map_initialJetSeparant]
  rfl

/-- Specializing an algebra-valued agreement equation to a field gives the field-valued cut. -/
theorem map_taylorAgreementEquationOver_eq {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A)
    (τ : ℕ := 2 * K) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquation (φ center) (map φ.toRingHom Q) K τ (φ x) (φ y) := by
  rw [map_taylorAgreementEquationOver (τ := τ)]
  simp only [taylorAgreementEquationOver, taylorAgreementEquation,
    commonTaylorNumeratorOver_eq]

/-- At a regular jet, a sufficiently padded symbolic agreement equation evaluates to the
separant power times the discrepancy of the reconstructed polynomial. -/
theorem aeval_map_taylorAgreementEquationOver_of_exponent {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) =
        aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
          ((rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) - φ y) := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS ⊢
  rw [map_taylorAgreementEquationOver_eq (τ := τ)]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    aeval_taylorAgreementEquation (φ center) (map φ.toRingHom Q) hτ jet hS (φ x) (φ y)

/-- At a regular jet, a default symbolic agreement equation evaluates to the separant power
times the discrepancy of the reconstructed polynomial. -/
theorem aeval_map_taylorAgreementEquationOver {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y)) =
      aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ (2 * K) *
        ((rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) - φ y) := by
  exact aeval_map_taylorAgreementEquationOver_of_exponent φ center Q K (2 * K)
    (taylorExponentSufficient_two_mul r K) jet hS x y

/-- A regular symbolic agreement equation vanishes exactly when the reconstructed polynomial
takes the received value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) = 0 ↔
      (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) = φ y := by
  rw [aeval_map_taylorAgreementEquationOver_of_exponent φ center Q K τ hτ jet hS]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- A regular default symbolic agreement equation vanishes exactly when the reconstructed
polynomial takes the received value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y)) = 0 ↔
      (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) = φ y := by
  rw [aeval_map_taylorAgreementEquationOver φ center Q K jet hS]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- Vanishing symbolic high cuts with a sufficient exponent bounds the degree of the
reconstructed polynomial. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K k τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).degree < k := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS
  refine degree_rationalTaylorPolynomial_lt (φ center) (map φ.toRingHom Q) hτ k jet hS ?_
  intro l hkl hlK
  simpa only [map_commonTaylorNumeratorOver_eq] using hhigh ⟨l, hlK⟩ hkl

/-- Vanishing default symbolic high cuts bounds the degree of the reconstructed polynomial. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K k : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (map φ.toRingHom (commonTaylorNumeratorOver F center Q (2 * K) l.val)) = 0) :
    (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).degree < k := by
  exact degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent φ center Q K k
    (2 * K) (taylorExponentSufficient_two_mul r K) jet hS hhigh

/-- Every symbolic common numerator evaluates to the cleared Taylor coefficient of the
reconstructed polynomial when its exponent is sufficient. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (l : Fin K) :
    aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q τ l.val)) =
      aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff l.val := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS ⊢
  have hS' : aeval jet (initialJetSeparant (φ center) (map φ.toRingHom Q)) ≠ 0 := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hS
  rw [map_commonTaylorNumeratorOver_eq,
    aeval_commonTaylorNumerator (φ center) (map φ.toRingHom Q) jet (hτ l) hS']
  rw [coeff_taylor_rationalTaylorPolynomial]
  simp [l.isLt]

/-- Every default symbolic common numerator evaluates to the corresponding cleared Taylor
coefficient of the reconstructed polynomial. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (l : Fin K) :
    aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q (2 * K) l.val)) =
      aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ (2 * K) *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff l.val := by
  exact aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ center Q K (2 * K)
    (taylorExponentSufficient_two_mul r K) jet hS l

end

end PolynomialDifferential
