/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorSpecialization
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Cuts


/-!
# Symbolic equations on the Taylor chart

Initial and agreement equations retain the coefficient algebra. Specialization gives the
literal field-valued cuts, and their regular points reconstruct actual degree-bounded
polynomials. The common numerator identities cover every reconstructed coefficient, without
assuming that the reconstructed polynomial is a differential solution.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] {r : ℕ}

/-- The initial equation with its coefficient algebra retained. -/
def initialJetEquationOver (center : A) (Q : DifferentialPolynomial A r) :
    MvPolynomial (Fin (r + 1)) A :=
  aeval (fun i ↦ i.elim (C center) X) Q

/-- The initial equation commutes with arbitrary coefficient specialization. -/
theorem map_initialJetEquationOver (f : A →+* B) (center : A)
    (Q : DifferentialPolynomial A r) :
    MvPolynomial.map f (initialJetEquationOver center Q) =
      initialJetEquationOver (f center) (MvPolynomial.map f Q) := by
  simp only [initialJetEquationOver, aeval_def, algebraMap_eq, map_eval₂]
  congr 1
  funext i
  cases i <;> simp

variable [Algebra F A]

/-- A cleared agreement equation retaining all coefficient parameters. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (x y : A) (τ : ℕ := 2 * K) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumeratorOver (F := F) center Q K l (τ := τ)) -
      C y * initialJetSeparantOver center Q ^ τ

/-- Cleared agreement equations commute with coefficient-algebra specialization. -/
theorem map_taylorAgreementEquationOver [Algebra F B] (φ : A →ₐ[F] B)
    (center : A) (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A)
    (τ : ℕ := 2 * K) :
    MvPolynomial.map φ.toRingHom
        (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquationOver (F := F) (φ center) (MvPolynomial.map φ.toRingHom Q)
        K (φ x) (φ y) (τ := τ) := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_C, map_pow,
    map_commonTaylorNumeratorOver, map_initialJetSeparantOver]
  rfl

variable {E : Type*} [Field E] [Algebra F E]

/-- Field specialization recovers the original initial equation. -/
theorem map_initialJetEquationOver_eq (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) :
    MvPolynomial.map φ.toRingHom (initialJetEquationOver center Q) =
      initialJetEquation (φ center) (MvPolynomial.map φ.toRingHom Q) := by
  exact map_initialJetEquationOver φ.toRingHom center Q

/-- Field specialization recovers the original separant polynomial. -/
theorem map_initialJetSeparantOver_eq (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) :
    MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q) =
      initialJetSeparant (φ center) (MvPolynomial.map φ.toRingHom Q) := by
  exact map_initialJetSeparantOver φ.toRingHom center Q

/-- Field specialization recovers the original agreement cut, even at singular points. -/
theorem map_taylorAgreementEquationOver_eq (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A)
    (τ : ℕ := 2 * K) :
    MvPolynomial.map φ.toRingHom
        (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquation (φ center) (MvPolynomial.map φ.toRingHom Q)
        K (φ x) (φ y) (τ := τ) := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_C, map_pow,
    map_commonTaylorNumeratorOver_eq, map_initialJetSeparantOver_eq,
    taylorAgreementEquation]
  rfl

/-- Evaluating the symbolic initial equation is the actual specialized jet evaluation. -/
theorem aeval_map_initialJetEquationOver (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (jet : Fin (r + 1) → E) :
    aeval jet (MvPolynomial.map φ.toRingHom (initialJetEquationOver center Q)) =
      jetEvaluation (MvPolynomial.map φ.toRingHom Q) (φ center) jet := by
  rw [map_initialJetEquationOver_eq, aeval_initialJetEquation]

/-- At a regular specialized point, a sufficiently padded agreement cut measures the
reconstructed discrepancy. -/
theorem aeval_map_taylorAgreementEquationOver_of_exponent
    (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (x y : A) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) =
        aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ^
          τ *
            (Polynomial.eval (φ x)
              (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet) -
                φ y) := by
  rw [map_initialJetSeparantOver_eq] at hS ⊢
  rw [map_taylorAgreementEquationOver_eq (τ := τ)]
  exact aeval_taylorAgreementEquation_of_exponent _ _ _ τ hτ _ hS _ _

/-- At a regular specialized point, default agreement cuts measure the reconstructed discrepancy. -/
theorem aeval_map_taylorAgreementEquationOver (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (x y : A) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y)) =
        aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ^
          (2 * K) *
            (Polynomial.eval (φ x)
              (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet) -
                φ y) := by
  exact aeval_map_taylorAgreementEquationOver_of_exponent φ center Q K (2 * K)
    (taylorExponentSufficient_two_mul r K) jet hS x y

/-- A regular symbolic agreement cut vanishes exactly at the received value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (x y : A) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) = 0 ↔
      Polynomial.eval (φ x)
        (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet) =
          φ y := by
  rw [aeval_map_taylorAgreementEquationOver_of_exponent φ center Q K τ hτ jet hS]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- A regular default symbolic agreement cut vanishes exactly at the received value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (x y : A) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y)) = 0 ↔
      Polynomial.eval (φ x)
        (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet) =
          φ y := by
  rw [aeval_map_taylorAgreementEquationOver φ center Q K jet hS]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- Vanishing sufficiently padded high symbolic numerators imposes the actual message-degree
restriction. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ))) = 0) :
    (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet).degree <
      k := by
  rw [map_initialJetSeparantOver_eq] at hS
  apply degree_rationalTaylorPolynomial_lt_of_high_cuts_and_exponent
    _ _ K k τ hτ jet hS
  intro l hl
  simpa only [map_commonTaylorNumeratorOver_eq (τ := τ)] using hhigh l hl

/-- Vanishing default high symbolic numerators imposes the actual message-degree restriction. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K k : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver (F := F) center Q K l)) = 0) :
    (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet).degree <
      k := by
  exact degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
    φ center Q K k (2 * K) (taylorExponentSufficient_two_mul r K) jet hS hhigh

/-- Every common numerator gives the corresponding actual coefficient of the reconstructed
polynomial after clearing the denominator. No differential-solution premise is used. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (l : Fin K) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ))) =
      aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ^ τ *
          Polynomial.coeff (Polynomial.taylor (φ center)
            (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet))
              l.val := by
  rw [map_initialJetSeparantOver_eq] at hS ⊢
  rw [map_commonTaylorNumeratorOver_eq (τ := τ),
    aeval_commonTaylorNumerator_of_exponent _ _ _ _ τ hτ _ hS]
  rw [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix, if_pos l.isLt]

/-- Every default common numerator gives the corresponding reconstructed coefficient. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (l : Fin K) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver (F := F) center Q K l)) =
      aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ^
        (2 * K) *
          Polynomial.coeff (Polynomial.taylor (φ center)
            (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K jet))
              l.val := by
  rw [map_initialJetSeparantOver_eq] at hS ⊢
  rw [map_commonTaylorNumeratorOver_eq, aeval_commonTaylorNumerator _ _ _ _ _ hS]
  rw [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix, if_pos l.isLt]

end

end ReedSolomon.HiddenDerivative
