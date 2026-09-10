/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart
public import Mathlib.LinearAlgebra.Lagrange


/-!
# Concrete cuts on the rational Taylor chart

High-coefficient equations first impose the actual message degree. Then agreement at `k`
distinct points determines at most one jet on the regular chart. All equations here are
the literal common-denominator polynomials; the argument does not assume geometric degree
or Bezout infrastructure.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {r : ℕ}

/-- Reconstruct a polynomial from the first `K` rational Taylor coefficients. -/
def rationalTaylorPolynomial (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (jet : Fin (r + 1) → F) : Polynomial F :=
  centeredCoefficientPrefix center (rationalTaylorCoefficient center Q jet) K

/-- The reconstructed polynomial retains its input jet when the prefix is long enough. -/
theorem polynomialJet_rationalTaylorPolynomial (center : F) (Q : DifferentialPolynomial F r)
    (K : ℕ) (hK : r < K) (jet : Fin (r + 1) → F) :
    polynomialJet (d := r) center (rationalTaylorPolynomial center Q K jet) = jet := by
  rw [rationalTaylorPolynomial, polynomialJet_centeredCoefficientPrefix center _ K hK]
  funext j
  exact rationalTaylorCoefficient_initial center Q jet j

/-- The polynomial reconstruction is injective on initial jets. -/
theorem rationalTaylorPolynomial_injective (center : F) (Q : DifferentialPolynomial F r)
    (K : ℕ) (hK : r < K) : Function.Injective (rationalTaylorPolynomial center Q K) := by
  intro jet jet' h
  have he := congrArg (polynomialJet (d := r) center) h
  simpa only [polynomialJet_rationalTaylorPolynomial center Q K hK] using he

/-- On the principal open, high common-numerator cuts impose the actual message degree. -/
theorem degree_rationalTaylorPolynomial_lt_of_high_cuts_and_exponent
    (center : F) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → F) (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (commonTaylorNumerator center Q K l (τ := τ)) = 0) :
    (rationalTaylorPolynomial center Q K jet).degree < k := by
  rw [← Polynomial.degree_taylor _ center, Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  change (Polynomial.taylor center (centeredCoefficientPrefix center
    (rationalTaylorCoefficient center Q jet) K)).coeff i = 0
  rw [coeff_taylor_centeredCoefficientPrefix]
  split_ifs with hiK
  · have hc := hhigh ⟨i, hiK⟩ hi
    rw [aeval_commonTaylorNumerator_of_exponent center Q jet K τ hτ ⟨i, hiK⟩ hS] at hc
    exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ hS)
  · rfl

/-- On the principal open, default high common-numerator cuts impose the message degree. -/
theorem degree_rationalTaylorPolynomial_lt_of_high_cuts
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (jet : Fin (r + 1) → F) (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (commonTaylorNumerator center Q K l) = 0) :
    (rationalTaylorPolynomial center Q K jet).degree < k := by
  exact degree_rationalTaylorPolynomial_lt_of_high_cuts_and_exponent
    center Q K k (2 * K) (taylorExponentSufficient_two_mul r K) jet hS hhigh

/-- Agreement cuts represent actual polynomial evaluation at every regular chart point,
without assuming that the reconstructed polynomial solves the differential equation. -/
theorem aeval_taylorAgreementEquation_of_exponent
    (center : F) (Q : DifferentialPolynomial F r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → F) (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (x y : F) :
    aeval jet (taylorAgreementEquation center Q K x y (τ := τ)) =
      aeval jet (initialJetSeparant center Q) ^ τ *
        ((rationalTaylorPolynomial center Q K jet).eval x - y) := by
  rw [taylorAgreementEquation, map_sub, map_sum]
  simp only [map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, map_pow]
  simp_rw [aeval_commonTaylorNumerator_of_exponent center Q jet K τ hτ _ hS]
  have he := congrArg (fun p : Polynomial F ↦ p.eval (x - center))
    (taylor_centeredCoefficientPrefix center (rationalTaylorCoefficient center Q jet) K)
  have hsum : (∑ l : Fin K, rationalTaylorCoefficient center Q jet l.val *
      (x - center) ^ l.val) = (rationalTaylorPolynomial center Q K jet).eval x := by
    simpa [rationalTaylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      Polynomial.taylor_eval] using he.symm
  have hreorder : (∑ l : Fin K, (x - center) ^ l.val *
      (aeval jet (initialJetSeparant center Q) ^ τ *
        rationalTaylorCoefficient center Q jet l.val)) =
      aeval jet (initialJetSeparant center Q) ^ τ *
        (∑ l : Fin K, rationalTaylorCoefficient center Q jet l.val * (x - center) ^ l.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hreorder, hsum]
  ring

/-- Default agreement cuts represent polynomial evaluation at every regular chart point. -/
theorem aeval_taylorAgreementEquation (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (jet : Fin (r + 1) → F) (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (x y : F) :
    aeval jet (taylorAgreementEquation center Q K x y) =
      aeval jet (initialJetSeparant center Q) ^ (2 * K) *
        ((rationalTaylorPolynomial center Q K jet).eval x - y) := by
  exact aeval_taylorAgreementEquation_of_exponent center Q K (2 * K)
    (taylorExponentSufficient_two_mul r K) jet hS x y

/-- A cleared agreement equation vanishes exactly at the prescribed received value. -/
theorem taylorAgreementEquation_eq_zero_iff_of_exponent
    (center : F) (Q : DifferentialPolynomial F r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (x y : F) :
    aeval jet (taylorAgreementEquation center Q K x y (τ := τ)) = 0 ↔
      (rationalTaylorPolynomial center Q K jet).eval x = y := by
  rw [aeval_taylorAgreementEquation_of_exponent center Q K τ hτ jet hS x y]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- A default cleared agreement equation vanishes exactly at the prescribed value. -/
theorem taylorAgreementEquation_eq_zero_iff (center : F) (Q : DifferentialPolynomial F r)
    (K : ℕ) (jet : Fin (r + 1) → F) (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (x y : F) :
    aeval jet (taylorAgreementEquation center Q K x y) = 0 ↔
      (rationalTaylorPolynomial center Q K jet).eval x = y := by
  rw [aeval_taylorAgreementEquation center Q K jet hS x y]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- After the high-coefficient cuts, `k` distinct agreement cuts leave at most one regular jet.
This is the concrete uniqueness fact used to rule out positive-dimensional retained components. -/
theorem eq_of_high_cuts_and_agreement_cuts (center : F) (Q : DifferentialPolynomial F r)
    (K k : ℕ) (hK : r < K) (domain : Fin k ↪ F) (received : Fin k → F)
    (jet jet' : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hS' : aeval jet' (initialJetSeparant center Q) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (commonTaylorNumerator center Q K l) = 0)
    (hhigh' : ∀ l : Fin K, k ≤ l.val → aeval jet' (commonTaylorNumerator center Q K l) = 0)
    (hcut : ∀ i, aeval jet (taylorAgreementEquation center Q K (domain i) (received i)) = 0)
    (hcut' : ∀ i, aeval jet' (taylorAgreementEquation center Q K (domain i) (received i)) = 0) :
    jet = jet' := by
  classical
  apply rationalTaylorPolynomial_injective center Q K hK
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := domain) (s := Finset.univ)
  · exact domain.injective.injOn
  · simpa using degree_rationalTaylorPolynomial_lt_of_high_cuts center Q K k jet hS hhigh
  · simpa using degree_rationalTaylorPolynomial_lt_of_high_cuts center Q K k jet' hS' hhigh'
  · intro i _
    exact ((taylorAgreementEquation_eq_zero_iff center Q K jet hS _ _).mp (hcut i)).trans
      ((taylorAgreementEquation_eq_zero_iff center Q K jet' hS' _ _).mp (hcut' i)).symm

end

end ReedSolomon.HiddenDerivative
