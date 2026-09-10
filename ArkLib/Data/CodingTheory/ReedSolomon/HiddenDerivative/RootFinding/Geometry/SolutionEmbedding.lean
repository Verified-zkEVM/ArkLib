/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SolutionExtension


/-! # A cardinality-preserving embedding of regular solutions into the Taylor chart -/

@[expose] public section

open PolynomialDifferential


noncomputable section
open MvPolynomial AffineHilbert
namespace ReedSolomon.HiddenDerivative
variable {F E : Type*} [Field F] [Field E] [Infinite E] {r : ℕ}

open Classical in
/-- Every finite regular solution family embeds faithfully into one regular Taylor
chart over an infinite extension, preserving each candidate's received-word agreement. -/
theorem exists_regular_solution_jet_family_of_exponent
    (f : F →+* E) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K)
    (S : Finset (Polynomial F)) {n A : ℕ} (domain received : Fin n → F)
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    ∃ (center : E) (J : Finset (Fin (r + 1) → E)), J.card = S.card ∧
      ∀ jet ∈ J,
        aeval jet (initialJetEquation center (MvPolynomial.map f Q)) = 0 ∧
        aeval jet (initialJetSeparant center (MvPolynomial.map f Q)) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval jet
            (commonTaylorNumerator center (MvPolynomial.map f Q) K l (τ := τ)) = 0) ∧
        A ≤ (Finset.univ.filter fun i ↦
          aeval jet (taylorAgreementEquation center (MvPolynomial.map f Q) K
            (f (domain i)) (f (received i)) (τ := τ)) = 0).card := by
  classical
  let QE := MvPolynomial.map f Q
  let SE := S.image (Polynomial.map f)
  have hSE := mapped_regular_solution_family f Q S k hdegree hsol hsep
  have hbinE := map_binomial_pivots f K hbin
  obtain ⟨center, hc⟩ := exists_common_regular_center QE SE (fun P hP ↦ (hSE P hP).2.2)
  refine ⟨center, SE.image (polynomialJet (d := r) center), ?_, ?_⟩
  · rw [card_image_polynomialJet_regular center QE K SE hbinE
      (fun P hP ↦ (hSE P hP).1.trans_le (Nat.cast_le.mpr hkK))
      (fun P hP ↦ (hSE P hP).2.1) hc]
    exact card_image_polynomial_map f S
  · intro jet hjet
    obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hjet
    have hp := hSE P hPS
    have hs := hc P hPS
    refine ⟨initialJetEquation_solution center QE P hp.2.1, ?_, ?_, ?_⟩
    · rwa [aeval_initialJetSeparant]
    · intro l hl
      rw [commonTaylorNumerator_solution_of_exponent center QE P hp.2.1 hs
        K τ hτ hbinE]
      have hcoeff : (Polynomial.taylor center P).coeff l.val = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simpa only [Polynomial.degree_taylor] using hp.1.trans_le (Nat.cast_le.mpr hl)
      rw [hcoeff, mul_zero]
    · have heq : (Finset.univ.filter fun i ↦
          aeval (polynomialJet center P)
            (taylorAgreementEquation center QE K (f (domain i)) (f (received i))
              (τ := τ)) = 0) =
          (Finset.univ.filter fun i ↦ P.eval (f (domain i)) = f (received i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [taylorAgreementEquation_solution_of_exponent center QE P hp.2.1 hs
          K τ hτ (hp.1.trans_le (Nat.cast_le.mpr hkK)) hbinE]
        have hS : aeval (polynomialJet center P) (initialJetSeparant center QE) ≠ 0 := by
          rwa [aeval_initialJetSeparant]
        simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]
      rw [heq]
      obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hPS
      rw [mapped_agreement_count]
      exact hagree P0 hP0

open Classical in
/-- The default `2K` chart gives the original regular-solution embedding. -/
theorem exists_regular_solution_jet_family
    (f : F →+* E) (Q : DifferentialPolynomial F r) (K k : ℕ) (hkK : k ≤ K)
    (S : Finset (Polynomial F)) {n A : ℕ} (domain received : Fin n → F)
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    ∃ (center : E) (J : Finset (Fin (r + 1) → E)), J.card = S.card ∧
      ∀ jet ∈ J,
        aeval jet (initialJetEquation center (MvPolynomial.map f Q)) = 0 ∧
        aeval jet (initialJetSeparant center (MvPolynomial.map f Q)) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (commonTaylorNumerator center (MvPolynomial.map f Q) K l) = 0) ∧
        A ≤ (Finset.univ.filter fun i ↦
          aeval jet (taylorAgreementEquation center (MvPolynomial.map f Q) K
            (f (domain i)) (f (received i))) = 0).card := by
  exact exists_regular_solution_jet_family_of_exponent f Q K k (2 * K)
    (taylorExponentSufficient_two_mul r K) hkK S domain received
      hdegree hsol hsep hbin hagree

omit [Infinite E] in
/-- Coefficient extension preserves the exact total jet degree used by the geometric bound. -/
theorem totalJetDegree_map_eq (f : F →+* E) (Q : DifferentialPolynomial F r) :
    (MvPolynomial.map f Q).weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) =
      Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) := by
  unfold MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective _ f.injective]

end ReedSolomon.HiddenDerivative
