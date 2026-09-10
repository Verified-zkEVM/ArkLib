/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.AgreementGeometry


/-! # Actual polynomial solutions in the regular Taylor geometry -/

@[expose] public section

open PolynomialDifferential


noncomputable section
open MvPolynomial
open AffineHilbert
namespace ReedSolomon.HiddenDerivative
variable {F : Type*} [Field F] {r : ℕ}

/-- A finite family of regular polynomial solutions has a common regular center
in every infinite field. -/
theorem exists_common_regular_center [Infinite F]
    (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F))
    (hS : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0) :
    ∃ center : F, ∀ P ∈ S,
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0 := by
  classical
  let R := ∏ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P
  have hR : R ≠ 0 := Finset.prod_ne_zero_iff.mpr hS
  have hex : ∃ center : F, R.eval center ≠ 0 := by
    by_contra! h
    apply hR
    apply Polynomial.funext
    simpa using h
  obtain ⟨center, hc⟩ := hex
  refine ⟨center, ?_⟩
  have hc' : ∀ P ∈ S,
      (differentialSpecialization (separant Q (Fin.last r)) P).eval center ≠ 0 := by
    simpa only [R, Polynomial.eval_prod, Finset.prod_ne_zero_iff] using hc
  intro P hP
  rw [← eval_differentialSpecialization]
  exact hc' P hP

/-- The regular initial jet distinguishes bounded actual solutions using exactly
the invertible Taylor pivots needed by the rational chart. -/
theorem polynomialJet_injective_on_regular_solutions
    (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    {P P' : Polynomial F} (hP : P.degree < K) (hP' : P'.degree < K)
    (hsol : differentialSpecialization Q P = 0)
    (hsol' : differentialSpecialization Q P' = 0)
    (hsep : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (hsep' : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P') ≠ 0)
    (hjet : polynomialJet (d := r) center P = polynomialJet center P') : P = P' := by
  apply Polynomial.taylor_injective center
  ext i
  by_cases hi : i < K
  · have heq := congrFun (congrArg (rationalTaylorMap center Q K) hjet) ⟨i, hi⟩
    rw [rationalTaylorMap_eq_solution center Q P hsol hsep K hbin,
      rationalTaylorMap_eq_solution center Q P' hsol' hsep' K hbin] at heq
    exact heq
  · rw [Polynomial.coeff_eq_zero_of_degree_lt, Polynomial.coeff_eq_zero_of_degree_lt]
    · simpa only [Polynomial.degree_taylor] using hP'.trans_le (Nat.cast_le.mpr (by omega))
    · simpa only [Polynomial.degree_taylor] using hP.trans_le (Nat.cast_le.mpr (by omega))

/-- All high coefficient equations hold at the jet of an actual low-degree solution. -/
theorem polynomialJet_mem_highTaylorCuts
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (P : Polynomial F) (hP : P.degree < k)
    (hsol : differentialSpecialization Q P = 0)
    (hsep : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    polynomialJet center P ∈ zeroLocus F (highTaylorCutsIdeal center Q K k) := by
  change highTaylorCutsIdeal center Q K k ≤ RingHom.ker (aeval (polynomialJet center P))
  apply Ideal.span_le.mpr
  rintro _ ⟨l, rfl⟩
  change aeval _ _ = 0
  rw [commonTaylorNumerator_solution center Q P hsol hsep K hbin]
  have hc : (Polynomial.taylor center P).coeff l.val.val = 0 := by
    apply Polynomial.coeff_eq_zero_of_degree_lt
    simpa only [Polynomial.degree_taylor] using hP.trans_le (Nat.cast_le.mpr l.property)
  rw [hc, mul_zero]

open Classical in
/-- Initial jets of a finite regular solution family preserve its cardinality. -/
theorem card_image_polynomialJet_regular
    (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (S : Finset (Polynomial F))
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : ∀ P ∈ S, P.degree < K)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S,
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    (S.image (polynomialJet (d := r) center)).card = S.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro P hP P' hP' heq
  exact polynomialJet_injective_on_regular_solutions center Q K hbin
    (hdegree P hP) (hdegree P' hP') (hsol P hP) (hsol P' hP')
    (hsep P hP) (hsep P' hP') heq

/-- A regular solution lies on the initial hypersurface and on every high cut. -/
theorem polynomialJet_mem_regular_solution_locus
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (P : Polynomial F) (hP : P.degree < k)
    (hsol : differentialSpecialization Q P = 0)
    (hsep : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    polynomialJet center P ∈ principalOpenZeroLocus
      (Ideal.span {initialJetEquation center Q} ⊔ highTaylorCutsIdeal center Q K k)
      (initialJetSeparant center Q) := by
  refine ⟨?_, ?_⟩
  · change Ideal.span {initialJetEquation center Q} ⊔ highTaylorCutsIdeal center Q K k ≤
      RingHom.ker (aeval (polynomialJet center P))
    apply sup_le
    · apply Ideal.span_le.mpr
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact initialJetEquation_solution center Q P hsol
    · exact polynomialJet_mem_highTaylorCuts center Q K k P hP hsol hsep hbin
  · rwa [aeval_initialJetSeparant]

/-- Received-word agreement is exactly a vanishing chart cut at a regular solution. -/
theorem polynomialJet_agreement_cut_iff
    (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (P : Polynomial F) (hP : P.degree < K)
    (hsol : differentialSpecialization Q P = 0)
    (hsep : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) (x y : F) :
    aeval (polynomialJet center P) (taylorAgreementEquation center Q K x y) = 0 ↔
      P.eval x = y := by
  rw [taylorAgreementEquation_solution center Q P hsol hsep K hP hbin x y,
    mul_eq_zero]
  have hs : aeval (polynomialJet center P) (initialJetSeparant center Q) ≠ 0 := by
    rwa [aeval_initialJetSeparant]
  exact or_iff_right (pow_ne_zero _ hs) |>.trans sub_eq_zero

end ReedSolomon.HiddenDerivative
