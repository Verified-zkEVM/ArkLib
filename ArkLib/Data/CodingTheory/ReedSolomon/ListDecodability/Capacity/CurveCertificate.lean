/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.DirectJetList
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate

/-!
# Whole-list bounds from received-curve certificates

A symbolic received-curve certificate specializes to a nonzero differential equation that
vanishes on every polynomial in the close list. The equation gives both an actual separant-chain
bound and the coarser direct-jet estimate for the complete list.

## Main statements

* exists_closePolynomial_list_of_curve_certificate_actualStages identifies the complete close
  list with a finite list bounded by its actual separant stages.
* close_list_bound_of_curve_certificate_directJetCoarse gives the coarse direct-jet bound.
* close_list_bound_of_curve_certificate_of_jetCharacteristic gives the agreement-gap bound
  under a characteristic hypothesis.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative

universe u

variable {F : Type u} [Field F]

open Classical in
/-- A constant received-curve certificate gives the complete close list and its actual
separant-stage bound. -/
theorem exists_closePolynomial_list_of_curve_certificate_actualStages
    {n k A d ν H : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{0, u} A k 0 ν d H domain
      (fun i ↦ Polynomial.C (received i)))
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (k - 1) (max d ν) < ringChar F) :
    let Q : DifferentialPolynomial F d :=
      MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q
    let K := max k (d + 1)
    ∃ stages terminal, ∃ list : Finset F[X],
      SeparantChain Q stages terminal ∧
      (list : Set F[X]) = closePolynomialSet domain received k A ∧
      (∀ P, P ∈ list ↔ P.degree < k ∧
        A ≤ (polynomialAgreementSet domain received P).card) ∧
      (list.card : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum := by
  classical
  dsimp only
  let Q : DifferentialPolynomial F d :=
    MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q
  let K := max k (d + 1)
  obtain ⟨hQ, hdegree, hsound⟩ := cert.specialization_sound (RingHom.id F) (0 : F)
  have hK : d < K := by
    dsimp only [K]
    omega
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hweight : jetTotalDegree Q ≤ ν := hdegree
  have hchar' : ringChar F = 0 ∨
      max (K - 1) (jetTotalDegree Q) < ringChar F := by
    apply hchar.imp_right
    intro hp
    have hkChar : k - 1 < ringChar F :=
      (Nat.le_max_left (k - 1) (max d ν)).trans_lt hp
    have hdνChar : max d ν < ringChar F :=
      (Nat.le_max_right (k - 1) (max d ν)).trans_lt hp
    have hdChar : d < ringChar F := (Nat.le_max_left d ν).trans_lt hdνChar
    have hνChar : ν < ringChar F := (Nat.le_max_right d ν).trans_lt hdνChar
    apply max_lt
    · dsimp only [K]
      omega
    · exact hweight.trans_lt hνChar
  obtain ⟨stages, terminal, hchain, hfinite, hbound⟩ :=
    exists_chain_directJetAgreementSolutions_finite_and_ncard_le
      Q hQ K k hK hkK domain received hkA hAn hchar'
  have hsolution (P : F[X]) :
      P ∈ directJetAgreementSolutions Q domain received k A ↔
        P ∈ closePolynomialSet domain received k A := by
    change (differentialSpecialization Q P = 0 ∧
        P.degree < k ∧ A ≤ (polynomialAgreementSet domain received P).card) ↔
      P.degree < k ∧ A ≤ (polynomialAgreementSet domain received P).card
    constructor
    · rintro ⟨_, hP⟩
      exact hP
    · intro hP
      refine ⟨?_, hP⟩
      let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
      apply hsound indices P hP.1 hP.2
      intro i hi
      simpa only [RingHom.id_apply, Polynomial.eval₂_C] using
        (Finset.mem_filter.mp hi).2
  let list := hfinite.toFinset
  refine ⟨stages, terminal, list, hchain, ?_, ?_, ?_⟩
  · ext P
    change P ∈ list ↔ P ∈ closePolynomialSet domain received k A
    rw [show P ∈ list ↔ P ∈ directJetAgreementSolutions Q domain received k A by
      exact hfinite.mem_toFinset]
    exact hsolution P
  · intro P
    rw [show P ∈ list ↔ P ∈ directJetAgreementSolutions Q domain received k A by
      exact hfinite.mem_toFinset]
    rw [hsolution]
    rfl
  · rw [Set.ncard_eq_toFinset_card _ hfinite] at hbound
    change (hfinite.toFinset.card : ℚ) ≤ _
    exact hbound

open Classical in
/-- A constant received-curve certificate gives the complete-list bound from actual
direct-jet stages and their common-order estimate. -/
theorem close_list_bound_of_curve_certificate_directJetCoarse
    {n k A d ν H : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{0, u} A k 0 ν d H domain
      (fun i ↦ Polynomial.C (received i)))
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (k - 1) (max d ν) < ringChar F) :
    let K := max k (d + 1)
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℚ) ≤
        (ν : ℚ) ^ 2 *
          ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  classical
  dsimp only
  let Q : DifferentialPolynomial F d :=
    MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q
  let K := max k (d + 1)
  obtain ⟨stages, terminal, list, hchain, hlist, _hmem, hactual⟩ :=
    exists_closePolynomial_list_of_curve_certificate_actualStages
      domain received cert hkA hAn hchar
  have hweight : jetTotalDegree Q ≤ ν :=
    (cert.specialization_sound (RingHom.id F) (0 : F)).2.1
  have hcommon := directJetStageCharge_sum_le_commonOrderSum
    hchain n A k K ν hAn hweight
  have hcoarse := directJetCommonOrderSum_le_coarse n A k K ν d hk hkA hAn
  constructor
  · rw [← hlist]
    exact list.finite_toSet
  · rw [← hlist]
    simpa only [Set.ncard_coe_finset] using hactual.trans (hcommon.trans hcoarse)

open Classical in
/-- A constant received-curve certificate gives the agreement-gap bound when the characteristic
exceeds the Taylor cutoff and jet-degree bounds. -/
theorem close_list_bound_of_curve_certificate_of_jetCharacteristic
    {n k A K d ν H : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{0, u} A k 0 ν d H domain
      (fun i ↦ Polynomial.C (received i)))
    (hk : 0 < k) (hkK : k ≤ K) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hδ : 0 < δ)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  obtain ⟨hQ, hdegree, hsound⟩ := cert.specialization_sound (RingHom.id F) (0 : F)
  apply closePolynomialSet_finite_and_ncard_le_of_differential_equation_and_gap
    (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q)
    K k ν hdK hkK hQ hdegree domain received hk hkA hAn hKn hν hδ hgap hchar
  intro P hP
  let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
  apply hsound indices P hP.1 hP.2
  intro i hi
  simpa only [RingHom.id_apply, Polynomial.eval₂_C] using
    (Finset.mem_filter.mp hi).2

end ReedSolomon
