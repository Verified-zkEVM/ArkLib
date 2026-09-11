/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.EquationBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.DirectJetList

/-! # Whole-list bounds from constant received-curve certificates -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative

universe u

open Classical in
/-- A constant received-curve certificate gives the complete polynomial list together with the
actual separant stages that bound it.

The Taylor cutoff is chosen as `max k (d + 1)`, so the positive-characteristic guard depends on
the actual message degree `k - 1`, differential order `d`, and certified jet cap `ν`, rather than
on an ambient interpolation degree.  No positivity assumption is needed: in particular, the
statement retains the `k = 0`, `d = 0`, and `ν = 0` cases. -/
theorem exists_closePolynomial_list_of_curve_certificate_actualStages
    {F : Type u} [Field F] {n k A d ν H : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{u, u} F A k 0 ν d H domain
      (fun i ↦ Polynomial.C (received i)))
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (k - 1) (max d ν) < ringChar F) :
    let Q : DifferentialPolynomial F d :=
      MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q
    let K := max k (d + 1)
    ∃ stages terminal, ∃ list : Finset F[X],
      SymbolicSeparantChain.Chain Q stages terminal ∧
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
  obtain ⟨hQ, hdegree, hsound⟩ :=
    cert.specialization_sound (RingHom.id F) (0 : F)
  have hK : d < K := by
    dsimp only [K]
    omega
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hweight : SymbolicSeparantChain.jetWeight Q ≤ ν := by
    change Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ ν
    rw [← jetTotalDegree_eq_weightedTotalDegree_elim]
    exact hdegree
  have hchar' : ringChar F = 0 ∨
      max (K - 1) (SymbolicSeparantChain.jetWeight Q) < ringChar F := by
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
        IsAgreementSolution domain received k A P) ↔
      P.degree < k ∧ A ≤ (polynomialAgreementSet domain received P).card
    constructor
    · rintro ⟨_, hP⟩
      exact hP
    · intro hP
      have hP' : IsAgreementSolution domain received k A P := by
        exact hP
      refine ⟨?_, hP'⟩
      apply hsound (polynomialAgreementSet domain received P) P hP'.1 hP'.2
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
/-- Compatibility projection of the actual-stage certificate theorem to the common coarse
direct-jet bound.  The Taylor cutoff remains `max k (d + 1)`, independently of any ambient
interpolation degree. -/
theorem close_list_bound_of_curve_certificate_directJetCoarse
    {F : Type u} [Field F] {n k A d ν H : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{u, u} F A k 0 ν d H domain
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
  have hweight : SymbolicSeparantChain.jetWeight Q ≤ ν := by
    obtain ⟨_, hdegree, _⟩ := cert.specialization_sound (RingHom.id F) (0 : F)
    change Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ ν
    rw [← jetTotalDegree_eq_weightedTotalDegree_elim]
    exact hdegree
  have hcommon := directJetStageCharge_sum_le_commonOrderSum
    hchain n A k K ν hAn hweight
  have hcoarse := directJetCommonOrderSum_le_coarse n A k K ν d hk hkA hAn
  constructor
  · rw [← hlist]
    exact list.finite_toSet
  · rw [← hlist]
    simpa only [Set.ncard_coe_finset] using hactual.trans (hcommon.trans hcoarse)

open Classical in
/-- Specialize one universally nonzero symbolic equation to explain the entire close list. -/
theorem close_list_bound_of_curve_certificate_of_jetCharacteristic {F : Type u} [Field F]
    {n k A K d ν H : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{u, u} F A k 0 ν d H domain
      (fun i ↦ Polynomial.C (received i)))
    (hk : 0 < k) (hkK : k ≤ K) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hδ : 0 < δ)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  obtain ⟨hQ, hdegree, hsound⟩ := cert.specialization_sound (RingHom.id F) (0 : F)
  apply close_list_bound_of_equation domain received _ hQ hdegree hk hkK hdK hKn
    hkA hAn hν hδ hgap hchar
  intro P hP
  apply hsound (Finset.univ.filter fun i ↦ P.eval (domain i) = received i) P hP.1 hP.2
  intro i hi
  simpa only [RingHom.id_apply, Polynomial.eval₂_C] using
    (Finset.mem_filter.mp hi).2

end ReedSolomon
