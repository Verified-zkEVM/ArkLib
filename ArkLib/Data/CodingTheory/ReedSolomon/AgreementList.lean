/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Finset.Powerset
/-!
# Finiteness and an incidence bound for Reed--Solomon agreement lists

Over an arbitrary field, the degree-`< k` polynomials agreeing with a received
word in at least `A ≥ k` positions form a finite set.  Double-counting their
`k`-element agreement samples gives the elementary bound
`list.card * A.choose k ≤ n.choose k`.

This is a supporting field-independent incidence estimate, not the all-rate list
size bound.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The set of degree-`< k` polynomials with at least `A` agreements. -/
def closePolynomialSet {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : Set F[X] :=
  {P | P.degree < k ∧ A ≤ (polynomialAgreementSet domain received P).card}

private lemma polynomial_eq_of_agrees_on
    {F : Type*} [Field F] [DecidableEq F] {n k : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (T : Finset (Fin n))
    (hTCard : T.card = k) (P Q : F[X]) (hPDegree : P.degree < k)
    (hQDegree : Q.degree < k)
    (hPAgreement : T ⊆ polynomialAgreementSet domain received P)
    (hQAgreement : T ⊆ polynomialAgreementSet domain received Q) : P = Q := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq T domain.injective.injOn
  · simpa [hTCard] using hPDegree
  · simpa [hTCard] using hQDegree
  · intro i hi
    rw [(Finset.mem_filter.mp (hPAgreement hi)).2,
      (Finset.mem_filter.mp (hQAgreement hi)).2]

/-- The close polynomials can be collected in a finite list satisfying the sharp
sample-incidence inequality.  No finiteness assumption on the field is used. -/
theorem exists_closePolynomial_finset_with_incidence_bound
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card * A.choose k ≤ n.choose k := by
  classical
  let samples := (Finset.univ : Finset (Fin n)).powersetCard k
  let candidates : Finset F[X] :=
    samples.image fun T ↦ Lagrange.interpolate T domain received
  let list := candidates.filter fun P ↦ P ∈ closePolynomialSet domain received k A
  have hlist : ∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A := by
    intro P
    constructor
    · intro hP
      exact (Finset.mem_filter.mp hP).2
    · intro hP
      obtain ⟨T, hTSubset, hTCard⟩ := Finset.exists_subset_card_eq
        (hAk.trans hP.2)
      have hTMem : T ∈ samples := by
        exact Finset.mem_powersetCard.mpr
          ⟨hTSubset.trans (Finset.subset_univ _), hTCard⟩
      have hinterpDegree : (Lagrange.interpolate T domain received).degree < k := by
        simpa [hTCard] using Lagrange.degree_interpolate_lt
          (s := T) (v := domain) (r := received) domain.injective.injOn
      have hinterpAgreement :
          T ⊆ polynomialAgreementSet domain received
            (Lagrange.interpolate T domain received) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
          Lagrange.eval_interpolate_at_node received domain.injective.injOn hi⟩
      have hPEq : P = Lagrange.interpolate T domain received :=
        polynomial_eq_of_agrees_on domain received T hTCard P _ hP.1
          hinterpDegree hTSubset hinterpAgreement
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨T, hTMem, hPEq.symm⟩, hP⟩
  let incidence :=
    list.sigma fun P ↦ (polynomialAgreementSet domain received P).powersetCard k
  have hincidenceLower : list.card * A.choose k ≤ incidence.card := by
    simp only [incidence, Finset.card_sigma]
    calc
      list.card * A.choose k = ∑ _P ∈ list, A.choose k := by simp
      _ ≤ ∑ P ∈ list,
          (polynomialAgreementSet domain received P).card.choose k := by
        apply Finset.sum_le_sum
        intro P hP
        exact Nat.choose_le_choose k (hlist P |>.mp hP).2
      _ = ∑ P ∈ list,
          ((polynomialAgreementSet domain received P).powersetCard k).card := by
        apply Finset.sum_congr rfl
        intro P _
        rw [Finset.card_powersetCard]
  have hincidenceUpper : incidence.card ≤ samples.card := by
    apply Finset.card_le_card_of_injOn Sigma.snd
    · intro x hx
      simp only [incidence] at hx
      obtain ⟨_, hxsample⟩ := Finset.mem_sigma.mp hx
      exact Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_powersetCard.mp hxsample).1.trans (Finset.subset_univ _),
          (Finset.mem_powersetCard.mp hxsample).2⟩
    · intro x hx y hy hxy
      simp only [incidence] at hx hy
      obtain ⟨hxlist, hxsample⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hylist, hysample⟩ := Finset.mem_sigma.mp hy
      have hxset := Finset.mem_powersetCard.mp hxsample
      have hyset := Finset.mem_powersetCard.mp hysample
      have hpoly : x.1 = y.1 := by
        apply polynomial_eq_of_agrees_on domain received x.2 hxset.2
        · exact (hlist x.1 |>.mp hxlist).1
        · exact (hlist y.1 |>.mp hylist).1
        · exact hxset.1
        · rw [hxy]
          exact hyset.1
      cases x with
      | mk xP xT =>
          cases y with
          | mk yP yT =>
              change xP = yP at hpoly
              change xT = yT at hxy
              subst yP
              subst yT
              rfl
  refine ⟨list, hlist, hincidenceLower.trans ?_⟩
  calc
    incidence.card ≤ samples.card := hincidenceUpper
    _ = n.choose k := by simp [samples]

/-- The close degree-`< k` polynomial set is finite over an arbitrary field when
the agreement threshold is at least `k`. -/
theorem closePolynomialSet_finite
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    (closePolynomialSet domain received k A).Finite := by
  obtain ⟨list, hlist, _⟩ :=
    exists_closePolynomial_finset_with_incidence_bound domain received hAk
  rw [show closePolynomialSet domain received k A = (list : Set F[X]) by
    ext P
    exact (hlist P).symm]
  exact list.finite_toSet

end

/-! ## Degree-bounded message lists over general index types -/

open ListDecoding

/-- The set of all degree-bounded polynomials meeting the absolute agreement threshold. -/
def agreeingPolynomials {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim minAgreement : ℕ) (received : index → F) :
    Set (MessagePolynomial F messageDim) :=
  {p | minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received}

/-- Raising the required number of agreements can only remove candidate polynomials. -/
theorem agreeingPolynomials_antitone {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] (domain : index ↪ F) (messageDim : ℕ) (received : index → F) :
    Antitone (fun A => agreeingPolynomials domain messageDim A received) := by
  intro A B hAB p hp
  exact hAB.trans hp

/-- A finite set of agreeing messages has a duplicate-free polynomial list with the same
cardinality. The degree condition is explicit and includes the zero polynomial.
This is classical finite-set extraction, not an algorithm or a complexity estimate. -/
theorem exists_finset_polynomial_list {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] (domain : index ↪ F) (k A : ℕ) (received : index → F)
    (hfinite : (agreeingPolynomials domain k A received).Finite) :
    ∃ list : Finset (Polynomial F),
      (∀ P, P ∈ list ↔ P.degree < k ∧
        A ≤ Code.agree (ReedSolomon.evalOnPoints domain P) received) ∧
      (list.card : ℕ∞) = (agreeingPolynomials domain k A received).encard := by
  classical
  refine ⟨hfinite.toFinset.map (messagePolynomialValue k), ?_, ?_⟩
  · intro P
    simp only [Finset.mem_map, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Polynomial.mem_degreeLT.mp p.property, hp⟩
    · rintro ⟨hdegree, hagree⟩
      exact ⟨⟨P, Polynomial.mem_degreeLT.mpr hdegree⟩, hagree, rfl⟩
  · rw [Finset.card_map, hfinite.encard_eq_coe_toFinset_card]

/-- No polynomial can meet an agreement threshold strictly larger than the block length. -/
theorem agreeingPolynomials_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement : ℕ} (hThreshold : Fintype.card index < minAgreement)
    (received : index → F) :
    agreeingPolynomials domain messageDim minAgreement received = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  change minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received at hp
  exact (Nat.not_le_of_lt hThreshold)
    (hp.trans (Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p) (v := received)))

end ReedSolomon
