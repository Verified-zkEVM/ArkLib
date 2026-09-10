/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import Mathlib.Tactic.LinearCombination
/-!
# Finite common-agreement pairs and simultaneous specialization

Pairs of degree-`< k` polynomials with `k` common agreements form a finite family:
each pair is the pair of interpolants on some `k`-sample. A finite family of distinct
pairs specializes injectively at some challenge in every infinite extension field,
even after excluding an arbitrary finite set of auxiliary challenges.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- All pairs obtained by interpolating the two words on a common `k`-sample. -/
def correlatedPairFamily {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (k : ℕ) : Finset (F[X] × F[X]) :=
  (Finset.univ.powersetCard k).image fun sample ↦
    (Lagrange.interpolate sample domain f, Lagrange.interpolate sample domain g)

/-- A common sample determines both constituent polynomials, so every sufficiently
agreeing pair belongs to the explicit finite family. -/
theorem mem_correlatedPairFamily_of_commonAgreement
    {F : Type*} [Field F] [DecidableEq F] {n k : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (P Q : F[X]) (hP : P.degree < k) (hQ : Q.degree < k)
    (hcommon : k ≤ (commonPolynomialAgreementSet domain f g P Q).card) :
    (P, Q) ∈ correlatedPairFamily domain f g k := by
  classical
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcommon
  have hinj : Set.InjOn domain sample := domain.injective.injOn
  have hPeq : P = Lagrange.interpolate sample domain f := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hinj
    · simpa [hcard] using hP
    · exact Lagrange.degree_interpolate_lt f hinj
    · intro i hi
      rw [Lagrange.eval_interpolate_at_node f hinj hi]
      have hmem := hsub hi
      simp only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hmem
      exact hmem.1
  have hQeq : Q = Lagrange.interpolate sample domain g := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hinj
    · simpa [hcard] using hQ
    · exact Lagrange.degree_interpolate_lt g hinj
    · intro i hi
      rw [Lagrange.eval_interpolate_at_node g hinj hi]
      have hmem := hsub hi
      simp only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hmem
      exact hmem.2
  unfold correlatedPairFamily
  apply Finset.mem_image.mpr
  exact ⟨sample, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩,
    Prod.ext hPeq.symm hQeq.symm⟩

/-- The number of sample interpolant pairs is at most the number of `k`-samples. -/
theorem correlatedPairFamily_card_le
    {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (k : ℕ) :
    (correlatedPairFamily domain f g k).card ≤ n.choose k := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp)

/-- The sample family contains exactly the degree-bounded pairs with at least `k`
common agreements. -/
theorem mem_correlatedPairFamily_iff
    {F : Type*} [Field F] [DecidableEq F] {n k : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (pair : F[X] × F[X]) :
    pair ∈ correlatedPairFamily domain f g k ↔
      pair.1.degree < k ∧ pair.2.degree < k ∧
        k ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card := by
  classical
  constructor
  · intro hpair
    obtain ⟨sample, hsample, rfl⟩ := Finset.mem_image.mp hpair
    have hcard := (Finset.mem_powersetCard.mp hsample).2
    have hinj : Set.InjOn domain sample := domain.injective.injOn
    refine ⟨?_, ?_, ?_⟩
    · simpa [hcard] using Lagrange.degree_interpolate_lt f hinj
    · simpa [hcard] using Lagrange.degree_interpolate_lt g hinj
    · rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      simp only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨Lagrange.eval_interpolate_at_node f hinj hi,
        Lagrange.eval_interpolate_at_node g hinj hi⟩
  · rintro ⟨hP, hQ, hcommon⟩
    exact mem_correlatedPairFamily_of_commonAgreement domain f g pair.1 pair.2 hP hQ hcommon

/-- Finiteness follows from common agreements, without a finite-base-field assumption. -/
theorem finite_commonAgreement_pairs
    {F : Type*} [Field F] [DecidableEq F] {n k : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) :
    {pair : F[X] × F[X] | pair.1.degree < k ∧ pair.2.degree < k ∧
      k ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card}.Finite := by
  classical
  apply (correlatedPairFamily domain f g k).finite_toSet.subset
  intro pair hpair
  exact mem_correlatedPairFamily_of_commonAgreement domain f g pair.1 pair.2
    hpair.1 hpair.2.1 hpair.2.2

/-- The polynomial on the graph of a base-field pair at an extension-field challenge. -/
def correlatedPairSpecialization {F E : Type*} [Field F] [Field E]
    (iota : F →+* E) (z : E) (pair : F[X] × F[X]) : E[X] :=
  pair.1.map iota + Polynomial.C z * pair.2.map iota

/-- Two distinct challenge specializations determine the constituent pair. -/
theorem pair_eq_of_correlatedPairSpecialization_eq_at_two
    {F E : Type*} [Field F] [Field E] (iota : F →+* E)
    {p q : F[X] × F[X]} {x y : E} (hxy : x ≠ y)
    (hx : correlatedPairSpecialization iota x p = correlatedPairSpecialization iota x q)
    (hy : correlatedPairSpecialization iota y p = correlatedPairSpecialization iota y q) :
    p = q := by
  have hG : p.2.map iota = q.2.map iota := by
    ext j
    have hxj := congrArg (fun R : E[X] ↦ R.coeff j) hx
    have hyj := congrArg (fun R : E[X] ↦ R.coeff j) hy
    simp only [correlatedPairSpecialization, coeff_add, coeff_C_mul] at hxj hyj
    have hprod : (x - y) * ((p.2.map iota).coeff j - (q.2.map iota).coeff j) = 0 := by
      linear_combination hxj - hyj
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hxy))
  have hF : p.1.map iota = q.1.map iota := by
    simpa only [correlatedPairSpecialization, hG, add_left_inj] using hx
  exact Prod.ext (Polynomial.map_injective iota iota.injective hF)
    (Polynomial.map_injective iota iota.injective hG)

/-- Distinct pairs collide at at most one extension-field challenge. -/
theorem subsingleton_correlatedPair_collisions
    {F E : Type*} [Field F] [Field E] (iota : F →+* E)
    {p q : F[X] × F[X]} (hpq : p ≠ q) :
    {z : E | correlatedPairSpecialization iota z p =
      correlatedPairSpecialization iota z q}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hpq (pair_eq_of_correlatedPairSpecialization_eq_at_two iota hxy hx hy)

/-- A finite pair family has only finitely many challenges at which specialization
fails to be injective. -/
theorem finite_correlatedPair_collision_challenges
    {F E : Type*} [Field F] [Field E] (iota : F →+* E)
    (pairs : Finset (F[X] × F[X])) :
    {z : E | ¬ Set.InjOn (correlatedPairSpecialization iota z) (↑pairs)}.Finite := by
  classical
  have hfinite : (⋃ p ∈ (↑pairs : Set (F[X] × F[X])),
      ⋃ q ∈ (↑pairs : Set (F[X] × F[X])),
      {z : E | p ≠ q ∧ correlatedPairSpecialization iota z p =
        correlatedPairSpecialization iota z q}).Finite := by
    apply pairs.finite_toSet.biUnion
    intro p _
    apply pairs.finite_toSet.biUnion
    intro q _
    by_cases hpq : p = q
    · simp [hpq]
    · exact (subsingleton_correlatedPair_collisions iota hpq).finite.subset
        (fun _ hz ↦ hz.2)
  apply hfinite.subset
  intro z hz
  simp only [Set.InjOn, not_forall] at hz
  obtain ⟨p, hp, q, hq, heq, hne⟩ := hz
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp,
    Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hne, heq⟩⟩⟩⟩

/-- Over an infinite extension, one ordinary scalar specializes an entire finite
pair family injectively while avoiding any prescribed finite auxiliary set. -/
theorem exists_correlatedPairSpecialization_injOn_avoiding
    {F E : Type*} [Field F] [Field E] [Infinite E] (iota : F →+* E)
    (pairs : Finset (F[X] × F[X])) (avoid : Finset E) :
    ∃ z : E, z ∉ avoid ∧
      Set.InjOn (correlatedPairSpecialization iota z) (↑pairs) := by
  classical
  have hfinite := (finite_correlatedPair_collision_challenges iota pairs).union
    avoid.finite_toSet
  obtain ⟨z, hz⟩ := hfinite.exists_notMem
  have hboth := not_or.mp hz
  exact ⟨z, hboth.2, not_not.mp hboth.1⟩

/-- The injective scalar may simultaneously keep finitely many nonzero auxiliary
polynomials nonzero, as needed for the restricted separants of chart pairs. -/
theorem exists_correlatedPairSpecialization_injOn_avoiding_roots
    {F E : Type*} [Field F] [Field E] [Infinite E] (iota : F →+* E)
    (pairs : Finset (F[X] × F[X])) (avoid : Finset E)
    (auxiliary : Finset E[X]) (hne : ∀ R ∈ auxiliary, R ≠ 0) :
    ∃ z : E, z ∉ avoid ∧
      Set.InjOn (correlatedPairSpecialization iota z) (↑pairs) ∧
        ∀ R ∈ auxiliary, R.eval z ≠ 0 := by
  classical
  obtain ⟨z, hz, hinj⟩ := exists_correlatedPairSpecialization_injOn_avoiding iota pairs
    (avoid ∪ auxiliary.biUnion fun R ↦ R.roots.toFinset)
  simp only [Finset.mem_union, not_or] at hz
  have hnot := hz
  refine ⟨z, hnot.1, hinj, ?_⟩
  intro R hR heval
  apply hnot.2
  exact Finset.mem_biUnion.mpr ⟨R, hR,
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne R hR)).mpr heval)⟩

end

end ReedSolomon
