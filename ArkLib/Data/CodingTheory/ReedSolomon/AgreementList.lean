/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.SampleIncidence
public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification
public import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange

/-!
# Finiteness and sample incidence for Reed–Solomon agreement lists

The generic sample-incidence theorem says that a family of finite sets is finite when `k ≤ A`,
every set has at least `A` elements, and distinct sets intersect in fewer than `k` elements. Here a
candidate polynomial is represented by its agreement set. Two distinct degree-`< k` polynomials
cannot share `k` evaluation points, so the generic theorem gives

`list.ncard * A.choose k ≤ n.choose k`.

No finiteness assumption on the field is used, and no Lagrange enumeration is needed: finiteness
is a consequence of the uniform bound on every finite subfamily.

For `k = 1` the candidates are constants, whose agreement sets are disjoint, and the bound reads
`list.ncard ≤ n / A` (`closePolynomialSet_one_ncard_le_div`).

The last section defines `agreeingPolynomials`, the same list as a set of degree-bounded message
polynomials (`ListDecoding.MessagePolynomial`) over any semiring and any finite index type.

## Main statements

* `closePolynomialSet_finite_and_ncard_mul_choose_le` and
  `closePolynomialSet_card_le_of_differential_equation`: finiteness and cardinality bounds for
  agreement lists.

## References

* [DKT26]
* [Kop15]

-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The complete Reed–Solomon agreement list over an arbitrary field.

`domain` embeds the `n` coordinate indices as distinct evaluation points, `received` is the word
being decoded, `k` is the message dimension, and `A` is an integral agreement threshold. -/
def closePolynomialSet {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : Set F[X] :=
  {P | P.degree < k ∧ A ≤ (polynomialAgreementSet domain received P).card}

open Classical in
/-- The complete degree-`< k` agreement set is finite and satisfies the sharp sample-incidence
bound. This is the Reed–Solomon specialization of the generic finite-set theorem. -/
theorem closePolynomialSet_finite_and_ncard_mul_choose_le
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    (closePolynomialSet domain received k A).Finite ∧
      (closePolynomialSet domain received k A).ncard * A.choose k ≤ n.choose k := by
  let S : F[X] → Finset (Fin n) := polynomialAgreementSet domain received
  have hlarge : ∀ P ∈ closePolynomialSet domain received k A, A ≤ (S P).card := by
    intro P hP
    exact hP.2
  have hpair : ∀ P ∈ closePolynomialSet domain received k A,
      ∀ Q ∈ closePolynomialSet domain received k A, P ≠ Q → ((S P) ∩ (S Q)).card < k := by
    intro P hP Q hQ hne
    by_contra hcard
    have hkCard : k ≤ ((S P) ∩ (S Q)).card := Nat.le_of_not_gt hcard
    apply hne
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      ((S P) ∩ (S Q)) domain.injective.injOn
    · exact hP.1.trans_le (by exact_mod_cast hkCard)
    · exact hQ.1.trans_le (by exact_mod_cast hkCard)
    · intro i hi
      have hiP := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
      have hiQ := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
      exact hiP.trans hiQ.symm
  simpa only [Fintype.card_fin] using
    Set.finite_and_ncard_mul_choose_le_of_inter_card_lt
      (closePolynomialSet domain received k A) S A k hAk hlarge hpair

/-- The close polynomials collected as the finite set supplied by the generic incidence theorem. -/
theorem exists_closePolynomial_finset_with_incidence_bound
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card * A.choose k ≤ n.choose k := by
  classical
  obtain ⟨hfinite, hbound⟩ :=
    closePolynomialSet_finite_and_ncard_mul_choose_le domain received hAk
  refine ⟨hfinite.toFinset, fun P ↦ hfinite.mem_toFinset, ?_⟩
  simpa [Set.ncard_eq_toFinset_card _ hfinite] using hbound

/-- The incidence inequality stated directly for the cardinality of the complete agreement set. -/
theorem closePolynomialSet_ncard_mul_choose_le
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    (closePolynomialSet domain received k A).ncard * A.choose k ≤ n.choose k :=
  (closePolynomialSet_finite_and_ncard_mul_choose_le domain received hAk).2

/-- The close degree-`< k` polynomial set is finite over an arbitrary field when the agreement
threshold is at least `k`. -/
theorem closePolynomialSet_finite
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    (closePolynomialSet domain received k A).Finite :=
  (closePolynomialSet_finite_and_ncard_mul_choose_le domain received hAk).1

/-- For message dimension `1`, the complete agreement list with threshold `A > 0` has at most
`n / A` elements: its members are constants, and distinct constants agree with the received word
on disjoint sets of coordinates. -/
theorem exists_closePolynomial_finset_one_card_le_div
    {F : Type*} [Field F] [DecidableEq F] {n A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hA : 0 < A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received 1 A) ∧ list.card ≤ n / A := by
  obtain ⟨list, hlist, hincidence⟩ :=
    exists_closePolynomial_finset_with_incidence_bound domain received hA
  exact ⟨list, hlist, (Nat.le_div_iff_mul_le hA).2 (by simpa using hincidence)⟩

/-- For message dimension `1` and threshold `A > 0`, the complete agreement list has at most
`n / A` elements. -/
theorem closePolynomialSet_one_ncard_le_div
    {F : Type*} [Field F] [DecidableEq F] {n A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hA : 0 < A) :
    (closePolynomialSet domain received 1 A).ncard ≤ n / A :=
  (Nat.le_div_iff_mul_le hA).2 (by
    simpa using closePolynomialSet_ncard_mul_choose_le domain received hA)

end

/-! ## Degree-bounded message lists over general index types -/

open ListDecoding

/-- The degree-`< messageDim` message polynomials whose evaluations on `domain` agree with
`received` in at least `minAgreement` coordinates. This is the set of messages accepted by
`ListDecoding.Accepts`; an exact decoder enumerates it. -/
def agreeingPolynomials {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim minAgreement : ℕ) (received : index → F) :
    Set (MessagePolynomial F messageDim) :=
  {p | minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received}

/-- Membership in `agreeingPolynomials` is the agreement count of `polynomialAgreementSet`. -/
theorem mem_agreeingPolynomials_iff {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] {domain : index ↪ F} {messageDim minAgreement : ℕ} {received : index → F}
    {p : MessagePolynomial F messageDim} :
    p ∈ agreeingPolynomials domain messageDim minAgreement received ↔
      minAgreement ≤ (polynomialAgreementSet domain received p).card :=
  Iff.rfl

/-! ## Differential constraints -/

open PolynomialDifferential
open Polynomial

/-- A finite set of degree-bounded polynomial solutions with at least `A` agreements on distinct
evaluation points has a cardinality bounded by the square of the differential equation's total
jet degree, times the agreement factor to the depth. -/
theorem closePolynomialSet_card_le_of_differential_equation
    {F : Type*} [Field F] [DecidableEq F] {d : ℕ} (Q : DifferentialPolynomial F d)
    (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K) (hQ : Q ≠ 0)
    (hcast : ∀ j, JetDegreeCastsNeZero Q j) (hdegree : jetTotalDegree Q ≤ ν)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (S : Finset F[X]) (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hS : ∀ P ∈ S, P ∈ closePolynomialSet domain received k A) :
    (S.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  let accepts : F[X] → Prop := fun P ↦ P ∈ closePolynomialSet domain received k A
  have hagreement : ∀ P, accepts P ↔
      P.degree < k ∧
        A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card := by
    intro P
    simp [accepts, closePolynomialSet, polynomialAgreementSet]
  exact finite_solutions_card_le_sq_totalJetDegree_of_agreement Q K k ν hK hkK hQ hcast
    hdegree domain received hk hkA hAn hbin accepts hagreement S hsol hS

end ReedSolomon
