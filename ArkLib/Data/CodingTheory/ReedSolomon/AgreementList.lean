/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.SampleIncidence
public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification

/-!
# Finiteness and sample incidence for Reed–Solomon agreement lists

The generic sample-incidence theorem says that a family of finite sets is finite when `k ≤ A`,
every set has at least `A` elements, and distinct sets intersect in fewer than `k` elements. Here a
candidate polynomial is represented by its agreement set. Two distinct degree-`< k` polynomials
cannot share `k` evaluation points, so the generic theorem gives

`list.ncard * A.choose k ≤ n.choose k`.

No finiteness assumption on the field is used, and no Lagrange enumeration is needed: finiteness
is a consequence of the uniform bound on every finite subfamily.

The last section defines `agreeingPolynomials`, the same list as a set of degree-bounded message
polynomials (`ListDecoding.MessagePolynomial`) over any semiring and any finite index type.

## References

`agreeingPolynomials` is ported from `ArkLib/Data/CodingTheory/ReedSolomon/AgreementList.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, unchanged; `mem_agreeingPolynomials_iff`
is new. The source's `agreeingPolynomials_antitone`, `exists_finset_polynomial_list` and
`agreeingPolynomials_eq_empty_of_card_lt` are deferred until an exact-list consumer needs them.
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

end ReedSolomon
