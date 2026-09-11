/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.UniformPowerAgreement
/-!
# Constant-code agreement on polynomial received curves

Constant messages require no characteristic hypothesis. Their agreement sets are disjoint, so
the exact list has size at most `n / A`. Polynomial-curve correlated agreement additionally uses
collision counting between received coordinate tuples.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F] {n ℓ : ℕ}

/-- For every challenge on a polynomial received curve, the complete constant-message list has
cardinality at most `n / A`. This includes the zero polynomial and works over arbitrary fields. -/
theorem exists_constantCode_list (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) (A : ℕ) (hA : 0 < A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain (powerBatchedWord w z) 1 A) ∧
      list.card ≤ n / A := by
  obtain ⟨list, hlist, hincidence⟩ :=
    exists_closePolynomial_finset_with_incidence_bound
      domain (powerBatchedWord w z) (show 1 ≤ A by omega)
  refine ⟨list, hlist, (Nat.le_div_iff_mul_le hA).2 ?_⟩
  simpa using hincidence

private def constantCodeCollisionPolynomial (w : Fin (ℓ + 1) → Fin n → F)
    (pair : Fin n × Fin n) : F[X] :=
  powerBatchedCoordinate (fun t ↦ w t pair.1) -
    powerBatchedCoordinate (fun t ↦ w t pair.2)

omit [DecidableEq F] in
private theorem constantCodeCollisionPolynomial_natDegree_le
    (w : Fin (ℓ + 1) → Fin n → F) (pair : Fin n × Fin n) :
    (constantCodeCollisionPolynomial w pair).natDegree ≤ ℓ := by
  exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
    (powerBatchedCoordinate_natDegree_le _) (powerBatchedCoordinate_natDegree_le _)

omit [DecidableEq F] in
private theorem constantCodeCollisionPolynomial_ne_zero
    (w : Fin (ℓ + 1) → Fin n → F) (pair : Fin n × Fin n)
    (hdifferent : (∃ t, w t pair.1 ≠ w t pair.2)) :
    constantCodeCollisionPolynomial w pair ≠ 0 := by
  obtain ⟨t, ht⟩ := hdifferent
  intro hzero
  have hcoeff := congrArg (fun P : F[X] ↦ P.coeff t.val) hzero
  simp only [constantCodeCollisionPolynomial, Polynomial.coeff_sub,
    powerBatchedCoordinate, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Fin.val_inj, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Polynomial.coeff_zero] at hcoeff
  exact ht (sub_eq_zero.mp hcoeff)

private def constantCodeOrderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n)).offDiag

private theorem constantCodeOrderedPairs_card (n : ℕ) :
    (constantCodeOrderedPairs n).card = 2 * n.choose 2 := by
  rw [constantCodeOrderedPairs, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_fin]
  calc
    n * n - n = n * (n - 1) := by rw [Nat.mul_sub_left_distrib, mul_one]
    _ = 2 * n.choose 2 := by
      rw [Nat.choose_two_right]
      rw [mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]

private def constantCodeCollisionIncidence (w : Fin (ℓ + 1) → Fin n → F) :
    Finset ((Fin n × Fin n) × F) := by
  classical
  exact (constantCodeOrderedPairs n).biUnion fun pair ↦
    {pair} ×ˢ (constantCodeCollisionPolynomial w pair).roots.toFinset

private theorem constantCodeCollisionIncidence_card_le
    (w : Fin (ℓ + 1) → Fin n → F) :
    (constantCodeCollisionIncidence w).card ≤ 2 * (ℓ * n.choose 2) := by
  classical
  calc
    (constantCodeCollisionIncidence w).card ≤
        ∑ pair ∈ constantCodeOrderedPairs n,
          ({pair} ×ˢ (constantCodeCollisionPolynomial w pair).roots.toFinset).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _pair ∈ constantCodeOrderedPairs n, ℓ := by
      apply Finset.sum_le_sum
      intro pair _
      rw [Finset.card_product, Finset.card_singleton, one_mul]
      exact (Multiset.toFinset_card_le _).trans <|
        (Polynomial.card_roots' _).trans (constantCodeCollisionPolynomial_natDegree_le w pair)
    _ = 2 * (ℓ * n.choose 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, constantCodeOrderedPairs_card]
      ac_rfl

private def constantCodeCollisionMultiplicity (w : Fin (ℓ + 1) → Fin n → F)
    (z : F) : ℕ :=
  ((constantCodeCollisionIncidence w).filter fun incidence ↦ incidence.2 = z).card

private def constantCodeCollisionChallenges (w : Fin (ℓ + 1) → Fin n → F) :
    Finset F :=
  (constantCodeCollisionIncidence w).image Prod.snd

private theorem constantCodeCollisionChallenges_sum_multiplicity
    (w : Fin (ℓ + 1) → Fin n → F) :
    ∑ z ∈ constantCodeCollisionChallenges w, constantCodeCollisionMultiplicity w z =
      (constantCodeCollisionIncidence w).card := by
  classical
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro incidence hincidence
  exact Finset.mem_image.mpr ⟨incidence, hincidence, rfl⟩

private theorem mem_constantCodeCollisionIncidence_of_batched_eq
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) (pair : Fin n × Fin n)
    (hne : pair.1 ≠ pair.2) (hdifferent : ∃ t, w t pair.1 ≠ w t pair.2)
    (hbatch : powerBatchedWord w z pair.1 = powerBatchedWord w z pair.2) :
    (pair, z) ∈ constantCodeCollisionIncidence w := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨pair, Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩, ?_⟩
  rw [Finset.mem_product]
  refine ⟨by simp, Multiset.mem_toFinset.mpr ?_⟩
  rw [Polynomial.mem_roots (constantCodeCollisionPolynomial_ne_zero w pair hdifferent)]
  change (constantCodeCollisionPolynomial w pair).eval z = 0
  simp only [constantCodeCollisionPolynomial, Polynomial.eval_sub,
    powerBatchedCoordinate_eval]
  exact sub_eq_zero.mpr hbatch

private theorem two_mul_card_sub_one_le_constantCodeCollisionMultiplicity
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) (S : Finset (Fin n))
    (hbatch : ∀ i ∈ S, ∀ j ∈ S,
      powerBatchedWord w z i = powerBatchedWord w z j)
    (hdifferent : ∃ i ∈ S, ∃ j ∈ S, ∃ t, w t i ≠ w t j) :
    2 * (S.card - 1) ≤ constantCodeCollisionMultiplicity w z := by
  classical
  obtain ⟨i, hi, j, hj, t, ht⟩ := hdifferent
  have hij : i ≠ j := by
    intro h
    subst j
    exact ht rfl
  let same := S.filter fun x ↦ ∀ t, w t x = w t i
  let different := S.filter fun x ↦ ∃ t, w t x ≠ w t i
  have hiSame : i ∈ same := by simp [same, hi]
  have hjDifferent : j ∈ different := by
    simp only [different, Finset.mem_filter]
    exact ⟨hj, ⟨t, Ne.symm ht⟩⟩
  have hpartition : same ∪ different = S := by
    ext x
    simp only [same, different, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases hs : ∀ t, w t x = w t i
      · exact Or.inl ⟨hx, hs⟩
      · exact Or.inr ⟨hx, not_forall.mp hs⟩
  have hdisjoint : Disjoint same different := by
    apply Finset.disjoint_left.mpr
    intro x hxs hxd
    obtain ⟨_, hsame⟩ := Finset.mem_filter.mp hxs
    obtain ⟨_, t', ht'⟩ := Finset.mem_filter.mp hxd
    exact ht' (hsame t')
  have hcards : same.card + different.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hpartition]
  have hproduct : S.card - 1 ≤ same.card * different.card := by
    have hspos : 0 < same.card := Finset.card_pos.mpr ⟨i, hiSame⟩
    have hdpos : 0 < different.card := Finset.card_pos.mpr ⟨j, hjDifferent⟩
    by_cases hsone : same.card = 1
    · rw [← hcards, hsone]
      simp
    by_cases hdone : different.card = 1
    · rw [← hcards, hdone]
      simp
    have hsTwo : 2 ≤ same.card := by omega
    have hdTwo : 2 ≤ different.card := by omega
    rw [← hcards]
    have hmul := Nat.add_le_mul hsTwo hdTwo
    omega
  let cross := same ×ˢ different ∪ different ×ˢ same
  have hcrossDisjoint : Disjoint (same ×ˢ different) (different ×ˢ same) := by
    apply Finset.disjoint_left.mpr
    intro pair hsd hds
    have hleftSame := (Finset.mem_product.mp hsd).1
    have hleftDifferent := (Finset.mem_product.mp hds).1
    exact Finset.disjoint_left.mp hdisjoint hleftSame hleftDifferent
  have hcrossCard : cross.card = 2 * (same.card * different.card) := by
    simp only [cross, Finset.card_union_of_disjoint hcrossDisjoint,
      Finset.card_product]
    ring
  have hcrossSubset : cross ×ˢ {z} ⊆
      (constantCodeCollisionIncidence w).filter fun incidence ↦ incidence.2 = z := by
    intro incidence hincidence
    obtain ⟨hpair, hz⟩ := Finset.mem_product.mp hincidence
    have hzeq : incidence.2 = z := by simpa using hz
    have hp : incidence.1 ∈ same ×ˢ different ∨
        incidence.1 ∈ different ×ˢ same := by
      simpa only [cross, Finset.mem_union] using hpair
    have hpS : incidence.1.1 ∈ S ∧ incidence.1.2 ∈ S := by
      rcases hp with hp | hp
      · exact ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1,
          (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1⟩
      · exact ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1,
          (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1⟩
    have hpDifferent : ∃ t, w t incidence.1.1 ≠ w t incidence.1.2 := by
      rcases hp with hp | hp
      · obtain ⟨hs, hd⟩ := Finset.mem_product.mp hp
        obtain ⟨t', ht'⟩ := (Finset.mem_filter.mp hd).2
        refine ⟨t', ?_⟩
        rw [(Finset.mem_filter.mp hs).2 t']
        exact Ne.symm ht'
      · obtain ⟨hd, hs⟩ := Finset.mem_product.mp hp
        obtain ⟨t', ht'⟩ := (Finset.mem_filter.mp hd).2
        refine ⟨t', ?_⟩
        rw [(Finset.mem_filter.mp hs).2 t']
        exact ht'
    have hpNe : incidence.1.1 ≠ incidence.1.2 := by
      intro heq
      obtain ⟨t', ht'⟩ := hpDifferent
      exact ht' (congrArg (w t') heq)
    apply Finset.mem_filter.mpr
    refine ⟨?_, hzeq⟩
    have heq : incidence = (incidence.1, z) := Prod.ext rfl hzeq
    rw [heq]
    exact mem_constantCodeCollisionIncidence_of_batched_eq w z incidence.1 hpNe
      hpDifferent (hbatch _ hpS.1 _ hpS.2)
  calc
    2 * (S.card - 1) ≤ 2 * (same.card * different.card) :=
      Nat.mul_le_mul_left 2 hproduct
    _ = cross.card := hcrossCard.symm
    _ = (cross ×ˢ {z}).card := by simp
    _ ≤ ((constantCodeCollisionIncidence w).filter fun incidence ↦
        incidence.2 = z).card := Finset.card_le_card hcrossSubset
    _ = constantCodeCollisionMultiplicity w z := rfl

private def constantCodeIncreasingPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun pair ↦ pair.1 < pair.2

private theorem constantCodeIncreasingPairs_card (n : ℕ) :
    (constantCodeIncreasingPairs n).card = n.choose 2 := by
  simpa [constantCodeIncreasingPairs] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

private def constantCodeCollisionChallengesHalf
    (w : Fin (ℓ + 1) → Fin n → F) : Finset F := by
  classical
  exact (constantCodeIncreasingPairs n).biUnion fun pair ↦
    (constantCodeCollisionPolynomial w pair).roots.toFinset

private theorem constantCodeCollisionChallengesHalf_card_le
    (w : Fin (ℓ + 1) → Fin n → F) :
    (constantCodeCollisionChallengesHalf w).card ≤ ℓ * n.choose 2 := by
  classical
  calc
    (constantCodeCollisionChallengesHalf w).card ≤
        ∑ pair ∈ constantCodeIncreasingPairs n,
          (constantCodeCollisionPolynomial w pair).roots.toFinset.card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _pair ∈ constantCodeIncreasingPairs n, ℓ := by
      apply Finset.sum_le_sum
      intro pair _
      exact (Multiset.toFinset_card_le _).trans <|
        (Polynomial.card_roots' _).trans (constantCodeCollisionPolynomial_natDegree_le w pair)
    _ = ℓ * n.choose 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, constantCodeIncreasingPairs_card]
      exact Nat.mul_comm _ _

private theorem mem_constantCodeCollisionChallengesHalf_of_batched_eq
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) {i j : Fin n} (hne : i ≠ j)
    (hdifferent : ∃ t, w t i ≠ w t j)
    (hbatch : powerBatchedWord w z i = powerBatchedWord w z j) :
    z ∈ constantCodeCollisionChallengesHalf w := by
  classical
  by_cases hij : i < j
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i, j), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩, ?_⟩
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (constantCodeCollisionPolynomial_ne_zero w (i, j) hdifferent)]
    change (constantCodeCollisionPolynomial w (i, j)).eval z = 0
    simp only [constantCodeCollisionPolynomial, Polynomial.eval_sub,
      powerBatchedCoordinate_eval]
    exact sub_eq_zero.mpr hbatch
  · have hji : j < i := lt_of_le_of_ne (not_lt.mp hij) (Ne.symm hne)
    apply Finset.mem_biUnion.mpr
    refine ⟨(j, i), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hji⟩, ?_⟩
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (constantCodeCollisionPolynomial_ne_zero w (j, i) ?_)]
    · change (constantCodeCollisionPolynomial w (j, i)).eval z = 0
      simp only [constantCodeCollisionPolynomial, Polynomial.eval_sub,
        powerBatchedCoordinate_eval]
      exact sub_eq_zero.mpr hbatch.symm
    · obtain ⟨t, ht⟩ := hdifferent
      exact ⟨t, Ne.symm ht⟩

private theorem hasExactPowerAgreement_constant_of_same
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (z : F) (Q : F[X])
    (hdegree : Q.degree < 1) (i : Fin n)
    (hi : i ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q)
    (hsame : ∀ j ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q,
      ∀ t, w t j = w t i) :
    HasExactPowerAgreement domain w (RingHom.id F) 1 z Q := by
  have hconstant : Q = Polynomial.C (Q.eval (domain i)) := by
    have hdegree' : Q.degree ≤ 0 := Order.lt_succ_iff.mp hdegree
    rw [Polynomial.eq_C_of_degree_le_zero hdegree']
    simp
  have hiEq : Q.eval (domain i) = powerBatchedWord w z i :=
    (Finset.mem_filter.mp hi).2
  let P : Fin (ℓ + 1) → F[X] := fun t ↦ Polynomial.C (w t i)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro t
    exact Polynomial.degree_C_lt
  · rw [hconstant, hiEq]
    ext x
    simp [P, powerBatchedPolynomial, powerBatchedWord,
      Polynomial.smul_eq_C_mul]
  · ext j
    constructor
    · intro hj
      have hjBase : j ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q := by
        simpa [mappedDomain] using hj
      have hjValues : ∀ t, (P t).eval (domain j) = w t j := by
        intro t
        simp [P, hsame j hjBase t]
      simpa [commonCurveAgreementSet] using hjValues
    · intro hj
      have hjValues : ∀ t, (P t).eval (domain j) = w t j := by
        simpa [commonCurveAgreementSet] using hj
      have hjBase : j ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hconstant, Polynomial.eval_C, hiEq]
        simp only [powerBatchedWord]
        apply Finset.sum_congr rfl
        intro t _
        simpa [P] using congrArg (fun x ↦ z ^ t.val * x) (hjValues t)
      simpa [mappedDomain] using hjBase

/-- For agreement threshold at least two, constant messages on a polynomial received curve have
one exceptional set of size at most `ℓ * n.choose 2 / (A - 1)`. The set is chosen before the
challenge and candidate, and the conclusion identifies the complete agreement set. -/
theorem uniformExactPowerAgreement_constantCode_of_two_le
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (A : ℕ) (hA : 2 ≤ A) :
    UniformExactPowerAgreement domain w 1 A (ℓ * n.choose 2 / (A - 1)) := by
  classical
  let challenges := constantCodeCollisionChallenges w
  let exceptional := challenges.filter fun z ↦
    2 * (A - 1) ≤ constantCodeCollisionMultiplicity w z
  refine ⟨exceptional, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le (by omega : 0 < A - 1)).2
    have hthreshold : exceptional.card * (2 * (A - 1)) ≤
        ∑ z ∈ exceptional, constantCodeCollisionMultiplicity w z := by
      calc
        exceptional.card * (2 * (A - 1)) = ∑ _z ∈ exceptional, 2 * (A - 1) := by
          simp
        _ ≤ ∑ z ∈ exceptional, constantCodeCollisionMultiplicity w z := by
          apply Finset.sum_le_sum
          intro z hz
          exact (Finset.mem_filter.mp hz).2
    have hsum : ∑ z ∈ exceptional, constantCodeCollisionMultiplicity w z ≤
        (constantCodeCollisionIncidence w).card := by
      calc
        _ ≤ ∑ z ∈ challenges, constantCodeCollisionMultiplicity w z := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro z hz
            exact (Finset.mem_filter.mp hz).1
          · intro _ _ _
            omega
        _ = (constantCodeCollisionIncidence w).card :=
          constantCodeCollisionChallenges_sum_multiplicity w
    have hincidence := constantCodeCollisionIncidence_card_le w
    have hdouble : exceptional.card * (2 * (A - 1)) ≤ 2 * (ℓ * n.choose 2) :=
      hthreshold.trans (hsum.trans hincidence)
    have hdouble' : 2 * (exceptional.card * (A - 1)) ≤ 2 * (ℓ * n.choose 2) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hdouble
    exact Nat.le_of_mul_le_mul_left hdouble' (by omega)
  · intro z hz Q hdegree hagree
    let agreement := polynomialAgreementSet domain (powerBatchedWord w z) Q
    have hagreementPos : 0 < agreement.card := (by omega : 0 < A).trans_le hagree
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hagreementPos
    have hconstant : Q = Polynomial.C (Q.eval (domain i)) := by
      have hdegree' : Q.degree ≤ 0 := Order.lt_succ_iff.mp hdegree
      rw [Polynomial.eq_C_of_degree_le_zero hdegree']
      simp
    have hsame : ∀ j ∈ agreement, ∀ t, w t j = w t i := by
      intro j hj
      by_contra hdifferent
      have hbatch : ∀ x ∈ agreement, ∀ y ∈ agreement,
          powerBatchedWord w z x = powerBatchedWord w z y := by
        intro x hx y hy
        have hxEq := (Finset.mem_filter.mp hx).2
        have hyEq := (Finset.mem_filter.mp hy).2
        rw [← hxEq, ← hyEq, hconstant]
        simp
      have hmult : 2 * (A - 1) ≤ constantCodeCollisionMultiplicity w z := by
        apply (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hagree 1)).trans
        apply two_mul_card_sub_one_le_constantCodeCollisionMultiplicity w z agreement hbatch
        exact ⟨j, hj, i, hi, not_forall.mp hdifferent⟩
      apply hz
      apply Finset.mem_filter.mpr
      refine ⟨?_, hmult⟩
      have hmultPos : 0 < constantCodeCollisionMultiplicity w z :=
        (by omega : 0 < 2 * (A - 1)).trans_le hmult
      obtain ⟨incidence, hincidence⟩ := Finset.card_pos.mp hmultPos
      exact Finset.mem_image.mpr ⟨incidence, (Finset.mem_filter.mp hincidence).1,
        (Finset.mem_filter.mp hincidence).2⟩
    exact hasExactPowerAgreement_constant_of_same domain w z Q hdegree i hi hsame

/-- At agreement threshold one, constant messages satisfy exact polynomial-curve agreement
outside the collision fallback set of size at most `ℓ * n.choose 2`. -/
theorem uniformExactPowerAgreement_constantCode_one (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) :
    UniformExactPowerAgreement domain w 1 1 (ℓ * n.choose 2) := by
  classical
  let exceptional := constantCodeCollisionChallengesHalf w
  refine ⟨exceptional, ?_, ?_⟩
  · exact constantCodeCollisionChallengesHalf_card_le w
  · intro z hz Q hdegree hagree
    let agreement := polynomialAgreementSet domain (powerBatchedWord w z) Q
    have hagreementPos : 0 < agreement.card := (by omega : 0 < 1).trans_le hagree
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hagreementPos
    have hconstant : Q = Polynomial.C (Q.eval (domain i)) := by
      have hdegree' : Q.degree ≤ 0 := Order.lt_succ_iff.mp hdegree
      rw [Polynomial.eq_C_of_degree_le_zero hdegree']
      simp
    have hsame : ∀ j ∈ agreement, ∀ t, w t j = w t i := by
      intro j hj
      by_contra hdifferent
      have hij : i ≠ j := by
        intro heq
        subst j
        exact hdifferent (fun _ ↦ rfl)
      apply hz
      apply mem_constantCodeCollisionChallengesHalf_of_batched_eq w z hij
        (by
          obtain ⟨t, ht⟩ := not_forall.mp hdifferent
          exact ⟨t, Ne.symm ht⟩)
      have hiEq := (Finset.mem_filter.mp hi).2
      have hjEq := (Finset.mem_filter.mp hj).2
      rw [← hiEq, ← hjEq, hconstant]
      simp
    exact hasExactPowerAgreement_constant_of_same domain w z Q hdegree i hi hsame

/-- Constant messages on a polynomial received curve satisfy exact mutual correlated agreement
over every field. For `A ≥ 2`, the collision count gains the exact `A - 1` divisor. -/
theorem uniformExactPowerAgreement_constantCode (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (A : ℕ) (hA : 0 < A) :
    UniformExactPowerAgreement domain w 1 A
      (if A = 1 then ℓ * n.choose 2 else ℓ * n.choose 2 / (A - 1)) := by
  classical
  by_cases hAone : A = 1
  · subst A
    change UniformExactPowerAgreement domain w 1 1 (ℓ * n.choose 2)
    exact uniformExactPowerAgreement_constantCode_one domain w
  · simp only [if_neg hAone]
    exact uniformExactPowerAgreement_constantCode_of_two_le domain w A (by omega)

end

end ReedSolomon
