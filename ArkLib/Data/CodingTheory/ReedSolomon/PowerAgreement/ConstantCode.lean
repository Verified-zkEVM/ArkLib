/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Exact power agreement for constant messages

For message dimension `k = 1` the Reed–Solomon code consists of the constant words. Let a
constant `Q` agree with the batched word `i ↦ ∑ t, z ^ t * w t i` on the set `S` of coordinates.
Then `Q` has exact power agreement exactly when the columns `(w t i)_t` coincide for all `i ∈ S`
(`hasExactPowerAgreement_constant_iff`). So exact power agreement fails at `z` only if two
coordinates with different columns have the same batched value, that is, `z` is a root of the
nonzero polynomial `∑ t, (w t i - w t j) * X ^ t` of degree at most `ℓ`.

Counting these roots over pairs of coordinates gives one exceptional set of challenges. A
challenge enters it only if at least `2 * max (A - 1) 1` ordered pairs collide there, which
divides the count `ℓ * (|ι|.choose 2)` of unordered collisions by `max (A - 1) 1`. No
characteristic or field-size hypothesis is used.

## Main statements

* `ReedSolomon.exists_exceptional_powerBatchedWord_collision`: outside at most
  `ℓ * (|ι|.choose 2) / max (A - 1) 1` challenges, a set of at least `A` coordinates on which the
  batched word is constant has constant columns.
* `ReedSolomon.hasExactPowerAgreement_constant_iff`: exact power agreement of a constant
  polynomial is constancy of the columns on its agreement set.
* `ReedSolomon.uniformExactPowerAgreement_constantCode`: uniform exact power agreement for
  `k = 1`, every threshold `A` and every field, with at most
  `ℓ * (|ι|.choose 2) / max (A - 1) 1` exceptional challenges;
  `ReedSolomon.uniformExactPowerAgreement_constantCode_of_two_le` is the form
  `ℓ * (|ι|.choose 2) / (A - 1)` for `A ≥ 2`.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

section Collision

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The polynomial `∑ t, (w t i - w t j) * X ^ t` in the batching challenge. -/
private def columnDifference (w : Fin (ℓ + 1) → ι → F) (i j : ι) : F[X] :=
  ∑ t, monomial t.val (w t i - w t j)

private theorem columnDifference_eval (w : Fin (ℓ + 1) → ι → F) (i j : ι) (z : F) :
    (columnDifference w i j).eval z = powerBatchedWord w z i - powerBatchedWord w z j := by
  simp [columnDifference, powerBatchedWord, eval_finsetSum, Finset.sum_sub_distrib,
    mul_comm]

private theorem columnDifference_natDegree_le (w : Fin (ℓ + 1) → ι → F) (i j : ι) :
    (columnDifference w i j).natDegree ≤ ℓ :=
  natDegree_sum_le_of_forall_le _ _ fun t _ ↦
    (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp t.isLt)

private theorem columnDifference_eq_zero_iff (w : Fin (ℓ + 1) → ι → F) (i j : ι) :
    columnDifference w i j = 0 ↔ ∀ t, w t i = w t j := by
  constructor
  · intro hzero t
    have hcoeff := congrArg (coeff · t.val) hzero
    simp only [columnDifference, finsetSum_coeff, coeff_monomial, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, coeff_zero] at hcoeff
    exact sub_eq_zero.mp hcoeff
  · intro h
    simp [columnDifference, h]

variable [Fintype ι]

/-- Ordered pairs of distinct coordinates with different columns, together with a challenge at
which their batched values coincide. -/
private def collisionIncidence (w : Fin (ℓ + 1) → ι → F) : Finset ((ι × ι) × F) := by
  classical
  exact (Finset.univ : Finset ι).offDiag.biUnion fun p ↦
    {p} ×ˢ (columnDifference w p.1 p.2).roots.toFinset

private theorem mem_collisionIncidence (w : Fin (ℓ + 1) → ι → F) (p : ι × ι) (z : F) :
    (p, z) ∈ collisionIncidence w ↔ p.1 ≠ p.2 ∧ (∃ t, w t p.1 ≠ w t p.2) ∧
      powerBatchedWord w z p.1 = powerBatchedWord w z p.2 := by
  classical
  simp only [collisionIncidence, Finset.mem_biUnion, Finset.mem_offDiag, Finset.mem_univ,
    true_and, Finset.mem_product, Finset.mem_singleton, Multiset.mem_toFinset, mem_roots',
    IsRoot.def, columnDifference_eval, sub_eq_zero, ne_eq, columnDifference_eq_zero_iff,
    not_forall]
  constructor
  · rintro ⟨q, hq, rfl, hz⟩
    exact ⟨hq, hz⟩
  · rintro ⟨hp, hz⟩
    exact ⟨p, hp, rfl, hz⟩

private theorem collisionIncidence_card_le (w : Fin (ℓ + 1) → ι → F) :
    (collisionIncidence w).card ≤ 2 * (ℓ * (Fintype.card ι).choose 2) := by
  classical
  calc (collisionIncidence w).card
      ≤ ∑ p ∈ (Finset.univ : Finset ι).offDiag,
          ({p} ×ˢ (columnDifference w p.1 p.2).roots.toFinset).card := by
        rw [collisionIncidence]
        convert Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (Finset.univ : Finset ι).offDiag, ℓ := by
        refine Finset.sum_le_sum fun p _ ↦ ?_
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact (Multiset.toFinset_card_le _).trans <|
          (card_roots' _).trans (columnDifference_natDegree_le w p.1 p.2)
    _ = 2 * (ℓ * (Fintype.card ι).choose 2) := by
        obtain ⟨m, hm⟩ := Nat.even_mul_pred_self (Fintype.card ι)
        rw [Finset.sum_const, smul_eq_mul, Finset.offDiag_card, Finset.card_univ,
          Nat.choose_two_right, ← Nat.mul_sub_one, hm, show (m + m) / 2 = m by omega]
        ring

/-- The number of colliding ordered pairs at the challenge `z`. -/
private def collisionMultiplicity (w : Fin (ℓ + 1) → ι → F) (z : F) : ℕ := by
  classical
  exact ((collisionIncidence w).filter fun x ↦ x.2 = z).card

/-- If the batched word is constant on `S` at `z` and two columns in `S` differ, then at least
`2 * max (|S| - 1) 1` ordered pairs collide at `z`. -/
private theorem two_mul_max_le_collisionMultiplicity (w : Fin (ℓ + 1) → ι → F) (z : F)
    (S : Finset ι) (hbatch : ∀ i ∈ S, ∀ j ∈ S, powerBatchedWord w z i = powerBatchedWord w z j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) {t : Fin (ℓ + 1)} (ht : w t i ≠ w t j) :
    2 * max (S.card - 1) 1 ≤ collisionMultiplicity w z := by
  classical
  let same := S.filter fun x ↦ ∀ t, w t x = w t i
  let different := S.filter fun x ↦ ¬ ∀ t, w t x = w t i
  have hsame : 0 < same.card := Finset.card_pos.mpr ⟨i, by simp [same, hi]⟩
  have hdifferent : 0 < different.card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, fun h ↦ ht (h t).symm⟩⟩
  have hcards : same.card + different.card = S.card := Finset.card_filter_add_card_filter_not _
  have hproduct : max (S.card - 1) 1 ≤ same.card * different.card := by
    have : same.card + different.card ≤ same.card * different.card + 1 := by nlinarith
    exact max_le (by omega) (Nat.mul_pos hsame hdifferent)
  have hdisjoint : Disjoint (same ×ˢ different) (different ×ˢ same) :=
    Finset.disjoint_left.mpr fun p hp hp' ↦
      (Finset.mem_filter.mp (Finset.mem_product.mp hp').1).2
        (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
  have hcross : ∀ p ∈ same ×ˢ different ∪ different ×ˢ same,
      p.1 ∈ S ∧ p.2 ∈ S ∧ ∃ t, w t p.1 ≠ w t p.2 := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_product, same, different, Finset.mem_filter] at hp
    rcases hp with ⟨⟨h1, h1'⟩, h2, h2'⟩ | ⟨⟨h1, h1'⟩, h2, h2'⟩
    · exact ⟨h1, h2, not_forall.mp fun h ↦ h2' fun t ↦ (h t).symm.trans (h1' t)⟩
    · exact ⟨h1, h2, not_forall.mp fun h ↦ h1' fun t ↦ (h t).trans (h2' t)⟩
  calc 2 * max (S.card - 1) 1
      ≤ 2 * (same.card * different.card) := Nat.mul_le_mul_left 2 hproduct
    _ = (same ×ˢ different ∪ different ×ˢ same).card := by
        rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_product, Finset.card_product]
        ring
    _ ≤ collisionMultiplicity w z := by
        rw [collisionMultiplicity]
        refine Finset.card_le_card_of_injOn (fun p ↦ (p, z)) (fun p hp ↦ ?_)
          (fun p _ q _ h ↦ (Prod.ext_iff.mp h).1)
        obtain ⟨h1, h2, t, ht⟩ := hcross p hp
        refine Finset.mem_filter.mpr ⟨(mem_collisionIncidence w p z).mpr
          ⟨fun h ↦ ht (by rw [h]), ⟨t, ht⟩, hbatch _ h1 _ h2⟩, rfl⟩

/-- **Few challenges identify coordinates with different columns.** For every threshold `A` there
is a set `bad` of at most `ℓ * (|ι|.choose 2) / max (A - 1) 1` challenges such that for every
`z ∉ bad`, the columns `(w t i)_t` coincide on every set of at least `A` coordinates on which the
batched word `powerBatchedWord w z` is constant.

Each pair of coordinates with different columns collides at the at most `ℓ` roots of a nonzero
polynomial of degree at most `ℓ`, and a challenge is exceptional only if it carries at least
`max (A - 1) 1` collisions of unordered pairs. -/
theorem exists_exceptional_powerBatchedWord_collision (w : Fin (ℓ + 1) → ι → F) (A : ℕ) :
    ∃ bad : Finset F, bad.card * max (A - 1) 1 ≤ ℓ * (Fintype.card ι).choose 2 ∧
      ∀ z ∉ bad, ∀ S : Finset ι, A ≤ S.card →
        (∀ i ∈ S, ∀ j ∈ S, powerBatchedWord w z i = powerBatchedWord w z j) →
        ∀ i ∈ S, ∀ j ∈ S, ∀ t, w t i = w t j := by
  classical
  set m := max (A - 1) 1 with hm
  let challenges := (collisionIncidence w).image Prod.snd
  refine ⟨challenges.filter fun z ↦ 2 * m ≤ collisionMultiplicity w z, ?_, ?_⟩
  · set bad := challenges.filter fun z ↦ 2 * m ≤ collisionMultiplicity w z
    have hsum : 2 * (bad.card * m) ≤ (collisionIncidence w).card := calc
      2 * (bad.card * m) = ∑ _z ∈ bad, 2 * m := by
        rw [Finset.sum_const, smul_eq_mul]
        ring
      _ ≤ ∑ z ∈ bad, collisionMultiplicity w z :=
        Finset.sum_le_sum fun z hz ↦ (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z ∈ challenges, collisionMultiplicity w z :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = (collisionIncidence w).card := by
        rw [Finset.card_eq_sum_card_image Prod.snd (collisionIncidence w)]
        rfl
    exact Nat.le_of_mul_le_mul_left (hsum.trans (collisionIncidence_card_le w)) two_pos
  · intro z hz S hS hbatch i hi j hj t
    by_contra ht
    have hmult := two_mul_max_le_collisionMultiplicity w z S hbatch hi hj ht
    have hle : 2 * m ≤ collisionMultiplicity w z :=
      le_trans (Nat.mul_le_mul_left 2 (max_le_max (by omega) le_rfl)) hmult
    refine hz (Finset.mem_filter.mpr ⟨?_, hle⟩)
    have hpos : 0 < collisionMultiplicity w z := lt_of_lt_of_le (by omega) hle
    rw [collisionMultiplicity] at hpos
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

end Collision

section Exact

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F] {ℓ : ℕ}

private theorem commonCurveAgreementSet_subset (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (z : F) :
    commonCurveAgreementSet domain w P ⊆
      polynomialAgreementSet domain (powerBatchedWord w z) (powerBatchedPolynomial P z) := by
  intro i hi
  rw [mem_commonCurveAgreementSet] at hi
  simp [powerBatchedPolynomial_eval, powerBatchedWord, hi]

/-- **Exact power agreement of a constant.** A polynomial `Q` of degree below `1` has exact power
agreement at `z` exactly when the columns `(w t i)_t` coincide on the agreement set of `Q` with
the batched word. -/
theorem hasExactPowerAgreement_constant_iff (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) {z : F}
    {Q : F[X]} (hQ : Q.degree < 1) :
    HasExactPowerAgreement domain w (RingHom.id F) 1 z Q ↔
      ∀ i ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q,
        ∀ j ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q, ∀ t, w t i = w t j := by
  have hconst {P : F[X]} (hP : P.degree < 1) (x y : F) : P.eval x = P.eval y := by
    rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP)]
    simp
  rw [hasExactPowerAgreement_id_iff]
  constructor
  · rintro ⟨P, hP, -, hset⟩ i hi j hj t
    rw [hset, mem_commonCurveAgreementSet] at hi hj
    rw [← hi t, ← hj t, hconst (hP t)]
  · intro hcols
    by_cases hne : (polynomialAgreementSet domain (powerBatchedWord w z) Q).Nonempty
    · obtain ⟨i, hi⟩ := hne
      have hiQ := (mem_polynomialAgreementSet _ _ _ _).mp hi
      have hQP : Q = powerBatchedPolynomial (fun t ↦ C (w t i)) z := by
        have hc : Q.coeff 0 = powerBatchedWord w z i := by
          rw [← hiQ, hconst hQ (domain i) 0, coeff_zero_eq_eval_zero]
        rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hQ), hc]
        simp [powerBatchedPolynomial, powerBatchedWord, map_sum, smul_C]
      refine ⟨fun t ↦ C (w t i), fun t ↦ degree_C_lt, hQP, ?_⟩
      ext j
      rw [mem_commonCurveAgreementSet]
      simp only [eval_C]
      constructor
      · exact fun hj t ↦ hcols i hi j hj t
      · intro hj
        rw [mem_polynomialAgreementSet, hconst hQ _ (domain i), hiQ]
        simp [powerBatchedWord, hj]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      let P : Fin (ℓ + 1) → F[X] := fun t ↦ if t = 0 then Q else 0
      have hQP : Q = powerBatchedPolynomial P z := by
        simp [P, powerBatchedPolynomial]
      refine ⟨P, fun t ↦ ?_, hQP, ?_⟩
      · simp only [P]
        split_ifs
        · exact hQ
        · simp
      · have hsub := commonCurveAgreementSet_subset domain w P z
        rw [← hQP, hne] at hsub
        rw [hne, Finset.subset_empty.mp hsub]

/-- **Uniform exact power agreement for constant messages.** For message dimension `1` and every
threshold `A`, one set of at most `ℓ * (|ι|.choose 2) / max (A - 1) 1` challenges contains every
challenge at which some constant with at least `A` agreements with the batched word fails exact
power agreement. The field is arbitrary. -/
theorem uniformExactPowerAgreement_constantCode (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (A : ℕ) :
    UniformExactPowerAgreement domain w 1 A (ℓ * (Fintype.card ι).choose 2 / max (A - 1) 1) := by
  obtain ⟨bad, hcard, hbad⟩ := exists_exceptional_powerBatchedWord_collision w A
  refine ⟨bad, (Nat.le_div_iff_mul_le (lt_max_of_lt_right one_pos)).2 hcard,
    fun z hz Q hQ hA ↦ (hasExactPowerAgreement_constant_iff domain w hQ).mpr ?_⟩
  refine hbad z hz _ hA fun i hi j hj ↦ ?_
  rw [mem_polynomialAgreementSet] at hi hj
  rw [← hi, ← hj, eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hQ), eval_C, eval_C]

/-- For a threshold `A ≥ 2`, uniform exact power agreement for constant messages holds with at
most `ℓ * (|ι|.choose 2) / (A - 1)` exceptional challenges. -/
theorem uniformExactPowerAgreement_constantCode_of_two_le (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) {A : ℕ} (hA : 2 ≤ A) :
    UniformExactPowerAgreement domain w 1 A (ℓ * (Fintype.card ι).choose 2 / (A - 1)) := by
  simpa [max_eq_left (by omega : 1 ≤ A - 1)] using
    uniformExactPowerAgreement_constantCode domain w A

end Exact

end

end ReedSolomon
