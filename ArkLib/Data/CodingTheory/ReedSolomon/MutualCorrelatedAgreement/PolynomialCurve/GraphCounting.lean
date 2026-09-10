/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphAdmissibility
/-!
# Counting retained polynomial graphs

A generic retained challenge separates a finite tuple family and avoids all restricted
separants.  The actual reconstruction identities then inject the tuple family into the
ordinary regular high-cut jets, where the sharp chart bound applies.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

/-- All polynomial tuples obtained by interpolating the received constituents on a common
`k`-sample. -/
def polynomialTupleFamily [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (k : ℕ) :
    Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (Finset.univ.powersetCard k).image fun sample t ↦
    Lagrange.interpolate sample domain (w t)

/-- A degree-`< k` tuple with at least `k` common agreements belongs to the explicit
sample-interpolation family. -/
theorem mem_polynomialTupleFamily_of_commonAgreement [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (P : Fin (ℓ + 1) → F[X]) (k : ℕ)
    (hdegree : ∀ t, (P t).degree < k)
    (hcommon : k ≤ (commonCurveAgreementSet domain w P).card) :
    P ∈ polynomialTupleFamily domain w k := by
  classical
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcommon
  have hinj : Set.InjOn domain sample := domain.injective.injOn
  apply Finset.mem_image.mpr
  refine ⟨sample, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
  funext t
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hinj
  · exact Lagrange.degree_interpolate_lt (w t) hinj
  · simpa only [hcard] using hdegree t
  · intro i hi
    rw [Lagrange.eval_interpolate_at_node (w t) hinj hi]
    have himem := hsub hi
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at himem
    exact (himem t).symm

/-- The explicit sample family has at most one tuple per `k`-subset. -/
theorem polynomialTupleFamily_card_le [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (k : ℕ) :
    (polynomialTupleFamily domain w k).card ≤ n.choose k := by
  classical
  exact Finset.card_image_le.trans_eq (by simp)

/-- The sample family consists exactly of degree-bounded tuples with at least `k` common
agreements. -/
theorem mem_polynomialTupleFamily_iff [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (P : Fin (ℓ + 1) → F[X]) (k : ℕ) :
    P ∈ polynomialTupleFamily domain w k ↔
      (∀ t, (P t).degree < k) ∧ k ≤ (commonCurveAgreementSet domain w P).card := by
  classical
  constructor
  · intro hP
    obtain ⟨sample, hsample, rfl⟩ := Finset.mem_image.mp hP
    have hcard := (Finset.mem_powersetCard.mp hsample).2
    have hinj : Set.InjOn domain sample := domain.injective.injOn
    constructor
    · intro t
      simpa only [hcard] using Lagrange.degree_interpolate_lt (w t) hinj
    · rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro t
      exact Lagrange.eval_interpolate_at_node (w t) hinj hi
  · rintro ⟨hdegree, hcommon⟩
    exact mem_polynomialTupleFamily_of_commonAgreement domain w P k hdegree hcommon

/-- The finite sample-interpolation family filtered by the intrinsic chart identities at a
specified common Taylor exponent. -/
def admissibleChartTupleFamilyAtExponent [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) : Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (polynomialTupleFamily domain w k).filter
    (IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ)

/-- When `k ≤ L`, the finite filtered family contains every admissible tuple and only
admissible tuples. -/
theorem mem_admissibleChartTupleFamilyAtExponent_iff [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) (hkL : k ≤ L) (P : Fin (ℓ + 1) → F[X]) :
    P ∈ admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ ↔
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P := by
  classical
  simp only [admissibleChartTupleFamilyAtExponent, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hP
    exact ⟨mem_polynomialTupleFamily_of_commonAgreement domain w P k hP.degree
      (hkL.trans hP.common), hP⟩

private theorem jetDegree_pos_of_initialSeparant_ne_zero (center : E)
    (Q : DifferentialPolynomial E r) (hS : initialJetSeparant center Q ≠ 0) :
    0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last r)
  rw [hC, pderiv_C] at hd
  exact hS hd.symm

/-- Any finite family of intrinsic admissible tuple graphs satisfies the sharp ordinary-chart
bound after one common regular specialization. -/
theorem admissibleChartTuples_card_le_of_exponent [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ (v : ℚ) *
      ((((n * (1 + τ * (v - 1)) : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  classical
  by_cases hempty : tuples = ∅
  · subst tuples
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let auxiliary := tuples.image fun P ↦
    chartTuplePullback iota center P (symbolicSourceSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ :=
    exists_polynomialTuple_specialization_injective_avoiding_roots (ℓ := ℓ)
      iota tuples ∅ auxiliary (by
      intro R hR
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hR
      exact (htuples P hP).regular)
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jets : Finset (Fin (r + 1) → E) := tuples.image (chartTupleJet iota center z)
  have hspec (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (htuples P hP).specialize hτ hkK z
      (havoid _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
  have hjetinj : Set.InjOn (chartTupleJet (r := r) iota center z)
      (tuples : Set (Fin (ℓ + 1) → F[X])) := by
    intro P hP R hR heq
    apply hinj hP hR
    change powerBatchedPolynomial (fun t ↦ (P t).map iota) z =
      powerBatchedPolynomial (fun t ↦ (R t).map iota) z
    rw [← (hspec P hP).2.2.2, ← (hspec R hR).2.2.2, heq]
  have hcard : jets.card = tuples.card := Finset.card_image_of_injOn hjetinj
  obtain ⟨P₀, hP₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hsep : initialJetSeparant center Qz ≠ 0 := by
    intro hz
    exact (hspec P₀ hP₀).2.1 (by rw [hz]; simp)
  have hvz := jetDegree_pos_of_initialSeparant_ne_zero center Qz hsep
  let domainE : Fin n ↪ E := mappedDomain domain iota
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hbound := finite_regularHighCutJets_card_le_of_exponent
    center Qz K k τ hτ hK hsep hvz
    domainE received hk hkL hLn jets (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      exact ⟨(hspec P hP).1, (hspec P hP).2.1,
        fun l ↦ (hspec P hP).2.2.1 l.val l.property⟩) (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      apply (htuples P hP).common.trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, taylorAgreementEquation_eq_zero_iff_of_exponent
        _ _ _ τ hτ _ (hspec P hP).2.1, (hspec P hP).2.2.2]
      have hi' : ∀ t, (P t).eval (domain i) = w t i := by
        simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      change (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
          (iota (domain i)) = ∑ t, z ^ t.val * iota (w t i)
      rw [powerBatchedPolynomial_eval]
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hi' t])
  rw [hcard] at hbound
  apply hbound.trans
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz K (τ := τ) ≤ 1 + τ * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvle 1)) 1
  apply mul_le_mul
  · exact_mod_cast hvle
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left n hB
  · positivity
  · positivity

/-- The complete finite family of admissible tuples satisfies the sharp ordinary-chart bound. -/
theorem admissibleChartTupleFamilyAtExponent_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      (v : ℚ) *
        ((((n * (1 + τ * (v - 1)) : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  apply admissibleChartTuples_card_le_of_exponent domain w iota center Q K k L v τ hτ
    hK hkK hk hkL hLn hjet
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

end ReedSolomon
