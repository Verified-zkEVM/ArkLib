/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpTupleCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.DerivativeCounting
/-!
# The derivative-degree bound for persistent polynomial tuples

A persistent tuple represents constituent polynomials, not a single bad challenge. To count
such tuples, specialize all of them at one auxiliary challenge where specialization is
injective and every separant remains nonzero. Their jets then lie in a single regular
first-order chart. Specialization cannot increase either total jet degree or derivative degree,
so the fixed-fiber count applies with the same bounds `v` and `u`.

Writing `b = 1 + τ(v-1)` and `c = min(b, τ(u-1)+K-1)`, the degree contribution is
`v*c + u*(b-c)`, including the full-triangle boundary `c=b`. The remaining ratio is
`(n-k+1)/(L-k+1)`: it counts tuples that agree with the constituents on at least `L` positions.
This is the persistent-tuple contribution to MCA; the joint source image controls the
separate contribution from candidates outside those tuples.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- One regular specialization bounds all admissible first-order tuples by the sharper
fixed-fiber degree, uniformly in the number of constituent words. -/
theorem admissibleChartTuples_card_le_derivativeCapped_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ firstOrderCurveFiberStageOne K v u τ *
      (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
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
  let jets : Finset (Fin 2 → E) := tuples.image (chartTupleJet iota center z)
  have hspec (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (htuples P hP).specialize hτ hkK z
      (havoid _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
  have hjetinj : Set.InjOn (chartTupleJet (r := 1) iota center z)
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
  let domainE : Fin n ↪ E := mappedDomain domain iota
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hderivz : Qz.degreeOf (some 1) ≤ u := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    exact (monomial_le_degreeOf (some 1)
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hderiv
  have hbound := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
    center Qz K k v u τ hτ hτpos hK hsep (hu.trans_le huv) hu huv hvle hderivz
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
  rwa [hcard] at hbound

/-- The complete admissible tuple family inherits the same derivative-degree bound. -/
theorem admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      firstOrderCurveFiberStageOne K v u τ *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  apply admissibleChartTuples_card_le_derivativeCapped_of_exponent
    domain w iota center Q K k L v u τ hτ hτpos hK hkK hk hkL hLn hu huv hjet hderiv
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

end ReedSolomon
