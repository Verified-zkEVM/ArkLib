/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.OrdinaryFactors
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.AggregationBounds
/-!
# Combining ordinary factor exceptional sets

The zero locus of the original polynomial is recovered from its distinct normalized factors.
This lemma unions their exceptional challenges with the root-independent content exceptions
and charges the union to the original coordinate-degree budgets.
-/

@[expose] public section

open scoped BigOperators
open MvPolynomial

namespace ReedSolomon

/-- Combine the content exception with the exceptions of the distinct root factors. -/
theorem exists_exceptional_ordinaryFactorAssembly
    {F W V R σ : Type*} [Field F] [CommRing R] [IsDomain R]
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option σ) F →+* R)
    (Good : W → V → Prop) (height : MvPolynomial (Option σ) F → ℕ)
    (theta : ℚ) (n D mu H : ℕ) (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (hroot : Q.degreeOf none ≤ mu)
    (hheight : height (ordinaryContent Q) +
      ∑ a ∈ ordinaryRootFactorClasses Q, height (ordinaryFactorRepresentative a) ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (ordinaryContent Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryContent Q) ≠ 0)
    (hfactors : ∀ a ∈ ordinaryRootFactorClasses Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryFactorRaw theta n D
        (degreeOf none (ordinaryFactorRepresentative a)) (height (ordinaryFactorRepresentative a)) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryFactorRepresentative a) = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryFactorRaw theta n D mu H ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  classical
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  let S := ordinaryRootFactorClasses Q
  choose factorEx hfCard hf using hfactors
  let allEx := contentEx ∪ S.biUnion fun a =>
    if ha : a ∈ S then factorEx a ha else ∅
  refine ⟨allEx, ?_, ?_⟩
  · have hUnion : allEx.card ≤ contentEx.card +
        ∑ a ∈ S, (if ha : a ∈ S then factorEx a ha else ∅).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le) _)
    have hsum : (∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ)) ≤
        ∑ a ∈ S, ordinaryFactorRaw theta n D
          (degreeOf none (ordinaryFactorRepresentative a))
          (height (ordinaryFactorRepresentative a)) := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [dif_pos ha] using hfCard a ha
    have hUnionQ : (allEx.card : ℚ) ≤ contentEx.card +
        ∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ) := by
      exact_mod_cast hUnion
    apply hUnionQ.trans
    apply (add_le_add (show (contentEx.card : ℚ) ≤ height (ordinaryContent Q) by
      exact_mod_cast hcCard) hsum).trans
    exact ordinaryFactorRaw_sum_le S
      (fun a => degreeOf none (ordinaryFactorRepresentative a))
      (fun a => height (ordinaryFactorRepresentative a)) theta n D mu H
      (height (ordinaryContent Q)) htheta hmu
      ((ordinary_root_degree_sum_le Q hQ).trans hroot) hheight
  · intro w hw v hzero
    have hwc : w ∉ contentEx := fun hm => hw (Finset.mem_union_left _ hm)
    have hsplit := (ordinary_split_zero_iff Q hQ (ev w v)).mpr hzero
    rw [map_mul] at hsplit
    have hr := (mul_eq_zero.mp hsplit).resolve_left (hc w hwc v)
    rw [ordinaryRootProduct, map_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨a, ha, hazero⟩ := hr
    apply hf a ha w _ v hazero
    intro hmem
    apply hw
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, by simpa only [dif_pos (show a ∈ S from ha)] using hmem⟩

end ReedSolomon
