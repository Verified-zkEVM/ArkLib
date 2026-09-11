/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.FactorAssembly
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Solutions
/-! # Assembly of polynomial-curve ordinary factor exceptional sets -/

@[expose] public section

open scoped BigOperators
open MvPolynomial

namespace ReedSolomon

/-- Content plus distinct factors fit in the original height and root-degree budgets. -/
theorem ordinaryPowerFactorRaw_sum_le {I : Type*} (S : Finset I) (a height : I → ℕ)
    (theta : ℚ) (n D ℓ mu H contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (ha : ∑ i ∈ S, a i ≤ mu)
    (hh : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) + ∑ i ∈ S, ordinaryPowerFactorRaw theta n D ℓ (a i) (height i) ≤
      ordinaryPowerFactorRaw theta n D ℓ mu H := by
  let c : ℚ := (2 * mu - 1 : ℕ) + theta * (1 + 4 * D * mu)
  let d : ℚ := theta * ℓ + (ℓ * (n - D - 1) : ℕ)
  have hc : 1 ≤ c := by
    have hnat : 1 ≤ 2 * mu - 1 := by omega
    have hcast : (1 : ℚ) ≤ (2 * mu - 1 : ℕ) := by exact_mod_cast hnat
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hterm (i : I) (hi : i ∈ S) :
      ordinaryPowerFactorRaw theta n D ℓ (a i) (height i) ≤
        c * height i + d * a i := by
    have hai : a i ≤ mu := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans ha
    have hsub : 2 * a i - 1 ≤ 2 * mu - 1 := by omega
    have hfirst : (((2 * a i - 1) * height i : ℕ) : ℚ) ≤
        (2 * mu - 1 : ℕ) * (height i : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right (height i) hsub
    have hprod : ((a i : ℚ) * height i) ≤ (mu : ℚ) * height i := by gcongr
    unfold ordinaryPowerFactorRaw
    push_cast
    dsimp [c, d]
    push_cast at hfirst ⊢
    nlinarith [mul_nonneg htheta (mul_nonneg (show (0 : ℚ) ≤ 4 * D by positivity)
      (sub_nonneg.mpr hprod))]
  have hsum := Finset.sum_le_sum hterm
  have hcontent : (contentHeight : ℚ) ≤ c * contentHeight := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg contentHeight)
  have hhQ : (contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ) ≤ H := by
    exact_mod_cast hh
  have haQ : (∑ i ∈ S, (a i : ℚ)) ≤ mu := by exact_mod_cast ha
  calc
    (contentHeight : ℚ) + ∑ i ∈ S, ordinaryPowerFactorRaw theta n D ℓ (a i) (height i) ≤
        c * contentHeight + ∑ i ∈ S, (c * height i + d * a i) :=
      add_le_add hcontent hsum
    _ = c * ((contentHeight : ℚ) + ∑ i ∈ S, (height i : ℚ)) +
        d * ∑ i ∈ S, (a i : ℚ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ c * H + d * mu := add_le_add (mul_le_mul_of_nonneg_left hhQ hc0)
      (mul_le_mul_of_nonneg_left haQ hd0)
    _ = ordinaryPowerFactorRaw theta n D ℓ mu H := by
      dsimp [c, d, ordinaryPowerFactorRaw]
      push_cast
      ring

/-- Combine the content exception with distinct root-factor exceptions, charging at most the
curve degree times the original ordinary factor budget. -/
theorem exists_exceptional_ordinaryPowerFactorAssembly
    {F W V R σ : Type*} [Field F] [CommRing R] [IsDomain R]
    (Q : MvPolynomial (Option σ) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option σ) F →+* R)
    (Good : W → V → Prop) (height : MvPolynomial (Option σ) F → ℕ)
    (theta : ℚ) (n D ℓ mu H : ℕ) (htheta : 0 ≤ theta) (_hℓ : 0 < ℓ) (hmu : 1 ≤ mu)
    (hroot : Q.degreeOf none ≤ mu)
    (hheight : height (ordinaryContent Q) +
      ∑ a ∈ ordinaryRootFactorClasses Q, height (ordinaryFactorRepresentative a) ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (ordinaryContent Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryContent Q) ≠ 0)
    (hfactors : ∀ a ∈ ordinaryRootFactorClasses Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryPowerFactorRaw theta n D ℓ
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryFactorRepresentative a) = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryPowerFactorRaw theta n D ℓ mu H ∧
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
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have hsum :
        (∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ)) ≤
          ∑ a ∈ S, ordinaryPowerFactorRaw theta n D ℓ
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
    exact ordinaryPowerFactorRaw_sum_le S
      (fun a => degreeOf none (ordinaryFactorRepresentative a))
      (fun a => height (ordinaryFactorRepresentative a)) theta n D ℓ mu H
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
