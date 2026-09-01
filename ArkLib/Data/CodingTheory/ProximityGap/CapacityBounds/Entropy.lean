/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Entropy.Counting

/-!
# Entropy-regime CA breakdown for Reed--Solomon codes

This module assembles the CS25 second-moment estimates from `Entropy.Counting` into complete
correlated-agreement breakdown for Reed--Solomon codes in the entropy-defined rate band.

## Main result

- `rs_epsCa_eq_one_of_entropy_rate` — ABF26 Theorem 4.17 [CS25 Cor 1].
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap
open EntropyInternal

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private theorem rs_entropy_rate_nat_margin {ι : Type} [Fintype ι] [Nonempty ι]
    (k f : ℕ)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤
      1 - (f : ℝ) / Fintype.card ι - 2 / (Fintype.card ι : ℝ)) :
    k + f + 2 ≤ Fintype.card ι := by
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  have h := mul_le_mul_of_nonneg_right hδ_hi hnR.le
  field_simp at h
  have hR : (k : ℝ) + f + 2 ≤ Fintype.card ι := by nlinarith
  exact_mod_cast hR

private theorem rs_entropy_rate_parameter_facts
    (q n k f : ℕ) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi :
      (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    k + f + 2 ≤ n ∧ 0 < f ∧ f < n ∧
      0 < qEntropy q ((f : ℝ) / n) - (f : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hslackR : (k : ℝ) + f + 2 ≤ n := by
    have h := mul_le_mul_of_nonneg_right hhi hnR.le
    field_simp at h
    nlinarith only [h]
  have hslack : k + f + 2 ≤ n := by exact_mod_cast hslackR
  have hfpos : 0 < f := by
    by_contra hf
    have hf0 : f = 0 := Nat.eq_zero_of_not_pos hf
    subst f
    simp only [Nat.cast_zero, zero_div, qEntropy_zero, sub_zero, one_div] at hlo hhi
    have htwo : (0 : ℝ) < 2 / n := div_pos (by norm_num) hnR
    linarith only [hlo, hhi, htwo]
  have hflt : f < n := by omega
  let s : ℝ :=
    ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hcomp :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) + s ≤
        1 - (f : ℝ) / n - 2 / (n : ℝ) := by
    exact le_trans hlo hhi
  have hgap : 4 / (n : ℝ) + s ≤
      qEntropy q ((f : ℝ) / n) - (f : ℝ) / n := by
    rw [show 4 / (n : ℝ) = 2 / (n : ℝ) + 2 / (n : ℝ) by ring]
    linarith only [hcomp]
  have hfour : (0 : ℝ) < 4 / n := div_pos (by norm_num) hnR
  have hdiff : 0 < qEntropy q ((f : ℝ) / n) - (f : ℝ) / n :=
    lt_of_lt_of_le (by linarith only [hfour, hs_nonneg] : 0 < 4 / (n : ℝ) + s) hgap
  exact ⟨hslack, hfpos, hflt, hdiff⟩

private theorem rs_entropy_rate_exponent_slack
    (q n k f : ℕ) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi :
      (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    let h : ℝ := qEntropy q ((f : ℝ) / n) - (f : ℝ) / n
    let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
    (((n - f - k : ℕ) : ℝ) + 2 + (n : ℝ) * s) ≤ (n : ℝ) * h := by
  dsimp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hslack, hfpos, hflt, hgap⟩ :=
    rs_entropy_rate_parameter_facts q n k f hn hlo hhi
  have hm := mul_le_mul_of_nonneg_right hlo hnR.le
  have hkn :
      (1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) * n ≤ k := by
    calc
      _ ≤ ((k : ℝ) / n) * n := hm
      _ = k := by field_simp
  have hkn' :
      (n : ℝ) - (n : ℝ) * qEntropy q ((f : ℝ) / n) + 2 +
          (n : ℝ) *
            ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2) ≤ k := by
    calc
      _ = (1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) * n := by
            field_simp
      _ ≤ k := hkn
  have hdcast : (((n - f - k : ℕ) : ℝ)) = (n : ℝ) - f - k := by
    rw [Nat.cast_sub (by omega : k ≤ n - f), Nat.cast_sub (by omega : f ≤ n)]
  have hrhs :
      (n : ℝ) * (qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) =
        (n : ℝ) * qEntropy q ((f : ℝ) / n) - f := by
    field_simp
  rw [hdcast, hrhs]
  linarith only [hkn']

private theorem rs_entropy_rate_full_parameter_facts_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi : (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    k + f + 2 ≤ n ∧ 0 < f ∧ f < n ∧ 2 ≤ n - f - k ∧
      n - f - k ≤ k + f := by
  obtain ⟨hmargin, hfpos, hflt, _⟩ :=
    rs_entropy_rate_parameter_facts q n k f hn hlo hhi
  have hdle := rs_entropy_rate_d_le_kf_proof q n k f hq hn hlo
  exact ⟨hmargin, hfpos, hflt, by omega, hdle⟩

private theorem rs_exact_error_exchange_fiber_card_le_proof
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Finset ι) (f ℓ : ℕ) (hE : E.card = f) :
    ((rsExactErrorSets (ι := ι) f).filter
      (fun E' => (E \ E').card = ℓ)).card ≤
      Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ := by
  classical
  let S : Finset (Finset ι) :=
    (rsExactErrorSets (ι := ι) f).filter (fun E' => (E \ E').card = ℓ)
  let T : Finset (Finset ι × Finset ι) :=
    E.powersetCard ℓ ×ˢ (Finset.univ \ E).powersetCard ℓ
  let φ : Finset ι → Finset ι × Finset ι :=
    fun E' => (E \ E', E' \ E)
  have hmap : Set.MapsTo φ (S : Set (Finset ι)) (T : Set (Finset ι × Finset ι)) := by
    intro E' hE'S
    have hm := Finset.mem_filter.mp hE'S
    have hE'card : E'.card = f := by
      simpa [rsExactErrorSets] using hm.1
    have hrightcard : (E' \ E).card = ℓ := by
      have hdiff := Finset.card_sdiff_comm (hE.trans hE'card.symm)
      omega
    have hleftsubset : E \ E' ⊆ E := Finset.sdiff_subset
    have hrightsubset : E' \ E ⊆ Finset.univ \ E := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
    change (E \ E', E' \ E) ∈ E.powersetCard ℓ ×ˢ (Finset.univ \ E).powersetCard ℓ
    rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_powersetCard]
      exact ⟨hleftsubset, hm.2⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hrightsubset, hrightcard⟩
  have hinj : (S : Set (Finset ι)).InjOn φ := by
    intro A hAS B hBS hab
    have hfst : E \ A = E \ B := congrArg Prod.fst hab
    have hsnd : A \ E = B \ E := congrArg Prod.snd hab
    have hrecover (X : Finset ι) :
        X = (E \ (E \ X)) ∪ (X \ E) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [hrecover A, hrecover B, hfst, hsnd]
  have hcard := Finset.card_le_card_of_injOn φ hmap hinj
  change S.card ≤ T.card at hcard
  simpa [S, T, Finset.card_product, Finset.card_powersetCard,
    Finset.card_sdiff, hE, Finset.card_univ] using hcard

private theorem rs_exact_error_union_card_proof
    {ι : Type} [DecidableEq ι] (E E' : Finset ι) (f : ℕ)
    (_hE : E.card = f) (hE' : E'.card = f) :
    (E ∪ E').card = f + (E \ E').card := by
  calc
    (E ∪ E').card = (E \ E').card + E'.card :=
      (Finset.card_sdiff_add_card E E').symm
    _ = f + (E \ E').card := by omega

private theorem rsAgreementPair_finrank_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E E' : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι)
    (hE : E.card = f) (hE' : E'.card = f) :
    Module.finrank F
      ↥(rsAgreementSpace domain k E ⊓ rsAgreementSpace domain k E') =
      k + f - min (E \ E').card (Fintype.card ι - f - k) := by
  have hfinE : Module.finrank F (rsAgreementSpace domain k E) = k + f := by
    rw [rsAgreementSpace_finrank domain k E, hE, min_eq_right hsmall]
  have hfinE' : Module.finrank F (rsAgreementSpace domain k E') = k + f := by
    rw [rsAgreementSpace_finrank domain k E', hE', min_eq_right hsmall]
  have hunion : (E ∪ E').card = f + (E \ E').card :=
    rs_exact_error_union_card_proof E E' f hE hE'
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (rsAgreementSpace domain k E) (rsAgreementSpace domain k E')
  rw [rsAgreementSpace_sup domain k E E', rsAgreementSpace_finrank,
    hunion, hfinE, hfinE'] at hdim
  by_cases hℓ : (E \ E').card ≤ Fintype.card ι - f - k
  · rw [min_eq_left hℓ]
    have hsumle : k + (f + (E \ E').card) ≤ Fintype.card ι := by omega
    rw [min_eq_right hsumle] at hdim
    omega
  · have hdle : Fintype.card ι - f - k ≤ (E \ E').card := by omega
    rw [min_eq_right hdle]
    have hnle : Fintype.card ι ≤ k + (f + (E \ E').card) := by omega
    rw [min_eq_left hnle] at hdim
    omega

private theorem rsAgreementPairCount_eq_pow_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E E' : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι)
    (hE : E.card = f) (hE' : E'.card = f) :
    rsAgreementPairCount domain k E E' =
      Fintype.card F ^
        (k + f - min (E \ E').card (Fintype.card ι - f - k)) := by
  classical
  unfold rsAgreementPairCount
  rw [← Fintype.card_subtype]
  let e :
      {w : ι → F // w ∈ rsAgreementSpace domain k E ∧
        w ∈ rsAgreementSpace domain k E'} ≃
      ↥(rsAgreementSpace domain k E ⊓ rsAgreementSpace domain k E') :=
    { toFun := fun w => ⟨w.1, Submodule.mem_inf.mpr w.2⟩
      invFun := fun w => ⟨w.1, Submodule.mem_inf.mp w.2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  calc
    Fintype.card {w : ι → F // w ∈ rsAgreementSpace domain k E ∧
        w ∈ rsAgreementSpace domain k E'} =
      Fintype.card ↥(rsAgreementSpace domain k E ⊓
        rsAgreementSpace domain k E') := Fintype.card_congr e
    _ = Fintype.card F ^
        Module.finrank F
          ↥(rsAgreementSpace domain k E ⊓ rsAgreementSpace domain k E') :=
      Module.card_eq_pow_finrank
    _ = _ := by
      rw [rsAgreementPair_finrank_proof domain k f E E' hsmall hE hE']

open scoped BigOperators in
private theorem rsAgreementPairCount_high_overlap_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f) :
    ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => Fintype.card ι - f - k ≤ (E \ E').card),
      rsAgreementPairCount domain k E E' ≤
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          Nat.choose (Fintype.card ι) f := by
  classical
  let d : ℕ := Fintype.card ι - f - k
  let S : Finset (Finset ι) :=
    (rsExactErrorSets (ι := ι) f).filter (fun E' => d ≤ (E \ E').card)
  let Q : ℕ := Fintype.card F ^ (k + f - d)
  have hterm : ∀ E' ∈ S, rsAgreementPairCount domain k E E' ≤ Q := by
    intro E' hE'S
    have hm := Finset.mem_filter.mp hE'S
    have hE'card : E'.card = f := by
      simpa [S, rsExactErrorSets] using hm.1
    have hp := rsAgreementPairCount_eq_pow_proof domain k f E E'
      hsmall hE hE'card
    have hmin : min (E \ E').card d = d := min_eq_right hm.2
    rw [hp, hmin]
  have hsum := Finset.sum_le_card_nsmul S
    (fun E' => rsAgreementPairCount domain k E E') Q hterm
  have hcard : S.card ≤ Nat.choose (Fintype.card ι) f := by
    calc
      S.card ≤ (rsExactErrorSets (ι := ι) f).card := by
        simpa only [S] using Finset.card_filter_le
          (rsExactErrorSets (ι := ι) f) (fun E' => d ≤ (E \ E').card)
      _ = Nat.choose (Fintype.card ι) f := rsExactErrorSets_card_proof f
  have hmul := Nat.mul_le_mul_right Q hcard
  change (∑ E' ∈ S, rsAgreementPairCount domain k E E') ≤
    Q * Nat.choose (Fintype.card ι) f
  exact le_trans (by simpa [Nat.nsmul_eq_mul] using hsum) (by
    simpa [Nat.mul_comm] using hmul)

open scoped BigOperators in
private theorem rsAgreementPairCount_low_overlap_fiber_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f ℓ : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f)
    (hℓ : ℓ < Fintype.card ι - f - k) :
    ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => (E \ E').card = ℓ),
      rsAgreementPairCount domain k E E' ≤
        Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ *
          Fintype.card F ^ (k + f - ℓ) := by
  classical
  let S : Finset (Finset ι) :=
    (rsExactErrorSets (ι := ι) f).filter (fun E' => (E \ E').card = ℓ)
  let Q : ℕ := Fintype.card F ^ (k + f - ℓ)
  have hterm : ∀ E' ∈ S, rsAgreementPairCount domain k E E' ≤ Q := by
    intro E' hE'S
    have hm := Finset.mem_filter.mp hE'S
    have hE'card : E'.card = f := by
      simpa [S, rsExactErrorSets] using hm.1
    have hp := rsAgreementPairCount_eq_pow_proof domain k f E E'
      hsmall hE hE'card
    have hmin : min (E \ E').card (Fintype.card ι - f - k) = ℓ := by
      rw [hm.2, min_eq_left (Nat.le_of_lt hℓ)]
    rw [hp, hmin]
  have hsum := Finset.sum_le_card_nsmul S
    (fun E' => rsAgreementPairCount domain k E E') Q hterm
  have hcard : S.card ≤ Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ := by
    simpa [S] using rs_exact_error_exchange_fiber_card_le_proof E f ℓ hE
  have hmul := Nat.mul_le_mul_right Q hcard
  change (∑ E' ∈ S, rsAgreementPairCount domain k E E') ≤
    Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ * Q
  exact le_trans (by simpa [Nat.nsmul_eq_mul] using hsum) (by
    simpa [Nat.mul_assoc] using hmul)

open scoped BigOperators in
private theorem rsAgreementPairCount_low_overlap_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => (E \ E').card < Fintype.card ι - f - k),
      rsAgreementPairCount domain k E E' ≤
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f := by
  classical
  let d : ℕ := Fintype.card ι - f - k
  have hregroup :
      (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
          (fun E' => (E \ E').card < d),
        rsAgreementPairCount domain k E E') =
        ∑ ℓ ∈ Finset.range d,
          ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => (E \ E').card = ℓ),
            rsAgreementPairCount domain k E E' := by
    have h := Finset.sum_fiberwise_eq_sum_filter
      (rsExactErrorSets (ι := ι) f) (Finset.range d)
      (fun E' : Finset ι => (E \ E').card)
      (fun E' => rsAgreementPairCount domain k E E')
    symm
    simpa only [Finset.mem_range] using h
  calc
    (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => (E \ E').card < Fintype.card ι - f - k),
      rsAgreementPairCount domain k E E') =
        ∑ ℓ ∈ Finset.range d,
          ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => (E \ E').card = ℓ),
            rsAgreementPairCount domain k E E' := by simpa only [d] using hregroup
    _ ≤ ∑ ℓ ∈ Finset.range d,
        Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ *
          Fintype.card F ^ (k + f - ℓ) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact rsAgreementPairCount_low_overlap_fiber_le_proof
        domain k f ℓ E hsmall hE (by simpa only [d] using Finset.mem_range.mp hℓ)
    _ = Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
        cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f := by
      unfold cs25SecondMomentANat
      rw [Finset.mul_sum]
      apply Finset.sum_congr
      · rfl
      · intro ℓ hℓ
        have hℓlt : ℓ < Fintype.card ι - f - k := Finset.mem_range.mp hℓ
        have hexp : k + f - ℓ =
            (k + f - (Fintype.card ι - f - k)) +
              (Fintype.card ι - f - k - ℓ) := by omega
        rw [hexp, pow_add]
        ac_rfl

open scoped BigOperators in
private theorem rsAgreementPairCount_fixed_error_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ∑ E' ∈ rsExactErrorSets (ι := ι) f,
      rsAgreementPairCount domain k E E' ≤
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
            Nat.choose (Fintype.card ι) f) := by
  classical
  let d : ℕ := Fintype.card ι - f - k
  let Q : ℕ := Fintype.card F ^ (k + f - d)
  let A : ℕ := cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f
  let N : ℕ := Nat.choose (Fintype.card ι) f
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (rsExactErrorSets (ι := ι) f) (fun E' : Finset ι => (E \ E').card < d)
    (fun E' => rsAgreementPairCount domain k E E')
  have hlo :
      (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
          (fun E' => (E \ E').card < d),
        rsAgreementPairCount domain k E E') ≤ Q * A := by
    simpa only [d, Q, A] using
      rsAgreementPairCount_low_overlap_sum_le_proof domain k f E hsmall hE hdle
  have hhi :
      (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
          (fun E' => d ≤ (E \ E').card),
        rsAgreementPairCount domain k E E') ≤ Q * N := by
    simpa only [d, Q, N] using
      rsAgreementPairCount_high_overlap_sum_le_proof domain k f E hsmall hE
  change (∑ E' ∈ rsExactErrorSets (ι := ι) f,
      rsAgreementPairCount domain k E E') ≤ Q * (A + N)
  calc
    (∑ E' ∈ rsExactErrorSets (ι := ι) f,
        rsAgreementPairCount domain k E E') =
        (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => (E \ E').card < d),
          rsAgreementPairCount domain k E E') +
        (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => d ≤ (E \ E').card),
          rsAgreementPairCount domain k E E') := by
      simpa only [not_lt] using hsplit.symm
    _ ≤ Q * A + Q * N := Nat.add_le_add hlo hhi
    _ = Q * (A + N) := by rw [Nat.mul_add]

open scoped BigOperators in
private theorem cs25CertificateCount_sq_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hsmall : k + f ≤ Fintype.card ι)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ∑ w : ι → F, (cs25CertificateCount domain k f w) ^ 2 ≤
      Nat.choose (Fintype.card ι) f *
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
            Nat.choose (Fintype.card ι) f) := by
  classical
  rw [cs25CertificateCount_sq_sum_eq_pair_sum_nat_proof domain k f]
  let Q : ℕ :=
    Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
      (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
        Nat.choose (Fintype.card ι) f)
  have hterm : ∀ E ∈ rsExactErrorSets (ι := ι) f,
      (∑ E' ∈ rsExactErrorSets (ι := ι) f,
        rsAgreementPairCount domain k E E') ≤ Q := by
    intro E hE
    have hEcard : E.card = f := by
      simpa [rsExactErrorSets] using hE
    simpa only [Q] using
      rsAgreementPairCount_fixed_error_sum_le_proof
        domain k f E hsmall hEcard hdle
  have hsum := Finset.sum_le_card_nsmul (rsExactErrorSets (ι := ι) f)
    (fun E => ∑ E' ∈ rsExactErrorSets (ι := ι) f,
      rsAgreementPairCount domain k E E') Q hterm
  calc
    (∑ E ∈ rsExactErrorSets (ι := ι) f,
        ∑ E' ∈ rsExactErrorSets (ι := ι) f,
          rsAgreementPairCount domain k E E') ≤
        (rsExactErrorSets (ι := ι) f).card • Q := hsum
    _ = Nat.choose (Fintype.card ι) f *
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
            Nat.choose (Fintype.card ι) f) := by
      rw [rsExactErrorSets_card_proof]
      simp only [Q, Nat.nsmul_eq_mul, Nat.mul_assoc]

open scoped BigOperators in
private theorem cs25CertificateSupport_lower_bound_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hqpos : 0 < Fintype.card F)
    (hsmall : k + f ≤ Fintype.card ι)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    (Nat.choose (Fintype.card ι) f : ℝ) *
        (Fintype.card F : ℝ) ^ Fintype.card ι ≤
      ((Finset.univ.filter (fun w : ι → F =>
          0 < cs25CertificateCount domain k f w)).card : ℝ) *
        ((Nat.choose (Fintype.card ι) f : ℝ) +
          cs25SecondMomentA (Fintype.card F) (Fintype.card ι) k f) := by
  classical
  let n : ℕ := Fintype.card ι
  let q : ℕ := Fintype.card F
  let d : ℕ := n - f - k
  let K : ℕ := k + f
  let N : ℕ := Nat.choose n f
  let AN : ℕ := cs25SecondMomentANat q n k f
  let A : ℝ := cs25SecondMomentA q n k f
  let X : (ι → F) → ℕ := fun w => cs25CertificateCount domain k f w
  let S : Finset (ι → F) := Finset.univ.filter (fun w => 0 < X w)
  have hf_le_n : f ≤ n := by dsimp [n]; omega
  have hNposNat : 0 < N := by
    dsimp [N]
    exact Nat.choose_pos hf_le_n
  have hqposR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hsumNat : ∑ w : ι → F, X w = N * q ^ K := by
    simpa only [X, N, q, n, K] using
      cs25CertificateCount_sum_nat_proof domain k f hsmall
  have hsumReal : ∑ w : ι → F, (X w : ℝ) = (N : ℝ) * (q : ℝ) ^ K := by
    exact_mod_cast hsumNat
  have hsumSupport :
      ∑ w ∈ S, (X w : ℝ) = (N : ℝ) * (q : ℝ) ^ K := by
    calc
      (∑ w ∈ S, (X w : ℝ)) = ∑ w : ι → F, (X w : ℝ) := by
        dsimp [S]
        apply Finset.sum_filter_of_ne
        intro w hw hne
        have hxne : X w ≠ 0 := by
          intro hx
          apply hne
          simp [hx]
        exact Nat.pos_of_ne_zero hxne
      _ = (N : ℝ) * (q : ℝ) ^ K := hsumReal
  have hsqNat :
      ∑ w : ι → F, (X w) ^ 2 ≤
        N * q ^ (K - d) * (AN + N) := by
    simpa only [X, N, q, n, K, d, AN] using
      cs25CertificateCount_sq_sum_le_proof domain k f hsmall hdle
  have hsqReal :
      ∑ w : ι → F, (X w : ℝ) ^ 2 ≤
        (N : ℝ) * (q : ℝ) ^ (K - d) * ((AN : ℝ) + (N : ℝ)) := by
    exact_mod_cast hsqNat
  have hANcast : (AN : ℝ) = A := by
    simpa only [AN, A, q, n] using cs25SecondMomentANat_cast_proof q n k f hqpos
  have hsqSupport :
      ∑ w ∈ S, (X w : ℝ) ^ 2 ≤
        (N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ)) := by
    calc
      (∑ w ∈ S, (X w : ℝ) ^ 2) = ∑ w : ι → F, (X w : ℝ) ^ 2 := by
        dsimp [S]
        apply Finset.sum_filter_of_ne
        intro w hw hne
        have hxne : X w ≠ 0 := by
          intro hx
          apply hne
          simp [hx]
        exact Nat.pos_of_ne_zero hxne
      _ ≤ (N : ℝ) * (q : ℝ) ^ (K - d) * ((AN : ℝ) + (N : ℝ)) := hsqReal
      _ = (N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ)) := by rw [hANcast]
  have hcs :
      (∑ w ∈ S, (X w : ℝ)) ^ 2 ≤
        (S.card : ℝ) * ∑ w ∈ S, (X w : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmoment :
      ((N : ℝ) * (q : ℝ) ^ K) ^ 2 ≤
        (S.card : ℝ) *
          ((N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ))) := by
    rw [hsumSupport] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_left hsqSupport (by positivity))
  have hKn : K + d = n := by
    dsimp [K, d, n]
    omega
  have hdK : d ≤ K := by simpa only [d, K, n] using hdle
  have hexp : (K - d) + n = K + K := by omega
  have hpowers :
      (q : ℝ) ^ (K - d) * (q : ℝ) ^ n =
        (q : ℝ) ^ K * (q : ℝ) ^ K := by
    rw [← pow_add, ← pow_add, hexp]
  have hleft :
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) =
        ((N : ℝ) * (q : ℝ) ^ K) ^ 2 := by
    rw [pow_two]
    calc
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) =
          (N : ℝ) * (N : ℝ) *
            ((q : ℝ) ^ (K - d) * (q : ℝ) ^ n) := by ring
      _ = (N : ℝ) * (N : ℝ) *
            ((q : ℝ) ^ K * (q : ℝ) ^ K) := by rw [hpowers]
      _ = ((N : ℝ) * (q : ℝ) ^ K) *
            ((N : ℝ) * (q : ℝ) ^ K) := by ring
  have hright :
      (S.card : ℝ) *
          ((N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ))) =
        ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((S.card : ℝ) * ((N : ℝ) + A)) := by ring
  have hfactor :
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) ≤
        ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((S.card : ℝ) * ((N : ℝ) + A)) := by
    calc
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) =
          ((N : ℝ) * (q : ℝ) ^ K) ^ 2 := hleft
      _ ≤ (S.card : ℝ) *
          ((N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ))) := hmoment
      _ = ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((S.card : ℝ) * ((N : ℝ) + A)) := hright
  have hfactorPos : (0 : ℝ) < (N : ℝ) * (q : ℝ) ^ (K - d) := by
    exact mul_pos (by exact_mod_cast hNposNat) (pow_pos hqposR _)
  change (N : ℝ) * (q : ℝ) ^ n ≤ (S.card : ℝ) * ((N : ℝ) + A)
  exact le_of_mul_le_mul_of_pos_left hfactor hfactorPos

open scoped BigOperators in
private theorem rsFarWords_weighted_card_bound_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hqpos : 0 < Fintype.card F)
    (hsmall : k + f ≤ Fintype.card ι)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ((rsFarWords domain k f).card : ℝ) *
        ((Nat.choose (Fintype.card ι) f : ℝ) +
          cs25SecondMomentA (Fintype.card F) (Fintype.card ι) k f) ≤
      (Fintype.card F : ℝ) ^ Fintype.card ι *
        cs25SecondMomentA (Fintype.card F) (Fintype.card ι) k f := by
  classical
  let n : ℕ := Fintype.card ι
  let q : ℕ := Fintype.card F
  let N : ℕ := Nat.choose n f
  let A : ℝ := cs25SecondMomentA q n k f
  let S : Finset (ι → F) := Finset.univ.filter
    (fun w => 0 < cs25CertificateCount domain k f w)
  let B : Finset (ι → F) := rsFarWords domain k f
  have hf_le : f ≤ Fintype.card ι := by omega
  have hsupport :
      (N : ℝ) * (q : ℝ) ^ n ≤ (S.card : ℝ) * ((N : ℝ) + A) := by
    simpa only [N, q, n, A, S] using
      cs25CertificateSupport_lower_bound_proof domain k f hqpos hsmall hdle
  have hclose : S = Finset.univ \ B := by
    simpa only [S, B] using
      rs_close_words_eq_certificate_support_proof domain k f hf_le
  have hcardNat : S.card + B.card = q ^ n := by
    have hcard0 :
        (Finset.univ \ B).card + B.card =
          (Finset.univ : Finset (ι → F)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    rw [← hclose, Finset.card_univ, Fintype.card_fun] at hcard0
    simpa only [q, n] using hcard0
  have hcardReal : (S.card : ℝ) + (B.card : ℝ) = (q : ℝ) ^ n := by
    exact_mod_cast hcardNat
  have hcardN := congrArg (fun x : ℝ => x * (N : ℝ)) hcardReal
  have hBN : (B.card : ℝ) * (N : ℝ) ≤ (S.card : ℝ) * A := by
    nlinarith [hsupport, hcardN]
  change (B.card : ℝ) * ((N : ℝ) + A) ≤ (q : ℝ) ^ n * A
  calc
    (B.card : ℝ) * ((N : ℝ) + A) =
        (B.card : ℝ) * (N : ℝ) + (B.card : ℝ) * A := by ring
    _ ≤ (S.card : ℝ) * A + (B.card : ℝ) * A :=
      add_le_add hBN le_rfl
    _ = ((S.card : ℝ) + (B.card : ℝ)) * A := by ring
    _ = (q : ℝ) ^ n * A := by rw [hcardReal]

private theorem rs_fraction_le_entropy_peak
    (q n f : ℕ) (hq : 2 ≤ q) (hnq : n ≤ q) (hf : f < n) :
    (f : ℝ) / n ≤ 1 - 1 / (q : ℝ) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq)
  have hdiv : (n : ℝ) / q ≤ 1 := (div_le_one hqR).2 (by exact_mod_cast hnq)
  rw [div_le_iff₀ hnR]
  have hfRle : (f : ℝ) + 1 ≤ n := by
    exact_mod_cast (show f + 1 ≤ n by omega)
  calc
    (f : ℝ) ≤ (n : ℝ) - 1 := by linarith
    _ ≤ (n : ℝ) - (n : ℝ) / q := by linarith
    _ = (1 - 1 / (q : ℝ)) * n := by ring

private theorem cs25_overlap_exp_le_entropy_power_proof
    (q n f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q)
    (hfpos : 0 < f) (hflt : f < n) :
    Real.exp (2 * Real.sqrt ((f : ℝ) * (n - f : ℕ) / q)) ≤
      (q : ℝ) ^ ((n : ℝ) *
        ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) := by
  have hn : 0 < n := lt_trans hfpos hflt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by positivity
  have hq2 : 2 ≤ q := by omega
  let x : ℝ := (f : ℝ) / n
  let h : ℝ := qEntropy q x - x
  let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
  let y : ℝ := (f : ℝ) * (n - f : ℕ) / q
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxlt : x < 1 := by
    dsimp [x]
    exact (div_lt_one hnR).2 (by exact_mod_cast hflt)
  have hxpeak : x ≤ 1 - 1 / (q : ℝ) := by
    dsimp [x]
    exact rs_fraction_le_entropy_peak q n f hq2 hnq hflt
  have hgap : 4 * x * (1 - x) ≤ (Real.log (q : ℝ)) ^ 2 * h := by
    dsimp [h]
    exact cs25_quadratic_entropy_gap_proof q x hq hxpos.le hxpeak
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have hh : 0 ≤ h := by
    have hleft : 0 < 4 * x * (1 - x) := by positivity
    nlinarith only [hgap, hleft, sq_nonneg (Real.log (q : ℝ))]
  have hy_nonneg : 0 ≤ y := by dsimp [y]; positivity
  have hnum_nonneg : 0 ≤ (f : ℝ) * (n - f : ℕ) := by positivity
  have hy_le : y ≤ (n : ℝ) * x * (1 - x) := by
    have hdiv : (f : ℝ) * (n - f : ℕ) / (q : ℝ) ≤
        (f : ℝ) * (n - f : ℕ) / (n : ℝ) :=
      div_le_div_of_nonneg_left hnum_nonneg hnR (by exact_mod_cast hnq)
    have hid : (f : ℝ) * (n - f : ℕ) / (n : ℝ) =
        (n : ℝ) * x * (1 - x) := by
      dsimp [x]
      rw [Nat.cast_sub (Nat.le_of_lt hflt)]
      field_simp [hnR.ne']
    rw [hid] at hdiv
    exact hdiv
  have hsq_bound : 4 * y ≤
      (Real.log (q : ℝ)) ^ 2 * (n : ℝ) * h := by
    have hm := mul_le_mul_of_nonneg_left hgap hnR.le
    nlinarith only [hm, hy_le]
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = h / (n : ℝ) := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact div_nonneg hh hnR.le
  have hl_nonneg : 0 ≤ 2 * Real.sqrt y := by positivity
  have hr_nonneg : 0 ≤ Real.log (q : ℝ) * ((n : ℝ) * s) := by positivity
  have hl_sq : (2 * Real.sqrt y) ^ 2 = 4 * y := by
    rw [mul_pow, Real.sq_sqrt hy_nonneg]
    norm_num
  have hr_sq : (Real.log (q : ℝ) * ((n : ℝ) * s)) ^ 2 =
      (Real.log (q : ℝ)) ^ 2 * (n : ℝ) * h := by
    rw [mul_pow, mul_pow, hs_sq]
    field_simp [hnR.ne']
  change Real.exp (2 * Real.sqrt y) ≤ (q : ℝ) ^ ((n : ℝ) * s)
  rw [Real.rpow_def_of_pos hqR]
  apply Real.exp_le_exp.mpr
  apply (sq_le_sq₀ hl_nonneg hr_nonneg).mp
  rw [hl_sq, hr_sq]
  exact hsq_bound

private theorem cs25SecondMomentA_le_entropy_power_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q)
    (hfpos : 0 < f) (hflt : f < n) :
    let h : ℝ := qEntropy q ((f : ℝ) / n) - (f : ℝ) / n
    let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
    cs25SecondMomentA q n k f ≤
      (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) := by
  dsimp
  have hqNat : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hover := cs25OverlapSum_le_exp_two_sqrt q n k f hqNat
  have hexp := cs25_overlap_exp_le_entropy_power_proof q n f hq hnq hfpos hflt
  have hcomp :
      cs25OverlapSum q n k f ≤
        (q : ℝ) ^ ((n : ℝ) *
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) :=
    le_trans hover hexp
  unfold cs25SecondMomentA
  calc
    (q : ℝ) ^ (n - f - k) * cs25OverlapSum q n k f ≤
        (q : ℝ) ^ (n - f - k) *
          (q : ℝ) ^ ((n : ℝ) *
            ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) *
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) := by
      rw [Real.rpow_add hqR, Real.rpow_natCast]

private theorem cs25_second_momentA_small_of_entropy_rate_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi : (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    ((q : ℝ) - 1) * cs25SecondMomentA q n k f <
      (Nat.choose n f : ℝ) := by
  obtain ⟨_, hfpos, hflt, _⟩ :=
    rs_entropy_rate_parameter_facts q n k f hn hlo hhi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by positivity
  have hqgt1R : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq1R : (1 : ℝ) ≤ q := hqgt1R.le
  have hqm1pos : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr hqgt1R
  let H : ℝ := qEntropy q ((f : ℝ) / n)
  let h : ℝ := H - (f : ℝ) / n
  let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
  let D : ℝ :=
    (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2)
  let B : ℝ := ((q : ℝ) - 1) ^ f * D
  have hxpos : (0 : ℝ) < (f : ℝ) / n := by positivity
  have hxlt : (f : ℝ) / n < 1 :=
    (div_lt_one hnR).2 (by exact_mod_cast hflt)
  have hbasepos :
      0 < 8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hnR) hxpos) (sub_pos.mpr hxlt)
  have hDpos : 0 < D := by
    dsimp [D]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_pos.2 hbasepos
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (pow_pos hqm1pos _) hDpos
  have hA0 := cs25SecondMomentA_le_entropy_power_proof q n k f hq hnq hfpos hflt
  have hA :
      cs25SecondMomentA q n k f ≤
        (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) := by
    simpa only [H, h, s] using hA0
  have hpower0 := cs25_shell_power_bound q n f hq hnq hfpos hflt
  have hpower : ((q : ℝ) - 1) ^ (f + 1) * D < (q : ℝ) ^ (f + 2) := by
    simpa only [D] using hpower0
  have hexp0 := rs_entropy_rate_exponent_slack q n k f hn hlo hhi
  have hexp :
      (((n - f - k : ℕ) : ℝ) + 2 + (n : ℝ) * s) ≤ (n : ℝ) * h := by
    simpa only [H, h, s] using hexp0
  have hid : (n : ℝ) * h + f = (n : ℝ) * H := by
    dsimp [h, H]
    field_simp [hnR.ne']
    ring
  have hexp' :
      (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s + ((f + 2 : ℕ) : ℝ)) ≤
        (n : ℝ) * H := by
    norm_num at hexp ⊢
    nlinarith only [hexp, hid]
  have hshell0 := cs25_entropy_shell_le_choose_proof q n f hq hn hfpos hflt
  have hshell :
      (q : ℝ) ^ ((n : ℝ) * H) ≤ (Nat.choose n f : ℝ) * B := by
    simpa only [H, B, D, mul_assoc] using hshell0
  have hprod :
      (((q : ℝ) - 1) * cs25SecondMomentA q n k f) * B <
        (Nat.choose n f : ℝ) * B := by
    calc
      (((q : ℝ) - 1) * cs25SecondMomentA q n k f) * B =
          cs25SecondMomentA q n k f * (((q : ℝ) - 1) ^ (f + 1) * D) := by
        dsimp [B]
        rw [pow_succ]
        ring
      _ ≤ (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) *
          (((q : ℝ) - 1) ^ (f + 1) * D) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ < (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) *
          (q : ℝ) ^ (f + 2) :=
        mul_lt_mul_of_pos_left hpower
          (Real.rpow_pos_of_pos hqR _)
      _ = (q : ℝ) ^
          (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s + ((f + 2 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hqR]
      _ ≤ (q : ℝ) ^ ((n : ℝ) * H) :=
        Real.rpow_le_rpow_of_exponent_le hq1R hexp'
      _ ≤ (Nat.choose n f : ℝ) * B := hshell
  exact lt_of_mul_lt_mul_right hprod hBpos.le

open scoped BigOperators in
private theorem rsFarWords_card_lt_of_entropy_rate_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hq : 10 ≤ Fintype.card F)
    (hnq : Fintype.card ι ≤ Fintype.card F)
    (hf : f ≤ Fintype.card ι)
    (hlo :
      1 - qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι) +
          2 / (Fintype.card ι : ℝ) +
          ((qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι) -
              (f : ℝ) / Fintype.card ι) /
            (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2) ≤
        (k : ℝ) / Fintype.card ι)
    (hhi :
      (k : ℝ) / Fintype.card ι ≤
        1 - (f : ℝ) / Fintype.card ι -
          2 / (Fintype.card ι : ℝ)) :
    (rsFarWords domain k f).card <
      Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  let n : ℕ := Fintype.card ι
  let q : ℕ := Fintype.card F
  let N : ℕ := Nat.choose n f
  let A : ℝ := cs25SecondMomentA q n k f
  let B : Finset (ι → F) := rsFarWords domain k f
  have hn : 0 < n := by simpa only [n] using (Fintype.card_pos : 0 < Fintype.card ι)
  have hqpos : 0 < q := by simpa only [q] using (Fintype.card_pos : 0 < Fintype.card F)
  have hq1 : 1 < q := by simpa only [q] using (show 1 < Fintype.card F by omega)
  obtain ⟨hmargin, hfpos, hflt, hd2, hdle⟩ :=
    rs_entropy_rate_full_parameter_facts_proof q n k f
      (by simpa only [q] using hq) hn
      (by simpa only [q, n] using hlo) (by simpa only [n] using hhi)
  have hkf : k + f ≤ n := by omega
  have hweighted :
      (B.card : ℝ) * ((N : ℝ) + A) ≤ (q : ℝ) ^ n * A := by
    simpa only [B, N, A, q, n] using
      rsFarWords_weighted_card_bound_proof domain k f
        (by simpa only [q] using hqpos) (by simpa only [n] using hkf)
        (by simpa only [q, n] using hdle)
  have hA : 0 ≤ A := by
    simpa only [A] using cs25SecondMomentA_nonneg_proof q n k f
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.choose_pos (by simpa only [n] using hf)
  have hAsm : ((q : ℝ) - 1) * A < (N : ℝ) := by
    simpa only [q, n, N, A] using
      cs25_second_momentA_small_of_entropy_rate_proof q n k f
        (by simpa only [q] using hq) (by simpa only [q, n] using hnq) hn
        (by simpa only [q, n] using hlo) (by simpa only [n] using hhi)
  have hfinal := nat_card_lt_pow_pred_of_weighted_bound
    q n N B.card A hq1 hn hN hA hAsm hweighted
  simpa only [q, n, B] using hfinal

open scoped ProbabilityTheory in
open scoped BigOperators in
private theorem rs_epsCa_eq_one_of_entropy_rate_impl
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hn_le_q : Fintype.card ι ≤ Fintype.card F)
    (_hf_le : f ≤ Fintype.card ι)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
            + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
                  - (f : ℝ) / Fintype.card ι)
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi :
        (k : ℝ) / Fintype.card ι ≤
          1 - (f : ℝ) / Fintype.card ι - 2 / (Fintype.card ι : ℝ)) :
    let δ : NNReal := (f : NNReal) / Fintype.card ι
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1 := by
  classical
  dsimp
  let C : Set (ι → F) := ReedSolomon.code domain k
  let v : ι → F := rsBoundaryWord domain k
  let δ : NNReal := (f : NNReal) / Fintype.card ι
  change epsCa (F := F) (A := F) C δ δ = 1
  have hbad :
      (Finset.univ.filter (fun w : ι → F =>
        ¬ Code.distFromCode w C ≤ f)).card <
        Fintype.card F ^ (Fintype.card ι - 1) := by
    dsimp [C]
    simpa [rsFarWords] using
      rsFarWords_card_lt_of_entropy_rate_proof domain k f
        _hq_ge _hn_le_q _hf_le _hδ_lo _hδ_hi
  obtain ⟨u0, hu0⟩ :=
    exists_base_all_translates_close_of_bad_count C v f hbad
  let u : Code.WordStack F (Fin 2) ι :=
    fun j => if j = 0 then u0 else v
  have hclose : ∀ γ : F,
      Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal) := by
    intro γ
    have habs := hu0 γ
    have hrel :=
      (Code.distFromCode_le_iff_relDistFromCode_le (u0 + γ • v) f).mp habs
    simpa [u, δ] using hrel
  have hmargin : k + f + 2 ≤ Fintype.card ι :=
    rs_entropy_rate_nat_margin k f _hδ_hi
  have hvfar : Code.distFromCode v C > f := by
    simpa [v, C] using rsBoundaryWord_far domain k f hmargin
  have hrelfar :
      ¬ Code.relDistFromCode (u 1) C ≤ (δ : ENNReal) := by
    intro hrel
    have hrel' : Code.relDistFromCode v C ≤ (δ : ENNReal) := by
      simpa [u] using hrel
    have habs : Code.distFromCode v C ≤ f :=
      (Code.distFromCode_le_iff_relDistFromCode_le v f).mpr (by
        simpa [δ] using hrel')
    exact (not_le_of_gt hvfar) habs
  have hjoint : ¬ Code.jointProximity C (u := u) δ :=
    not_jointProximity_of_second_row_far C u δ hrelfar
  exact epsCa_eq_one_of_all_folds_close_not_joint C δ u hjoint hclose

omit [DecidableEq ι] in
/-- Complete CA breakdown for a Reed--Solomon code whose rate lies in the entropy band

  `1 - H_q(f/n) + 2/n + √((H_q(f/n) - f/n)/n) ≤ ρ ≤ 1 - f/n - 2/n`

The radius is the integer grid point `f/n`; the entropy hypothesis is not extended to arbitrary
real radii. -/
theorem rs_epsCa_eq_one_of_entropy_rate
    (domain : ι ↪ F) (k f : ℕ)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hn_le_q : Fintype.card ι ≤ Fintype.card F)
    (_hf_le : f ≤ Fintype.card ι)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
            + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
                  - (f : ℝ) / Fintype.card ι)
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi :
        (k : ℝ) / Fintype.card ι ≤
          1 - (f : ℝ) / Fintype.card ι - 2 / (Fintype.card ι : ℝ)) :
    let δ : ℝ≥0 := (f : ℝ≥0) / Fintype.card ι
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1 := by
  classical
  exact rs_epsCa_eq_one_of_entropy_rate_impl domain k f
    _hq_ge _hn_le_q _hf_le _hδ_lo _hδ_hi

end ReedSolomon

end CodingTheory
