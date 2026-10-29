/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Frs.Pinning
public import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator

/-!
# Affine-line MCA bounds for subspace-design codes

Pinning, list-decoding amplification, and the affine-line MCA bound at radius
`1 - τ(2t) - 3/(2t)`.
-/

@[expose] public section

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap FrsInternal

open scoped NNReal in
open scoped BigOperators in
/-- A subspace-design bound yields strong line decodability by pinning. -/
theorem strongLineDecodable_of_subspaceDesign
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r a b : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (hr : 0 < r) (ε : ℝ) (hε : 2 / (r : ℝ) < ε)
    (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 - τ r - ε)
    (hb : 2 ≤ b)
    (hretain : (b : ℝ) * ((r : ℝ) + ε) ≤ (a : ℝ) * ε) :
    StrongLineDecodable (C : Set (ι → Fin s → F)) δ a b := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hεpos : 0 < ε := lt_trans (by positivity : (0 : ℝ) < 2 / (r : ℝ)) hε
  intro f₀ f₁ U hU T hTclose ha
  have hspanlt := subspaceDesign_lineCloseSpan_finrank_lt τ C hdesign
    f₀ f₁ U hU (δ : ℝ) ε r hr hδ hε
  have hspanle : Module.finrank F (lineCloseSpan f₀ f₁ U (δ : ℝ)) ≤ r :=
    Nat.le_of_lt hspanlt
  obtain ⟨S, hterm, hpot⟩ := exists_terminal_line_pinning τ C hdesign
    f₀ f₁ U (δ : ℝ) ε hU hspanle hεpos T hTclose hδ ∅
  rw [linePinnedSeedsOn_empty,
    pinnedSubspace_empty (lineCloseSpan f₀ f₁ U (δ : ℝ))] at hpot
  have haR : (a : ℝ) ≤ T.card := by exact_mod_cast ha
  have haeps : (a : ℝ) * ε ≤ (T.card : ℝ) * ε :=
    mul_le_mul_of_nonneg_right haR hεpos.le
  have hdR : (Module.finrank F (lineCloseSpan f₀ f₁ U (δ : ℝ)) : ℝ) < r := by
    exact_mod_cast hspanlt
  have hA0 : (0 : ℝ) ≤ (linePinnedSeedsOn T f₀ f₁ U S).card := Nat.cast_nonneg _
  have hdim :
      ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) *
          ((Module.finrank F (lineCloseSpan f₀ f₁ U (δ : ℝ)) : ℝ) + ε) ≤
        ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) * ((r : ℝ) + ε) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    linarith only [hdR]
  have hchain : (b : ℝ) * ((r : ℝ) + ε) ≤
      ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) * ((r : ℝ) + ε) :=
    hretain.trans (haeps.trans (hpot.trans hdim))
  have hden : 0 < (r : ℝ) + ε := by linarith only [hrR, hεpos]
  have hbR : (b : ℝ) ≤ (linePinnedSeedsOn T f₀ f₁ U S).card :=
    le_of_mul_le_mul_right hchain hden
  have hbNat : b ≤ (linePinnedSeedsOn T f₀ f₁ U S).card := by
    exact_mod_cast hbR
  have hterm' : lineCloseSpan f₀ f₁ U (δ : ℝ) ⊓
      vanishOnCoordinates (F := F) (s := s) S = ⊥ := by
    simpa only [pinnedSubspace] using hterm
  obtain ⟨u₀, hu₀, u₁, hu₁, halign⟩ :=
    pinned_lineSeeds_lie_on_affine_codeword_line C f₀ f₁ U (δ : ℝ)
      T hTclose hU S hterm' (hb.trans hbNat)
  refine ⟨u₀, hu₀, u₁, hu₁, hbNat.trans (Finset.card_le_card ?_)⟩
  intro γ hγ
  have hdata : γ ∈ T ∧ ∀ i ∈ S, U γ i = f₀ i + γ • f₁ i := by
    simpa only [linePinnedSeedsOn, Finset.mem_filter] using hγ
  apply Finset.mem_filter.mpr
  exact ⟨hdata.1, halign γ hγ⟩

/-- Pinning at dimension `2t` and slack `3/(2t)`. -/
theorem strongLineDecodable_two_mul_of_subspaceDesign
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s t a : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (ht : 0 < t)
    (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 - τ (2 * t) - 3 / (2 * (t : ℝ)))
    (hretain : (2 * (t : ℝ)) * (2 * t + 3 / (2 * t)) ≤
      (a : ℝ) * (3 / (2 * t))) :
    StrongLineDecodable (C : Set (ι → Fin s → F)) δ a (2 * t) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  refine strongLineDecodable_of_subspaceDesign τ C hdesign (by omega)
    (3 / (2 * (t : ℝ))) ?_ δ hδ (by omega) ?_
  · push_cast
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hretain

open scoped NNReal in
/-- Strong line decodability when the profile is bounded by a rate plus `1/(2t)`. -/
theorem strongLineDecodable_two_mul_of_profile_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s t : ℕ} (τ : ℕ → ℝ) (R : ℝ)
    (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (ht : 3 ≤ t)
    (δ : NNReal)
    (hprofile : τ (2 * t) ≤ R + 1 / (2 * (t : ℝ)))
    (hδ : (δ : ℝ) ≤ 1 - R - 2 / (t : ℝ)) :
    StrongLineDecodable (C : Set (ι → Fin s → F)) δ
      (3 * t ^ 3) (2 * t) := by
  have htpos : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have htR3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hrad : (δ : ℝ) ≤
      1 - τ (2 * t) - 3 / (2 * (t : ℝ)) := by
    have hid : 1 / (2 * (t : ℝ)) + 3 / (2 * (t : ℝ)) = 2 / (t : ℝ) := by
      field_simp
      ring
    nlinarith only [hprofile, hδ, hid]
  have hret : (((2 * t : ℕ) : ℝ)) *
        ((((2 * t : ℕ) : ℝ)) + 3 / (2 * (t : ℝ))) ≤
      (((3 * t ^ 3 : ℕ) : ℝ)) * (3 / (2 * (t : ℝ))) := by
    have hsq : (9 : ℝ) ≤ (t : ℝ) ^ 2 := by
      have hmul : (0 : ℝ) ≤ ((t : ℝ) - 3) * ((t : ℝ) + 3) :=
        mul_nonneg (sub_nonneg.mpr htR3) (by linarith)
      nlinarith only [hmul]
    push_cast
    field_simp
    nlinarith only [hsq]
  apply strongLineDecodable_two_mul_of_subspaceDesign τ C hdesign htpos δ hrad
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hret

/-- Boost strong line decodability using a list bound and convert it to an MCA bound. -/
theorem mcaError_le_of_strongLineDecodable
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    {s t a : ℕ} (C : Submodule F (ι → Fin s → F)) (δ : NNReal)
    (ht : 0 < t) (hδpos : 0 < δ) (hδlt : δ < 1)
    (hweak : StrongLineDecodable (C : Set (ι → Fin s → F)) δ a (2 * t))
    (hlist : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (2 * (t : ℝ)) / (2 * (t : ℝ) - 1)) ≤ (t : ℕ∞))
    (hbudget : (t + 1) ^ 2 ≤ Fintype.card ι * t + a) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) * t + a) / Fintype.card F) := by
  by_cases hfield : (t + 1) ^ 2 < Fintype.card F
  · have hstrong : StrongLineDecodable (C : Set (ι → Fin s → F)) δ
        (Fintype.card ι * t + a) (Fintype.card ι + 1) :=
      strongLineDecodable_boost_of_lambda_le C hweak (by omega)
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlist) hfield
    have hline := strongLineDecodable_to_isLineDecodable
      (F := F) (C : Set (ι → Fin s → F)) δ hstrong
    have hmca := IsLineDecodable.mcaError_le C δ
      (Fintype.card ι * t + a)
      (by exact_mod_cast hδpos) hδlt hline
    change mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ _ at hmca
    have hnorm : ENNReal.ofReal
        (((Fintype.card ι : ℝ) * t + (a : ℝ)) / Fintype.card F) =
        ((Fintype.card ι * t + a : ℕ) : ENNReal) /
          (Fintype.card F : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity)]
      have hnum : (Fintype.card ι : ℝ) * t + (a : ℝ) =
          ((Fintype.card ι * t + a : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hnum, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [hnorm]
    exact hmca
  · have hq : Fintype.card F ≤ (t + 1) ^ 2 := by omega
    have hqP : Fintype.card F ≤ Fintype.card ι * t + a := hq.trans hbudget
    refine (mcaError_le_one (AffineLineGenerator F) C (δ : ℝ)).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by positivity)]
    norm_num only [one_mul]
    exact_mod_cast hqP

/-- An affine-line MCA bound for a `τ`-subspace-design code:

  `ε_mca(C, 1 - τ(2t) - 3/(2t)) ≤ (t·n + 4·t³) / |F|`.

[GG25, Corollary 4.9] prints `τ(tℓ+ℓ)`, while its proof through Theorem 4.8 gives
`τ((ℓ+1)t)`. The affine specialization uses `ℓ = 1`. -/
theorem subspace_design_mcaError_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (t : ℕ) (_ht : 0 < t) :
    mcaError (AffineLineGenerator F) C
        (1 - τ (2 * t) - 3 / (2 * t)) ≤
      ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 3) / Fintype.card F) := by
  classical
  have htR : (0 : ℝ) < t := by exact_mod_cast _ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast _ht
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbudget : (t + 1) ^ 2 ≤ Fintype.card ι * t + 4 * t ^ 3 := by
    have hn' : 1 ≤ Fintype.card ι := Fintype.card_pos
    have hc : t ^ 2 ≤ t ^ 3 := by
      calc
        t ^ 2 = t ^ 2 * 1 := by ring
        _ ≤ t ^ 2 * t := Nat.mul_le_mul_left _ _ht
        _ = t ^ 3 := by ring
    nlinarith only [hn', _ht, hc, sq_nonneg (t - 1)]
  by_cases hC : C = ⊥
  · subst C
    refine (mcaError_affineLine_bot_le _).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hn, ht1, pow_nonneg htR.le 3]
  have hτ : 0 ≤ τ (2 * t) := _h.profile_nonneg hC (by omega)
  let δr : ℝ := 1 - τ (2 * t) - 3 / (2 * t)
  change mcaError (AffineLineGenerator F) C δr ≤ _
  by_cases hδneg : δr < 0
  · rw [mcaError_eq_zero_of_neg_radius _ _ hδneg]
    exact bot_le
  have hδ0 : 0 ≤ δr := le_of_not_gt hδneg
  by_cases hδzero : δr = 0
  · rw [hδzero]
    refine (mcaError_affineLine_zero_le_inv_card C).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [hn, ht1, pow_nonneg htR.le 3]
  have hδpos : 0 < δr := lt_of_le_of_ne hδ0 (Ne.symm hδzero)
  have ht2 : 2 ≤ t := by
    by_contra hsmall
    have ht_eq : t = 1 := by omega
    simp only [δr, ht_eq, Nat.cast_one] at hδpos
    rw [ht_eq] at hτ
    linarith
  let δ : NNReal := ⟨δr, hδ0⟩
  have hweak : StrongLineDecodable (C : Set (ι → Fin s → F)) δ
      (4 * t ^ 3) (2 * t) := by
    apply strongLineDecodable_two_mul_of_subspaceDesign τ C _h _ht δ le_rfl
    have ht2R : (2 : ℝ) ≤ t := by exact_mod_cast ht2
    push_cast
    field_simp
    nlinarith only [sq_nonneg ((t : ℝ) - 2), ht2R]
  have hboost : (δ : ℝ) * (2 * (t : ℝ)) / (2 * (t : ℝ) - 1) <
      (t : ℝ) / (t + 1) * (1 - τ (2 * t)) := by
    have hd : (0 : ℝ) < 2 * t - 1 := by linarith
    have htadd : (0 : ℝ) < t + 1 := by positivity
    change δr * (2 * (t : ℝ)) / (2 * (t : ℝ) - 1) < _
    dsimp [δr]
    rw [div_lt_iff₀ hd]
    field_simp
    nlinarith only [mul_nonneg htR.le hτ, htR]
  have hlist := subspaceDesign_lambda_le_of_radius_lt _h
    (show 1 ≤ t by omega) (show t ≤ 2 * t by omega) hboost
  have hδlt : δ < 1 := by
    rw [← NNReal.coe_lt_coe]
    change δr < 1
    dsimp [δr]
    have heps : (0 : ℝ) < 3 / (2 * t) := by positivity
    linarith
  have hmca := mcaError_le_of_strongLineDecodable C δ _ht
    (by exact_mod_cast hδpos) hδlt hweak hlist hbudget
  change mcaError (AffineLineGenerator F) C δr ≤ _ at hmca
  convert hmca using 1
  push_cast
  ring

end CodingTheory
