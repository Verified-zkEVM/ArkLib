/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.SubspaceDesign

/-!
# MCA bound for folded Reed-Solomon codes up to capacity

This file proves the affine-line MCA bound for admissibly folded Reed--Solomon codes in the
capacity regime, via an affine-line collision-counting argument and a subspace-design
"pinning"/rank-drop induction.

## Main result

- `frs_mcaError_le` — ABF26 T4.14 [GG25 Cor 4.10]: folded RS up to capacity has the
  integer-native bound `ε_mca(C, 1 - ρ - 2/t) ≤ (nt + 3t³)/|F|`.

## References

- [GG25] Goyal and Guruswami, *Optimal Proximity Gaps for Subspace-Design Codes and (Random)
  Reed-Solomon Codes*, ePrint 2025/2054. Corollary 4.10.
-/

@[expose] public section

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap
open FrsInternal
open scoped NNReal in
open Code in
private theorem frs_mcaError_le_proof
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hω : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hcard : s * Fintype.card ι < Fintype.card F)
    (t : ℕ) (_ht_pos : 0 < t)
    (_hs_gt : 4 * t ^ 2 < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - ρ - 2 / (t : ℝ)) ≤
      ENNReal.ofReal ((n * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) := by
  classical
  dsimp
  let R : ℝ := (k : ℝ) / ((s : ℝ) * Fintype.card ι)
  let δr : ℝ := 1 - R - 2 / (t : ℝ)
  change mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω) δr ≤
    ENNReal.ofReal (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F)
  by_cases hδneg : δr < 0
  · rw [mcaError_eq_zero_of_neg_radius _ _ hδneg]
    exact bot_le
  have hδ0 : 0 ≤ δr := le_of_not_gt hδneg
  by_cases hδzero : δr = 0
  · rw [hδzero]
    calc
      mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω) 0
          ≤ ENNReal.ofReal (1 / (Fintype.card F : ℝ)) :=
        mcaError_affineLine_zero_le_inv_card _
      _ ≤ ENNReal.ofReal
          (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) := by
        apply ENNReal.ofReal_le_ofReal
        have hqR : (0 : ℝ) < Fintype.card F := by positivity
        rw [div_le_div_iff₀ hqR hqR]
        have hntNat : 1 ≤ Fintype.card ι * t := by
          apply Nat.one_le_iff_ne_zero.mpr
          exact mul_ne_zero (Nat.ne_of_gt Fintype.card_pos) (Nat.ne_of_gt _ht_pos)
        have hnumNat : 1 ≤ Fintype.card ι * t + 3 * t ^ 3 := by omega
        have hnum : (1 : ℝ) ≤ (Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3 := by
          exact_mod_cast hnumNat
        exact mul_le_mul_of_nonneg_right hnum hqR.le
  have hδpos : 0 < δr := lt_of_le_of_ne hδ0 (Ne.symm hδzero)
  by_cases htsmall : t ≤ 2
  · have htR0 : (0 : ℝ) < t := by exact_mod_cast _ht_pos
    have hR0' : 0 ≤ R := by dsimp [R]; positivity
    dsimp [δr] at hδpos
    interval_cases t <;> norm_num at hδpos ⊢ <;> nlinarith only [hδpos, hR0']
  have ht3 : 3 ≤ t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hs_pos : 0 < s := lt_of_le_of_lt (Nat.zero_le _) _hs_gt
  have hFn : Fintype.card ι < Fintype.card F := by
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hs_pos) _hcard
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    dsimp [δr] at hδ0
    nlinarith only [hδ0, div_pos (show (0 : ℝ) < 2 by norm_num) htR]
  have hRlt : R < 1 := by
    dsimp [δr] at hδ0
    nlinarith only [hδ0, div_pos (show (0 : ℝ) < 2 by norm_num) htR]
  have hsn_pos : (0 : ℝ) < (s : ℝ) * Fintype.card ι := by positivity
  have hkR : (k : ℝ) < (s : ℝ) * Fintype.card ι := by
    rw [← div_lt_one hsn_pos]
    exact hRlt
  have hk : k ≤ s * Fintype.card ι := by exact_mod_cast hkR.le
  let C := ReedSolomon.Folded.frsCode domain k s ω
  have hdesign := isSubspaceDesign_frsCode_sharpProfile domain k s ω hFn _hadm _hω _hω_gen hk
  have hprof : sharpSubspaceProfile (ι := ι) s R (2 * t) ≤ R + 1 / (2 * (t : ℝ)) :=
    sharpSubspaceProfile_two_mul_le_rate_add s t R _ht_pos _hs_gt hR0 hR1
  let δ : NNReal := ⟨δr, hδ0⟩
  have hweak : StrongLineDecodable (C : Set (ι → Fin s → F)) δ
      (3 * t ^ 3) (2 * t) := by
    apply strongLineDecodable_two_mul_of_profile_le
      (sharpSubspaceProfile (ι := ι) s R) R C hdesign ht3 δ hprof
    change δr ≤ δr
    exact le_rfl
  have hrate : (LinearCode.alphabetRate C : ℝ) = R := by
    simpa only [C, R, Nat.cast_mul] using
      (ReedSolomon.Folded.alphabetRate_frsCode domain k s ω _hadm _hω hk)
  have h2tle : 2 * t ≤ s := by
    nlinarith only [_hs_gt, sq_nonneg ((t : ℝ) - 1)]
  have ht_le_s : t ≤ s := le_trans (by omega : t ≤ 2 * t) h2tle
  change IsSubspaceDesign s (sharpSubspaceProfile (ι := ι) s R) C at hdesign
  have hdesignList := hdesign
  rw [sharpSubspaceProfile_eq_fun s R] at hdesignList
  have hlist0 := subspaceDesign_lambda_le s R C hrate hdesignList
    t (by omega) ht_le_s
  have hboostrad : (δ : ℝ) * (((2 * t : ℕ) : ℝ)) / (((2 * t - 1 : ℕ) : ℝ)) ≤
      (t : ℝ) / (t + 1) * (1 - (s : ℝ) * R / ((s : ℝ) - t + 1)) := by
    change δr * (((2 * t : ℕ) : ℝ)) / (((2 * t - 1 : ℕ) : ℝ)) ≤ _
    exact boosted_frs_radius_le_list_radius s t R ht3 _hs_gt hR0
  have hlist : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (((2 * t : ℕ) : ℝ)) / (((2 * t - 1 : ℕ) : ℝ))) ≤ (t : ℕ∞) := by
    exact (Code.Lambda_mono hboostrad).trans hlist0
  have hsub : 1 ≤ 2 * t := by omega
  have hlist' : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (((2 * t : ℕ) : ℝ)) / ((((2 * t : ℕ) : ℝ)) - 1)) ≤ (t : ℕ∞) := by
    simpa only [Nat.cast_sub hsub, Nat.cast_one] using hlist
  have hδlt : δ < 1 := by
    rw [← NNReal.coe_lt_coe]
    change δr < (1 : ℝ)
    dsimp [δr]
    have htwo : (0 : ℝ) < 2 / t := div_pos (by norm_num) htR
    nlinarith only [hR0, htwo]
  have hbudget : (t + 1) ^ 2 ≤ Fintype.card ι * t + 3 * t ^ 3 := by
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    nlinarith only [hn, ht3, sq_nonneg (t - 1)]
  have hmca := mcaError_le_of_strongLineDecodable C δ _ht_pos
    (by exact_mod_cast hδpos) hδlt hweak
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlist') hbudget
  change mcaError (AffineLineGenerator F) C δr ≤ _ at hmca
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hmca

/-- A capacity-regime MCA bound for an admissibly folded Reed--Solomon code. For an integer
`t > 0` and folding parameter `s > 4t²`,

  `ε_mca(C, 1 - ρ - 2/t) ≤ (nt + 3t³)/|F|`

The rate is alphabet-normalized as `ρ = k/(s·n)`. The hypotheses require a generator of
`Fˣ`, an admissible folding domain, and `s·n < |F|`; these are the conditions used by the
subspace-design argument. The integer parameter is kept explicit rather than replaced by an
unrounded real expression. -/
theorem frs_mcaError_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hω : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hcard : s * Fintype.card ι < Fintype.card F)
    (t : ℕ) (_ht_pos : 0 < t)
    (_hs_gt : 4 * t ^ 2 < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - ρ - 2 / (t : ℝ)) ≤
      ENNReal.ofReal ((n * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) := by
  classical
  exact frs_mcaError_le_proof domain k s ω _hω _hω_gen _hadm _hcard t _ht_pos _hs_gt

/-- Threshold form of `frs_mcaError_le`: any target `ε_star` that the explicit
`(nt + 3t³)/|F|` budget clears at the instantiated parameters is a genuine affine-line MCA
bound for the folded Reed-Solomon code. The numeric budget check is a hypothesis, so the
contentful-range condition is discharged at the use site rather than assumed by the reader. -/
theorem frs_mcaError_le_of_budget
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hω : ω ≠ 0)
    (hω_gen : orderOf ω = Fintype.card F - 1)
    (hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (hcard : s * Fintype.card ι < Fintype.card F)
    (t : ℕ) (ht_pos : 0 < t)
    (hs_gt : 4 * t ^ 2 < s)
    (ε_star : ℝ≥0)
    (hbudget :
      ENNReal.ofReal (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F)
        ≤ (ε_star : ENNReal)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - (k : ℝ) / (s * (Fintype.card ι : ℝ)) - 2 / (t : ℝ)) ≤ (ε_star : ENNReal) := by
  classical
  exact le_trans (frs_mcaError_le domain k s ω hω hω_gen hadm hcard t ht_pos hs_gt) hbudget

end CodingTheory
