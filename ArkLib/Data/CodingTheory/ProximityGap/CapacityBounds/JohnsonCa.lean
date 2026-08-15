/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# Ben-Sasson--Guruswami--Kopparty--Sudan CA bound

This file proves the 1.5-Johnson correlated-agreement bound for linear codes. The proof
extracts dense agreement triples and reconstructs a common affine codeword line.

## Main result

- `linear_epsCa_le_one_point_five_johnson` is [BenSassonGKS20, Lemma 3.2].

## References

- [BenSassonGKS20] Lemma 3.2.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped BigOperators in
private def jointProximity_of_many_affine_agreements
    (C : LinearCode ι F) (u0 u1 v0 v1 : ι → F)
    (A : Finset F) (S : ↥A → Finset ι) (d e : ℝ≥0)
    (he : 0 < (e : ℝ)) (hde : d + e ≤ 1)
    (hv0 : v0 ∈ C) (hv1 : v1 ∈ C)
    (hA : 1 / (e : ℝ) + 2 < (A.card : ℝ))
    (hS : ∀ x : ↥A,
      (1 - (d : ℝ)) * Fintype.card ι ≤ ((S x).card : ℝ))
    (hagree : ∀ x : ↥A, ∀ i ∈ S x,
      u0 i + (x : F) * u1 i = v0 i + (x : F) * v1 i) :
    Code.jointProximity (C : Set (ι → F))
      (Code.finMapTwoWords u0 u1) (d + e) := by
  classical
  let T : Finset ι := Finset.univ.filter fun i =>
    u0 i = v0 i ∧ u1 i = v1 i
  let total : ℝ := ∑ x : ↥A, ((S x).card : ℝ)
  have hsum_eq :
      total = ∑ i : ι,
        (((Finset.univ.filter fun x : ↥A => i ∈ S x).card : ℝ)) := by
    dsimp [total]
    calc
      (∑ x : ↥A, ((S x).card : ℝ)) =
          ∑ x : ↥A, ∑ i : ι, if i ∈ S x then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            simp
      _ = ∑ i : ι, ∑ x : ↥A, if i ∈ S x then (1 : ℝ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i : ι,
          (((Finset.univ.filter fun x : ↥A => i ∈ S x).card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp
  have hfiber (i : ι) :
      ((Finset.univ.filter fun x : ↥A => i ∈ S x).card : ℝ) ≤
        (if i ∈ T then (A.card : ℝ) else 1) := by
    by_cases hiT : i ∈ T
    · rw [if_pos hiT]
      have hnat :
          (Finset.univ.filter fun x : ↥A => i ∈ S x).card ≤ A.card := by
        simpa using
          (Finset.card_le_card
            (Finset.filter_subset (fun x : ↥A => i ∈ S x) Finset.univ))
      exact_mod_cast hnat
    · rw [if_neg hiT]
      exact_mod_cast Finset.card_le_one.mpr (by
        intro x hx y hy
        have hxeq := hagree x i (Finset.mem_filter.mp hx).2
        have hyeq := hagree y i (Finset.mem_filter.mp hy).2
        apply Subtype.ext
        by_contra hxy
        have hmul : ((x : F) - (y : F)) * (u1 i - v1 i) = 0 := by
          calc
            ((x : F) - (y : F)) * (u1 i - v1 i) =
                (u0 i + (x : F) * u1 i - (v0 i + (x : F) * v1 i)) -
                (u0 i + (y : F) * u1 i - (v0 i + (y : F) * v1 i)) := by ring
            _ = 0 := by rw [hxeq, hyeq]; ring
        have hu1 : u1 i = v1 i := by
          have hsub : u1 i - v1 i = 0 :=
            (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hxy)
          exact sub_eq_zero.mp hsub
        have hu0 : u0 i = v0 i := by
          rw [hu1] at hxeq
          simpa using hxeq
        exact hiT (by simp [T, hu0, hu1]))
  have htotal_upper :
      total ≤ (T.card : ℝ) * (A.card : ℝ) + Fintype.card ι := by
    rw [hsum_eq]
    calc
      (∑ i : ι,
          (((Finset.univ.filter fun x : ↥A => i ∈ S x).card : ℝ))) ≤
          ∑ i : ι, (if i ∈ T then (A.card : ℝ) else 1) := by
            exact Finset.sum_le_sum (fun i hi => hfiber i)
      _ ≤ ∑ i : ι, ((if i ∈ T then (A.card : ℝ) else 0) + 1) := by
            exact Finset.sum_le_sum (fun i hi => by
              by_cases hiT : i ∈ T <;> simp [hiT])
      _ = (T.card : ℝ) * (A.card : ℝ) + Fintype.card ι := by
            rw [Finset.sum_add_distrib]
            simp [mul_comm]
  have htotal_lower :
      (A.card : ℝ) * ((1 - (d : ℝ)) * Fintype.card ι) ≤ total := by
    dsimp [total]
    calc
      (A.card : ℝ) * ((1 - (d : ℝ)) * Fintype.card ι) =
          ∑ x : ↥A, ((1 - (d : ℝ)) * Fintype.card ι) := by simp
      _ ≤ ∑ x : ↥A, ((S x).card : ℝ) := by
            exact Finset.sum_le_sum (fun x hx => hS x)
  have hMpos : 0 < (A.card : ℝ) := by
    have : 0 < 1 / (e : ℝ) + 2 := by positivity
    linarith
  have hMe : 1 < (A.card : ℝ) * (e : ℝ) := by
    have hinv : 1 / (e : ℝ) < (A.card : ℝ) := by linarith
    exact (div_lt_iff₀ he).mp hinv
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have htarget :
      (1 - (d : ℝ) - (e : ℝ)) * Fintype.card ι ≤ (T.card : ℝ) := by
    by_contra hnot
    have hlt : (T.card : ℝ) <
        (1 - (d : ℝ) - (e : ℝ)) * Fintype.card ι := lt_of_not_ge hnot
    have hupper_lt :
        (T.card : ℝ) * (A.card : ℝ) + Fintype.card ι <
          ((1 - (d : ℝ) - (e : ℝ)) * Fintype.card ι) *
              (A.card : ℝ) + Fintype.card ι := by
      simpa [add_comm] using
        (add_lt_add_right (mul_lt_mul_of_pos_right hlt hMpos) (Fintype.card ι : ℝ))
    have hgain :
        (Fintype.card ι : ℝ) <
          (A.card : ℝ) * (e : ℝ) * Fintype.card ι := by
      nlinarith [mul_pos (sub_pos.mpr hMe) hn]
    have hgap :
        ((1 - (d : ℝ) - (e : ℝ)) * Fintype.card ι) *
              (A.card : ℝ) + Fintype.card ι <
          (A.card : ℝ) * ((1 - (d : ℝ)) * Fintype.card ι) := by
      nlinarith
    exact (not_lt_of_ge (le_trans htotal_lower htotal_upper))
      (lt_trans hupper_lt hgap)
  have hdereal : (d : ℝ) + (e : ℝ) ≤ 1 := by
    exact_mod_cast hde
  have htarget' :
      (((1 - (d + e) : ℝ≥0) : ℝ) * Fintype.card ι) ≤ (T.card : ℝ) := by
    rw [NNReal.coe_sub hde]
    push_cast
    nlinarith
  have hTcard :
      (1 - (d + e)) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) := by
    exact_mod_cast htarget'
  rw [← Code.jointAgreement_iff_jointProximity]
  refine ⟨T, hTcard, Code.finMapTwoWords v0 v1, ?_⟩
  intro j
  fin_cases j
  · constructor
    · exact hv0
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [Code.finMapTwoWords] using hi'.symm
  · constructor
    · exact hv1
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [Code.finMapTwoWords] using hi'.symm

private noncomputable def linearBGKSClosestCodeword
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι) (x : F) : ι → F := by
  letI : Nonempty (C : Set (ι → F)) := ⟨⟨0, C.zero_mem⟩⟩
  exact (Code.pickRelClosestCodeword_of_Nonempty_Code
    (C : Set (ι → F)) (u 0 + x • u 1)).1

private noncomputable def linearBGKSAgreementSet
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι) (x : F) : Finset ι :=
  Finset.univ.filter fun i : ι =>
    u 0 i + x * u 1 i = linearBGKSClosestCodeword C u x i

private def linearBGKSClosestCodeword_mem
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι) (x : F) :
    linearBGKSClosestCodeword C u x ∈ C := by
  classical
  letI : Nonempty (C : Set (ι → F)) := ⟨⟨0, C.zero_mem⟩⟩
  simp [linearBGKSClosestCodeword]

private def linearBGKSCollisionNumeric (e M : ℝ) (he : 0 < e) (he3 : e < 1 / 3)
    (hM : 2 / e ^ 2 < M) :
    3 * M ^ 2 < (e / 2) * M ^ 3 := by
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  have hEM : 2 < e ^ 2 * M := by
    simpa [mul_comm] using (div_lt_iff₀ he2).mp hM
  have h6 : 6 < e * M := by
    have h2e : 6 * e < 2 := by nlinarith
    have heM : 2 < e * (e * M) := by nlinarith [hEM]
    nlinarith
  have hMpos : 0 < M := lt_trans (by positivity : 0 < 2 / e ^ 2) hM
  have hmul := mul_lt_mul_of_pos_right h6 (sq_pos_of_pos hMpos)
  nlinarith

open scoped NNReal in
private noncomputable def linearBGKSGoodScalars
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι) (δ_src : ℝ≥0) : Finset F :=
  Finset.univ.filter fun x : F =>
    δᵣ(u 0 + x • u 1, (C : Set (ι → F))) < (δ_src : ENNReal)

open scoped NNReal in
private def linearBGKSAgreementSet_card_gt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_src : ℝ≥0) (x : F)
    (hx : x ∈ linearBGKSGoodScalars C u δ_src) :
    (1 - (δ_src : ℝ)) * Fintype.card ι <
      ((linearBGKSAgreementSet C u x).card : ℝ) := by
  classical
  have hxclose :
      δᵣ(u 0 + x • u 1, (C : Set (ι → F))) < (δ_src : ENNReal) :=
    (Finset.mem_filter.mp hx).2
  letI : Nonempty (C : Set (ι → F)) := ⟨⟨0, C.zero_mem⟩⟩
  rw [Code.relDistFromPickRelClosestCodeword_of_Nonempty_Code] at hxclose
  have hpair :
      ((δᵣ(u 0 + x • u 1, linearBGKSClosestCodeword C u x) : ℚ≥0) : ENNReal) <
        (δ_src : ENNReal) := by
    simpa [linearBGKSClosestCodeword] using hxclose
  have hpairR :
      (δᵣ(u 0 + x • u 1, linearBGKSClosestCodeword C u x) : ℝ) <
        (δ_src : ℝ) := by
    exact_mod_cast hpair
  rw [Code.relHammingDist_coe] at hpairR
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdist :
      (Δ₀(u 0 + x • u 1, linearBGKSClosestCodeword C u x) : ℝ) <
        (δ_src : ℝ) * Fintype.card ι :=
    (div_lt_iff₀ hn).mp hpairR
  have hcard :
      (linearBGKSAgreementSet C u x).card =
        Code.agree (u 0 + x • u 1) (linearBGKSClosestCodeword C u x) := by
    simp [linearBGKSAgreementSet, Code.agree, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hagreeNat :=
    Code.agree_add_hammingDist
      (u := u 0 + x • u 1) (v := linearBGKSClosestCodeword C u x)
  have hagreeR :
      (Code.agree (u 0 + x • u 1) (linearBGKSClosestCodeword C u x) : ℝ) +
          (Δ₀(u 0 + x • u 1, linearBGKSClosestCodeword C u x) : ℝ) =
        (Fintype.card ι : ℝ) := by
    exact_mod_cast hagreeNat
  rw [hcard]
  nlinarith

open scoped NNReal in
private noncomputable def linearBGKSDenseTriples
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι) (δ_src : ℝ≥0) :
    Finset (↥(linearBGKSGoodScalars C u δ_src) ×
      ↥(linearBGKSGoodScalars C u δ_src) ×
      ↥(linearBGKSGoodScalars C u δ_src)) :=
  Finset.univ.filter fun p =>
    Fintype.card ι - Code.minDist (C : Set (ι → F)) <
      (linearBGKSAgreementSet C u p.1 ∩
        linearBGKSAgreementSet C u p.2.1 ∩
        linearBGKSAgreementSet C u p.2.2).card

open scoped NNReal in
private noncomputable def linearBGKSDistinctDenseTriples
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι) (δ_src : ℝ≥0) :
    Finset (↥(linearBGKSGoodScalars C u δ_src) ×
      ↥(linearBGKSGoodScalars C u δ_src) ×
      ↥(linearBGKSGoodScalars C u δ_src)) :=
  (linearBGKSDenseTriples C u δ_src).filter fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2

open scoped NNReal in
open scoped ProbabilityTheory in
private def linearBGKSGoodScalars_card_gt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_src η : ℝ≥0) (hη : 0 < η)
    (hprob : ENNReal.ofReal (2 / ((η : ℝ) ^ 2 * Fintype.card F)) <
      Pr_{
        let x ← $ᵖ F}[δᵣ(u 0 + x • u 1, (C : Set (ι → F))) < δ_src]) :
    2 / (η : ℝ) ^ 2 < ((linearBGKSGoodScalars C u δ_src).card : ℝ) := by
  classical
  have he : 0 < (η : ℝ) := by exact_mod_cast hη
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Probability.prob_uniform_eq_ofReal] at hprob
  have hprob' :
      ENNReal.ofReal (2 / ((η : ℝ) ^ 2 * Fintype.card F)) <
        ENNReal.ofReal
          (((linearBGKSGoodScalars C u δ_src).card : ℝ) /
            (Fintype.card F : ℝ)) := by
    simpa [linearBGKSGoodScalars] using hprob
  have hreal :
      2 / ((η : ℝ) ^ 2 * Fintype.card F) <
        ((linearBGKSGoodScalars C u δ_src).card : ℝ) /
          (Fintype.card F : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff').mp hprob' |>.1
  calc
    2 / (η : ℝ) ^ 2 =
        (2 / ((η : ℝ) ^ 2 * Fintype.card F)) * Fintype.card F := by
          field_simp
    _ < (((linearBGKSGoodScalars C u δ_src).card : ℝ) /
          (Fintype.card F : ℝ)) * Fintype.card F :=
      mul_lt_mul_of_pos_right hreal hq
    _ = ((linearBGKSGoodScalars C u δ_src).card : ℝ) := by field_simp

open scoped BigOperators in
private def linearBGKS_card_indicator
    {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) :
    (s.card : ℝ) = ∑ i : α, if i ∈ s then (1 : ℝ) else 0 := by
  simp

open scoped NNReal in
private def linearBGKS_codewords_affine_of_distinctDenseTriple
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_src : ℝ≥0)
    (x b g : ↥(linearBGKSGoodScalars C u δ_src))
    (htriple : (x, b, g) ∈ linearBGKSDistinctDenseTriples C u δ_src) :
    let v1 : ι → F := (((b : F) - (x : F))⁻¹) •
      (linearBGKSClosestCodeword C u b - linearBGKSClosestCodeword C u x)
    let v0 : ι → F := linearBGKSClosestCodeword C u x - (x : F) • v1
    v0 ∈ C ∧ v1 ∈ C ∧
      linearBGKSClosestCodeword C u g = v0 + (g : F) • v1 := by
  classical
  let v1 : ι → F := (((b : F) - (x : F))⁻¹) •
    (linearBGKSClosestCodeword C u b - linearBGKSClosestCodeword C u x)
  let v0 : ι → F := linearBGKSClosestCodeword C u x - (x : F) • v1
  change v0 ∈ C ∧ v1 ∈ C ∧
    linearBGKSClosestCodeword C u g = v0 + (g : F) • v1
  rw [linearBGKSDistinctDenseTriples, Finset.mem_filter] at htriple
  rcases htriple with ⟨hdense, hxb, hxg, hbg⟩
  have hbxval : (b : F) ≠ (x : F) := by
    intro heq
    apply hxb
    exact Subtype.ext heq.symm
  have hbx : (b : F) - (x : F) ≠ 0 := sub_ne_zero.mpr hbxval
  have hcx : linearBGKSClosestCodeword C u x ∈ C :=
    linearBGKSClosestCodeword_mem C u x
  have hcb : linearBGKSClosestCodeword C u b ∈ C :=
    linearBGKSClosestCodeword_mem C u b
  have hcg : linearBGKSClosestCodeword C u g ∈ C :=
    linearBGKSClosestCodeword_mem C u g
  have hv1 : v1 ∈ C := by
    dsimp [v1]
    exact C.smul_mem _ (C.sub_mem hcb hcx)
  have hv0 : v0 ∈ C := by
    dsimp [v0]
    exact C.sub_mem hcx (C.smul_mem _ hv1)
  have hline : v0 + (g : F) • v1 ∈ C :=
    C.add_mem hv0 (C.smul_mem _ hv1)
  refine ⟨hv0, hv1, ?_⟩
  let I : Finset ι :=
    linearBGKSAgreementSet C u x ∩
      linearBGKSAgreementSet C u b ∩
      linearBGKSAgreementSet C u g
  let T : Finset ι := Iᶜ
  rw [linearBGKSDenseTriples, Finset.mem_filter] at hdense
  have hinter :
      Fintype.card ι - Code.minDist (C : Set (ι → F)) < I.card := by
    simpa [I] using hdense.2
  have hdle : Code.minDist (C : Set (ι → F)) ≤ Fintype.card ι := by
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _
  have hIle : I.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_card (Finset.subset_univ I)
  have hTcard : T.card < Code.minDist (C : Set (ι → F)) := by
    dsimp [T]
    rw [Finset.card_compl]
    omega
  apply Code.eq_of_disagreementCols_subset_of_card_lt_minDist hcg hline T
  · intro i hi
    rw [Finset.mem_compl]
    intro hiI
    have hi_ne :
        linearBGKSClosestCodeword C u g i ≠
          (v0 + (g : F) • v1) i := by
      simpa only [Code.mem_disagreementCols] using hi
    rcases Finset.mem_inter.mp hiI with ⟨hixb, hig⟩
    rcases Finset.mem_inter.mp hixb with ⟨hix, hib⟩
    have hxagree :
        u 0 i + (x : F) * u 1 i = linearBGKSClosestCodeword C u x i := by
      simpa [linearBGKSAgreementSet, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hix
    have hbagree :
        u 0 i + (b : F) * u 1 i = linearBGKSClosestCodeword C u b i := by
      simpa [linearBGKSAgreementSet, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hib
    have hgagree :
        u 0 i + (g : F) * u 1 i = linearBGKSClosestCodeword C u g i := by
      simpa [linearBGKSAgreementSet, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hig
    have hdiff :
        linearBGKSClosestCodeword C u b i - linearBGKSClosestCodeword C u x i =
          ((b : F) - (x : F)) * u 1 i := by
      rw [← hbagree, ← hxagree]
      ring
    have hv1i : v1 i = u 1 i := by
      change ((b : F) - (x : F))⁻¹ *
          (linearBGKSClosestCodeword C u b i -
            linearBGKSClosestCodeword C u x i) = u 1 i
      rw [hdiff, ← mul_assoc, inv_mul_cancel₀ hbx, one_mul]
    have hv0i : v0 i = u 0 i := by
      change linearBGKSClosestCodeword C u x i - (x : F) * v1 i = u 0 i
      rw [hv1i, ← hxagree]
      ring
    apply hi_ne
    calc
      linearBGKSClosestCodeword C u g i = u 0 i + (g : F) * u 1 i := hgagree.symm
      _ = v0 i + (g : F) * v1 i := by rw [hv0i, hv1i]
      _ = (v0 + (g : F) • v1) i := by rfl
  · exact hTcard

open scoped BigOperators in
private def linearBGKS_filter_card_indicator
    {α : Type} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    (((Finset.univ.filter p).card : ℝ)) =
      ∑ x : α, if p x then (1 : ℝ) else 0 := by
  simp

open scoped NNReal in
private def linearBGKS_numeric_setup
    (C : LinearCode ι F) (δ_min η δ_src : ℝ≥0)
    (hδmin : (δ_min : ℝ) =
      (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_third : (η : ℝ) < 1 / 3)
    (hsrc : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    (δ_min : ℝ) ≤ 1 ∧
      0 < 1 - (δ_min : ℝ) + (η : ℝ) ∧
      1 - (δ_min : ℝ) + (η : ℝ) < (1 - (δ_src : ℝ)) ^ 3 ∧
      (δ_src : ℝ) + (η : ℝ) < 1 := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hminNat : Code.minDist (C : Set (ι → F)) ≤ Fintype.card ι := by
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _
  have hminR :
      (Code.minDist (C : Set (ι → F)) : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hminNat
  have hdmin_le : (δ_min : ℝ) ≤ 1 := by
    rw [hδmin]
    exact (div_le_one hn).2 hminR
  have heta : 0 < (η : ℝ) := by exact_mod_cast hη
  let a : ℝ := 1 - (δ_min : ℝ) + (η : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    nlinarith
  let r : ℝ := a ^ ((1 : ℝ) / 3)
  have hr0 : 0 ≤ r := by
    exact Real.rpow_nonneg (le_of_lt ha) _
  have hrpow : r ^ 3 = a := by
    dsimp [r]
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow (x := a) (n := 3) (le_of_lt ha) (by norm_num))
  have hr_lt : r < 1 - (δ_src : ℝ) := by
    dsimp [r, a]
    linarith
  have hcube : a < (1 - (δ_src : ℝ)) ^ 3 := by
    rw [← hrpow]
    exact pow_lt_pow_left₀ hr_lt hr0 (by norm_num)
  have heta_lt_one : (η : ℝ) < 1 := by nlinarith
  have heta_cube_lt : (η : ℝ) ^ 3 < (η : ℝ) := by
    nlinarith [sq_pos_of_pos heta]
  have heta_le_a : (η : ℝ) ≤ a := by
    dsimp [a]
    nlinarith
  have heta_lt_r : (η : ℝ) < r := by
    by_contra hnot
    have hr_le : r ≤ (η : ℝ) := le_of_not_gt hnot
    have hpow_le : r ^ 3 ≤ (η : ℝ) ^ 3 :=
      pow_le_pow_left₀ hr0 hr_le 3
    nlinarith [hrpow, heta_cube_lt, heta_le_a]
  refine ⟨hdmin_le, ha, hcube, ?_⟩
  nlinarith [hr_lt, heta_lt_r]

private def linearBGKS_repeated_triples_card_le
    {α : Type} [Fintype α] [DecidableEq α] :
    (((Finset.univ.filter fun p : α × α × α =>
      p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2).card : ℝ)) ≤
      3 * (Fintype.card α : ℝ) ^ 2 := by
  classical
  let E01 : Finset (α × α × α) :=
    Finset.univ.image fun q : α × α => (q.1, q.1, q.2)
  let E02 : Finset (α × α × α) :=
    Finset.univ.image fun q : α × α => (q.1, q.2, q.1)
  let E12 : Finset (α × α × α) :=
    Finset.univ.image fun q : α × α => (q.1, q.2, q.2)
  let R : Finset (α × α × α) :=
    Finset.univ.filter fun p =>
      p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2
  have hsub : R ⊆ E01 ∪ E02 ∪ E12 := by
    rintro ⟨x, b, g⟩ hp
    have hrep : x = b ∨ x = g ∨ b = g := by
      simpa [R] using (Finset.mem_filter.mp hp).2
    rcases hrep with hxb | hxg | hbg
    · subst b
      simp [E01, E02, E12]
    · subst g
      simp [E01, E02, E12]
    · subst g
      simp [E01, E02, E12]
  have hE01 : E01.card ≤ (Fintype.card α) ^ 2 := by
    calc
      E01.card ≤ (Finset.univ : Finset (α × α)).card := by
        dsimp [E01]
        exact Finset.card_image_le
      _ = (Fintype.card α) ^ 2 := by simp [pow_two]
  have hE02 : E02.card ≤ (Fintype.card α) ^ 2 := by
    calc
      E02.card ≤ (Finset.univ : Finset (α × α)).card := by
        dsimp [E02]
        exact Finset.card_image_le
      _ = (Fintype.card α) ^ 2 := by simp [pow_two]
  have hE12 : E12.card ≤ (Fintype.card α) ^ 2 := by
    calc
      E12.card ≤ (Finset.univ : Finset (α × α)).card := by
        dsimp [E12]
        exact Finset.card_image_le
      _ = (Fintype.card α) ^ 2 := by simp [pow_two]
  have hR : R.card ≤ 3 * (Fintype.card α) ^ 2 := by
    have hcardSub := Finset.card_le_card hsub
    have hu1 := Finset.card_union_le E01 E02
    have hu2 := Finset.card_union_le (E01 ∪ E02) E12
    omega
  have hReq : R = Finset.univ.filter (fun p : α × α × α =>
      p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2) := rfl
  rw [← hReq]
  exact_mod_cast hR

open scoped BigOperators in
private def linearBGKS_triple_fiber_card_sum
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Finset (α × α × α)) :
    (D.card : ℝ) = ∑ x : α, ∑ b : α,
      (((Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card : ℝ)) := by
  classical
  have hnat : D.card = Finset.univ.sum (fun x : α =>
      Finset.univ.sum (fun b : α =>
        (Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card)) := by
    calc
      D.card = Finset.univ.sum (fun p : α × α × α => if p ∈ D then 1 else 0) := by
        simp
      _ = Finset.univ.sum (fun x : α =>
          Finset.univ.sum (fun b : α =>
            Finset.univ.sum (fun g : α => if (x, b, g) ∈ D then 1 else 0))) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Fintype.sum_prod_type]
      _ = Finset.univ.sum (fun x : α =>
          Finset.univ.sum (fun b : α =>
            (Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.card_filter]
  exact_mod_cast hnat

open scoped BigOperators in
private def linearBGKS_rich_fiber_of_many_distinct
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Finset (α × α × α)) (e : ℝ)
    (he : 0 < e)
    (hM : 2 / e ^ 2 < (Fintype.card α : ℝ))
    (hD : (e / 2) * (Fintype.card α : ℝ) ^ 3 < (D.card : ℝ))
    (hdistinct : ∀ p ∈ D,
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) :
    ∃ x b : α, x ≠ b ∧
      1 / e <
        (((Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card : ℝ)) := by
  classical
  by_contra hno
  push Not at hno
  have hsumR :
      (D.card : ℝ) = Finset.univ.sum (fun x : α =>
        Finset.univ.sum (fun b : α =>
          ((Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card : ℝ))) :=
    linearBGKS_triple_fiber_card_sum D
  have hfiber_le (x b : α) :
      ((Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card : ℝ) ≤ 1 / e := by
    by_cases hxb : x = b
    · subst b
      have hempty : Finset.univ.filter (fun g : α => (x, x, g) ∈ D) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro g hg
        have hmem := (Finset.mem_filter.mp hg).2
        exact (hdistinct (x, x, g) hmem).1 rfl
      rw [hempty]
      simp only [Finset.card_empty, CharP.cast_eq_zero, one_div, inv_nonneg, ge_iff_le]
      positivity
    · exact hno x b hxb
  have hupper :
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ 2 / e := by
    rw [hsumR]
    calc
      Finset.univ.sum (fun x : α =>
          Finset.univ.sum (fun b : α =>
            ((Finset.univ.filter (fun g : α => (x, b, g) ∈ D)).card : ℝ))) ≤
        Finset.univ.sum (fun _x : α =>
          Finset.univ.sum (fun _b : α => 1 / e)) := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro b hb
            exact hfiber_le x b
      _ = (Fintype.card α : ℝ) ^ 2 / e := by
        simp [pow_two]
        field_simp
  have hMpos : 0 < (Fintype.card α : ℝ) :=
    lt_trans (by positivity : 0 < 2 / e ^ 2) hM
  have hsep : (Fintype.card α : ℝ) ^ 2 / e <
      (e / 2) * (Fintype.card α : ℝ) ^ 3 := by
    have he2 : 0 < e ^ 2 := sq_pos_of_pos he
    have hbase : 2 < (Fintype.card α : ℝ) * e ^ 2 :=
      (div_lt_iff₀ he2).mp hM
    have hfacpos : 0 < (Fintype.card α : ℝ) ^ 2 / 2 := by positivity
    have hmul := mul_lt_mul_of_pos_left hbase hfacpos
    rw [div_lt_iff₀ he]
    nlinarith [hmul]
  exact (not_lt_of_ge hupper) (lt_trans hsep hD)

open scoped BigOperators in
private def linearBGKS_triple_intersection_moment
    {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    {κ : Type} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    (S : α → Finset κ) (r : ℝ)
    (hS : ∀ x : α, r * Fintype.card κ < ((S x).card : ℝ)) :
    r ^ 3 * Fintype.card κ * (Fintype.card α : ℝ) ^ 3 <
      ∑ x : α, ∑ b : α, ∑ g : α,
        (((S x ∩ S b ∩ S g).card : ℝ)) := by
  classical
  let m : κ → ℝ := fun i =>
    ((Finset.univ.filter fun x : α => i ∈ S x).card : ℝ)
  have hsum_m :
      (∑ i : κ, m i) = ∑ x : α, ((S x).card : ℝ) := by
    dsimp [m]
    calc
      (∑ i : κ,
          (((Finset.univ.filter fun x : α => i ∈ S x).card : ℝ))) =
          ∑ i : κ, ∑ x : α, if i ∈ S x then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact linearBGKS_filter_card_indicator (fun x : α => i ∈ S x)
      _ = ∑ x : α, ∑ i : κ, if i ∈ S x then (1 : ℝ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ x : α, ((S x).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (linearBGKS_card_indicator (S x)).symm
  have factor_three (a : α → ℝ) :
      (∑ x : α, a x) ^ 3 =
        ∑ x : α, ∑ b : α, ∑ g : α, a x * a b * a g := by
    rw [pow_three]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    simp only [mul_assoc]
  have htriple :
      (∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ))) =
        ∑ i : κ, (m i) ^ 3 := by
    calc
      (∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ))) =
          ∑ x : α, ∑ b : α, ∑ g : α, ∑ i : κ,
            if i ∈ S x ∩ S b ∩ S g then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro g hg
              exact linearBGKS_card_indicator (S x ∩ S b ∩ S g)
      _ = ∑ x : α, ∑ b : α, ∑ g : α, ∑ i : κ,
            (if i ∈ S x then (1 : ℝ) else 0) *
            (if i ∈ S b then (1 : ℝ) else 0) *
            (if i ∈ S g then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro g hg
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hix : i ∈ S x <;>
                by_cases hib : i ∈ S b <;>
                  by_cases hig : i ∈ S g <;> simp [hix, hib, hig]
      _ = ∑ i : κ, ∑ x : α, ∑ b : α, ∑ g : α,
            (if i ∈ S x then (1 : ℝ) else 0) *
            (if i ∈ S b then (1 : ℝ) else 0) *
            (if i ∈ S g then (1 : ℝ) else 0) := by
              calc
                (∑ x : α, ∑ b : α, ∑ g : α, ∑ i : κ,
                    (if i ∈ S x then (1 : ℝ) else 0) *
                    (if i ∈ S b then (1 : ℝ) else 0) *
                    (if i ∈ S g then (1 : ℝ) else 0)) =
                    ∑ x : α, ∑ b : α, ∑ i : κ, ∑ g : α,
                    (if i ∈ S x then (1 : ℝ) else 0) *
                    (if i ∈ S b then (1 : ℝ) else 0) *
                    (if i ∈ S g then (1 : ℝ) else 0) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      apply Finset.sum_congr rfl
                      intro b hb
                      rw [Finset.sum_comm]
                _ = ∑ x : α, ∑ i : κ, ∑ b : α, ∑ g : α,
                    (if i ∈ S x then (1 : ℝ) else 0) *
                    (if i ∈ S b then (1 : ℝ) else 0) *
                    (if i ∈ S g then (1 : ℝ) else 0) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [Finset.sum_comm]
                _ = ∑ i : κ, ∑ x : α, ∑ b : α, ∑ g : α,
                    (if i ∈ S x then (1 : ℝ) else 0) *
                    (if i ∈ S b then (1 : ℝ) else 0) *
                    (if i ∈ S g then (1 : ℝ) else 0) := by
                      rw [Finset.sum_comm]
      _ = ∑ i : κ, (m i) ^ 3 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← factor_three]
            dsimp [m]
            exact congrArg (fun z : ℝ => z ^ 3)
              (linearBGKS_filter_card_indicator
                (fun x : α => i ∈ S x)).symm
  have hsum_lower :
      r * Fintype.card κ * (Fintype.card α : ℝ) < ∑ i : κ, m i := by
    rw [hsum_m]
    have hlt :
        (∑ x : α, r * Fintype.card κ) <
          ∑ x : α, ((S x).card : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro x hx
      exact hS x
    simpa [mul_assoc, mul_comm, mul_left_comm] using hlt
  have hκpos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hαpos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hm_nonneg (i : κ) : 0 ≤ m i := by
    dsimp [m]
    positivity
  have hmean :
      (∑ i : κ, m i) ^ 3 / (Fintype.card κ : ℝ) ^ 2 ≤
        ∑ i : κ, (m i) ^ 3 := by
    simpa using
      (pow_sum_div_card_le_sum_pow
        (s := (Finset.univ : Finset κ)) (f := m)
        (fun i hi => hm_nonneg i) 2)
  by_cases hr : 0 ≤ r
  · have hbase_nonneg :
        0 ≤ r * Fintype.card κ * (Fintype.card α : ℝ) := by positivity
    have hcubelt :
        (r * Fintype.card κ * (Fintype.card α : ℝ)) ^ 3 <
          (∑ i : κ, m i) ^ 3 :=
      pow_lt_pow_left₀ hsum_lower hbase_nonneg (by norm_num)
    calc
      r ^ 3 * Fintype.card κ * (Fintype.card α : ℝ) ^ 3 =
          (r * Fintype.card κ * (Fintype.card α : ℝ)) ^ 3 /
            (Fintype.card κ : ℝ) ^ 2 := by
              field_simp
      _ < (∑ i : κ, m i) ^ 3 / (Fintype.card κ : ℝ) ^ 2 :=
        div_lt_div_of_pos_right hcubelt (sq_pos_of_pos hκpos)
      _ ≤ ∑ i : κ, (m i) ^ 3 := hmean
      _ = ∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ)) := htriple.symm
  · have hrneg : r < 0 := lt_of_not_ge hr
    have hr3 : r ^ 3 < 0 := by nlinarith [sq_pos_of_neg hrneg]
    have hleft :
        r ^ 3 * Fintype.card κ * (Fintype.card α : ℝ) ^ 3 < 0 :=
      mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hr3 hκpos) (pow_pos hαpos 3)
    have hright :
        0 ≤ ∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ)) := by
      apply Finset.sum_nonneg
      intro x hx
      apply Finset.sum_nonneg
      intro b hb
      apply Finset.sum_nonneg
      intro g hg
      exact_mod_cast Nat.zero_le (S x ∩ S b ∩ S g).card
    exact lt_of_lt_of_le hleft hright

open scoped NNReal in
open scoped BigOperators in
private def linearBGKSDenseTriples_card_gt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_min η δ_src : ℝ≥0)
    (hmin : (δ_min : ℝ) =
      (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη3 : (η : ℝ) < 1 / 3) (_hηd : η < δ_min)
    (hsrc : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hgood : 2 / (η : ℝ) ^ 2 <
      ((linearBGKSGoodScalars C u δ_src).card : ℝ)) :
    (η : ℝ) * ((linearBGKSGoodScalars C u δ_src).card : ℝ) ^ 3 <
      ((linearBGKSDenseTriples C u δ_src).card : ℝ) := by
  classical
  let good : Finset F := linearBGKSGoodScalars C u δ_src
  let α := ↥good
  let S : α → Finset ι := fun x => linearBGKSAgreementSet C u x
  let D : Finset (α × α × α) := linearBGKSDenseTriples C u δ_src
  let n : ℕ := Fintype.card ι
  let d : ℕ := Code.minDist (C : Set (ι → F))
  have he : 0 < (η : ℝ) := by exact_mod_cast hη
  have hMposR : 0 < (good.card : ℝ) :=
    lt_trans (by positivity : 0 < 2 / (η : ℝ) ^ 2) (by simpa [good] using hgood)
  have hMpos : 0 < good.card := by exact_mod_cast hMposR
  letI : Nonempty α := Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp hMpos)
  have hnR : 0 < (n : ℝ) := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hdle : d ≤ n := by
    dsimp [d, n]
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _
  have hsubcast : ((n - d : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) := by
    exact Nat.cast_sub hdle
  have hnum := linearBGKS_numeric_setup C δ_min η δ_src hmin hη hη3 hsrc
  rcases hnum with ⟨hdmin_le, ha_pos, hcube, hsum_lt⟩
  have hS (x : α) :
      (1 - (δ_src : ℝ)) * Fintype.card ι < ((S x).card : ℝ) := by
    dsimp [S]
    exact linearBGKSAgreementSet_card_gt C u δ_src x x.property
  have hmom :
      (1 - (δ_src : ℝ)) ^ 3 * Fintype.card ι *
          (Fintype.card α : ℝ) ^ 3 <
        ∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ)) :=
    linearBGKS_triple_intersection_moment S (1 - (δ_src : ℝ)) hS
  have htotal_prod :
      (∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ))) =
        ∑ p : α × α × α,
          (((S p.1 ∩ S p.2.1 ∩ S p.2.2).card : ℝ)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Fintype.sum_prod_type]
  have hinter_le (p : α × α × α) :
      (((S p.1 ∩ S p.2.1 ∩ S p.2.2).card : ℝ)) ≤
        ((n - d : ℕ) : ℝ) + if p ∈ D then (n : ℝ) else 0 := by
    by_cases hp : p ∈ D
    · rw [if_pos hp]
      have hcard : (S p.1 ∩ S p.2.1 ∩ S p.2.2).card ≤ n := by
        dsimp [n]
        simpa using
          (Finset.card_le_card
            (Finset.subset_univ (S p.1 ∩ S p.2.1 ∩ S p.2.2)))
      have hcardR :
          (((S p.1 ∩ S p.2.1 ∩ S p.2.2).card : ℝ)) ≤ (n : ℝ) := by
        exact_mod_cast hcard
      have hsubnonneg : 0 ≤ ((n - d : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (n - d)
      linarith
    · rw [if_neg hp, add_zero]
      have hp' : ¬ n - d < (S p.1 ∩ S p.2.1 ∩ S p.2.2).card := by
        intro hdense
        apply hp
        change p ∈ linearBGKSDenseTriples C u δ_src
        rw [linearBGKSDenseTriples, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [S, n, d] using hdense
      exact_mod_cast Nat.le_of_not_gt hp'
  have hupper :
      (∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ))) ≤
        ((n - d : ℕ) : ℝ) * (good.card : ℝ) ^ 3 +
          (n : ℝ) * (D.card : ℝ) := by
    rw [htotal_prod]
    calc
      (∑ p : α × α × α,
          (((S p.1 ∩ S p.2.1 ∩ S p.2.2).card : ℝ))) ≤
          ∑ p : α × α × α,
            (((n - d : ℕ) : ℝ) + if p ∈ D then (n : ℝ) else 0) := by
              exact Finset.sum_le_sum (fun p hp => hinter_le p)
      _ = ((n - d : ℕ) : ℝ) * (good.card : ℝ) ^ 3 +
          (n : ℝ) * (D.card : ℝ) := by
            rw [Finset.sum_add_distrib]
            have hconst :
                (∑ _p : α × α × α, ((n - d : ℕ) : ℝ)) =
                  ((n - d : ℕ) : ℝ) * (good.card : ℝ) ^ 3 := by
              simp [α, pow_three, mul_assoc, mul_comm]
            rw [hconst]
            have hind :
                (∑ p : α × α × α, if p ∈ D then (n : ℝ) else 0) =
                  (n : ℝ) * (D.card : ℝ) := by
              calc
                (∑ p : α × α × α, if p ∈ D then (n : ℝ) else 0) =
                    (n : ℝ) *
                      (∑ p : α × α × α, if p ∈ D then (1 : ℝ) else 0) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro p hp
                        by_cases hpD : p ∈ D <;> simp [hpD]
                _ = (n : ℝ) * (D.card : ℝ) := by
                      rw [← linearBGKS_card_indicator D]
            rw [hind]
  have hcardα : (Fintype.card α : ℝ) = (good.card : ℝ) := by simp [α]
  rw [hcardα] at hmom
  have hd_eq : (d : ℝ) = (δ_min : ℝ) * (n : ℝ) := by
    dsimp [d, n]
    rw [hmin]
    field_simp
  by_contra hnot
  have hDle : (D.card : ℝ) ≤ (η : ℝ) * (good.card : ℝ) ^ 3 := by
    have hnot' : ¬ (η : ℝ) * (good.card : ℝ) ^ 3 < (D.card : ℝ) := by
      simpa [D, good] using hnot
    exact le_of_not_gt hnot'
  have hfactor_pos :
      0 < (n : ℝ) * (good.card : ℝ) ^ 3 :=
    mul_pos hnR (pow_pos hMposR 3)
  have hcube' :
      (1 - (δ_min : ℝ) + (η : ℝ)) * (n : ℝ) *
          (good.card : ℝ) ^ 3 <
        (1 - (δ_src : ℝ)) ^ 3 * (n : ℝ) *
          (good.card : ℝ) ^ 3 := by
    simpa [mul_assoc] using mul_lt_mul_of_pos_right hcube hfactor_pos
  have hlower :
      (1 - (δ_min : ℝ) + (η : ℝ)) * (n : ℝ) *
          (good.card : ℝ) ^ 3 <
        ∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ)) := by
    have hmom' :
        (1 - (δ_src : ℝ)) ^ 3 * (n : ℝ) *
            (good.card : ℝ) ^ 3 <
          ∑ x : α, ∑ b : α, ∑ g : α,
            (((S x ∩ S b ∩ S g).card : ℝ)) := by
      simpa [n] using hmom
    exact lt_trans hcube' hmom'
  have hmulD :
      (n : ℝ) * (D.card : ℝ) ≤
        (n : ℝ) * ((η : ℝ) * (good.card : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hDle (le_of_lt hnR)
  have hupper' :
      (∑ x : α, ∑ b : α, ∑ g : α,
          (((S x ∩ S b ∩ S g).card : ℝ))) ≤
        ((n - d : ℕ) : ℝ) * (good.card : ℝ) ^ 3 +
          (n : ℝ) * ((η : ℝ) * (good.card : ℝ) ^ 3) :=
    le_trans hupper (by
      simpa [add_comm] using
        add_le_add_left hmulD (((n - d : ℕ) : ℝ) * (good.card : ℝ) ^ 3))
  have heq :
      ((n - d : ℕ) : ℝ) * (good.card : ℝ) ^ 3 +
          (n : ℝ) * ((η : ℝ) * (good.card : ℝ) ^ 3) =
        (1 - (δ_min : ℝ) + (η : ℝ)) * (n : ℝ) *
          (good.card : ℝ) ^ 3 := by
    rw [hsubcast, hd_eq]
    ring
  rw [heq] at hupper'
  exact (not_lt_of_ge hupper') hlower

open scoped NNReal in
private def linearBGKSDistinctDenseTriples_card_gt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_min η δ_src : ℝ≥0)
    (hmin : (δ_min : ℝ) =
      (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη3 : (η : ℝ) < 1 / 3) (hηd : η < δ_min)
    (hsrc : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hgood : 2 / (η : ℝ) ^ 2 <
      ((linearBGKSGoodScalars C u δ_src).card : ℝ)) :
    ((η : ℝ) / 2) *
        ((linearBGKSGoodScalars C u δ_src).card : ℝ) ^ 3 <
      ((linearBGKSDistinctDenseTriples C u δ_src).card : ℝ) := by
  classical
  let good : Finset F := linearBGKSGoodScalars C u δ_src
  let α := ↥good
  let D : Finset (α × α × α) := linearBGKSDenseTriples C u δ_src
  let P : (α × α × α) → Prop := fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2
  let R : Finset (α × α × α) := Finset.univ.filter fun p =>
    p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2
  let B : Finset (α × α × α) := D.filter fun p =>
    p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2
  have hneg : D.filter (fun p => ¬ P p) = B := by
    ext p
    simp only [B, P, Finset.mem_filter]
    tauto
  have hpartNat : (D.filter P).card + B.card = D.card := by
    rw [← hneg]
    exact Finset.card_filter_add_card_filter_not P
  have hpart :
      ((D.filter P).card : ℝ) + (B.card : ℝ) = (D.card : ℝ) := by
    exact_mod_cast hpartNat
  have hBsub : B ⊆ R := by
    intro p hp
    have hrep :
        p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2 :=
      (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hrep⟩
  have hR :
      (R.card : ℝ) ≤ 3 * (good.card : ℝ) ^ 2 := by
    have h := linearBGKS_repeated_triples_card_le (α := α)
    simpa [R, α] using h
  have hB :
      (B.card : ℝ) ≤ 3 * (good.card : ℝ) ^ 2 := by
    have hcardNat : B.card ≤ R.card := Finset.card_le_card hBsub
    have hcard : (B.card : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hcardNat
    exact le_trans hcard hR
  have hDense :
      (η : ℝ) * (good.card : ℝ) ^ 3 < (D.card : ℝ) := by
    simpa [good, D] using
      (linearBGKSDenseTriples_card_gt C u δ_min η δ_src
        hmin hη hη3 hηd hsrc hgood)
  have he : 0 < (η : ℝ) := by exact_mod_cast hη
  have hCollision :
      3 * (good.card : ℝ) ^ 2 <
        ((η : ℝ) / 2) * (good.card : ℝ) ^ 3 :=
    linearBGKSCollisionNumeric (η : ℝ) (good.card : ℝ) he hη3
      (by simpa [good] using hgood)
  have hresult :
      ((η : ℝ) / 2) * (good.card : ℝ) ^ 3 <
        ((D.filter P).card : ℝ) := by
    linarith
  simpa [good, D, P, linearBGKSDistinctDenseTriples] using hresult

open scoped NNReal in
private def linearBGKS_rich_affine_line
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_min η δ_src : ℝ≥0)
    (hmin : (δ_min : ℝ) =
      (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη3 : (η : ℝ) < 1 / 3) (hηd : η < δ_min)
    (hsrc : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hgood : 2 / (η : ℝ) ^ 2 <
      ((linearBGKSGoodScalars C u δ_src).card : ℝ)) :
    ∃ v0 v1 : ι → F, v0 ∈ C ∧ v1 ∈ C ∧
      ∃ A : Finset F, 1 / (η : ℝ) + 2 < (A.card : ℝ) ∧
        ∃ T : ↥A → Finset ι,
          (∀ x, (1 - (δ_src : ℝ)) * Fintype.card ι ≤ ((T x).card : ℝ)) ∧
          (∀ x i, i ∈ T x →
            u 0 i + (x : F) * u 1 i = v0 i + (x : F) * v1 i) := by
  classical
  let good : Finset F := linearBGKSGoodScalars C u δ_src
  let α := ↥good
  let D : Finset (α × α × α) := linearBGKSDistinctDenseTriples C u δ_src
  have he : 0 < (η : ℝ) := by exact_mod_cast hη
  have hM : 2 / (η : ℝ) ^ 2 < (Fintype.card α : ℝ) := by
    simpa [α, good] using hgood
  have hD :
      ((η : ℝ) / 2) * (Fintype.card α : ℝ) ^ 3 < (D.card : ℝ) := by
    simpa [α, good, D] using
      (linearBGKSDistinctDenseTriples_card_gt C u δ_min η δ_src
        hmin hη hη3 hηd hsrc hgood)
  have hdistinct : ∀ p ∈ D,
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
    intro p hp
    dsimp [D] at hp
    rw [linearBGKSDistinctDenseTriples, Finset.mem_filter] at hp
    exact hp.2
  obtain ⟨x, b, hxb, hrich⟩ :=
    linearBGKS_rich_fiber_of_many_distinct D (η : ℝ) he hM hD hdistinct
  let G : Finset α := Finset.univ.filter fun g : α => (x, b, g) ∈ D
  have hGcard : 1 / (η : ℝ) < (G.card : ℝ) := by
    simpa [G] using hrich
  have hxbval : (x : F) ≠ (b : F) := by
    intro h
    apply hxb
    exact Subtype.ext h
  have hbx : (b : F) - (x : F) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hxbval)
  let v1 : ι → F := (((b : F) - (x : F))⁻¹) •
    (linearBGKSClosestCodeword C u b - linearBGKSClosestCodeword C u x)
  let v0 : ι → F := linearBGKSClosestCodeword C u x - (x : F) • v1
  have hcx : linearBGKSClosestCodeword C u x ∈ C :=
    linearBGKSClosestCodeword_mem C u x
  have hcb : linearBGKSClosestCodeword C u b ∈ C :=
    linearBGKSClosestCodeword_mem C u b
  have hv1 : v1 ∈ C := by
    dsimp [v1]
    exact C.smul_mem _ (C.sub_mem hcb hcx)
  have hv0 : v0 ∈ C := by
    dsimp [v0]
    exact C.sub_mem hcx (C.smul_mem _ hv1)
  have hxline :
      linearBGKSClosestCodeword C u x = v0 + (x : F) • v1 := by
    funext i
    change linearBGKSClosestCodeword C u x i =
      (linearBGKSClosestCodeword C u x i - (x : F) * v1 i) +
        (x : F) * v1 i
    ring
  have hbline :
      linearBGKSClosestCodeword C u b = v0 + (b : F) • v1 := by
    funext i
    change linearBGKSClosestCodeword C u b i =
      (linearBGKSClosestCodeword C u x i -
        (x : F) * (((b : F) - (x : F))⁻¹ *
          (linearBGKSClosestCodeword C u b i -
            linearBGKSClosestCodeword C u x i))) +
      (b : F) * (((b : F) - (x : F))⁻¹ *
        (linearBGKSClosestCodeword C u b i -
          linearBGKSClosestCodeword C u x i))
    symm
    calc
      (linearBGKSClosestCodeword C u x i -
          (x : F) * (((b : F) - (x : F))⁻¹ *
            (linearBGKSClosestCodeword C u b i -
              linearBGKSClosestCodeword C u x i))) +
        (b : F) * (((b : F) - (x : F))⁻¹ *
          (linearBGKSClosestCodeword C u b i -
            linearBGKSClosestCodeword C u x i)) =
          linearBGKSClosestCodeword C u x i +
            (((b : F) - (x : F)) * ((b : F) - (x : F))⁻¹) *
              (linearBGKSClosestCodeword C u b i -
                linearBGKSClosestCodeword C u x i) := by ring
      _ = linearBGKSClosestCodeword C u x i +
            (linearBGKSClosestCodeword C u b i -
              linearBGKSClosestCodeword C u x i) := by
            rw [mul_inv_cancel₀ hbx, one_mul]
      _ = linearBGKSClosestCodeword C u b i := by ring
  have hGtriple (g : α) (hg : g ∈ G) : (x, b, g) ∈ D :=
    (Finset.mem_filter.mp hg).2
  have hGdistinct (g : α) (hg : g ∈ G) :
      x ≠ b ∧ x ≠ g ∧ b ≠ g :=
    hdistinct (x, b, g) (hGtriple g hg)
  have hGline (g : α) (hg : g ∈ G) :
      linearBGKSClosestCodeword C u g = v0 + (g : F) • v1 := by
    have hg' : (x, b, g) ∈ linearBGKSDistinctDenseTriples C u δ_src := by
      simpa [D] using hGtriple g hg
    have haff :=
      linearBGKS_codewords_affine_of_distinctDenseTriple C u δ_src x b g hg'
    dsimp only at haff
    exact haff.2.2
  let Gval : Finset F := G.image fun g : α => (g : F)
  have hxnotG : (x : F) ∉ Gval := by
    intro hxmem
    rcases Finset.mem_image.mp hxmem with ⟨g, hg, hval⟩
    exact (hGdistinct g hg).2.1 (Subtype.ext hval.symm)
  have hbnotG : (b : F) ∉ Gval := by
    intro hbmem
    rcases Finset.mem_image.mp hbmem with ⟨g, hg, hval⟩
    exact (hGdistinct g hg).2.2 (Subtype.ext hval.symm)
  have hGvalcard : Gval.card = G.card := by
    dsimp [Gval]
    exact Finset.card_image_of_injective G Subtype.val_injective
  let A : Finset F := insert (x : F) (insert (b : F) Gval)
  have hxnotInner : (x : F) ∉ insert (b : F) Gval := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxbval, hxnotG⟩
  have hAcardNat : A.card = G.card + 2 := by
    dsimp [A]
    rw [Finset.card_insert_of_notMem hxnotInner]
    rw [Finset.card_insert_of_notMem hbnotG]
    rw [hGvalcard]
  have hAcard : 1 / (η : ℝ) + 2 < (A.card : ℝ) := by
    have hcast : (A.card : ℝ) = (G.card : ℝ) + 2 := by
      exact_mod_cast hAcardNat
    rw [hcast]
    linarith
  have hAgood (y : F) (hy : y ∈ A) : y ∈ good := by
    simp only [A, Finset.mem_insert] at hy
    rcases hy with hy | hy | hy
    · subst y
      exact x.property
    · subst y
      exact b.property
    · rcases Finset.mem_image.mp hy with ⟨g, hg, rfl⟩
      exact g.property
  let T : ↥A → Finset ι := fun y => linearBGKSAgreementSet C u (y : F)
  refine ⟨v0, v1, hv0, hv1, A, hAcard, T, ?_, ?_⟩
  · intro y
    have hyGood : (y : F) ∈ linearBGKSGoodScalars C u δ_src := by
      simpa [good] using hAgood (y : F) y.property
    have hcard := linearBGKSAgreementSet_card_gt C u δ_src (y : F) hyGood
    simpa [T] using le_of_lt hcard
  · intro y i hi
    have hi' : i ∈ linearBGKSAgreementSet C u (y : F) := by
      simpa [T] using hi
    have hyagree :
        u 0 i + (y : F) * u 1 i =
          linearBGKSClosestCodeword C u (y : F) i := by
      simpa [linearBGKSAgreementSet, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hi'
    have hyA : (y : F) ∈ A := y.property
    simp only [A, Finset.mem_insert] at hyA
    rcases hyA with hyx | hyb | hyG
    · calc
        u 0 i + (y : F) * u 1 i =
            linearBGKSClosestCodeword C u (y : F) i := hyagree
        _ = linearBGKSClosestCodeword C u x i := by rw [hyx]
        _ = v0 i + (x : F) * v1 i := by
          simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hxline i
        _ = v0 i + (y : F) * v1 i := by rw [hyx]
    · calc
        u 0 i + (y : F) * u 1 i =
            linearBGKSClosestCodeword C u (y : F) i := hyagree
        _ = linearBGKSClosestCodeword C u b i := by rw [hyb]
        _ = v0 i + (b : F) * v1 i := by
          simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hbline i
        _ = v0 i + (y : F) * v1 i := by rw [hyb]
    · rcases Finset.mem_image.mp hyG with ⟨g, hg, hgy⟩
      have hgline := hGline g hg
      calc
        u 0 i + (y : F) * u 1 i =
            linearBGKSClosestCodeword C u (y : F) i := hyagree
        _ = linearBGKSClosestCodeword C u g i := by rw [← hgy]
        _ = v0 i + (g : F) * v1 i := by
          simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hgline i
        _ = v0 i + (y : F) * v1 i := by rw [hgy]

open scoped NNReal in
private def linearBGKS_jointProximity_of_good_card_gt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_min η δ_src : ℝ≥0)
    (hmin : (δ_min : ℝ) =
      (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη3 : (η : ℝ) < 1 / 3) (hηd : η < δ_min)
    (hsrc : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hgood : 2 / (η : ℝ) ^ 2 <
      ((linearBGKSGoodScalars C u δ_src).card : ℝ)) :
    Code.jointProximity (C : Set (ι → F)) u (δ_src + η) := by
  have hnum := linearBGKS_numeric_setup C δ_min η δ_src hmin hη hη3 hsrc
  have hsumR : (δ_src : ℝ) + (η : ℝ) < 1 := hnum.2.2.2
  have hde : δ_src + η ≤ 1 := by
    exact_mod_cast le_of_lt hsumR
  have he : 0 < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨v0, v1, hv0, hv1, A, hA, T, hT, hagree⟩ :=
    linearBGKS_rich_affine_line C u δ_min η δ_src
      hmin hη hη3 hηd hsrc hgood
  have hj := jointProximity_of_many_affine_agreements
    C (u 0) (u 1) v0 v1 A T δ_src η he hde hv0 hv1 hA hT hagree
  have hu : Code.finMapTwoWords (u 0) (u 1) = u := by
    funext j
    fin_cases j <;> rfl
  simpa [hu] using hj

open scoped NNReal in
open scoped ProbabilityTheory in
private def linear_close_probability_le_strict_of_radius_lt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_fld δ_src : ℝ≥0) (hδ : δ_fld < δ_src) :
    Pr_{let x ← $ᵖ F}[δᵣ(u 0 + x • u 1, (C : Set (ι → F))) ≤ δ_fld] ≤
      Pr_{let x ← $ᵖ F}[δᵣ(u 0 + x • u 1, (C : Set (ι → F))) < δ_src] := by
  apply Probability.Pr_le_Pr_of_implies
  intro x hx
  exact lt_of_le_of_lt hx (by exact_mod_cast hδ)

open scoped NNReal in
open scoped ProbabilityTheory in
private def linear_close_probability_mono_of_radius_lt
    (C : LinearCode ι F) (u : Code.WordStack F (Fin 2) ι)
    (δ_fld δ_src : ℝ≥0) (hδ : δ_fld < δ_src) :
    Pr_{let x ← $ᵖ F}[δᵣ(u 0 + x • u 1, (C : Set (ι → F))) ≤ δ_fld] ≤
      Pr_{let x ← $ᵖ F}[δᵣ(u 0 + x • u 1, (C : Set (ι → F))) ≤ δ_src] := by
  apply Probability.Pr_le_Pr_of_implies
  intro x hx
  exact le_trans hx (by exact_mod_cast hδ.le)

open scoped NNReal in
open scoped ProbabilityTheory in
private def linear_epsCa_le_one_point_five_johnson_aux
    (C : LinearCode ι F) (δ_min η δ_fld δ_src : ℝ≥0)
    (hmin : (δ_min : ℝ) = (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη3 : (η : ℝ) < 1 / 3) (hηd : η < δ_min)
    (_hδ_fld_pos : 0 < δ_fld) (hδlt : δ_fld < δ_src)
    (hsrc : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    epsCa (F := F) (A := F) ((C : Set (ι → F))) δ_fld (δ_src + η) ≤
      ENNReal.ofReal (2 / ((η : ℝ) ^ 2 * Fintype.card F)) := by
  classical
  unfold epsCa
  refine iSup_le fun u => ?_
  by_cases hjp : Code.jointProximity (C : Set (ι → F)) u (δ_src + η)
  · rw [if_pos hjp]
    exact zero_le
  · rw [if_neg hjp]
    apply le_of_not_gt
    intro hgt
    have hstrict :
        ENNReal.ofReal (2 / ((η : ℝ) ^ 2 * Fintype.card F)) <
          Pr_{let x ← $ᵖ F}[
            δᵣ(u 0 + x • u 1, (C : Set (ι → F))) < δ_src] :=
      lt_of_lt_of_le hgt
        (linear_close_probability_le_strict_of_radius_lt
          C u δ_fld δ_src hδlt)
    have hgood := linearBGKSGoodScalars_card_gt
      C u δ_src η hη hstrict
    exact hjp (linearBGKS_jointProximity_of_good_card_gt
      C u δ_min η δ_src hmin hη hη3 hηd hsrc hgood)

/-- A CA bound for a linear code in the 1.5-Johnson regime. For `δ_fld < δ_src` and
`δ_src < 1 - ∛(1 - δ_min(C) + η)`,

  `ε_ca(C, δ_fld, δ_int := δ_src + η) ≤ 2 / (η² · |F|)`

The strict gap `δ_fld < δ_src` embeds ArkLib's non-strict close event into the source's strict
event and avoids an unsupported endpoint case. -/
theorem linear_epsCa_le_one_point_five_johnson
    (C : LinearCode ι F) (δ_min η δ_fld δ_src : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_third : (η : ℝ) < 1 / 3) (_hη_lt_δ_min : η < δ_min)
    (_hδ_fld_pos : 0 < δ_fld) (_hδ_fld_lt : δ_fld < δ_src)
    (_hδ_src : (δ_src : ℝ) <
      1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    epsCa (F := F) (A := F) ((C : Set (ι → F))) δ_fld (δ_src + η) ≤
      ENNReal.ofReal (2 / ((η : ℝ) ^ 2 * Fintype.card F)) := by
  exact linear_epsCa_le_one_point_five_johnson_aux
    C δ_min η δ_fld δ_src _h_δ_min _hη _hη_lt_third _hη_lt_δ_min
      _hδ_fld_pos _hδ_fld_lt _hδ_src

end General

end CodingTheory
