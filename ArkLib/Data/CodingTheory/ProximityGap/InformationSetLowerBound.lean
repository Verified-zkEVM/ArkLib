/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.Basic.LinearCode

/-!
# Mutual correlated agreement information-set lower bound

This file proves a lower bound on affine-line mutual correlated agreement for linear codes.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/

namespace ProximityGap

open NNReal Code Finset CoreDefinitions
open scoped BigOperators NNReal ENNReal ProbabilityTheory
open Probability

/-- For a linear code `C` and a radius below its relative minimum distance, affine-line mutual
correlated agreement is at least `min(⌊δ n⌋ / |F|, 1)`. -/
theorem linear_mcaError_ge_information_set
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (δ : ℝ≥0)
    (hδ : (δ : ℝ) * Fintype.card ι < (Code.dist (C : Set (ι → F)) : ℝ)) :
    (↑(min ((⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ≥0) /
      (Fintype.card F : ℝ≥0)) 1) : ℝ≥0∞) ≤
      mcaError (AffineLineGenerator F) C (δ : ℝ) := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set n : ℕ := Fintype.card ι with hn
  set d : ℕ := Code.dist (C : Set (ι → F)) with hd
  set m : ℕ := ⌊δ * (n : ℝ≥0)⌋₊ with hm
  set r : ℕ := min m (Fintype.card F) with hr
  have hn_pos : 0 < n := Fintype.card_pos
  have hd_le_n : d ≤ n := Code.dist_le_card (C : Set (ι → F))
  have hm_le_real : (m : ℝ) ≤ (δ : ℝ) * n := by
    have h : (m : ℝ≥0) ≤ δ * (n : ℝ≥0) :=
      Nat.floor_le (a := δ * (n : ℝ≥0)) (by positivity)
    have h' := NNReal.coe_le_coe.mpr h
    push_cast at h'
    exact h'
  have hm_lt_d : m < d := by
    have : (m : ℝ) < (d : ℝ) := lt_of_le_of_lt hm_le_real hδ
    exact_mod_cast this
  have hm_le_d1 : m ≤ d - 1 := by omega
  have hd_pos : 1 ≤ d := by omega
  have hδ_lt_one : (δ : ℝ) < 1 := by
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hdn : (δ : ℝ) * n < n := lt_of_lt_of_le hδ (by exact_mod_cast hd_le_n)
    by_contra h
    rw [not_lt] at h
    have h2 : (n : ℝ) ≤ δ * n := by
      have := mul_le_mul_of_nonneg_right h hn_pos_real.le
      rwa [one_mul] at this
    linarith
  have hδ_le_one : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hδ_lt_one.le
  have hr_le_d1 : r ≤ d - 1 := le_trans (min_le_left _ _) hm_le_d1
  have hr_le_cardF : r ≤ Fintype.card F := min_le_right _ _
  have hr_le_n : r ≤ n := by omega
  obtain ⟨S₀, -, hS₀card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := n - (d - 1))
      (by rw [Finset.card_univ, ← hn]; omega)
  have hS₀card' : Fintype.card S₀ =
      Fintype.card ι - (‖(C : Set (ι → F))‖₀ - 1) := by
    rw [Fintype.card_coe, hS₀card]
  have hcompl_card : (S₀ᶜ).card = d - 1 := by
    rw [Finset.card_compl, hS₀card, ← hn]
    omega
  obtain ⟨D, hD_sub, hDcard⟩ :=
    Finset.exists_subset_card_eq (s := S₀ᶜ) (n := r) (by rw [hcompl_card]; exact hr_le_d1)
  have hS₀_sub_Dcompl : S₀ ⊆ Dᶜ := Finset.subset_compl_comm.mp hD_sub
  have hemb : Nonempty ({x // x ∈ D} ↪ F) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_coe, hDcard]
    exact hr_le_cardF
  obtain ⟨φ⟩ := hemb
  set chal : ι → F := fun j => if hj : j ∈ D then φ ⟨j, hj⟩ else 0 with hchal
  have hchal_mem : ∀ {j : ι} (hj : j ∈ D), chal j = φ ⟨j, hj⟩ := by
    intro j hj
    simp only [hchal]
    rw [dif_pos hj]
  have hchal_injOn : Set.InjOn chal (D : Set ι) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    rw [hchal_mem ha, hchal_mem hb] at hab
    exact Subtype.ext_iff.mp (φ.injective hab)
  set f₂ : ι → F := fun j => if j ∈ D then (1 : F) else 0 with hf₂
  set f₁ : ι → F := fun j => if j ∈ D then -(chal j) else 0 with hf₁
  have hf₂_mem : ∀ {j : ι}, j ∈ D → f₂ j = 1 := by
    intro j hj
    simp only [hf₂]
    rw [if_pos hj]
  have hf₂_not : ∀ {j : ι}, j ∉ D → f₂ j = 0 := by
    intro j hj
    simp only [hf₂]
    rw [if_neg hj]
  have hf₁_mem : ∀ {j : ι}, j ∈ D → f₁ j = -(chal j) := by
    intro j hj
    simp only [hf₁]
    rw [if_pos hj]
  have hf₁_not : ∀ {j : ι}, j ∉ D → f₁ j = 0 := by
    intro j hj
    simp only [hf₁]
    rw [if_neg hj]
  set G : Finset F := D.image chal with hG
  have hGcard : G.card = r := by
    rw [hG, Finset.card_image_of_injOn hchal_injOn, hDcard]
  let U : Fin 2 → ι → F := ![f₁, f₂]
  have hcomb (c : F) (i : ι) :
      (∑ j : Fin 2, AffineLineGenerator F c j • U j i) = f₁ i + c • f₂ i := by
    simp [AffineLineGenerator, U]
  have hbad : ∀ c ∈ G, IsMCA (AffineLineGenerator F) C c U (δ : ℝ) := by
    intro c hc
    rw [hG, Finset.mem_image] at hc
    obtain ⟨x, hxD, hcx⟩ := hc
    have hx_not : x ∉ Dᶜ := Finset.notMem_compl.mpr hxD
    let T := insert x Dᶜ
    have hTcardNN : (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := by
      have hTc : T.card = (n - r) + 1 := by
        rw [show T = insert x Dᶜ from rfl, Finset.card_insert_of_notMem hx_not,
          Finset.card_compl, hDcard, ← hn]
      rw [ge_iff_le, ← hn, hTc, ← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub hδ_le_one,
        NNReal.coe_sub (show (r : ℝ≥0) ≤ (n : ℝ≥0) by exact_mod_cast hr_le_n)]
      have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast min_le_left m (Fintype.card F)
      have hexp : (1 - (δ : ℝ)) * n = (n : ℝ) - (δ : ℝ) * n := by ring
      rw [hexp]
      linarith [hm_le_real, hrm]
    have hTcardR : (T.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) := by
      have hco := NNReal.coe_le_coe.mpr hTcardNN
      rw [NNReal.coe_mul, NNReal.coe_sub hδ_le_one] at hco
      push_cast at hco
      nlinarith
    refine ⟨T, hTcardR, ?_, ?_⟩
    · rw [LinearCode.mem_projectedCodeSubmod_iff]
      refine ⟨0, C.zero_mem, ?_⟩
      funext i
      rw [LinearCode.projectedWord]
      change (∑ j : Fin 2, AffineLineGenerator F c j • U j i.val) = 0
      rw [hcomb]
      have hiT : (i.val : ι) ∈ insert x Dᶜ := by
        simpa only [T] using i.property
      rw [Finset.mem_insert] at hiT
      rcases hiT with hi | hi
      · rw [hi, hf₁_mem hxD, hf₂_mem hxD, hcx]
        simp
      · rw [Finset.mem_compl] at hi
        rw [hf₁_not hi, hf₂_not hi]
        simp
    · refine ⟨1, ?_⟩
      intro hf₂proj
      rw [LinearCode.mem_projectedCodeSubmod_iff] at hf₂proj
      obtain ⟨v₁, hv₁, hproj⟩ := hf₂proj
      have hv₁_zero : v₁ = 0 := by
        apply projection_injective (C : Set (ι → F)) hd_pos S₀ hS₀card' v₁ 0 hv₁ C.zero_mem
        funext i
        have hiT : (i.val : ι) ∈ T :=
          Finset.mem_insert_of_mem (hS₀_sub_Dcompl i.property)
        have hi_notD : (i.val : ι) ∉ D := Finset.mem_compl.mp (hS₀_sub_Dcompl i.property)
        change v₁ i.val = (0 : ι → F) i.val
        have heq := congr_fun hproj ⟨i.val, hiT⟩
        change f₂ i.val = v₁ i.val at heq
        rw [← heq, hf₂_not hi_notD]
        rfl
      have hxT : x ∈ T := Finset.mem_insert_self _ _
      have heq := congr_fun hproj ⟨x, hxT⟩
      change f₂ x = v₁ x at heq
      rw [hv₁_zero, hf₂_mem hxD] at heq
      exact one_ne_zero heq
  have hcount : r ≤ (Finset.filter
      (fun c => IsMCA (AffineLineGenerator F) C c U (δ : ℝ))
      (Finset.univ : Finset F)).card := by
    rw [← hGcard]
    refine Finset.card_le_card (fun c hc => ?_)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hbad c hc⟩
  have hcardF_pos : (0 : ℝ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcardF_ne : (Fintype.card F : ℝ≥0) ≠ 0 := ne_of_gt hcardF_pos
  have hmin_eq : min ((m : ℝ≥0) / (Fintype.card F : ℝ≥0)) 1 =
      (r : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    rcases le_total m (Fintype.card F) with h | h
    · have hrm : r = m := by rw [hr]; exact min_eq_left h
      rw [hrm]
      exact min_eq_left ((div_le_one hcardF_pos).mpr (by exact_mod_cast h))
    · have hrc : r = Fintype.card F := by rw [hr]; exact min_eq_right h
      rw [hrc, div_self hcardF_ne]
      exact min_eq_right ((one_le_div hcardF_pos).mpr (by exact_mod_cast h))
  have hPr : (↑(min ((m : ℝ≥0) / (Fintype.card F : ℝ≥0)) 1) : ℝ≥0∞) ≤
      Pr_{let γ ←$ᵖ F}[IsMCA (AffineLineGenerator F) C γ U (δ : ℝ)] := by
    rw [prob_uniform_eq_card_filter_div_card, ← ENNReal.coe_div hcardF_ne,
      ENNReal.coe_le_coe, hmin_eq]
    gcongr
  refine le_trans hPr ?_
  unfold mcaError
  exact le_iSup (fun V : Fin 2 → (ι → F) =>
    Pr_{let γ ←$ᵖ F}[IsMCA (AffineLineGenerator F) C γ V (δ : ℝ)]) U

end ProximityGap
