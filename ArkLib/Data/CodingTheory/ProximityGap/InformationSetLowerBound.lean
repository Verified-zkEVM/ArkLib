/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.Basic.LinearCode

/-!
# MCA information-set lower bound (ABF26 `prop:mca-information-set-lower-bound`)

This file proves the elementary information-set lower bound on the mutual correlated agreement
(MCA) error of a linear code, from
*Open Problems in List Decoding and Correlated Agreement*
(Arnon, Boneh, Fenzi; 2026), Section 4:

> Let `C ⊆ F^n` be a linear code and let `δ ∈ (0, δ_min(C))`. Then
> `ε_mca(C, δ) ≥ min(⌊δ·n⌋ / |F|, 1)`.

## Proof

Write `m := ⌊δ·n⌋`, `r := min(m, |F|)`, `d := δ_min(C)·n` (the minimum distance). The hypothesis
`δ·n < d` forces `δ < 1` (since `d ≤ n`) and `m ≤ d − 1`.

Rather than exhibit a size-`k` information set, we use the projection lemma
`projection_injective`: on a coordinate set `S₀` of size `n − (d − 1)`, restriction is injective
on `C`. Its complement has size `d − 1 ≥ r`, so we place `r` "bad" positions `D` there (`D ⊆ S₀ᶜ`,
so `S₀ ⊆ Dᶜ`), and choose `r` distinct field values `(γ_x)_{x ∈ D}` (possible since `r ≤ |F|`).
Define

* `f₂` = indicator of `D` (value `1` on `D`, `0` elsewhere),
* `f₁(x) = −γ_x` on `D`, `0` elsewhere.

For each of the `r` distinct challenges `c = γ_x`, the witness set `S_x := Dᶜ ∪ {x}` (of size
`(n − r) + 1 ≥ (1−δ)·n`) makes `f₁ + c·f₂` vanish (hence agrees with the zero codeword on `S_x`),
yet no codeword pair agrees with `(f₁, f₂)` on `S_x`: any `v₁ ∈ C` matching `f₂` on `S_x` vanishes
on `S₀ ⊆ Dᶜ ⊆ S_x`, so `v₁ = 0` by injectivity, contradicting `v₁(x) = f₂(x) = 1`. Thus MCA fails
at `r` distinct challenges, so `ε_mca ≥ r/|F| = min(m/|F|, 1)`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open NNReal Code Finset
open scoped BigOperators NNReal ENNReal ProbabilityTheory
open Probability

/-- **ABF26 `prop:mca-information-set-lower-bound`.** For a linear code `C ⊆ F^n` and a proximity
parameter `δ` with `δ·n < δ_min(C)·n` (i.e. `δ ∈ (0, δ_min(C))`), the MCA error is bounded below
by `min(⌊δ·n⌋ / |F|, 1)`.

The distinct-challenge witnesses `(f₁, f₂)` are built from an injective-projection coordinate set
(playing the role of the paper's information set): `f₂` is the indicator of
`r := min(⌊δ·n⌋, |F|)` bad positions and `f₁` cancels a distinct field value at each. -/
theorem linear_epsMCA_ge_informationSet
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (δ : ℝ≥0)
    (hδ : (δ : ℝ) * Fintype.card ι < (Code.dist (C : Set (ι → F)) : ℝ)) :
    (↑(min ((⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℝ≥0) / (Fintype.card F : ℝ≥0)) 1) : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (C : Set (ι → F)) δ := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set n : ℕ := Fintype.card ι with hn
  set d : ℕ := Code.dist (C : Set (ι → F)) with hd
  set m : ℕ := ⌊δ * (n : ℝ≥0)⌋₊ with hm
  set r : ℕ := min m (Fintype.card F) with hr
  -- Basic numeric facts.
  have hn_pos : 0 < n := Fintype.card_pos
  have hd_le_n : d ≤ n := Code.dist_le_card (C : Set (ι → F))
  -- `m ≤ δ·n` (real).
  have hm_le_real : (m : ℝ) ≤ (δ : ℝ) * n := by
    have h : (m : ℝ≥0) ≤ δ * (n : ℝ≥0) := Nat.floor_le (a := δ * (n : ℝ≥0)) (by positivity)
    have h2 := NNReal.coe_le_coe.mpr h
    push_cast at h2
    exact h2
  -- `m < d`, hence `m ≤ d - 1` and `d ≥ 1`.
  have hm_lt_d : m < d := by
    have : (m : ℝ) < (d : ℝ) := lt_of_le_of_lt hm_le_real hδ
    exact_mod_cast this
  have hm_le_d1 : m ≤ d - 1 := by omega
  have hd_pos : 1 ≤ d := by omega
  -- `δ < 1`.
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
    rw [← NNReal.coe_le_coe]; push_cast; exact hδ_lt_one.le
  -- `r` bounds.
  have hr_le_d1 : r ≤ d - 1 := le_trans (min_le_left _ _) hm_le_d1
  have hr_le_cardF : r ≤ Fintype.card F := min_le_right _ _
  have hr_le_n : r ≤ n := by omega
  -- Injective-projection coordinate set `S₀`, of size `n - (d - 1)`.
  obtain ⟨S₀, -, hS₀card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := n - (d - 1))
      (by rw [Finset.card_univ, ← hn]; omega)
  have hS₀card' : Fintype.card S₀ = Fintype.card ι - (‖(C : Set (ι → F))‖₀ - 1) := by
    rw [Fintype.card_coe, hS₀card]
  -- Complement has size `d - 1`, giving room for `r` bad positions `D ⊆ S₀ᶜ`.
  have hcompl_card : (S₀ᶜ).card = d - 1 := by
    rw [Finset.card_compl, hS₀card, ← hn]; omega
  obtain ⟨D, hD_sub, hDcard⟩ :=
    Finset.exists_subset_card_eq (s := S₀ᶜ) (n := r) (by rw [hcompl_card]; exact hr_le_d1)
  have hS₀_sub_Dcompl : S₀ ⊆ Dᶜ := Finset.subset_compl_comm.mp hD_sub
  -- `r` distinct field values indexed by `D`.
  have hemb : Nonempty ({x // x ∈ D} ↪ F) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_coe, hDcard]; exact hr_le_cardF
  obtain ⟨φ⟩ := hemb
  set chal : ι → F := fun j => if hj : j ∈ D then φ ⟨j, hj⟩ else 0 with hchal
  have hchal_mem : ∀ {j : ι} (hj : j ∈ D), chal j = φ ⟨j, hj⟩ := by
    intro j hj; simp only [hchal]; rw [dif_pos hj]
  have hchal_injOn : Set.InjOn chal (D : Set ι) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    rw [hchal_mem ha, hchal_mem hb] at hab
    exact Subtype.ext_iff.mp (φ.injective hab)
  -- The two words.
  set f₂ : ι → F := fun j => if j ∈ D then (1 : F) else 0 with hf₂
  set f₁ : ι → F := fun j => if j ∈ D then -(chal j) else 0 with hf₁
  have hf₂_mem : ∀ {j : ι}, j ∈ D → f₂ j = 1 := by intro j hj; simp only [hf₂]; rw [if_pos hj]
  have hf₂_not : ∀ {j : ι}, j ∉ D → f₂ j = 0 := by intro j hj; simp only [hf₂]; rw [if_neg hj]
  have hf₁_mem : ∀ {j : ι}, j ∈ D → f₁ j = -(chal j) := by
    intro j hj; simp only [hf₁]; rw [if_pos hj]
  have hf₁_not : ∀ {j : ι}, j ∉ D → f₁ j = 0 := by intro j hj; simp only [hf₁]; rw [if_neg hj]
  -- The set of bad challenges.
  set G : Finset F := D.image chal with hG
  have hGcard : G.card = r := by rw [hG, Finset.card_image_of_injOn hchal_injOn, hDcard]
  -- **Core claim:** every `c ∈ G` is a bad MCA challenge for `(f₁, f₂)`.
  have hbad : ∀ c ∈ G, mcaEvent (C : Set (ι → F)) δ f₁ f₂ c := by
    intro c hc
    rw [hG, Finset.mem_image] at hc
    obtain ⟨x, hxD, hcx⟩ := hc
    have hx_not : x ∉ Dᶜ := Finset.notMem_compl.mpr hxD
    refine ⟨insert x Dᶜ, ?_, ?_, ?_⟩
    · -- Size clause: `(n - r) + 1 ≥ (1 - δ)·n`.
      have hSc : (insert x Dᶜ).card = (n - r) + 1 := by
        rw [Finset.card_insert_of_notMem hx_not, Finset.card_compl, hDcard, ← hn]
      rw [ge_iff_le, ← hn, hSc, ← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub hδ_le_one,
        NNReal.coe_sub (show (r : ℝ≥0) ≤ (n : ℝ≥0) by exact_mod_cast hr_le_n)]
      have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast min_le_left m (Fintype.card F)
      have hexp : (1 - (δ : ℝ)) * n = (n : ℝ) - (δ : ℝ) * n := by ring
      rw [hexp]
      linarith [hm_le_real, hrm]
    · -- Line agreement with the zero codeword.
      refine ⟨0, (C : Submodule F (ι → F)).zero_mem, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with hi | hi
      · subst hi
        rw [hf₁_mem hxD, hf₂_mem hxD, hcx]; simp
      · rw [Finset.mem_compl] at hi
        rw [hf₁_not hi, hf₂_not hi]; simp
    · -- No codeword pair agrees with `(f₁, f₂)` on the witness set.
      rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
      have hv₁_zero : v₁ = 0 := by
        apply projection_injective (C : Set (ι → F)) hd_pos S₀ hS₀card' v₁ 0 hv₁
          ((C : Submodule F (ι → F)).zero_mem)
        funext i
        have hi_mem : (i.val : ι) ∈ insert x Dᶜ :=
          Finset.mem_insert_of_mem (hS₀_sub_Dcompl i.property)
        have hi_notD : (i.val : ι) ∉ D := Finset.mem_compl.mp (hS₀_sub_Dcompl i.property)
        change v₁ i.val = (0 : ι → F) i.val
        rw [(hag i.val hi_mem).2, hf₂_not hi_notD]; rfl
      have hx_mem : x ∈ insert x Dᶜ := Finset.mem_insert_self _ _
      have hxeq := (hag x hx_mem).2
      rw [hv₁_zero, hf₂_mem hxD] at hxeq
      exact one_ne_zero hxeq.symm
  -- `G ⊆ filter`, so the winning-challenge count is at least `r`.
  have hcount : r ≤ (Finset.filter (fun c => mcaEvent (C : Set (ι → F)) δ f₁ f₂ c)
      (Finset.univ : Finset F)).card := by
    rw [← hGcard]
    refine Finset.card_le_card (fun c hc => ?_)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hbad c hc⟩
  -- Per-word probability lower bound.
  have hcardF_pos : (0 : ℝ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcardF_ne : (Fintype.card F : ℝ≥0) ≠ 0 := ne_of_gt hcardF_pos
  have hmin_eq : min ((m : ℝ≥0) / (Fintype.card F : ℝ≥0)) 1
      = (r : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    rcases le_total m (Fintype.card F) with h | h
    · have hrm : r = m := by rw [hr]; exact min_eq_left h
      rw [hrm]
      exact min_eq_left ((div_le_one hcardF_pos).mpr (by exact_mod_cast h))
    · have hrc : r = Fintype.card F := by rw [hr]; exact min_eq_right h
      rw [hrc, div_self hcardF_ne]
      exact min_eq_right ((one_le_div hcardF_pos).mpr (by exact_mod_cast h))
  have hPr : (↑(min ((m : ℝ≥0) / (Fintype.card F : ℝ≥0)) 1) : ℝ≥0∞)
      ≤ Pr_{ let γ ←$ᵖ F }[ mcaEvent (C : Set (ι → F)) δ f₁ f₂ γ ] := by
    rw [prob_uniform_eq_card_filter_div_card, ← ENNReal.coe_div hcardF_ne,
      ENNReal.coe_le_coe, hmin_eq]
    gcongr
  -- Feed into the supremum defining `epsMCA`.
  refine le_trans hPr ?_
  unfold epsMCA
  have hsup := le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (C : Set (ι → F)) δ (u 0) (u 1) γ ]) (![f₁, f₂])
  simpa using hsup

end ProximityGap
