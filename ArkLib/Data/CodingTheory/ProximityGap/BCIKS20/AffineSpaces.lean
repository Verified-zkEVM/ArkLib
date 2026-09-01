/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces.Basic

/-!
# Bucketing and core affine-space proximity results

The Section 6 averaging lemmas, finite affine-space bridge, scaling invariance, and
all-elements-close theorem live in `AffineSpaces.Basic`. This module contains the bucketing
argument and the main BCIKS20 affine-space correlated-agreement results.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory ReedSolomon Code
open scoped BigOperators LinearCode ProbabilityTheory
open Probability
open AffineSpacesInternal


private theorem exists_large_of_finset_cover' {α : Type}
    {U : Finset α} {L : ℕ} {buckets : Fin L → Finset α}
    (hcover : ∀ x ∈ U, ∃ i, x ∈ buckets i)
    {B : ℕ} (hLB : L * B < U.card) :
    ∃ i, B < (buckets i).card := by
  classical
  by_contra hall
  push Not at hall
  have hle : U.card ≤ L * B := by
    calc U.card
        ≤ (Finset.univ.biUnion buckets).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, hi⟩ := hcover x hx
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      _ ≤ ∑ i : Fin L, (buckets i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin L, B := Finset.sum_le_sum (fun i _ => hall i)
      _ = L * B := by simp [Finset.sum_const]
  exact absurd hle (not_le.mpr hLB)


section Bucketing

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- BCIKS20 §6.3 bucketing: given an affine subspace U whose elements are all δ-close
to a linear code V, there exist a codeword v₀ and agreement set D' of size ≥ (1-δ)|ι|
such that the basepoint agrees with v₀ on D' and every generator direction agrees with
some codeword on D'. -/
theorem bucket_exists_common_codeword
    {k : ℕ} [NeZero k] (V : Submodule F (ι → F)) (u₀ : ι → F) (dirs : Fin k → ι → F)
    {δ : ℝ≥0}
    (h_elem_ja : ∀ x ∈ (Affine.affineSubspaceAtOrigin (F := F) u₀ dirs : Set (ι → F)),
        jointAgreement (C := (V : Set (ι → F))) (δ := δ)
          (W := finMapTwoWords u₀ (x - u₀)))
    (h_pair_ja : ∀ j : Fin k,
        jointAgreement (C := (V : Set (ι → F))) (δ := δ)
          (W := finMapTwoWords u₀ (dirs j)))
    (h_list_bound : ∀ (w : ι → F) (close : Finset (ι → F)),
        (∀ v ∈ close, v ∈ (V : Set (ι → F)) ∧ δᵣ(w, v) ≤ δ) →
        close.card < Fintype.card F)
    (hδ_exact : ∀ v ∈ (V : Set (ι → F)), δᵣ(u₀, v) ≤ δ → (δᵣ(u₀, v) : ℝ≥0) ≥ δ) :
    ∃ (v₀ : ι → F) (D' : Finset ι),
      v₀ ∈ (V : Set (ι → F)) ∧
      (D'.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      D' ⊆ Finset.filter (fun c => v₀ c = u₀ c) Finset.univ ∧
      ∀ j : Fin k, ∃ w_j ∈ (V : Set (ι → F)),
        D' ⊆ Finset.filter (fun c => w_j c = dirs j c) Finset.univ := by
  classical
  -- Step A: Per-direction JA witnesses.
  choose S_j hS_j v_pair hv_pair using fun j => h_pair_ja j
  set U_fin := affineFinset u₀ dirs
  have h_elem_fin : ∀ x ∈ U_fin, jointAgreement (C := (V : Set (ι → F))) (δ := δ)
      (W := finMapTwoWords u₀ (x - u₀)) := by
    intro x hx; apply h_elem_ja; rwa [← affine_mem_iff_finset_mem] at hx
  -- For each x ∈ U, extract the u₀-codeword (v 0) and its agreement set.
  -- Use a non-dependent wrapper to avoid membership-in-filter issues.
  have h_ja_all : ∀ x ∈ U_fin, ∃ (Sx : Finset ι) (_ : Sx.card ≥ (1 - δ) * Fintype.card ι)
      (vx : Fin 2 → ι → F),
      (∀ i, vx i ∈ (V : Set (ι → F)) ∧
        Sx ⊆ Finset.filter (fun j => vx i j = (finMapTwoWords u₀ (x - u₀)) i j) Finset.univ) := by
    intro x hx; obtain ⟨S, hS, v, hv⟩ := h_elem_fin x hx; exact ⟨S, hS, v, hv⟩
  choose S_x hS_x v_x hv_x using h_ja_all
  -- pickCodeword: for each x ∈ U, the codeword close to u₀.
  let pickCW : (x : ι → F) → x ∈ U_fin → (ι → F) := fun x hx => v_x x hx 0
  -- closeWords: image of pickCW over U.
  let closeWords : Finset (ι → F) := U_fin.attach.image (fun ⟨x, hx⟩ => pickCW x hx)
  have h_cw_mem : ∀ x (hx : x ∈ U_fin), pickCW x hx ∈ (V : Set (ι → F)) :=
    fun x hx => (hv_x x hx 0).1
  -- pickCW x agrees with u₀ on S_x (which has size ≥ (1-δ)|ι|).
  have h_cw_agree : ∀ x (hx : x ∈ U_fin),
      S_x x hx ⊆ Finset.filter (fun c => pickCW x hx c = u₀ c) Finset.univ := by
    intro x hx
    exact (hv_x x hx 0).2
  -- Step B: Bucket U by pickCW, pigeonhole for dominant bucket.
  -- h_list_bound needs δᵣ(u₀, v) ≤ δ. This is relHammingDist (ℚ≥0) vs δ (ℝ≥0).
  -- Agreement on ≥ (1-δ)|ι| coords ⟹ disagreement on ≤ δ|ι| coords ⟹ relHammingDist ≤ δ.
  have h_cw_close : ∀ x (hx : x ∈ U_fin), δᵣ(u₀, pickCW x hx) ≤ δ := by
    intro x hx
    have h_agree := h_cw_agree x hx
    have h_agree_size := hS_x x hx
    -- hammingDist ≤ |ι| - |S_x|
    have h_filter_card : (S_x x hx).card ≤
        (Finset.filter (fun c => u₀ c = pickCW x hx c) Finset.univ).card := by
      apply Finset.card_le_card; intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_agree hc ⊢
      exact (Finset.mem_filter.mp (h_agree hc)).2.symm
    have h_compl : (Finset.filter (fun c => ¬u₀ c = pickCW x hx c) Finset.univ).card =
        Fintype.card ι - (Finset.filter (fun c => u₀ c = pickCW x hx c) Finset.univ).card := by
      have := Finset.card_filter_add_card_filter_not
          (s := Finset.univ) (p := fun c => u₀ c = pickCW x hx c)
      simp only [Finset.card_univ] at this
      omega
    have h_ham : hammingDist u₀ (pickCW x hx) ≤ Fintype.card ι - (S_x x hx).card := by
      simp only [hammingDist]; rw [h_compl]; omega
    have h_sx_le : (S_x x hx).card ≤ Fintype.card ι := Finset.card_le_univ _
    -- Work in ℝ to avoid NNReal subtraction issues.
    -- Goal: δᵣ(u₀, pickCW x hx) ≤ δ, i.e., relHammingDist ≤ δ
    -- relHammingDist = ham / |ι|. Suffices ham ≤ δ * |ι|.
    -- Lift to ℝ via NNReal.coe_le_coe and work there.
    suffices h : (hammingDist u₀ (pickCW x hx) : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) by
      unfold relHammingDist
      -- Goal: ↑(↑ham / ↑|ι| : ℚ≥0) ≤ δ in ℝ≥0
      -- Convert via NNReal.coe_le_coe and ℝ
      apply NNReal.coe_le_coe.mp
      push_cast
      have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
      exact (div_le_iff₀ hn).mpr h
    calc (hammingDist u₀ (pickCW x hx) : ℝ)
        ≤ (Fintype.card ι : ℝ) - ((S_x x hx).card : ℝ) := by exact_mod_cast h_ham
      _ ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := by
          have h1 := h_agree_size
          -- h1 : (|S_x| : ℝ≥0) ≥ (1 - δ) * |ι|
          -- Lift to ℝ
          have h2 : ((S_x x hx).card : ℝ) ≥ ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
            by_cases hδ_le : δ ≤ 1
            · have h1' : ((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) ≤ ((S_x x hx).card : ℝ≥0) := h1.le
              calc ((S_x x hx).card : ℝ)
                  ≥ ((((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) := by exact_mod_cast h1'
                _ = ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
                    rw [NNReal.coe_mul, NNReal.coe_sub hδ_le, NNReal.coe_one, NNReal.coe_natCast]
            · push Not at hδ_le
              have hδ_real : (1 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_le
              linarith only [Nat.cast_nonneg' (α := ℝ) (S_x x hx).card,
                        mul_nonpos_of_nonpos_of_nonneg (by linarith only [hδ_real] : (1 : ℝ) - ↑δ ≤ 0)
                          (Nat.cast_nonneg' (α := ℝ) (Fintype.card ι))]
          linarith only [h2]
  have h_cw_bound : closeWords.card < Fintype.card F := by
    apply h_list_bound u₀
    intro v hv
    obtain ⟨⟨x, hx⟩, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨h_cw_mem x hx, h_cw_close x hx⟩
  -- Step B (cont): Pigeonhole via exists_large_of_finset_cover.
  -- Need buckets indexed by Fin L. Enumerate closeWords.
  let L := closeWords.card
  let cwList := closeWords.val.toList
  have hcwLen : cwList.length = L := by simp [cwList, L]
  -- Build Fin L-indexed buckets.
  let bucketsFin : Fin L → Finset (ι → F) :=
    fun i => U_fin.filter (fun x => ∃ hx : x ∈ U_fin, pickCW x hx = cwList.get (i.cast hcwLen.symm))
  -- Cover: every x ∈ U is in some bucket.
  have h_cover_fin : ∀ x ∈ U_fin, ∃ i : Fin L, x ∈ bucketsFin i := by
    intro x hx
    have h_in_cw : pickCW x hx ∈ closeWords :=
      Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    have h_in_list : pickCW x hx ∈ cwList := by
      simp only [cwList, Multiset.mem_toList]; exact h_in_cw
    obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem h_in_list
    refine ⟨⟨idx, by omega⟩, ?_⟩
    simp only [bucketsFin, Finset.mem_filter]
    exact ⟨hx, ⟨hx, by simp only [Fin.cast_mk, List.get_eq_getElem]; exact heq.symm⟩⟩
  -- Handle r = 0 case separately: U = {u₀}, all dirs = 0, conclusion trivial.
  set r := Module.finrank F ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F)))
    with hr_def
  by_cases hr : r = 0
  · -- r = 0: span(dirs) = ⊥, so all dirs j = 0. Conclusion trivial.
    have h_span_bot : Submodule.span F (Finset.univ.image dirs : Set (ι → F)) = ⊥ := by
      rwa [Submodule.finrank_eq_zero] at hr
    have h_dirs_zero : ∀ j, dirs j = 0 := by
      intro j
      have : dirs j ∈ (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)) :=
        Submodule.subset_span (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      rw [h_span_bot] at this
      exact (Submodule.mem_bot F).mp this
    set j₀ : Fin k := ⟨0, NeZero.pos k⟩
    refine ⟨v_pair j₀ 0, S_j j₀, (hv_pair j₀ 0).1, hS_j j₀, ?_, ?_⟩
    · intro c hc
      have hc' := ((hv_pair j₀ 0).2 hc)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ c, ?_⟩
      simpa [finMapTwoWords, h_dirs_zero j₀] using (Finset.mem_filter.mp hc').2
    · intro j
      refine ⟨0, V.zero_mem, ?_⟩
      intro c _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply]
      exact (h_dirs_zero j ▸ rfl)
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
  -- Size bound: L * |F|^{r-1} < |U| = |F|^r since L < |F|.
  have h_size : L * Fintype.card F ^ (r - 1) < U_fin.card := by
    rw [affine_finset_card_eq]
    have hF_pos : 0 < Fintype.card F := Fintype.card_pos
    have : Fintype.card F * Fintype.card F ^ (r - 1) = Fintype.card F ^ r := by
      calc Fintype.card F * Fintype.card F ^ (r - 1)
          = Fintype.card F ^ (r - 1) * Fintype.card F := Nat.mul_comm _ _
        _ = Fintype.card F ^ (r - 1 + 1) := (pow_succ _ _).symm
        _ = Fintype.card F ^ r := by
          congr 1; exact Nat.succ_pred_eq_of_pos hr_pos
    calc L * Fintype.card F ^ (r - 1)
        < Fintype.card F * Fintype.card F ^ (r - 1) := by
          exact Nat.mul_lt_mul_of_pos_right h_cw_bound (Nat.pos_of_ne_zero (by
            intro h; rw [Nat.pow_eq_zero] at h; omega))
      _ = Fintype.card F ^ r := this
  obtain ⟨i₀, h_big⟩ := exists_large_of_finset_cover' h_cover_fin h_size
  -- u₀ ∈ U and u₀ + dirs j ∈ U.
  have h_u0_mem : u₀ ∈ U_fin := by
    simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset]
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  -- Step C: Choose v₀ as dominant bucket's codeword. Build h_restrict.
  -- The dominant bucket bucketsFin i₀ has codeword cwList[i₀].
  set v₀ := cwList.get (i₀.cast hcwLen.symm) with hv₀_def
  -- v₀ ∈ closeWords, so v₀ = pickCW x hx for some x.
  have hv₀_in_cw : v₀ ∈ closeWords := by
    have h1 : v₀ ∈ cwList := List.get_mem cwList _
    simp only [cwList, Multiset.mem_toList] at h1
    exact Finset.mem_def.mpr h1
  obtain ⟨⟨x₀, hx₀⟩, _, hpick₀⟩ := Finset.mem_image.mp hv₀_in_cw
  have hv₀_mem : v₀ ∈ (V : Set (ι → F)) := by rw [← hpick₀]; exact h_cw_mem x₀ hx₀
  set D' := S_x x₀ hx₀
  have hD'_size : (D'.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := hS_x x₀ hx₀
  have hD'_sub_filter : D' ⊆ Finset.filter (fun c => v₀ c = u₀ c) Finset.univ := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := Finset.mem_filter.mp (h_cw_agree x₀ hx₀ hc)
    rw [← hpick₀]; exact this.2
  have h_restrict : ∀ x ∈ U_fin, ∃ w ∈ (V : Set (ι → F)),
      D' ⊆ Finset.filter (fun c => w c = x c) Finset.univ := by
    let B_v₀ := U_fin.filter (fun x => ∃ w ∈ (V : Set (ι → F)),
        D' ⊆ Finset.filter (fun c => w c = x c) Finset.univ)
    have h_bucket_sub : ∀ x (hx : x ∈ U_fin), pickCW x hx = v₀ → x ∈ B_v₀ := by
      intro x hx hpick
      simp only [B_v₀, Finset.mem_filter]
      refine ⟨hx, v₀ + v_x x hx 1, V.add_mem hv₀_mem (hv_x x hx 1).1, ?_⟩
      -- hδ_exact forces δᵣ(u₀, v₀) = δ, making {c | v₀ c = u₀ c} have exact size (1-δ)|ι|.
      -- Since S_x ⊆ {c | v₀ c = u₀ c} and |S_x| ≥ (1-δ)|ι| = |{c | v₀ c = u₀ c}|,
      -- S_x = {c | v₀ c = u₀ c} ⊇ D'. Then (v₀ + v_x 1) agrees with x on S_x ⊇ D'.
      have hSx_sub_filter : S_x x hx ⊆ Finset.filter (fun c => v₀ c = u₀ c) Finset.univ := by
        have h := h_cw_agree x hx; rw [hpick] at h; exact h
      have hv₀_close : δᵣ(u₀, v₀) ≤ δ := by rw [← hpick]; exact h_cw_close x hx
      have hv₀_far : (δᵣ(u₀, v₀) : ℝ≥0) ≥ δ := hδ_exact v₀ hv₀_mem hv₀_close
      have hv₀_eq : (δᵣ(u₀, v₀) : ℝ≥0) = δ := le_antisymm hv₀_close hv₀_far
      -- S_x = {c | v₀ c = u₀ c} because both have the same cardinality
      have hfilter_card : (Finset.filter (fun c => v₀ c = u₀ c) Finset.univ).card =
          Fintype.card ι - hammingDist u₀ v₀ := by
        have h_compl := Finset.card_filter_add_card_filter_not
          (s := Finset.univ) (p := fun c => v₀ c = u₀ c)
        simp only [Finset.card_univ] at h_compl
        have : (Finset.filter (fun c => ¬v₀ c = u₀ c) Finset.univ).card = hammingDist u₀ v₀ := by
          unfold hammingDist
          congr with c
          exact not_congr eq_comm
        omega
      have hSx_eq_filter : S_x x hx = Finset.filter (fun c => v₀ c = u₀ c) Finset.univ :=
        Finset.eq_of_subset_of_card_le hSx_sub_filter (by
          rw [hfilter_card]
          -- Use the existing h_cw_close proof pattern (L896-928) for NNReal arithmetic.
          -- Filter card = |ι| - ham. |S_x| ≥ (1-δ)|ι|. ham = δ*|ι| from hv₀_eq.
          -- So filter card = (1-δ)|ι| ≤ |S_x|.
          have h_ham_le : hammingDist u₀ v₀ ≤ Fintype.card ι := hammingDist_le_card_fintype
          -- Extract |S_x| bound in ℕ via ℝ detour
          suffices h : (Fintype.card ι - hammingDist u₀ v₀ : ℤ) ≤ (S_x x hx).card by omega
          -- Work in ℝ: from hv₀_eq get ham = δ*|ι|, from hS_x get |S_x| ≥ (1-δ)*|ι|.
          suffices h_real :
              (Fintype.card ι : ℝ) - (hammingDist u₀ v₀ : ℝ) ≤ ((S_x x hx).card : ℝ) by
            exact_mod_cast h_real
          -- Step 1: Extract ham = δ * |ι| in ℝ from hv₀_eq
          have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
          have h_ham_real : (hammingDist u₀ v₀ : ℝ) = (δ : ℝ) * (Fintype.card ι : ℝ) := by
            -- hv₀_eq : (δᵣ(u₀, v₀) : ℝ≥0) = δ, i.e. (ham/|ι| : ℚ≥0) cast to ℝ≥0 = δ
            -- Cast both sides to ℝ: (ham/|ι|) = δ in ℝ, multiply by |ι|.
            have h_le : (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) ≤ (δ : ℝ) := by
              calc (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ)
                  = ((hammingDist u₀ v₀ / Fintype.card ι : ℚ≥0) : ℝ) := by
                    push_cast; norm_cast
                _ ≤ (δ : ℝ) := by exact_mod_cast hv₀_close
            have h_ge : (δ : ℝ) ≤ (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) := by
              calc (δ : ℝ)
                  ≤ ((δᵣ(u₀, v₀) : ℝ≥0) : ℝ) := by exact_mod_cast hv₀_far.le
                _ = ((hammingDist u₀ v₀ / Fintype.card ι : ℚ≥0) : ℝ) := by rfl
                _ = (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) := by
                    push_cast; norm_cast
            have h_eq : (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) = (δ : ℝ) :=
              le_antisymm h_le h_ge
            rwa [div_eq_iff (ne_of_gt hn_pos)] at h_eq
          -- Step 2: Extract |S_x| ≥ (1-δ)*|ι| in ℝ
          have h_sx_real : ((S_x x hx).card : ℝ) ≥ ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
            have h1 := hS_x x hx  -- (|S_x| : ℝ≥0) ≥ (1 - δ) * |ι|
            by_cases hδ_le : δ ≤ 1
            · have h1' : ((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) ≤ ((S_x x hx).card : ℝ≥0) := h1.le
              calc ((S_x x hx).card : ℝ)
                  ≥ ((((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) := by exact_mod_cast h1'
                _ = ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
                    rw [NNReal.coe_mul, NNReal.coe_sub hδ_le, NNReal.coe_one, NNReal.coe_natCast]
            · push Not at hδ_le
              have hδ_real : (1 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_le
              linarith [Nat.cast_nonneg' (α := ℝ) (S_x x hx).card,
                        mul_nonpos_of_nonpos_of_nonneg (by linarith : (1 : ℝ) - ↑δ ≤ 0)
                          (Nat.cast_nonneg' (α := ℝ) (Fintype.card ι))]
          -- Step 3: Combine
          linarith)
      -- D' ⊆ {c | v₀ c = u₀ c} = S_x, so D' ⊆ S_x
      have hD'_sub_Sx : D' ⊆ S_x x hx := hSx_eq_filter ▸ hD'_sub_filter
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
      have hc_Sx := hD'_sub_Sx hc
      have hcD' := (Finset.mem_filter.mp (hD'_sub_filter hc)).2
      have h1 : v_x x hx 1 c = (finMapTwoWords u₀ (x - u₀)) 1 c :=
        (Finset.mem_filter.mp ((hv_x x hx 1).2 hc_Sx)).2
      simp only [finMapTwoWords] at h1
      rw [hcD', h1, Pi.sub_apply]; ring
    have h_Bv0_sub_U : ↑B_v₀ ⊆ (Affine.affineSubspaceAtOrigin (F := F) u₀ dirs : Set (ι → F)) := by
      intro x hx
      exact (affine_mem_iff_finset_mem u₀ dirs x).mpr
        (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
    -- B_v₀ is affine: it's {x ∈ U | x|_{D'} ∈ V|_{D'}}, preimage of linear sub under affine map.
    have h_Bv0_affine : B_v₀ ≠ U_fin →
        ∃ (m : ℕ) (u₀' : ι → F) (dirs' : Fin m → ι → F),
          B_v₀ = affineFinset u₀' dirs' ∧
          (Submodule.span F (Finset.univ.image dirs' : Set (ι → F)) :
            Submodule F (ι → F)) <
          Submodule.span F (Finset.univ.image dirs : Set (ι → F)) := by
      intro h_ne
      let π : (ι → F) →ₗ[F] (↑D' → F) := {
        toFun := fun f i => f i.1
        map_add' := fun _ _ => funext fun _ => rfl
        map_smul' := fun _ _ => funext fun _ => rfl
      }
      let span_dirs := Submodule.span F (Finset.univ.image dirs : Set (ι → F))
      let W := span_dirs ⊓ Submodule.comap π (Submodule.map π V)
      -- Extract basis of W, produce dirs'
      let m := Module.finrank F ↥W
      let bW := Module.finBasis F ↥W
      let dirs' : Fin m → ι → F := fun i => ((bW i : ↥W) : ι → F)
      -- span(dirs') = W: basis of W spans W via subtype inclusion
      have h_span_eq : Submodule.span F (Finset.univ.image dirs' : Set (ι → F)) = W := by
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          exact (bW i).2
        · intro x hx
          have h := bW.sum_repr ⟨x, hx⟩
          apply_fun Subtype.val at h
          simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
          rw [← h]
          exact Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span
              (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
      -- v₀ agrees with u₀ on D'
      have hv₀_agree : ∀ c ∈ D', v₀ c = u₀ c := fun c hc =>
        (Finset.mem_filter.mp (hD'_sub_filter hc)).2
      -- B_v₀ = affineFinset u₀ dirs'  (both equal W.toFinset.image (· + u₀))
      have h_eq : B_v₀ = affineFinset u₀ dirs' := by
        simp only [affineFinset, h_span_eq]
        ext x
        simp only [B_v₀, Finset.mem_filter, Finset.mem_image, Set.mem_toFinset]
        constructor
        · rintro ⟨hxU, w, hw, hD⟩
          refine ⟨x - u₀, ?_, by abel⟩
          refine ⟨?_, ?_⟩
          · -- x - u₀ ∈ span_dirs
            have hxU' := hxU
            simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset] at hxU'
            obtain ⟨d, hd, hxd⟩ := hxU'
            have : x - u₀ = d := by rw [← hxd]; abel
            rw [this]; exact hd
          · -- x - u₀ ∈ comap π (map π V)
            change π (x - u₀) ∈ Submodule.map π V
            rw [Submodule.mem_map]
            refine ⟨w - v₀, V.sub_mem hw hv₀_mem, ?_⟩
            ext ⟨c, hc⟩
            have hcD := hD hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcD
            simp only [π, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
            rw [hcD, hv₀_agree c hc]
        · rintro ⟨d, ⟨hd_span, hd_comap⟩, rfl⟩
          constructor
          · simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset]
            exact ⟨d, hd_span, rfl⟩
          · have hd_comap' : π d ∈ Submodule.map π V := hd_comap
            rw [Submodule.mem_map] at hd_comap'
            obtain ⟨w', hw', hπeq⟩ := hd_comap'
            refine ⟨w' + v₀, V.add_mem hw' hv₀_mem, ?_⟩
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
            have h1 : w' c = d c := congr_fun hπeq ⟨c, hc⟩
            rw [h1, hv₀_agree c hc, add_comm]
      -- W < span_dirs (from B_v₀ ≠ U_fin)
      have hW_lt : W < span_dirs := by
        rw [lt_iff_le_and_ne]
        refine ⟨inf_le_left, fun h_eq_W => h_ne ?_⟩
        suffices h : affineFinset u₀ dirs' = affineFinset u₀ dirs by
          rwa [h_eq]
        ext x
        simp only [affineFinset, Finset.mem_image, Set.mem_toFinset]
        have h_sub_eq : Submodule.span F (↑(image dirs' univ) : Set (ι → F)) =
            Submodule.span F (↑(image dirs univ) : Set (ι → F)) :=
          h_span_eq.trans h_eq_W
        constructor
        · rintro ⟨d, hd, rfl⟩
          exact ⟨d, h_sub_eq ▸ hd, rfl⟩
        · rintro ⟨d, hd, rfl⟩
          exact ⟨d, h_sub_eq ▸ hd, rfl⟩
      exact ⟨m, u₀, dirs', h_eq, h_span_eq ▸ hW_lt⟩
    -- |B_v₀| > |F|^{r-1}: dominant bucket ⊆ B_v₀ via h_bucket_sub.
    have h_Bv0_big : Fintype.card F ^ (Module.finrank F
        ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F))) - 1) < B_v₀.card := by
      calc Fintype.card F ^ (Module.finrank F
              ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F))) - 1)
          < (bucketsFin i₀).card := h_big
        _ ≤ B_v₀.card := by
            apply Finset.card_le_card
            intro x hx
            simp only [bucketsFin, Finset.mem_filter] at hx
            obtain ⟨hx_U, hx_mem, hpick⟩ := hx
            exact h_bucket_sub x hx_U hpick
    have h_Bv0_eq_U : B_v₀ = U_fin := by
      by_contra h_ne
      obtain ⟨m, u₀', dirs', h_eq, h_proper⟩ := h_Bv0_affine h_ne
      have := proper_affine_sub_card_le u₀ dirs B_v₀ h_Bv0_sub_U ⟨m, u₀', dirs', h_eq, h_proper⟩
      omega
    intro x hx
    have : x ∈ B_v₀ := h_Bv0_eq_U ▸ hx
    exact (Finset.mem_filter.mp this).2
  -- Step D: take v₀ and D'. For directions, use h_restrict at u₀ + dirs j.
  refine ⟨v₀, D', hv₀_mem, hD'_size, hD'_sub_filter, ?_⟩
  · intro j
    have h_uj_mem : u₀ + dirs j ∈ U_fin := by
      simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset]
      exact ⟨dirs j, Submodule.subset_span (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩), rfl⟩
    obtain ⟨w, hw_mem, hw_agree⟩ := h_restrict (u₀ + dirs j) h_uj_mem
    refine ⟨w - v₀, V.sub_mem hw_mem hv₀_mem, ?_⟩
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply]
    have hw_c := Finset.mem_filter.mp (hw_agree hc) |>.2
    have hv₀_c : v₀ c = u₀ c := (Finset.mem_filter.mp (hD'_sub_filter hc)).2
    rw [hw_c, hv₀_c, Pi.add_apply, add_sub_cancel_left]

end Bucketing

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Pigeonhole for finite covers: if `U` is covered by `L` indexed subsets and
`L * B < |U|`, then some subset has more than `B` elements. -/
theorem exists_large_of_finset_cover {α : Type}
    {U : Finset α} {L : ℕ} {buckets : Fin L → Finset α}
    (hcover : ∀ x ∈ U, ∃ i, x ∈ buckets i)
    {B : ℕ} (hLB : L * B < U.card) :
    ∃ i, B < (buckets i).card := by
  classical
  by_contra hall
  push Not at hall
  have hle : U.card ≤ L * B := by
    calc U.card
        ≤ (Finset.univ.biUnion buckets).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, hi⟩ := hcover x hx
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      _ ≤ ∑ i : Fin L, (buckets i).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin L, B := Finset.sum_le_sum (fun i _ => hall i)
      _ = L * B := by simp [Finset.sum_const]
  exact absurd hle (not_le.mpr hLB)

/-- If `S` is a finite set of elements that are all roots of a nonzero polynomial `Q`,
then `|S| ≤ deg(Q)`. Wrapper around Mathlib's `card_le_degree_of_subset_roots`. -/
theorem card_roots_finset_le_natDegree {R : Type} [CommRing R] [IsDomain R]
    {Q : Polynomial R} (hQ : Q ≠ 0)
    {S : Finset R} (hroots : ∀ a ∈ S, Polynomial.IsRoot Q a) :
    S.card ≤ Q.natDegree := by
  classical
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  exact (Polynomial.mem_roots hQ).mpr (hroots a ha)

omit [DecidableEq F] in
/-- The Guruswami-Sudan list-decoding bound: given a nonzero polynomial `Q` over `F[X]`
whose `Y`-degree is less than `|F|`, the number of distinct polynomials `P` such that
`(Y - P(X)) | Q(X, Y)` is strictly less than `|F|`. This is the structural core of the
list-decoding argument (BCIKS20 §5). -/
theorem card_divisors_lt_field
    {Q : Polynomial (Polynomial F)} (hQ : Q ≠ 0)
    (hd : Q.natDegree < Fintype.card F)
    {polys : Finset (Polynomial F)}
    (hdiv : ∀ P ∈ polys, (Polynomial.X - Polynomial.C P) ∣ Q) :
    polys.card < Fintype.card F := by
  calc polys.card
      ≤ Q.natDegree := by
        apply card_roots_finset_le_natDegree hQ
        intro P hP
        exact (Polynomial.dvd_iff_isRoot).mp (hdiv P hP)
    _ < Fintype.card F := hd

/-- Degree-bound numerator step: `(m + 1/2) * s * n / (deg - 1) ≤ 5 / (4 * μ)`.
Extracted from `exists_gs_multiplicity` to reduce heartbeat pressure. -/
private lemma gs_degree_bound_le_inv_mu
    {s η : ℝ} {m deg : ℕ} {n : ℕ}
    (hs_pos : 0 < s) (hη_pos : 0 < η)
    (hs_sq : s ^ 2 = (deg : ℝ) / n) (hn_pos : (0 : ℝ) < n)
    (hdeg : 1 < deg)
    (hm_bound : (m : ℝ) + 1 / 2 ≤ s / (2 * η) + 5 / 2)
    (μ : ℝ) (hμ_pos : 0 < μ) (hμ_le_η : μ ≤ η) (hμ_le_s20 : μ ≤ s / 20) :
    (↑m + 1/2) * s * (n : ℝ) / (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / (4 * μ) := by
  have hdeg1 : 0 < deg - 1 := by omega
  have hdeg_pos : (0 : ℝ) < deg := by exact_mod_cast (show 0 < deg by omega)
  have hdeg1_cast_eq : (↑(deg - 1 : ℕ) : ℝ) = (deg : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ deg), Nat.cast_one]
  have hdeg1_ge : (↑(deg - 1 : ℕ) : ℝ) ≥ (deg : ℝ) / 2 := by
    rw [hdeg1_cast_eq]
    linarith only [show (2 : ℝ) ≤ deg from by exact_mod_cast hdeg]
  have h_num : (↑m + 1/2) * s * (n : ℝ) ≤
      (deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s) := by
    have h1 : (↑m + 1/2) * s * (n : ℝ) ≤
        (s / (2 * η) + 5/2) * s * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hm_bound hs_pos.le) hn_pos.le
    have hsqn : s ^ 2 * (n : ℝ) = (deg : ℝ) := by
      rw [hs_sq, div_mul_cancel₀ _ hn_pos.ne']
    have h2 : (s / (2 * η) + 5/2) * s * (n : ℝ) =
        (deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s) := by
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hη_ne : η ≠ 0 := ne_of_gt hη_pos
      field_simp
      nlinarith only [hsqn]
    linarith only [h1, h2]
  have hdeg_le_2d1 : (deg : ℝ) ≤ 2 * ↑(deg - 1 : ℕ) := by
    linarith only [hdeg1_ge]
  have h3 : (deg : ℝ) / (2 * η) / (↑(deg - 1 : ℕ) : ℝ) ≤ 1 / η := by
    have hd1_pos : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
    rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) hd1_pos) hη_pos, one_mul]
    nlinarith only [mul_le_mul_of_nonneg_right hdeg_le_2d1 hη_pos.le]
  have h4 : 5 * (deg : ℝ) / (2 * s) / (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / s := by
    have hd1_pos : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
    rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) hd1_pos) hs_pos]
    nlinarith only [mul_le_mul_of_nonneg_right hdeg_le_2d1 hs_pos.le]
  have h5 : 1 / η ≤ 1 / μ := by
    rw [div_le_div_iff₀ hη_pos hμ_pos]
    linarith only [hμ_le_η]
  have h6 : 5 / s ≤ 1 / (4 * μ) := by
    rw [div_le_div_iff₀ hs_pos (by positivity : (0:ℝ) < 4 * μ)]
    linarith only [hμ_le_s20]
  calc (↑m + 1/2) * s * (n : ℝ) / (↑(deg - 1 : ℕ) : ℝ)
      ≤ ((deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s)) / (↑(deg - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right h_num (by positivity)
    _ = (deg : ℝ) / (2 * η) / (↑(deg - 1 : ℕ) : ℝ) +
        5 * (deg : ℝ) / (2 * s) / (↑(deg - 1 : ℕ) : ℝ) := add_div _ _ _
    _ ≤ 1 / η + 5 / s := add_le_add h3 h4
    _ ≤ 1 / μ + 1 / (4 * μ) := add_le_add h5 h6
    _ = 5 / (4 * μ) := by ring

omit [DecidableEq ι] [DecidableEq F] in
/-- Construct a GS multiplicity `m` satisfying both the Johnson radius bound and the degree
bound. Witness: `m = ⌈√ρ/(2η)⌉ + 1` where `η = 1 - √ρ - δ`. -/
lemma exists_gs_multiplicity {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1)
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ) :
    ∃ m : ℕ, 1 ≤ m
      ∧ (δ : ℝ) < gs_johnson deg (Fintype.card ι) m
      ∧ gs_degree_bound deg (Fintype.card ι) m / (deg - 1) < Fintype.card F := by
  have hn_le : Fintype.card ι ≤ Fintype.card F :=
    Fintype.card_le_of_injective domain domain.injective
  have hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1 :=
    ReedSolomon.sqrtRate_le_one _ _
  have hδ_real : (δ : ℝ) < 1 - (ReedSolomon.sqrtRate deg domain : ℝ) := by
    calc (δ : ℝ) < ((1 - ReedSolomon.sqrtRate deg domain : ℝ≥0) : ℝ) := by exact_mod_cast hδ
      _ = 1 - (ReedSolomon.sqrtRate deg domain : ℝ) := by
          rw [NNReal.coe_sub hsqrt_le, NNReal.coe_one]
  have hη_pos : 0 < 1 - (ReedSolomon.sqrtRate deg domain : ℝ) - (δ : ℝ) := by
    linarith only [hδ_real]
  set s : ℝ := (ReedSolomon.sqrtRate deg domain : ℝ) with hs_def
  set η : ℝ := 1 - s - (δ : ℝ) with hη_def
  -- For deg ≤ 1: degree bound is trivial (Nat division by 0 = 0)
  by_cases hdeg : 1 < deg
  · -- deg ≥ 2: full GS multiplicity construction
    set m := Nat.ceil (s / (2 * η)) + 1
    refine ⟨m, by omega, ?_, ?_⟩
    · -- Johnson bound: δ < gs_johnson deg n m
      have hn_pos : (0 : ℝ) < Fintype.card ι := by positivity
      have hm_pos : (0 : ℝ) < m := by positivity
      have hs_eq : s = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
        simp only [s, hs_def, ReedSolomon.sqrtRate]
        rw [Real.coe_sqrt]
        congr 1
        have : NeZero deg := ⟨by omega⟩
        have hdim := ReedSolomon.dim_eq_deg_of_le (α := domain) (n := deg)
          (by omega : deg ≤ Fintype.card ι)
        rw [LinearCode.rate, hdim]
        simp [LinearCode.length]
      have hgs_eq : gs_johnson deg (Fintype.card ι) m = 1 - s - s / (2 * m) := by
        unfold gs_johnson; simp only
        rw [hs_eq]
        have : (↑(↑deg / ↑(Fintype.card ι) : ℚ) : ℝ) = (deg : ℝ) / Fintype.card ι := by
          push_cast; ring
        rw [this]
      rw [hgs_eq]
      have hm_gt : s / (2 * η) < m := by
        have h1 : s / (2 * η) ≤ ↑(Nat.ceil (s / (2 * η))) := Nat.le_ceil _
        have h2 : (↑(Nat.ceil (s / (2 * η))) : ℝ) + 1 = (m : ℝ) := by
          simp only [m, Nat.cast_add, Nat.cast_one]
        linarith only [h1, h2]
      have hs_nn : (0 : ℝ) ≤ s := by positivity
      have hs_div_lt : s / (2 * ↑m) < η := by
        rcases eq_or_lt_of_le hs_nn with hs0 | hs_pos
        · rw [← hs0]; simp only [zero_div]; exact hη_pos
        · have h2m_pos : (0 : ℝ) < 2 * ↑m := by positivity
          rw [div_lt_iff₀ h2m_pos]
          have h2η_pos : (0 : ℝ) < 2 * η := by positivity
          have := (div_lt_iff₀ h2η_pos).mp hm_gt
          linarith only [this]
      linarith only [hs_div_lt]
    · -- Degree bound: gs_degree_bound deg n m / (deg - 1) < |F|
      have hn_pos : (0 : ℝ) < Fintype.card ι := by
        exact_mod_cast (show 0 < Fintype.card ι from Fintype.card_pos)
      have hdeg_pos : (0 : ℝ) < deg := by exact_mod_cast (show 0 < deg by omega)
      have hs_lt_one : s < 1 := by
        linarith only [NNReal.coe_pos.mpr hδ_pos, hδ_real]
      have hs_eq : s = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
        simp only [s, hs_def, ReedSolomon.sqrtRate]
        rw [Real.coe_sqrt]; congr 1
        have : NeZero deg := ⟨by omega⟩
        have hdim := ReedSolomon.dim_eq_deg_of_le (α := domain) (n := deg)
          (by omega : deg ≤ Fintype.card ι)
        rw [LinearCode.rate, hdim]; simp [LinearCode.length]
      have hs_pos : 0 < s := by
        rw [hs_eq]; exact Real.sqrt_pos_of_pos (div_pos hdeg_pos hn_pos)
      have hs_sq : s ^ 2 = (deg : ℝ) / Fintype.card ι :=
        hs_eq ▸ Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have hdeg1 : 0 < deg - 1 := by omega
      suffices h_real : (gs_degree_bound deg (Fintype.card ι) m : ℝ) /
          (↑(deg - 1 : ℕ) : ℝ) < (Fintype.card F : ℝ) by
        have hdeg1_cast : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
        have hmul := (div_lt_iff₀ hdeg1_cast).mp h_real
        exact Nat.div_lt_of_lt_mul (by
          have : (gs_degree_bound deg (Fintype.card ι) m : ℝ) <
            ↑(deg - 1 : ℕ) * ↑(Fintype.card F) := by linarith only [hmul]
          exact_mod_cast this)
      -- floor ≤ real expression
      have hfloor_le : (gs_degree_bound deg (Fintype.card ι) m : ℝ) ≤
          (↑m + 1/2) * s * (Fintype.card ι : ℝ) := by
        unfold gs_degree_bound; dsimp only
        have hnn : (0 : ℝ) ≤ (↑m + 1 / 2) * √↑(↑deg / ↑(Fintype.card ι) : ℚ) *
          ↑(Fintype.card ι) := by positivity
        have hcast : (↑(↑deg / ↑(Fintype.card ι) : ℚ) : ℝ) =
            (deg : ℝ) / Fintype.card ι := by push_cast; ring
        calc (↑⌊(↑m + 1 / 2) * √↑(↑deg / ↑(Fintype.card ι) : ℚ) *
              ↑(Fintype.card ι)⌋₊ : ℝ)
            ≤ (↑m + 1/2) * √↑(↑deg / ↑(Fintype.card ι) : ℚ) * ↑(Fintype.card ι) :=
              Nat.floor_le hnn
          _ = (↑m + 1/2) * s * (Fintype.card ι : ℝ) := by rw [hcast, ← hs_eq]
      -- Bound using μ = min(η, s/20)
      have hdeg1_cast_eq : (↑(deg - 1 : ℕ) : ℝ) = (deg : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ deg), Nat.cast_one]
      have hdeg1_ge : (↑(deg - 1 : ℕ) : ℝ) ≥ (deg : ℝ) / 2 := by
        rw [hdeg1_cast_eq]
        linarith only [show (2 : ℝ) ≤ deg from by exact_mod_cast hdeg]
      set μ : ℝ := min η (s / 20) with hμ_def
      have hμ_pos : 0 < μ := lt_min hη_pos (by positivity)
      have hμ_le_η : μ ≤ η := min_le_left _ _
      have hμ_le_s20 : μ ≤ s / 20 := min_le_right _ _
      have hμ_lt_one20 : μ < 1 / 20 := lt_of_le_of_lt hμ_le_s20 (by linarith)
      have hm_bound : (m : ℝ) + 1/2 ≤ s / (2 * η) + 5/2 := by
        have hm_eq : (m : ℝ) = ↑(Nat.ceil (s / (2 * η))) + 1 := by
          simp only [m, Nat.cast_add, Nat.cast_one]
        have hceil_le : (↑(Nat.ceil (s / (2 * η))) : ℝ) ≤ s / (2 * η) + 1 :=
          le_of_lt (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ s / (2 * η)))
        linarith only [hm_eq, hceil_le]
      have h_le_54μ : (↑m + 1/2) * s * (Fintype.card ι : ℝ) /
          (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / (4 * μ) :=
        gs_degree_bound_le_inv_mu hs_pos hη_pos hs_sq hn_pos hdeg
          hm_bound μ hμ_pos hμ_le_η hμ_le_s20
      -- 5/(4μ) < |F| via errorBound < 1
      have h_160 : 160 * μ ^ 6 < (deg : ℝ) ^ 2 := by
        have hμ6 : μ ^ 6 < (1/20 : ℝ) ^ 6 :=
          pow_lt_pow_left₀ hμ_lt_one20 hμ_pos.le (by omega)
        have h4 : (4 : ℝ) ≤ (deg : ℝ) ^ 2 := by
          exact_mod_cast Nat.pow_le_pow_left (show 2 ≤ deg by omega) 2
        calc
          160 * μ ^ 6 < 160 * (1 / 20 : ℝ) ^ 6 :=
            mul_lt_mul_of_pos_left hμ6 (by norm_num)
          _ < 4 := by norm_num
          _ ≤ (deg : ℝ) ^ 2 := h4
      have h_54_lt_deg2 : 5 / (4 * μ) < (deg : ℝ) ^ 2 / (128 * μ ^ 7) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        convert mul_lt_mul_of_pos_right h_160 (show (0 : ℝ) < 4 * μ by positivity) using 1
        all_goals ring
      -- Extract |F| bound from hε
      have h_field : (deg : ℝ) ^ 2 / (128 * μ ^ 7) < Fintype.card F := by
        classical
        set rate_nn : ℝ≥0 := ↑(LinearCode.rate (ReedSolomon.code domain deg))
        set sqr_nn := NNReal.sqrt rate_nn
        have h_johnson : δ ∈ Set.Ioo ((1 - rate_nn) / 2) (1 - sqr_nn) := by
          constructor
          · simpa [rate_nn] using hJ
          · simpa [sqr_nn, rate_nn, ReedSolomon.sqrtRate] using hδ
        rw [ProximityGap.errorBound_eq_johnson (by
          simpa [rate_nn, sqr_nn] using h_johnson)] at hε
        have hsqr_s : (↑sqr_nn : ℝ) = s := by
          simp [sqr_nn, rate_nn, ReedSolomon.sqrtRate, hs_def]
        have hδ_le : δ ≤ 1 - sqr_nn := le_of_lt h_johnson.2
        have hsqr_le1 : sqr_nn ≤ 1 := by
          simp [sqr_nn, rate_nn]
        have hmin_eq : (↑(min (1 - sqr_nn - δ) (sqr_nn / 20)) : ℝ) = μ := by
          rw [NNReal.coe_min, NNReal.coe_sub hδ_le, NNReal.coe_sub hsqr_le1,
            NNReal.coe_one, NNReal.coe_div, hsqr_s]
          norm_num [hμ_def, hη_def]
        have hε_real : (↑(↑deg ^ 2 : ℝ≥0) : ℝ) /
            ((2 * (↑(min (1 - sqr_nn - δ) (sqr_nn / 20)) : ℝ)) ^ 7 *
              ↑(Fintype.card F)) < 1 := by
          change (↑deg ^ 2 : ℝ≥0) /
            ((2 * min (1 - sqr_nn - δ) (sqr_nn / 20)) ^ 7 * ↑(Fintype.card F)) < 1 at hε
          exact_mod_cast hε
        rw [hmin_eq] at hε_real
        have hd : (0 : ℝ) < (2 * μ) ^ 7 * ↑(Fintype.card F) := by positivity
        have hlt := (div_lt_one hd).mp hε_real
        rw [show (2 * μ) ^ 7 = 128 * μ ^ 7 from by ring] at hlt
        have hcast : (↑(↑deg ^ 2 : ℝ≥0) : ℝ) = (↑deg : ℝ) ^ 2 := by push_cast; ring
        rw [hcast] at hlt
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 128 * μ ^ 7)]
        linarith only [hlt]
      calc (gs_degree_bound deg (Fintype.card ι) m : ℝ) / ↑(deg - 1 : ℕ)
          ≤ (↑m + 1/2) * s * ↑(Fintype.card ι) / ↑(deg - 1 : ℕ) :=
            div_le_div_of_nonneg_right hfloor_le (by positivity)
        _ ≤ 5 / (4 * μ) := h_le_54μ
        _ < (deg : ℝ) ^ 2 / (128 * μ ^ 7) := h_54_lt_deg2
        _ < Fintype.card F := h_field
  · -- deg ≤ 1: degree bound trivial (div by 0 = 0), Johnson bound via m selection
    have h_deg_le : deg ≤ 1 := by omega
    -- Degree bound is always trivial: deg - 1 = 0 in ℕ, so Nat.div _ 0 = 0 < |F|
    have h_deg_bound : ∀ m,
        gs_degree_bound deg (Fintype.card ι) m / (deg - 1) < Fintype.card F := by
      intro m
      have h0 : deg - 1 = 0 := by omega
      simp [h0]
    -- For deg = 0: gs_johnson 0 n m = 1 (√(0/n) = 0), and δ < 1 trivially.
    -- For deg = 1: use m = ⌈s/(2η)⌉ + 1 with dim_eq_deg_of_le'.
    rcases h_deg_le.eq_or_lt with rfl | h1
    · -- deg = 1
      set m := Nat.ceil (s / (2 * η)) + 1
      refine ⟨m, by omega, ?_, h_deg_bound m⟩
      have hn_pos : (0 : ℝ) < Fintype.card ι := by positivity
      have hs_eq : s = Real.sqrt ((1 : ℝ) / Fintype.card ι) := by
        simp only [s, hs_def, ReedSolomon.sqrtRate]; rw [Real.coe_sqrt]; congr 1
        have : NeZero (1 : ℕ) := ⟨by omega⟩
        have hdim := ReedSolomon.dim_eq_deg_of_le (α := domain) (n := 1)
          (by omega : 1 ≤ Fintype.card ι)
        rw [LinearCode.rate, hdim]; simp [LinearCode.length]
      have hgs_eq : gs_johnson 1 (Fintype.card ι) m = 1 - s - s / (2 * m) := by
        simp only [gs_johnson, Nat.cast_one, one_div, Rat.cast_inv, Rat.cast_natCast,
          Real.sqrt_inv]
        congr 1 <;> [congr 1; congr 2] <;>
          rw [hs_eq, Real.sqrt_div (by positivity : (0:ℝ) ≤ 1), Real.sqrt_one, one_div]
      rw [hgs_eq]
      have hm_gt : s / (2 * η) < m := by
        have h1 : s / (2 * η) ≤ ↑(Nat.ceil (s / (2 * η))) := Nat.le_ceil _
        linarith [show (↑(Nat.ceil (s / (2 * η))) : ℝ) + 1 = (m : ℝ) from by
          simp only [m, Nat.cast_add, Nat.cast_one]]
      have hs_nn : (0 : ℝ) ≤ s := by positivity
      have hs_div_lt : s / (2 * ↑m) < η := by
        rcases eq_or_lt_of_le hs_nn with hs0 | hs_pos
        · rw [← hs0]; simp only [zero_div]; exact hη_pos
        · have h2m_pos : (0 : ℝ) < 2 * ↑m := by positivity
          rw [div_lt_iff₀ h2m_pos]
          have h2η_pos : (0 : ℝ) < 2 * η := by positivity
          have := (div_lt_iff₀ h2η_pos).mp hm_gt
          linarith only [this]
      linarith only [hs_div_lt]
    · -- deg = 0: gs_johnson 0 n m = 1 trivially > δ
      have hdeg0 : deg = 0 := by omega
      subst hdeg0
      refine ⟨1, le_refl 1, ?_, h_deg_bound 1⟩
      -- gs_johnson 0 n 1 = 1 - √(0/n) - √(0/n)/2 = 1
      show (δ : ℝ) < gs_johnson 0 (Fintype.card ι) 1
      have hgs0 : gs_johnson 0 (Fintype.card ι) 1 = 1 := by
        simp only [gs_johnson, CharP.cast_eq_zero, zero_div, Rat.cast_zero, Real.sqrt_zero,
          sub_zero, Nat.cast_one, mul_one]
      rw [hgs0]
      linarith only [hδ_real, show (0 : ℝ) ≤ s from by positivity]

omit [DecidableEq ι] in
theorem rs_listDecoding_card_lt_field {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ) (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1)
    (w : ι → F)
    (closeWords : Finset (ι → F))
    (hclose : ∀ v ∈ closeWords, v ∈ ReedSolomon.code domain deg ∧ δᵣ(w, v) ≤ δ) :
    closeWords.card < Fintype.card F := by
  classical
  -- Each codeword v is in (degreeLT F deg).map (evalOnPoints domain),
  -- so ∃ P ∈ degreeLT, evalOnPoints domain P = v.
  -- Choose a polynomial witness for each codeword.
  let choosePoly : (v : ι → F) → v ∈ closeWords → Polynomial F :=
    fun v hv => ((Submodule.mem_map).mp ((hclose v hv).1)).choose
  have heval : ∀ (v : ι → F) (hv : v ∈ closeWords),
      ReedSolomon.evalOnPoints domain (choosePoly v hv) = v :=
    fun v hv => ((Submodule.mem_map).mp ((hclose v hv).1)).choose_spec.2
  -- Build the image Finset of polynomials.
  let polys : Finset (Polynomial F) :=
    closeWords.attach.image (fun ⟨v, hv⟩ => choosePoly v hv)
  -- Injectivity: if choosePoly v₁ = choosePoly v₂, then
  -- v₁ = evalOnPoints(choosePoly v₁) = evalOnPoints(choosePoly v₂) = v₂.
  have hinj : ∀ (a₁ a₂ : closeWords),
      choosePoly a₁.1 a₁.2 = choosePoly a₂.1 a₂.2 → a₁ = a₂ := by
    intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
    apply Subtype.ext; change v₁ = v₂
    calc v₁ = ReedSolomon.evalOnPoints domain (choosePoly v₁ hv₁) := (heval v₁ hv₁).symm
      _ = ReedSolomon.evalOnPoints domain (choosePoly v₂ hv₂) := by rw [h]
      _ = v₂ := heval v₂ hv₂
  have hcard_eq : polys.card = closeWords.card := by
    simp only [polys]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  -- Case split: deg ≤ 1 is trivial (code too small), deg ≥ 2 uses GS.
  by_cases hdeg : 1 < deg
  case neg =>
    -- deg ≤ 1: code ⊆ (degreeLT F deg).map evalOnPoints, dim ≤ deg ≤ 1.
    -- closeWords.card ≤ polys.card, and polys injects into degreeLT F deg.
    -- degreeLT F 0 = ⊥, degreeLT F 1 has dim 1, so |code| ≤ |F|^1 = |F|.
    -- But we need strict <. For deg = 0, code = {0}, card ≤ 1 < |F|.
    -- For deg = 1, polys ⊆ degreeLT F 1 = constants, |polys| ≤ |F|.
    -- We use: polys.card = closeWords.card, and polys ⊆ F (as constant polys).
    -- Actually: closeWords.card = polys.card ≤ (degreeLT F deg).card.
    -- For deg = 0: degreeLT F 0 = ⊥, so code = {0}, closeWords ⊆ {0}.
    push Not at hdeg
    interval_cases deg
    · -- deg = 0: code α 0 = ⊥, so closeWords ⊆ {0}, card ≤ 1 < |F|.
      have hcode_triv : ∀ v ∈ closeWords, v = 0 := fun v hv => by
        simpa [ReedSolomon.code_zero] using (hclose v hv).1
      have : closeWords.card ≤ 1 :=
        Finset.card_le_one_iff.mpr (fun hx hy => (hcode_triv _ hx).trans (hcode_triv _ hy).symm)
      linarith only [this,
        Fintype.one_lt_card_iff_nontrivial.mpr (Field.toNontrivial : Nontrivial F)]
    · -- deg = 1: each poly has degree < 1, so is constant: p = C(p.coeff 0).
      -- Inject closeWords into F via coeff 0. Strict < follows from injectivity.
      have hinj_F : ∀ (v₁ : ι → F) (hv₁ : v₁ ∈ closeWords)
          (v₂ : ι → F) (hv₂ : v₂ ∈ closeWords),
          (choosePoly v₁ hv₁).coeff 0 = (choosePoly v₂ hv₂).coeff 0 → v₁ = v₂ := by
        intro v₁ hv₁ v₂ hv₂ hcoeff
        have h1 := ((Submodule.mem_map).mp ((hclose v₁ hv₁).1)).choose_spec.1
        have h2 := ((Submodule.mem_map).mp ((hclose v₂ hv₂).1)).choose_spec.1
        have hp1 : choosePoly v₁ hv₁ = Polynomial.C ((choosePoly v₁ hv₁).coeff 0) := by
          apply Polynomial.eq_C_of_degree_le_zero
          rw [Polynomial.mem_degreeLT] at h1
          exact Order.lt_succ_iff.mp (by exact_mod_cast h1)
        have hp2 : choosePoly v₂ hv₂ = Polynomial.C ((choosePoly v₂ hv₂).coeff 0) := by
          apply Polynomial.eq_C_of_degree_le_zero
          rw [Polynomial.mem_degreeLT] at h2
          exact Order.lt_succ_iff.mp (by exact_mod_cast h2)
        have : choosePoly v₁ hv₁ = choosePoly v₂ hv₂ := by rw [hp1, hp2, hcoeff]
        calc v₁ = evalOnPoints domain (choosePoly v₁ hv₁) := (heval v₁ hv₁).symm
          _ = evalOnPoints domain (choosePoly v₂ hv₂) := by rw [this]
          _ = v₂ := heval v₂ hv₂
      -- Each close codeword v is constant: v = fun i => (choosePoly v hv).coeff 0.
      -- Show each close constant c must appear in range(w) (otherwise dist = 1 > δ).
      have hv_const : ∀ (v : ι → F) (hv : v ∈ closeWords) (i : ι),
          v i = (choosePoly v hv).coeff 0 := by
        intro v hv i
        have hmem := ((Submodule.mem_map).mp ((hclose v hv).1)).choose_spec.1
        have hp : choosePoly v hv = Polynomial.C ((choosePoly v hv).coeff 0) := by
          apply Polynomial.eq_C_of_degree_le_zero
          rw [Polynomial.mem_degreeLT] at hmem
          exact Order.lt_succ_iff.mp (by exact_mod_cast hmem)
        have h := congr_fun (heval v hv) i
        simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at h
        rw [hp, Polynomial.eval_C] at h
        exact h.symm
      -- closeWords.card ≤ |range(w)|: inject closeWords → range(w) via coeff 0
      -- Every close constant c must be in range(w)
      have hsqrt_pos : (0 : ℝ≥0) < ReedSolomon.sqrtRate 1 domain :=
        ReedSolomon.sqrtRate_pos (by simp)
      have hc_in_range : ∀ (v : ι → F) (hv : v ∈ closeWords),
          (choosePoly v hv).coeff 0 ∈ Finset.image w Finset.univ := by
        intro v hv
        by_contra hc
        simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hc
        have hdist_all : ∀ i, w i ≠ v i := fun i => by rw [hv_const v hv i]; exact hc i
        have hdist_eq : hammingDist w v = Fintype.card ι := by
          simp [hammingDist, Finset.filter_true_of_mem (fun i _ => hdist_all i)]
        have hrel : relHammingDist w v = 1 := by
          simp only [relHammingDist, hdist_eq]
          exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        have hle : (1 : ℝ≥0) ≤ δ := by
          have := (hclose v hv).2; rw [hrel] at this; exact_mod_cast this
        exact absurd (lt_of_lt_of_le hδ tsub_le_self) (not_lt.mpr hle)
      -- closeWords.card ≤ |image w univ| ≤ card ι
      have hcard_le_range : closeWords.card ≤ (Finset.image w Finset.univ).card := by
        let img := closeWords.attach.image (fun ⟨v, hv⟩ => (choosePoly v hv).coeff 0)
        have himg_card : img.card = closeWords.card := by
          rw [Finset.card_image_of_injective]
          · exact Finset.card_attach
          · intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
            exact Subtype.ext (hinj_F v₁ hv₁ v₂ hv₂ h)
        have himg_sub : img ⊆ Finset.image w Finset.univ := by
          intro c hc
          rw [Finset.mem_image] at hc
          obtain ⟨⟨v, hv⟩, _, rfl⟩ := hc
          exact hc_in_range v hv
        rw [← himg_card]
        exact Finset.card_le_card himg_sub
      have hrange_le : (Finset.image w Finset.univ).card ≤ Fintype.card ι :=
        (Finset.card_image_le).trans (by simp)
      -- card ι ≤ card F (from domain injective)
      have hn_le : Fintype.card ι ≤ Fintype.card F :=
        Fintype.card_le_of_injective domain domain.injective
      -- If card ι < card F, done
      by_cases hn_eq : Fintype.card ι = Fintype.card F
      · -- card ι = card F. If closeWords nonempty, derive contradiction.
        -- w maps ι to F. range(w) ⊆ F with |range| ≤ |ι| = |F|.
        -- Each close codeword is const_c with c ∈ range(w).
        -- Since each const_c is constant, agreement with w at position i iff w(i) = c.
        -- Sum over all c in range of |agree_c| = |ι| = n.
        -- If closeWords is nonempty, pick v ∈ closeWords. v = const_c.
        -- δᵣ(w, v) ≤ δ ≤ 1 - sqrtRate.
        -- For deg = 1: sqrtRate = √(1/n). So δ ≤ 1 - 1/√n.
        -- hammingDist(w, v) = n - |{i : w i = c}|
        -- |{i : w i = c}| ≤ n, and we need to show δᵣ gives contradiction.
        -- Since |range(w)| ≤ n = |F|, and each c in range has |agree_c| ≥ 1,
        -- if |range(w)| = |F| = n, each agree = 1, so hammingDist = n-1.
        -- δᵣ = (n-1)/n. Need (n-1)/n > 1 - 1/√n. Equiv to 1/√n > 1/n. True for n ≥ 2.
        -- If |range(w)| < |F| = n, some c ∉ range so closeWords doesn't map to it,
        -- but range(w).card < n = |F| and closeWords.card ≤ range.card < |F|. Done.
        by_cases hrange_full : (Finset.image w Finset.univ).card = Fintype.card F
        · -- range(w) = F, so |range| = n = |F|.
          -- Every position gives a distinct value, so w is injective.
          -- Then each agreement set has size ≤ n / |F| = 1.
          -- Pick any v ∈ closeWords (if empty, 0 < |F| is trivial).
          by_cases hempty : closeWords = ∅
          · simp [hempty]
          · -- closeWords nonempty, range(w) = F, n = |F|. Derive contradiction.
            -- w is injective: card(image w univ) = card(univ) implies InjOn
            have hw_inj : Function.Injective w := by
              rw [← Set.injOn_univ]
              have h : (Finset.image w (Finset.univ : Finset ι)).card =
                  (Finset.univ : Finset ι).card := by
                simp [hrange_full, hn_eq]
              rwa [← Finset.coe_univ, ← Finset.card_image_iff]
            exfalso
            obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
            -- v is constant, c ∈ range(w). w injective gives exactly 1 agreement.
            have hc_range := hc_in_range v hv
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc_range
            obtain ⟨i₀, hi₀⟩ := hc_range
            -- All j ≠ i₀ disagree: w j ≠ v j (v is constant (choosePoly v hv).coeff 0)
            have hdisagree : ∀ j, j ≠ i₀ → w j ≠ v j := by
              intro j hne
              rw [hv_const v hv j]
              intro heq; exact hne (hw_inj (heq.trans hi₀.symm))
            -- hammingDist ≥ n - 1
            have hdist_ge : hammingDist w v ≥ Fintype.card ι - 1 := by
              unfold hammingDist
              calc (Finset.univ.filter (fun i => w i ≠ v i)).card
                  ≥ ((Finset.univ).erase i₀).card := by
                    apply Finset.card_le_card; intro j hj
                    simp only [Finset.mem_erase, Finset.mem_univ] at hj
                    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdisagree j hj.1⟩
                _ = Fintype.card ι - 1 := by
                    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
            -- hammingDist = n means all disagree → δᵣ = 1 → same contradiction as hc_in_range
            -- hammingDist = n - 1 means δᵣ = (n-1)/n
            -- But actually: just need hammingDist ≥ n - 1 and n ≥ 2.
            -- δᵣ = hammingDist/n ≥ (n-1)/n
            -- Need (n-1)/n > 1 - sqrtRate (in ℝ≥0).
            -- sqrtRate = √(rate), rate = dim/n. For deg = 1: dim ≥ 1, rate ≥ 1/n.
            -- sqrtRate ≥ 1/√n. And (n-1)/n = 1 - 1/n.
            -- 1 - 1/n > 1 - 1/√n ⟺ 1/√n > 1/n ⟺ n > √n ⟺ n ≥ 2. ✓
            -- Cast to ℝ and derive contradiction.
            -- hammingDist = n - 1 (w injective, exactly one agreement at i₀)
            have hi₀_agree : w i₀ = v i₀ := by rw [hv_const v hv i₀]; exact hi₀
            have hdist_lt_n : hammingDist w v < Fintype.card ι := by
              unfold hammingDist
              calc (Finset.univ.filter (fun i => w i ≠ v i)).card
                  < Finset.univ.card := Finset.card_lt_card
                    (Finset.filter_ssubset.mpr ⟨i₀, Finset.mem_univ _, by simp [hi₀_agree]⟩)
                _ = Fintype.card ι := Finset.card_univ
            have hdist_eq : hammingDist w v = Fintype.card ι - 1 :=
              le_antisymm (by omega) hdist_ge
            -- Chain in ℝ: (n-1)/n ≤ δᵣ ≤ δ, δ + sqrtRate ≤ 1 ⟹ sqrtRate ≤ 1/n.
            -- But √(rate) > rate ≥ 1/n ⟹ sqrtRate > 1/n. Contradiction.
            have hv_dist' : (δᵣ(w, v) : ℝ≥0) ≤ δ := (hclose v hv).2
            have hsqrt_le_one : ReedSolomon.sqrtRate 1 domain ≤ 1 :=
              ReedSolomon.sqrtRate_le_one 1 domain
            have h_add_le : δ + ReedSolomon.sqrtRate 1 domain ≤ 1 :=
              (le_tsub_iff_right hsqrt_le_one).mp (le_of_lt hδ)
            have h_add_real : (δ : ℝ) + (ReedSolomon.sqrtRate 1 domain : ℝ) ≤ 1 := by
              exact_mod_cast h_add_le
            have hrel_le_delta : (δᵣ(w, v) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hv_dist'
            have hn_pos : (0 : ℝ) < Fintype.card ι := by positivity
            have hrel_val : (δᵣ(w, v) : ℝ) = (Fintype.card ι - 1 : ℝ) / Fintype.card ι := by
              unfold relHammingDist; rw [hdist_eq]
              have hn_ne : (Fintype.card ι : ℚ≥0) ≠ 0 :=
                Nat.cast_ne_zero.mpr Fintype.card_ne_zero
              rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
              congr 1
              rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
            have hsqrt_le_inv : (ReedSolomon.sqrtRate 1 domain : ℝ) ≤
                1 / Fintype.card ι := by
              have h : (Fintype.card ι - 1 : ℝ) / Fintype.card ι =
                  1 - 1 / Fintype.card ι := by field_simp
              linarith only [hrel_val, hrel_le_delta, h_add_real, h]
            -- sqrtRate > 1/n: √rate > rate ≥ 1/n
            have hrate_pos : (0 : ℝ≥0) <
                (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) := by
              exact_mod_cast @DivergenceOfSets.reedSolomon_rate_pos ι _ _ F _ _ _ Nat.one_pos
            have hrate_lt_one :
                (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) < 1 := by
              have hdim_le := @DivergenceOfSets.reedSolomon_dim_le_deg ι _ F _ 1 domain
              have hdlt : LinearCode.dim (ReedSolomon.code domain 1) <
                  LinearCode.length (ReedSolomon.code domain 1) := by
                simp only [LinearCode.length]; omega
              exact_mod_cast show (LinearCode.rate (ReedSolomon.code domain 1) : ℚ≥0) < 1 from by
                rw [LinearCode.rate]
                exact (div_lt_one (by positivity : (0 : ℚ≥0) < _)).mpr (by exact_mod_cast hdlt)
            have hrate_ge_inv : (1 : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤
                (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) := by
              have hdim_ge : 1 ≤ LinearCode.dim (ReedSolomon.code domain 1) := by
                have hmul := @DivergenceOfSets.reedSolomon_rate_mul_card_eq_dim ι _ _ F _ 1 domain
                have h0 : (0 : ℝ≥0) < (LinearCode.dim (ReedSolomon.code domain 1) : ℝ≥0) :=
                  hmul ▸ mul_pos (by positivity) hrate_pos
                have : 0 < LinearCode.dim (ReedSolomon.code domain 1) := by exact_mod_cast h0
                omega
              have hge : (1 : ℚ≥0) / (Fintype.card ι : ℚ≥0) ≤
                  (LinearCode.rate (ReedSolomon.code domain 1) : ℚ≥0) := by
                rw [LinearCode.rate]; simp only [LinearCode.length]
                exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℚ≥0) < _)).mpr
                  (by exact_mod_cast hdim_ge)
              calc (1 : ℝ≥0) / (Fintype.card ι : ℝ≥0)
                  = ((1 : ℚ≥0) / (Fintype.card ι : ℚ≥0) : ℝ≥0) := by push_cast; ring
                _ ≤ _ := by exact_mod_cast hge
            have h_sqrt_gt : (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) <
                NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) := by
              have h1 : (_ : ℝ≥0) * _ < _ * 1 :=
                mul_lt_mul_of_pos_left hrate_lt_one hrate_pos
              rw [mul_one] at h1
              calc _ = NNReal.sqrt (_ * _) := (NNReal.sqrt_mul_self _).symm
                _ < NNReal.sqrt _ := NNReal.sqrt_lt_sqrt.2 h1
            have hsqrt_gt_inv : 1 / (Fintype.card ι : ℝ) <
                (ReedSolomon.sqrtRate 1 domain : ℝ) := by
              have h1 : ((1 : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ) =
                  1 / (Fintype.card ι : ℝ) := by push_cast; ring
              rw [← h1]
              exact_mod_cast show ((1 : ℝ≥0) / (Fintype.card ι : ℝ≥0)) <
                  ReedSolomon.sqrtRate 1 domain from
                calc (1 : ℝ≥0) / _ ≤ _ := hrate_ge_inv
                  _ < NNReal.sqrt _ := h_sqrt_gt
                  _ = ReedSolomon.sqrtRate 1 domain := by simp [ReedSolomon.sqrtRate]
            linarith only [hsqrt_le_inv, hsqrt_gt_inv]
        · -- range(w).card < |F|
          calc closeWords.card ≤ (Finset.image w Finset.univ).card := hcard_le_range
            _ < Fintype.card F := by omega
      · -- card ι < card F
        calc closeWords.card
            ≤ (Finset.image w Finset.univ).card := hcard_le_range
          _ ≤ Fintype.card ι := hrange_le
          _ < Fintype.card F := by omega
  case pos =>
  -- Split on UD vs Johnson regime
  by_cases hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ
  swap
  · -- UD regime: δ ≤ (1-ρ)/2. Unique decoding gives at most 1 close codeword.
    push Not at hJ
    have hcard_le_one : closeWords.card ≤ 1 :=
      Finset.card_le_one_iff.mpr fun {v₁ v₂} hv₁ hv₂ => by
      have hv₁_code := (hclose v₁ hv₁).1
      have hv₂_code := (hclose v₂ hv₂).1
      have hv₁_dist := (hclose v₁ hv₁).2
      have hv₂_dist := (hclose v₂ hv₂).2
      have : NeZero deg := ⟨by omega⟩
      have hrelUDR : Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
          (C := (ReedSolomon.code domain deg : Set (ι → F))) =
          ((1 : ℝ≥0) - ↑deg / ↑(Fintype.card ι)) / 2 :=
        ReedSolomon.relativeUniqueDecodingRadius_RS_eq (by omega)
      have hrate_eq : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) =
          (↑deg : ℝ≥0) / ↑(Fintype.card ι) := by
        have hdim := ReedSolomon.dim_eq_deg_of_le (α := domain) (n := deg) (by omega)
        simp [LinearCode.rate, hdim, LinearCode.length]
      rw [hrate_eq] at hJ
      rw [← hrelUDR] at hJ
      have h_v₁_le : (hammingDist w v₁ : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤
          Code.relativeUniqueDecodingRadius
            (C := (ReedSolomon.code domain deg : Set (ι → F))) := by
        calc (hammingDist w v₁ : ℝ≥0) / (Fintype.card ι : ℝ≥0)
            = ((δᵣ(w, v₁) : ℚ≥0) : ℝ≥0) := by
              simp [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
          _ ≤ (δ : ℝ≥0) := by exact_mod_cast hv₁_dist
          _ ≤ _ := hJ
      have h_v₂_le : (hammingDist w v₂ : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤
          Code.relativeUniqueDecodingRadius
            (C := (ReedSolomon.code domain deg : Set (ι → F))) := by
        calc (hammingDist w v₂ : ℝ≥0) / (Fintype.card ι : ℝ≥0)
            = ((δᵣ(w, v₂) : ℚ≥0) : ℝ≥0) := by
              simp [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
          _ ≤ (δ : ℝ≥0) := by exact_mod_cast hv₂_dist
          _ ≤ _ := hJ
      have hudr₁ : hammingDist w v₁ ≤ Code.uniqueDecodingRadius
          (C := (ReedSolomon.code domain deg : Set (ι → F))) :=
        (Code.dist_le_UDR_iff_relDist_le_relUDR _ _).2 h_v₁_le
      have hudr₂ : hammingDist w v₂ ≤ Code.uniqueDecodingRadius
          (C := (ReedSolomon.code domain deg : Set (ι → F))) :=
        (Code.dist_le_UDR_iff_relDist_le_relUDR _ _).2 h_v₂_le
      exact eq_of_le_uniqueDecodingRadius _ w hv₁_code hv₂_code hudr₁ hudr₂
    linarith only [hcard_le_one,
      Fintype.one_lt_card_iff_nontrivial.mpr (Field.toNontrivial : Nontrivial F)]
  -- Johnson regime: use Guruswami-Sudan with parameterized multiplicity m.
  suffices ∃ (Q : Polynomial (Polynomial F)), Q ≠ 0 ∧ Q.natDegree < Fintype.card F ∧
      ∀ P ∈ polys, (Polynomial.X - Polynomial.C P) ∣ Q by
    obtain ⟨Q, hQ_ne, hQ_deg, hQ_div⟩ := this
    rw [← hcard_eq]
    exact card_divisors_lt_field hQ_ne hQ_deg hQ_div
  have hn_le : Fintype.card ι ≤ Fintype.card F :=
    Fintype.card_le_of_injective domain domain.injective
  let ωs : Fin (Fintype.card ι) ↪ F := (Fintype.equivFin ι).symm.toEmbedding.trans domain
  let f : Fin (Fintype.card ι) → F := w ∘ (Fintype.equivFin ι).symm
  have hn_ne : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  -- Choose multiplicity m satisfying both GS conditions:
  -- (A) gs_johnson(deg,n,m) > δ (hence > δᵣ for all close codewords)
  -- (B) gs_degree_bound(deg,n,m) / (deg-1) < |F| (degree bound for Q)
  -- Requires strict gap δ < 1-sqrtRate (from rationality of δᵣ).
  -- gs_johnson(k,n,m) = 1-√(k/n)·(1+1/(2m)) → 1-√(k/n) as m→∞.
  obtain ⟨m, hm, hm_johnson, hm_degree⟩ :=
    exists_gs_multiplicity hδ_pos hδ hRS hε hJ
  obtain ⟨Q, hQ⟩ := GuruswamiSudan.gs_existence
    deg (Fintype.card ι) ωs f hdeg hn_ne hm
  refine ⟨Q, hQ.Q_ne_0, ?_, ?_⟩
  · -- Q.natDegree < |F|
    have hb : 0 < deg - 1 := by omega
    have hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (deg - 1) ≤
        gs_degree_bound deg (Fintype.card ι) m := by
      have h := hQ.Q_deg
      rw [Polynomial.Bivariate.weightedDegree_eq_natWeightedDegree] at h
      exact Option.some_le_some.mp h
    exact lt_of_le_of_lt (GuruswamiSudan.natDegree_le_of_natWeightedDegree hb hwd) hm_degree
  · -- ∀ P ∈ polys, (Y - C P) ∣ Q
    intro P hP
    simp only [polys, Finset.mem_image] at hP
    obtain ⟨⟨v, hv⟩, _, rfl⟩ := hP
    have hv_code := (hclose v hv).1
    have hP_deg : (choosePoly v hv) ∈ Polynomial.degreeLT F deg :=
      ((Submodule.mem_map).mp hv_code).choose_spec.1
    have hP_in_code : (fun i => (choosePoly v hv).eval (ωs i)) ∈
        ReedSolomon.code ωs deg :=
      Submodule.mem_map.mpr ⟨choosePoly v hv, hP_deg, rfl⟩
    let p : ReedSolomon.code ωs deg :=
      ⟨fun i => (choosePoly v hv).eval (ωs i), hP_in_code⟩
    have h_poly_eq : ReedSolomon.toPolynomial p = choosePoly v hv := by
      symm; rw [ReedSolomon.toPolynomial]
      exact Lagrange.eq_interpolate (ωs.injective.injOn) (by
        rw [Polynomial.mem_degreeLT] at hP_deg
        calc (choosePoly v hv).degree < deg := hP_deg
          _ ≤ Fintype.card (Fin (Fintype.card ι)) := by simp; omega)
    rw [← h_poly_eq]
    apply GuruswamiSudan.gs_divisibility hRS hm p hQ
    -- Bridge: hammingDist f (toPolynomial p ∘ ωs) / n ≤ δᵣ(w,v) ≤ δ < gs_johnson
    have hv_dist : (δᵣ(w, v) : ℝ≥0) ≤ δ := (hclose v hv).2
    have h_dist_eq : hammingDist f (fun i =>
        (ReedSolomon.toPolynomial p).eval (ωs i)) = hammingDist w v := by
      have hvi : ∀ i : Fin (Fintype.card ι),
          (choosePoly v hv).eval (ωs i) = v ((Fintype.equivFin ι).symm i) := by
        intro i
        have h := congr_fun (heval v hv) ((Fintype.equivFin ι).symm i)
        simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at h
        rw [← h]; congr 1
      simp only [hammingDist, h_poly_eq, f]; simp_rw [hvi]
      exact Finset.card_bij (fun i _ => (Fintype.equivFin ι).symm i)
        (fun i hi => by simpa [Finset.mem_filter] using hi)
        (fun _ _ _ _ h => (Fintype.equivFin ι).symm.injective h)
        (fun j hj => ⟨(Fintype.equivFin ι) j,
          by simp only [comp_apply, ne_eq, mem_filter, mem_univ, Equiv.symm_apply_apply,
            true_and] at hj ⊢; exact hj,
          (Fintype.equivFin ι).symm_apply_apply j⟩)
    rw [show (Fintype.card ι : ℝ) = ((Fintype.card ι : ℚ≥0) : ℝ) from by push_cast; ring]
    calc (hammingDist f (fun i => (ReedSolomon.toPolynomial p).eval (ωs i)) : ℝ) /
          ((Fintype.card ι : ℚ≥0) : ℝ)
        = (hammingDist w v : ℝ) / ((Fintype.card ι : ℚ≥0) : ℝ) := by rw [h_dist_eq]
      _ = ((δᵣ(w, v) : ℚ≥0) : ℝ) := by
          simp [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
      _ ≤ (δ : ℝ) := by exact_mod_cast hv_dist
      _ < gs_johnson deg (Fintype.card ι) m := hm_johnson

/-- Theorem 1.7 (Correlated agreement over affine spaces) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space with origin `u₀` and affine generating set `u₁, ..., uκ`
such that the probability a random point in the affine space is `δ`-close to the Reed-Solomon
code is greater than `ε`. Then the words `u₀, ..., uκ` have correlated agreement.

Note that we have `k + 2` vectors to form the affine space. This an intricacy needed us to be
able to isolate the affine origin from the affine span and to form a generating set of the
correct size. The reason for taking an extra vector is that after isolating the affine origin,
the affine span is formed as the span of the difference of the rest of the vector set. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (_hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (_hε : errorBound δ deg domain < 1) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  intro u hPr
  classical
  -- BCIKS20 §6.3 (p31). Proof structure follows the paper exactly.
  -- Overview:
  -- 1. All elements of U are δ-close to V (Lemma 6.3 + extension to span(U)).
  -- 2. Pick u* ∈ U achieving min distance δ* to V. δ* ≤ δ.
  -- 3. For each x ∈ U, Thm 1.4 on line (u*, x-u*) assigns a codeword for u*.
  --    List-decoding: < |F| possible codewords.
  -- 4. Pigeonhole: |U| = |F|^k elements → < |F| buckets → some bucket = U.
  -- 5. D' = {col : u* = v₀} has size (1-δ*)|ι| ≥ (1-δ)|ι|.
  --    ALL words agree with codewords on D' (bucket = U property).
  --    One D' for all words — no intersection, hence (1-δ) not (1-kδ).
  set V := ReedSolomon.code domain deg with hV_def
  set U := (Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u) : Set (ι → F))
  have hPr_sub : Pr_{let y ← $ᵖ (Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(↑y, (V : Set (ι → F))) ≤ δ] > errorBound δ deg domain := by
    convert hPr using 1
  have h_all_close : ∀ x ∈ U, δᵣ(x, (V : Set (ι → F))) ≤ δ :=
    all_affine_elements_close u (le_of_lt hδ) hPr_sub
  have hu0_mem : u 0 ∈ U := by
    change u 0 ∈ Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u)
    rw [Affine.mem_affineSubspaceFrom_iff]; exact ⟨0, by simp⟩
  -- ═══════════════════════════════════════════════════════════
  -- Step 2: Pick u* ∈ U achieving divergence (max distance to V).
  -- ═══════════════════════════════════════════════════════════
  have : Nonempty (V : Set (ι → F)) := ⟨0, V.zero_mem⟩
  have : Nonempty U := ⟨⟨u 0, hu0_mem⟩⟩
  obtain ⟨u_star, hu_star_mem, hu_star_div⟩ :=
    DivergenceOfSets.divergence_attains (U := U) (V := (V : Set (ι → F)))
  -- Extract u*'s affine coefficients without destroying u_star via rfl.
  have hu_star_aff : ∃ α_star : Fin k → F,
      u_star = u 0 + ∑ i : Fin k, α_star i • Fin.tail u i :=
    (Affine.mem_affineSubspaceFrom_iff (F := F) (u 0) (Fin.tail u) u_star).mp hu_star_mem
  obtain ⟨α_star, hα_star⟩ := hu_star_aff
  set δ_star : ℝ≥0 :=
    (DivergenceOfSets.divergence U (V : Set (ι → F)) : ℝ≥0) with hδ_star_def
  have hu_star_eq : (δᵣ'(u_star, (V : Set (ι → F))) : ℝ≥0) = δ_star := by
    simp only [δ_star]; exact_mod_cast hu_star_div
  have hδ_star_le : δ_star ≤ δ := by
    rw [← hu_star_eq]
    have h_close := h_all_close u_star hu_star_mem
    rw [relDistFromCode'_eq_relDistFromCode] at h_close
    exact_mod_cast h_close
  have hδ_star_le_sqrt : δ_star ≤ 1 - ReedSolomon.sqrtRate deg domain :=
    le_trans hδ_star_le (le_of_lt hδ)
  -- The affine space with u* as origin equals U (same direction span).
  have hU_star_eq : (Affine.affineSubspaceAtOrigin (F := F) u_star (Fin.tail u) :
      Set (ι → F)) = U := by
    ext x; constructor
    · intro hx
      have hx' := (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) x).mp hx
      obtain ⟨β, rfl⟩ := hx'
      exact (Affine.mem_affineSubspaceFrom_iff (F := F) (u 0) (Fin.tail u) _).mpr
        ⟨fun i => α_star i + β i, by rw [hα_star]; simp [Finset.sum_add_distrib, add_smul]; abel⟩
    · intro hx
      have hx' := (Affine.mem_affineSubspaceFrom_iff (F := F) (u 0) (Fin.tail u) x).mp hx
      obtain ⟨β, rfl⟩ := hx'
      exact (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) _).mpr
        ⟨fun i => β i - α_star i, by rw [hα_star]; simp [Finset.sum_sub_distrib, sub_smul]⟩
  -- Lines through u* in U stay in U.
  have h_line_in_U_star : ∀ x ∈ U, ∀ z : F, u_star + z • (x - u_star) ∈ U := by
    intro x hx z
    rw [← hU_star_eq] at hx ⊢
    obtain ⟨β, rfl⟩ := (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) x).mp hx
    exact (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) _).mpr
      ⟨fun i => z * β i, by
        congr 1; simp only [add_sub_cancel_left, Finset.smul_sum, smul_smul]⟩
  -- For any direction, line through u* has Pr[δ_star-close] = 1.
  have h_line_pr1_star : ∀ (dir : ι → F),
      (∀ z : F, u_star + z • dir ∈ U) →
      Pr_{let z ← $ᵖ F}[δᵣ((finMapTwoWords u_star dir) 0
        + z • (finMapTwoWords u_star dir) 1,
        (V : Set (ι → F))) ≤ δ_star] = 1 := by
    intro dir h_line_in_U
    rw [prob_uniform_eq_card_filter_div_card]
    have : Finset.filter (fun z : F =>
        δᵣ((finMapTwoWords u_star dir) 0
          + z • (finMapTwoWords u_star dir) 1,
          (V : Set (ι → F))) ≤ ↑δ_star) Finset.univ = Finset.univ := by
      ext z; constructor
      · exact fun _ => Finset.mem_univ _
      · intro _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ z, ?_⟩
        simp only [finMapTwoWords]
        have hx_mem := h_line_in_U z
        have hx_le_div := DivergenceOfSets.relDistFromCode'_le_divergence
          (U := U) (V := (V : Set (ι → F))) _ hx_mem
        have h_eq := relDistFromCode'_eq_relDistFromCode
          (u_star + z • dir) (V : Set (ι → F))
        rw [h_eq]
        apply ENNReal.coe_le_coe.mpr
        show (δᵣ'(u_star + z • dir, (V : Set (ι → F))) : ℝ≥0) ≤ δ_star
        simp only [hδ_star_def]
        exact_mod_cast hx_le_div
    rw [this, Finset.card_univ]
    exact_mod_cast div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- ═══════════════════════════════════════════════════════════
  -- Step 3: Direction generators through u* stay in U.
  -- ═══════════════════════════════════════════════════════════
  have h_dir_in_U_star : ∀ j : Fin k, ∀ z : F,
      u_star + z • Fin.tail u j ∈ U := by
    intro j z
    rw [← hU_star_eq]
    exact (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) _).mpr
      ⟨Pi.single j z, by simp⟩
  -- ═══════════════════════════════════════════════════════════
  -- Step 4: Apply Thm 1.4 with u* and δ_star.
  -- ═══════════════════════════════════════════════════════════
  have hε_star : errorBound δ_star deg domain < 1 :=
    lt_of_le_of_lt (DivergenceOfSets.errorBound_mono hdeg hδ_star_le hδ) _hε
  have hεδ_star_lt_one : (errorBound δ_star deg domain : ENNReal) < 1 := by
    exact_mod_cast hε_star
  have h_pair_ja : ∀ j : Fin k,
      jointAgreement (C := (V : Set (ι → F))) (δ := δ_star)
        (W := finMapTwoWords u_star (Fin.tail u j)) := by
    intro j
    apply RS_correlatedAgreement_affineLines hδ_star_le_sqrt
    rw [h_line_pr1_star _ (h_dir_in_U_star j)]
    exact hεδ_star_lt_one
  choose S_j hS_j v_pair hv_pair using fun j => h_pair_ja j
  -- Step 5: BCIKS20 §6.3 bucketing with u* and δ_star.
  have h_elem_ja : ∀ x ∈ (Affine.affineSubspaceAtOrigin (F := F) u_star (Fin.tail u) :
      Set (ι → F)),
      jointAgreement (C := (V : Set (ι → F))) (δ := δ_star)
        (W := finMapTwoWords u_star (x - u_star)) := by
    intro x hx
    have hx_U := (hU_star_eq ▸ hx : x ∈ U)
    apply RS_correlatedAgreement_affineLines hδ_star_le_sqrt
    rw [h_line_pr1_star _ (fun z => h_line_in_U_star x hx_U z)]
    exact hεδ_star_lt_one
  have hδ_star_strict : δ_star < 1 - ReedSolomon.sqrtRate deg domain :=
    lt_of_le_of_lt hδ_star_le hδ
  have h_bucket := bucket_exists_common_codeword V u_star (Fin.tail u) h_elem_ja h_pair_ja
    (fun w close hclose => by
      by_cases hδs_pos : (0 : ℝ≥0) < δ_star
      · exact rs_listDecoding_card_lt_field hδs_pos hδ_star_strict hRS hε_star w close
          (fun v hv => ⟨(hclose v hv).1, (hclose v hv).2⟩)
      · -- δ_star = 0: only w itself can be at distance 0, so |closeWords| ≤ 1 < |F|
        push Not at hδs_pos
        have hδs_eq : δ_star = 0 := le_antisymm hδs_pos (zero_le)
        have hclose_eq : ∀ v ∈ close, v = w := by
          intro v hv
          have hd := (hclose v hv).2
          have hd0 : hammingDist w v = 0 := by
            rw [hammingDist_eq_zero]
            by_contra hne
            have hpos : 0 < hammingDist w v := Nat.pos_of_ne_zero (hammingDist_ne_zero.mpr hne)
            have hrel_pos : (0 : ℚ≥0) < δᵣ(w, v) := by
              simp only [relHammingDist]
              exact div_pos (Nat.cast_pos.mpr hpos) (by positivity)
            have hrel_le : (δᵣ(w, v) : ℝ≥0) ≤ 0 := by
              calc (δᵣ(w, v) : ℝ≥0) ≤ δ_star := hd
                _ = 0 := hδs_eq
            exact absurd (show (0 : ℝ≥0) < δᵣ(w, v) from by exact_mod_cast hrel_pos)
              (not_lt.mpr hrel_le)
          exact (hammingDist_eq_zero.mp hd0).symm
        have hcard1 : close.card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          exact (hclose_eq a ha).trans (hclose_eq b hb).symm
        have hF_card : 1 < Fintype.card F :=
          Fintype.one_lt_card_iff_nontrivial.mpr (Field.toNontrivial)
        omega)
    (fun v hv hv_close => by
      -- hδ_exact: δᵣ(u*, v) ≥ δ_star. Since δ_star = δᵣ'(u*, V) = min_{v∈V} δᵣ(u*, v).
      rw [← hu_star_eq]
      change (relDistFromCode' u_star (V : Set (ι → F)) : ℝ≥0) ≤ (relHammingDist u_star v : ℝ≥0)
      exact_mod_cast Finset.min'_le _ _
        (Finset.mem_image.mpr ⟨(⟨v, hv⟩ : (V : Set (ι → F))), Finset.mem_univ _, rfl⟩))
  obtain ⟨v₀, D', hv₀_mem, hD'_card, hD'_ustar, h_dirs⟩ := h_bucket
  choose w_j hw_j_mem hw_j_agree using h_dirs
  -- D' has size ≥ (1-δ_star)|ι| ≥ (1-δ)|ι|.
  have hD'_card_δ : (D'.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := by
    calc (D'.card : ℝ≥0) ≥ (1 - (δ_star : ℝ≥0)) * Fintype.card ι := hD'_card
      _ ≥ (1 - δ) * Fintype.card ι := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact tsub_le_tsub_left hδ_star_le 1
  -- Build codeword for u 0: u 0 ∈ U = u* + span(dirs), so u 0 = u* + ∑ α_j • dirs j.
  -- On D': v₀ c = u* c and w_j c = dirs j c, so (v₀ + ∑ α_j • w_j) c = u 0 c.
  have hu0_in_star : u 0 ∈ (Affine.affineSubspaceAtOrigin (F := F) u_star (Fin.tail u) :
      Set (ι → F)) := hU_star_eq ▸ hu0_mem
  obtain ⟨α_u0, hα_u0⟩ := (Affine.mem_affineSubspaceFrom_iff (F := F) u_star
    (Fin.tail u) (u 0)).mp hu0_in_star
  set v_u0 := v₀ + ∑ j : Fin k, α_u0 j • w_j j with hv_u0_def
  have hv_u0_mem : v_u0 ∈ (V : Set (ι → F)) := by
    apply V.add_mem hv₀_mem
    exact V.sum_mem fun j _ => V.smul_mem _ (hw_j_mem j)
  have hv_u0_agree : D' ⊆ Finset.filter (fun c => v_u0 c = u 0 c) Finset.univ := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_star : v₀ c = u_star c := by
      have := hD'_ustar hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have h_dirs_c : ∀ j, w_j j c = Fin.tail u j c := by
      intro j
      have := hw_j_agree j hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [hv_u0_def, Pi.add_apply, Finset.sum_apply, h_star]
    conv_rhs => rw [hα_u0, Pi.add_apply, Finset.sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, h_dirs_c j]
  refine ⟨D', hD'_card_δ, ?_⟩
  refine ⟨fun i => if h : i = 0 then v_u0
    else w_j (i.pred (Fin.pos_iff_ne_zero.mp (Fin.pos_of_ne_zero h))), ?_⟩
  intro i
  by_cases hi : i = 0
  · subst hi; simp only [dite_true]
    exact ⟨hv_u0_mem, hv_u0_agree⟩
  · simp only [hi, dite_false]
    set j := i.pred (Fin.pos_iff_ne_zero.mp (Fin.pos_of_ne_zero hi))
    refine ⟨hw_j_mem j, fun c hc => ?_⟩
    have := hw_j_agree j hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
    rw [show i = Fin.succ j from (Fin.succ_pred i hi).symm]
    exact this

end CoreResults

end ProximityGap
