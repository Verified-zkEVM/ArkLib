/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Relative Distances for Codes

This module contains relative Hamming distance, relative distance-to-code, and the
finite-range/computable variants used by the coding-theory development.
-/

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

noncomputable section

open NNReal
open scoped NNReal
variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

section

variable [Nonempty ι] [DecidableEq F]

def relHammingDist (u v : ι → F) : ℚ≥0 :=
  hammingDist u v / Fintype.card ι

/--
  `δᵣ(u,v)` denotes the relative Hamming distance between vectors `u` and `v`.
-/
notation "δᵣ(" u ", " v ")" => relHammingDist u v

/-- The relative Hamming distance from a vector to a code, defined as the infimum
    of all relative distances from `u` to codewords in `C`.
    The type is `ENNReal` (ℝ≥0∞) to correctly handle the case `C = ∅`.
  For case of Nonempty C, we can use `relDistFromCode (δᵣ')` for smaller value range in
    `ℚ≥0`, which is equal to this definition. -/
noncomputable def relDistFromCode (u : ι → F) (C : Set (ι → F)) : ENNReal :=
  sInf {d | ∃ v ∈ C, (relHammingDist u v) ≤ d}

/-- `δᵣ(u,C)` denotes the relative distance from u to C. This is the main standard definition
used in statements. The NNRat version of it is `δᵣ'(u, C)`. -/
notation "δᵣ(" u ", " C ")" => relDistFromCode u C

omit [Nonempty ι] in
/-- The relative distance to a code is at most the relative distance to any specific codeword. -/
lemma relDistFromCode_le_relDist_to_mem (u : ι → F) {C : Set (ι → F)} (v : ι → F) (hv : v ∈ C) :
    δᵣ(u, C) ≤ δᵣ(u, v) := by
  apply csInf_le
  · -- Show the set is bounded below
    use 0
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    rcases hd with ⟨w, _, h_dist⟩
    exact (zero_le _).trans h_dist
  · -- Show relHammingDist u v is in the set
    simp only [Set.mem_setOf_eq]
    exact ⟨v, hv, le_refl _⟩

@[simp]
theorem relDistFromCode_of_empty (u : n → R) : δᵣ(u, (∅ : Set (n → R))) = ⊤ := by
  simp [relDistFromCode]

/-- This follows proof strategy from `exists_closest_codeword_of_Nonempty_Code`. However, it's NOT
used to construct `pickRelClosestCodeword_of_Nonempty_Code`. -/
lemma exists_relClosest_codeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    ∃ M ∈ C, (relHammingDist u M) = δᵣ(u, C) := by
  -- 1. Let `f` be the function that gives the relative distance as an NNReal
  let f := fun (v : ι → F) => ((relHammingDist u v : ENNReal))
  -- 2. Let `S_dists` be the set of all *actual* distances from `u` to `C`.
  let S_dists := f '' C
  -- 3. Show `S_dists` is non-empty (since C is non-empty)
  have hS_nonempty : S_dists.Nonempty := by
    -- `S_dists` is the image of a non-empty set `C`.
    apply Set.image_nonempty.mpr
    (expose_names; exact Set.nonempty_coe_sort.mp inst_2)
  -- 4. Show `S_dists` is finite
  have hS_finite : S_dists.Finite := by
    -- The set of *possible* Hamming distances is finite (a subset of {0..n})
    let S_ham_range := (SetLike.coe (Finset.range (Fintype.card ι + 1)) : Set ℕ)
    have hS_ham_range_finite : S_ham_range.Finite := Finset.finite_toSet _
    -- The set of *actual* Hamming distances `S_ham = {hammingDist u v | v ∈ C}`
    -- is a subset of this finite set.
    let S_ham := hammingDist u '' C
    have hS_ham_finite : S_ham.Finite := by
      apply Set.Finite.subset hS_ham_range_finite
      intro d hd
      simp only [S_ham, Set.mem_image] at hd
      rcases hd with ⟨v, _, rfl⟩
      simp only [Finset.coe_range, Set.mem_Iio, S_ham_range]
      let res := hammingDist_le_card_fintype (x := u) (y := v)
      omega
    -- `S_dists` is the image of the finite set `S_ham` under `g(d) = d/n`.
    -- So `S_dists` is also finite.
    have h_img_img : S_dists =
      (fun (d : ℕ) => ((((d : ℚ≥0) / ((Fintype.card ι) : ℚ≥0)) : ℚ≥0) : ENNReal)) '' S_ham := by
      ext d; simp only [relHammingDist, Set.mem_image, Set.image_image, S_dists, f, S_ham]
    rw [h_img_img]
    exact Set.Finite.image _ hS_ham_finite
  -- 5. Show that `δᵣ(u, C)` is just the `sInf` of this finite, non-empty set.
  have h_sInf_eq : δᵣ(u, C) = sInf S_dists := by
    -- This follows from `relDistFromCode`'s definition being the `sInf` of
    -- all upper bounds, which is equivalent to the `sInf` of the set itself.
    let S := {d | ∃ v ∈ C, f v ≤ d}
    apply le_antisymm
    · -- sInf S ≤ sInf S_dists (because S_dists ⊆ S)
      apply csInf_le_csInf
      · -- S is bounded below (by 0)
        use 0
        intro d hd
        simp only [Set.mem_setOf_eq] at hd
        rcases hd with ⟨v, _, hfv_le_d⟩
        exact (zero_le _).trans hfv_le_d
      · exact hS_nonempty
      · -- S_dists ⊆ S
        intro d' hd'
        simp only [S_dists, Set.mem_image, Set.mem_setOf_eq, f] at hd' ⊢
        rcases hd' with ⟨v, hv_mem, rfl⟩
        use v
    · -- sInf S_dists ≤ sInf S (because sInf S_dists is a lower bound for S)
      apply le_csInf
      · -- S is nonempty
        obtain ⟨v, hv⟩ := Set.nonempty_coe_sort.mp (by (expose_names; exact inst_2))
        use (f v : ENNReal)
        simp only [Set.mem_setOf_eq]
        use v, hv
      · intro d' hd'
        simp only [Set.mem_setOf_eq] at hd'
        rcases hd' with ⟨v, hv_mem, hfv_le_d'⟩
        -- `sInf S_dists` is a lower bound for `S_dists`, so `sInf S_dists ≤ f v`.
        have h_sInf_le_fv := csInf_le (by
          use 0; intro; (expose_names; exact fun a_1 ↦ zero_le a)) (Set.mem_image_of_mem f hv_mem)
        -- By transitivity, `sInf S_dists ≤ f v ≤ d'`, so `sInf S_dists ≤ d'`.
        exact h_sInf_le_fv.trans hfv_le_d'
  -- 6. The `sInf` of a finite, non-empty set is *in* the set.
  have h_sInf_mem : sInf S_dists ∈ S_dists := by
    -- exact NNReal.sInf_mem hS_finite hS_nonempty
    exact Set.Nonempty.csInf_mem hS_nonempty hS_finite
  -- 7. Unfold the definitions to get the goal.
  rw [h_sInf_eq]
  -- Goal: `sInf S_dists ∈ S_dists`
  -- This is exactly `h_sInf_mem`.
  exact h_sInf_mem

theorem relDistFromCode_eq_distFromCode_div (u : ι → F) (C : Set (ι → F)) :
    δᵣ(u, C) = (Δ₀(u, C) : ENNReal) / (Fintype.card ι : ENNReal) := by
  -- 1. Unfold definitions
  -- 2. Handle the case where C is empty
  by_cases hC_empty : C = ∅
  · rw [hC_empty]
    -- Both sides are ⊤
    simp only [relDistFromCode, distFromCode, relHammingDist]
    simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false, _root_.sInf_empty,
      ENat.toENNReal_top]
    rw [ENNReal.top_div]
    simp only [ENNReal.natCast_ne_top, ↓reduceIte]
  · -- 3. Handle the non-empty case
    letI : Nonempty C := by exact Set.nonempty_iff_ne_empty'.mpr hC_empty
    rcases exists_closest_codeword_of_Nonempty_Code C u with ⟨M, hM_mem, hM_is_min_abs⟩
    -- ⊢ δᵣ(u, C) = ↑Δ₀(u, C) / ↑(Fintype.card ι)
    have h_rhs : (Δ₀(u, C) : ENNReal) / (Fintype.card ι : ENNReal) =
                   (Δ₀(u, M) : ENNReal) / (Fintype.card ι : ENNReal) := by
      congr 1
      rw [←hM_is_min_abs]
      simp only [ENat.toENNReal_coe]
    rw [h_rhs]
    -- (LHS of our goal). We can show δᵣ(u, C) = (Δ₀(u, M) : ENNReal) / n
    -- by showing M is also the minimum for the relative distance.
    apply le_antisymm
    · -- 1. Goal: `δᵣ(u, C) ≤ ↑Δ₀(u, M) / ↑(Fintype.card ι)`
      -- This is true because the minimum distance to the code (LHS)
      -- must be less than or equal to the distance of *any* specific codeword.
      -- We show that the RHS is just the `relHammingDist` to M, cast to ENNReal.
      have h_rel_dist_M : ((relHammingDist u M) : ENNReal) = ↑Δ₀(u, M) / ↑(Fintype.card ι) := by
        simp only [relHammingDist]
        rw [NNRat.cast, NNRatCast.nnratCast, ENNReal.instNNRatCast] -- unfold the NNRat.cast
        simp only [NNRat.cast_div, NNRat.cast_natCast, ne_eq, Nat.cast_eq_zero,
          Fintype.card_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_natCast]
      rw [← h_rel_dist_M]
      -- The lemma `relDistFromCode_le_relDist_to_mem` states `δᵣ(u, C) ≤ ↑(relHammingDist u v)`
      exact relDistFromCode_le_relDist_to_mem u M hM_mem
    · -- 2. Goal: `↑Δ₀(u, M) / ↑(Fintype.card ι) ≤ δᵣ(u, C)`
      -- We show that the relative distance to M (LHS) is a lower bound
      -- for all relative distances, which means it must be ≤ the infimum (RHS).
      -- First, get the codeword `M'` that *actually* minimizes the relative distance.
      rcases exists_relClosest_codeword_of_Nonempty_Code C u with ⟨M', hM'_mem, hM'_is_min_rel⟩
      -- By definition of `M'`, `δᵣ(u, C) = relHammingDist u M'`.
      rw [←hM'_is_min_rel, relHammingDist]
      conv_rhs =>
        rw [ENNReal.coe_NNRat_coe_NNReal]; rw [NNRat.cast_div];
        simp only [NNRat.cast_natCast, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
          not_false_eq_true, ENNReal.coe_div, ENNReal.coe_natCast]
      gcongr
      rw [←ENat.coe_le_coe]
      -- Goal: `(↑Δ₀(u, M) : ENat) ≤ (↑Δ₀(u, M') : ENat)`
      -- This is true because M minimizes the absolute distance
      rw [hM_is_min_abs] -- `↑Δ₀(u, M) = Δ₀(u, C)` from `hM_is_min_abs`
      -- And we know `Δ₀(u, C) ≤ ↑Δ₀(u, v)` for *any* v, including M'
      exact distFromCode_le_dist_to_mem u M' hM'_mem

theorem pairDist_eq_distFromCode_iff_eq_relDistFromCode_div
    (u v : ι → F) (C : Set (ι → F)) [Nonempty C] : Δ₀(u, v) = Δ₀(u, C) ↔ δᵣ(u, v) = δᵣ(u, C) := by
  conv_rhs => rw [relDistFromCode_eq_distFromCode_div]
  constructor
  · intro h_dist_eq
    dsimp only [relHammingDist]
    conv_lhs =>
      rw [ENNReal.coe_NNRat_coe_NNReal, NNRat.cast_div];
      simp only [NNRat.cast_natCast, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
        not_false_eq_true, ENNReal.coe_div, ENNReal.coe_natCast]
    rw [←h_dist_eq]; rfl
  · intro h_rel_dist_eq
    dsimp only [relHammingDist] at h_rel_dist_eq
    conv_lhs at h_rel_dist_eq =>
      rw [ENNReal.coe_NNRat_coe_NNReal, NNRat.cast_div]; simp only [NNRat.cast_natCast,
      ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, ENNReal.coe_div,
      ENNReal.coe_natCast];
    conv at h_rel_dist_eq =>
      -- remove the denominator in both sides via ENNReal.eq_div_iff
      simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
        ENNReal.natCast_ne_top, ENNReal.eq_div_iff]
      rw [mul_comm]
      simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
        ENNReal.natCast_ne_top, ENNReal.div_mul_cancel]
    exact ENat.toENNReal_inj.mp h_rel_dist_eq

/-- Note that this gives the same codeword as `pickClosestCodeword_of_Nonempty_Code`. -/
noncomputable def pickRelClosestCodeword_of_Nonempty_Code
    (C : Set (ι → F)) [Nonempty C] (u : ι → F) : C := by
  have h_exists := exists_closest_codeword_of_Nonempty_Code C u
  let M_val := Classical.choose h_exists
  have h_M_spec := Classical.choose_spec h_exists
  exact ⟨M_val, h_M_spec.1⟩

lemma relDistFromPickRelClosestCodeword_of_Nonempty_Code
    (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    δᵣ(u, C) = δᵣ(u, pickRelClosestCodeword_of_Nonempty_Code C u) := by
  have h_exists := exists_closest_codeword_of_Nonempty_Code C u
  have h_M_spec := Classical.choose_spec h_exists
  let h_absolute_closest := h_M_spec.2.symm
  apply Eq.symm
  let h_pairDist_eq_relDistFromCode_iff :=
    pairDist_eq_distFromCode_iff_eq_relDistFromCode_div (u := u)
    (v := pickRelClosestCodeword_of_Nonempty_Code C u) (C := C)
  rw [←h_pairDist_eq_relDistFromCode_iff]
  exact id (Eq.symm h_absolute_closest)

omit [Nonempty ι] [DecidableEq F] in
/-- Relative distance version of `closeToCode_iff_closeToCodeword_of_minDist`.
    If the distance to a code is at most δ, then there exists a codeword within distance δ.
NOTE: can we make this shorter using `relDistFromCode_eq_distFromCode_div`?
-/
lemma relCloseToCode_iff_relCloseToCodeword_of_minDist [Nonempty ι] [DecidableEq F]
    {C : Set (ι → F)} (u : ι → F) (δ : ℝ≥0) :
    δᵣ(u, C) ≤ δ ↔ ∃ v ∈ C, δᵣ(u, v) ≤ δ := by
  constructor
  · -- Direction 1: (→)
    -- Assume: δᵣ(u, C) ≤ ↑δ
    -- Goal: ∃ v ∈ C, δᵣ(u, v) ≤ δ
    intro h_dist_le_e
    -- We need to handle two cases: the code C being empty or non-empty.
    by_cases hC_empty : C = ∅
    · -- Case 1: C is empty
      -- The goal is `∃ v ∈ ∅, ...`, which is `False`.
      -- We must show the assumption `h_dist_le_e` is also `False`.
      rw [hC_empty] at h_dist_le_e
      rw [relDistFromCode_of_empty] at h_dist_le_e
      -- h_dist_le_e is now `⊤ ≤ ↑e`.
      -- Since `e : ℕ`, `↑e` is finite (i.e., `↑e ≠ ⊤`).
      have h_e_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top (r := δ)
      -- `⊤ ≤ ↑e` is only true if `↑e = ⊤`, so this is a contradiction.
      simp only [top_le_iff, ENNReal.coe_ne_top] at h_dist_le_e
    · -- Case 2: C is non-empty
      have hC_nonempty : Set.Nonempty C := Set.nonempty_iff_ne_empty.mpr hC_empty
      have hC_nonempty_instance : Nonempty C := Set.Nonempty.to_subtype hC_nonempty
      let v := pickRelClosestCodeword_of_Nonempty_Code C u
      use v; constructor
      · simp only [Subtype.coe_prop]
      · rw [relDistFromPickRelClosestCodeword_of_Nonempty_Code] at h_dist_le_e
        simp only at h_dist_le_e
        rw [←ENNReal.coe_le_coe]
        exact h_dist_le_e
  · -- Direction 2: (←)
    -- Assume: `∃ v ∈ C, δᵣ(u, v) ≤ e`
    -- Goal: `δᵣ(u, C) ≤ ↑e`
    intro h_exists
    -- Unpack the assumption
    rcases h_exists with ⟨v, hv_mem, h_dist_le_e⟩
    -- Goal is `sInf {d | ∃ w ∈ C, ↑(δᵣ(u, w)) ≤ d} ≤ ↑e`
    -- We can use the lemma `ENat.sInf_le` (or `sInf_le` for complete linear orders)
    -- which says `sInf S ≤ x` if `x ∈ S`.
    have h_sInf_le: δᵣ(u, C) ≤ δᵣ(u, v) := by
      apply sInf_le
      simp only [Set.mem_setOf_eq]
      use v
    calc δᵣ(u, C) ≤ δᵣ(u, v) := h_sInf_le
    _ ≤ δ := by exact ENNReal.coe_le_coe.mpr h_dist_le_e

/-- Equivalence between relative and natural distance bounds. -/
lemma pairRelDist_le_iff_pairDist_le (δ : NNReal) :
    (δᵣ(u, v) ≤ δ) ↔ (Δ₀(u, v) ≤ Nat.floor (δ * Fintype.card ι)) := by
  -- 1. Get n > 0 from [Nonempty ι]
  have h_n_pos : 0 < Fintype.card ι := Fintype.card_pos
  have h_n_pos_nnreal : 0 < (Fintype.card ι : NNReal) := by exact_mod_cast h_n_pos
  -- 2. Unfold the definition and handle the coercion from ℚ≥0 to NNReal
  unfold relHammingDist
  simp only [NNRat.cast_div, NNRat.cast_natCast]
  conv_lhs => change (Δ₀(u, v) : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ δ
  conv_rhs => change Δ₀(u, v) ≤ Nat.floor ((δ : ℝ) * (Fintype.card ι : ℝ))
  conv_lhs => rw [div_le_iff₀ (by exact_mod_cast h_n_pos)]
  conv_rhs => simp [Nat.le_floor_iff]
  rfl

omit [Nonempty ι] in
/--
A word `u` is close to a code `C` within an absolute error bound `e` if and only if
it is close within the equivalent relative error bound `e / n`.
-/
theorem distFromCode_le_iff_relDistFromCode_le {C : Set (ι → F)} [Nonempty ι] (u : ι → F) (e : ℕ) :
    Δ₀(u, C) ≤ e ↔ δᵣ(u, C) ≤ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  have h_n_pos : 0 < Fintype.card ι := Fintype.card_pos
  have h_n_pos_nnreal : 0 < (Fintype.card ι : ℝ≥0) := by exact_mod_cast h_n_pos
  rw [closeToCode_iff_closeToCodeword_of_minDist]
  conv_rhs => rw [←ENNReal.coe_div (hr := by
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])]
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist (u := u) (C := C)
    (δ := (e : ℝ≥0) / (Fintype.card ι : ℝ≥0))]
  apply exists_congr
  intro v
  simp only [and_congr_right_iff]
  intro hv_mem
  rw [pairRelDist_le_iff_pairDist_le]
  simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel, Nat.floor_natCast]

/--
A word `u` is relatively close to a code `C` within an relative error bound `δ` if and only if
it is relatively close within the equivalent absolute error bound `⌊δ * n⌋`.
-/
theorem relDistFromCode_le_iff_distFromCode_le {C : Set (ι → F)} (u : ι → F) (δ : ℝ≥0) :
    δᵣ(u, C) ≤ δ ↔ Δ₀(u, C) ≤ Nat.floor (δ * Fintype.card ι) := by
  have h_n_pos : 0 < Fintype.card ι := Fintype.card_pos
  have h_n_pos_nnreal : 0 < (Fintype.card ι : ℝ≥0) := by exact_mod_cast h_n_pos
  conv_rhs => rw [closeToCode_iff_closeToCodeword_of_minDist]
  conv_lhs => rw [relCloseToCode_iff_relCloseToCodeword_of_minDist (u := u) (C := C)]
  apply exists_congr
  intro v
  simp only [and_congr_right_iff]
  intro hv_mem
  rw [pairRelDist_le_iff_pairDist_le]

theorem relDistFromCode_le_iff_distFromCode_toENNReal_le {C : Set (ι → F)} (u : ι → F) (δ : ℝ≥0) :
    δᵣ(u, C) ≤ δ ↔ (Δ₀(u, C) : ENNReal) ≤ δ * (Fintype.card ι : ℝ≥0) := by
  rw [relDistFromCode_le_iff_distFromCode_le] 
  constructor <;> intro h 
  · simp_all only [ENNReal.coe_natCast]
    convert ENNReal.ofReal_le_ofReal 
      (Nat.floor_le (show 0 ≤ δ * (Fintype.card ι : ℝ≥0) by positivity)) |> 
        le_trans (ENNReal.ofReal_le_ofReal <| ?_) using 1
    any_goals exact Nat.cast (distFromCode u C |> ENat.toNat)
    · cases h : distFromCode u C <;> aesop
    · simp [ENNReal.ofReal_mul]
    · cases h' : distFromCode u C <;> aesop
  · contrapose! h
    cases h' : distFromCode u C 
    · simp_all only [ENat.coe_lt_top, ENNReal.coe_natCast, ENat.toENNReal_top]
      exact ENNReal.mul_lt_top (ENNReal.coe_lt_top) (ENNReal.natCast_lt_top _)
    · simp_all only [Nat.cast_lt, ENNReal.coe_natCast, ENat.toENNReal_coe]
      exact_mod_cast Nat.lt_of_floor_lt h
        
theorem relCloseToWord_iff_exists_possibleDisagreeCols
    {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [DecidableEq F] (u v : ι → F) (δ : ℝ≥0) :
    δᵣ(u, v) ≤ δ ↔ ∃ (D : Finset ι), D.card ≤ Nat.floor (δ * Fintype.card ι)
                                      ∧ (∀ (colIdx : ι), colIdx ∉ D → u colIdx = v colIdx) := by
  rw [pairRelDist_le_iff_pairDist_le]
  letI : DecidableEq ι := by exact Classical.typeDecidableEq ι
  rw [closeToWord_iff_exists_possibleDisagreeCols]

theorem relCloseToWord_iff_exists_agreementCols
    {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [DecidableEq F] (u v : ι → F) (δ : ℝ≥0) :
    δᵣ(u, v) ≤ δ ↔ ∃ (S : Finset ι),
      Fintype.card ι - Nat.floor (δ * Fintype.card ι) ≤ S.card
      ∧ (∀ (colIdx : ι), ((colIdx ∈ S → u colIdx = v colIdx)
                          ∧ (u colIdx ≠ v colIdx → colIdx ∉ S))) := by
  rw [pairRelDist_le_iff_pairDist_le]
  letI : DecidableEq ι := by exact Classical.typeDecidableEq ι
  rw [closeToWord_iff_exists_agreementCols]

lemma NNReal.floor_ge_Nat_of_gt
    {r : ℝ≥0} {n : ℕ} (h : r > n) :
    Nat.floor r ≥ n := by
  apply (Nat.le_floor_iff (NNReal.coe_nonneg r)).mpr
  apply le_of_lt
  exact_mod_cast h

lemma NNReal.sub_eq_zero_of_le (x y : ℝ≥0) (h : x ≤ y) : x - y = 0 := by
  exact tsub_eq_zero_of_le h

/-- The equivalence between the two lowerbound of `upperBound` in Nat and NNReal context.
In which, `upperBound` is viewed as the size of an **agreement set** `S` (e.g. between two words,
or between a word to a code, ...).
Specifically, `n - ⌊δ * n⌋ ≤ (upperBound : ℕ) ↔ (1 - δ) * n ≤ (upperBound : ℝ≥0)`.
This lemma is useful for jumping back-and-forth between absolute distance and relative distance
realms, especially when we work with an agreement set. For example, it can be used after `simp`ing
with `closeToWord_iff_exists_agreementCols` and `relCloseToWord_iff_exists_agreementCols`.
-/
lemma relDist_floor_bound_iff_complement_bound (n upperBound : ℕ) (δ : ℝ≥0) :
    n - Nat.floor (δ * (n)) ≤ upperBound ↔
    (1 - δ) * (n : ℝ≥0) ≤ (upperBound : ℝ≥0) := by
  let k := upperBound
  set r : ℝ≥0 := δ * n
  set m : ℕ := Nat.floor r
  have h_m_le_r_NNReal : (m : NNReal) ≤ r := Nat.floor_le (a := r) (ha := zero_le r)
  have h_m_le_r_ENNReal : (m : ENNReal) ≤ (r : ENNReal) := by
    change ( (m : NNReal) : ENNReal) ≤ (r : ENNReal)
    rw [ENNReal.coe_le_coe]
    exact h_m_le_r_NNReal
  have hr : ↑m ≤ r := Nat.floor_le (mul_nonneg δ.coe_nonneg n.cast_nonneg)
  have hr' : r < ↑m + 1 := Nat.lt_floor_add_one r
  have h_sub : ↑(n - m) = max (↑n - ↑m) 0 := by
    by_cases h : m ≤ n
    · simp only [zero_le, sup_of_le_left]
    · simp only [zero_le, sup_of_le_left]
  conv_rhs => -- convert rhs to ENNReal
    rw [←ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_sub,
      ENNReal.coe_one, ENNReal.coe_natCast]
    rw [ENNReal.sub_mul (h := fun h1 h2 => by exact ENNReal.natCast_ne_top n)]
    simp only [one_mul, ENNReal.coe_natCast]
  conv_lhs => -- convert lhs to ENNReal
    rw [←Nat.cast_le (α := ENNReal) (m := n - m) (n := k)]
    simp only [ENNReal.natCast_sub]
  by_cases h_r_le_n : r ≤ n
  · have h_m_le_n : m ≤ n := by exact Nat.floor_le_of_le h_r_le_n
    constructor
    · intro hNat_le
      calc
        _ ≤ (n : ENNReal) - (m : ENNReal) := by
          rw [ENNReal.sub_le_sub_iff_left (b := ↑δ * ↑n) (c := (m : ENNReal))
            (h := Nat.cast_le.mpr h_m_le_n) (h' := ENNReal.natCast_ne_top n)]
          exact h_m_le_r_ENNReal
        _ ≤ _ := by exact hNat_le
    · intro hNNReal_le
      -- APPROACH: Exploting the gap between any two consecutive Nat
      let sub_eq := ENNReal.natCast_sub (m := n) (n := m)
      rw [←sub_eq]
      rw [Nat.cast_le]
      rw [←Nat.lt_add_one_iff]
      -- Convert to ℝ
      rw [← Nat.cast_lt (α := ℝ)]
      rw [Nat.cast_sub h_m_le_n, Nat.cast_add, Nat.cast_one]
      -- The goal is now `(n : ℝ) - (m : ℝ) < (k : ℝ) + 1`
      have h_hyp_ℝ : (n : ℝ) - (r : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hNNReal_le
      have h_floor_lt_ℝ : (r : ℝ) < (m : ℝ) + 1 := by
        exact_mod_cast hr'
      -- `linarith` proves `n - m < k + 1` from: `n - r ≤ k` AND `r < m + 1`
      -- by showing `n - m < n - r + 1 ≤ k + 1`
      linarith
  · have h_n_lt_r : n < r := by exact lt_of_not_ge h_r_le_n
    have h_m_ge_n : m ≥ n :=
      NNReal.floor_ge_Nat_of_gt (r := r) (n := n) (h := lt_of_not_ge h_r_le_n)
    have h_n_sub_m_eq_0 : n - m = 0 := Nat.sub_eq_zero_of_le h_m_ge_n
    have h_n_sub_r_eq_0 : (n : ENNReal) - r = 0 := by
      change ((n : NNReal) : ENNReal) - r = 0
      rw [←ENNReal.coe_sub] -- ↑((n : ℝ≥0) - r) = 0
      have h_n_sub_r_eq_0_NNReal : (n : NNReal) - r = 0 := by
        apply NNReal.sub_eq_zero_of_le
        exact le_of_lt h_n_lt_r
      rw [h_n_sub_r_eq_0_NNReal]
      exact rfl
    conv_lhs => -- convert ↑n - ↑m into 0
      rw [←ENNReal.natCast_sub]
      rw [h_n_sub_m_eq_0, Nat.cast_zero]
    conv_rhs => -- convert ↑n - ↑r into 0
      change (n : ENNReal) - r ≤ k
      rw [h_n_sub_r_eq_0]

/-- The relative Hamming distance between two vectors is at most `1`.
-/
@[simp]
lemma relHammingDist_le_one : δᵣ(u, v) ≤ 1 := by
  unfold relHammingDist
  qify
  rw [div_le_iff₀ (by simp)]
  simp [hammingDist_le_card_fintype]

/-- The relative Hamming distance between two vectors is non-negative.
-/
@[simp]
lemma zero_le_relHammingDist : 0 ≤ δᵣ(u, v) := by
  unfold relHammingDist
  qify
  rw [le_div_iff₀ (by simp)]
  simp

end

/-- The range of the relative Hamming distance function.
-/
def relHammingDistRange (ι : Type*) [Fintype ι] : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ d' : ℕ, d' ≤ Fintype.card ι ∧ d = d' / Fintype.card ι}

/-- The range of the relative Hamming distance is well-defined.
-/
@[simp]
lemma relHammingDist_mem_relHammingDistRange [DecidableEq F] : δᵣ(u, v) ∈ relHammingDistRange ι :=
  ⟨hammingDist _ _, Finset.card_filter_le _ _, rfl⟩

/-- The range of the relative Hamming distance function is finite.
-/
@[simp]
lemma finite_relHammingDistRange [Nonempty ι] : (relHammingDistRange ι).Finite := by
  simp only [relHammingDistRange, ← Set.finite_coe_iff, Set.coe_setOf]
  exact
    finite_iff_exists_equiv_fin.2
      ⟨Fintype.card ι + 1,
        ⟨⟨
        fun ⟨s, _⟩ ↦ ⟨(s * Fintype.card ι).num, by aesop (add safe (by omega))⟩,
        fun n ↦ ⟨n / Fintype.card ι, by use n; simp [Nat.le_of_lt_add_one n.2]⟩,
        fun ⟨_, _, _, h₂⟩ ↦ by simp only [h₂]; ring_nf; simp [NNRat.num_natCast]; ring,
        fun _ ↦ by simp
        ⟩⟩
      ⟩

omit [Fintype ι] in
/-- The set of pairs of distinct elements from a finite set is finite.
-/
@[simp]
lemma finite_offDiag [Finite ι] [Finite F] : C.offDiag.Finite := by
  letI := Fintype.ofFinite ι
  exact Set.Finite.offDiag (Set.toFinite C)

section

variable [DecidableEq F]

/-- The set of possible distances between distinct codewords in a code.
-/
def possibleRelHammingDists (C : Set (ι → F)) : Set ℚ≥0 :=
  possibleDists C relHammingDist

/-- The set of possible distances between distinct codewords in a code is a subset of the range of
 the relative Hamming distance function.
-/
@[simp]
lemma possibleRelHammingDists_subset_relHammingDistRange :
    possibleRelHammingDists C ⊆ relHammingDistRange ι := fun _ ↦ by
    aesop (add simp [possibleRelHammingDists, possibleDists])

variable [Nonempty ι]

/-- The set of possible distances between distinct codewords in a code is a finite set.
-/
@[simp]
lemma finite_possibleRelHammingDists : (possibleRelHammingDists C).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleRelHammingDists_subset_relHammingDistRange

open Classical in
/-- The minimum relative Hamming distance of a code.
-/
def minRelHammingDistCode (C : Set (ι → F)) : ℚ≥0 :=
  haveI : Fintype (possibleRelHammingDists C) := @Fintype.ofFinite _ finite_possibleRelHammingDists
  if h : (possibleRelHammingDists C).Nonempty
  then (possibleRelHammingDists C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

end

/-- `δᵣ C` denotes the minimum relative Hamming distance of a code `C`.
-/
notation "δᵣ" C => minRelHammingDistCode C

/-- The range set of possible relative Hamming distances from a vector to a code is a subset
  of the range of the relative Hamming distance function.
-/
@[simp]
lemma possibleRelHammingDistsToC_subset_relHammingDistRange [DecidableEq F] :
    possibleDistsToCode w C relHammingDist ⊆ relHammingDistRange ι := fun _ ↦ by
    aesop (add simp Code.possibleDistsToCode)

/-- The set of possible relative Hamming distances from a vector to a code is a finite set.
-/
@[simp]
lemma finite_possibleRelHammingDistsToCode [Nonempty ι] [DecidableEq F] :
    (possibleDistsToCode w C relHammingDist).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleRelHammingDistsToC_subset_relHammingDistRange

instance [Nonempty ι] [DecidableEq F] :
    Fintype (possibleDistsToCode w C relHammingDist) :=
  @Fintype.ofFinite _ finite_possibleRelHammingDistsToCode

-- NOTE: this does not look clean, also `possibleDistsToCode` has the condition `c ≠ w`
-- which seems not a standard since `w` can be a codeword, so commented out for now
-- open Classical in
-- /-- The relative Hamming distance from a vector to a code.
-- -/
-- def relDistFromCode [Nonempty ι] [DecidableEq F] (w : ι → F) (C : Set (ι → F)) : ℚ≥0 :=
--   if h : (possibleDistsToCode w C relHammingDist).Nonempty
--   then distToCode w C relHammingDist finite_possibleRelHammingDistsToCode |>.get (p h)
--   else 0
--   where p (h : (possibleDistsToCode w C relHammingDist).Nonempty) := by
--           by_contra c
--           simp [distToCode] at c ⊢
--           rw [WithTop.none_eq_top, Finset.min_eq_top, Set.toFinset_eq_empty] at c
--           simp_all

/-- Computable version of the relative Hamming distance from a vector `w` to a finite
non-empty code `C`. This one is intended to mimic the definition of `distFromCode'`.
However, **we don't have `ENNRat (ℚ≥0∞)` (as counterpart of `ENat (ℕ∞)` in `distFromCode'`)**
so we require `[Nonempty C]`.
TODO: define `ENNRat (ℚ≥0∞)` so we can migrate both `relDistFromCode`
  and `relDistFromCode'` to `ℚ≥0∞` -/
def relDistFromCode' {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [DecidableEq F]
    (w : ι → F) (C : Set (ι → F)) [Fintype C] [Nonempty C] : ℚ≥0 :=
  Finset.min'
    (Finset.univ.image (fun (c : C) => relHammingDist w c))
    (Finset.univ_nonempty.image _)

/-- `δᵣ'(w,C)` denotes the relative Hamming distance between a vector `w` and a code `C`.
This is a different statement of the generic definition `δᵣ(w,C)`. -/
notation "δᵣ'(" w ", " C ")" => relDistFromCode' w C

lemma relDistFromCode'_eq_relDistFromCode {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [DecidableEq F]
    (w : ι → F) (C : Set (ι → F)) [Fintype C] [Nonempty C] :
    (δᵣ(w, C)) = δᵣ'(w, C) := by
  classical
  -- 1. Identify the set of distances V
  let V : Finset ℚ≥0 := Finset.univ.image (fun (c : C) => relHammingDist w c)
  conv_rhs => rw [ENNReal.coe_NNRat_coe_NNReal]
  have h_C_ne_empty : C ≠ ∅ := by
    intro h_empty
    let c : C := Classical.choice (inferInstance : Nonempty C)
    simpa [h_empty] using c.property
  have h_dist_w_C_ne_top: Δ₀(w, C) ≠ ⊤ := by
    by_contra dist_w_C_eq_top
    rw [distFromCode_eq_top_iff_empty (n := ι) (u := w) (C := C)] at dist_w_C_eq_top
    exact h_C_ne_empty dist_w_C_eq_top
  apply (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp ?_
  · -- ⊢ δᵣ(w, C) ≠ ⊤
    rw [relDistFromCode_eq_distFromCode_div]
    apply ENNReal.div_ne_top (h1 := by -- ⊢ ↑Δ₀(w, C) ≠ ⊤
      simp only [ne_eq, ENat.toENNReal_eq_top, h_dist_w_C_ne_top, not_false_eq_true]
    ) (h2 := by -- ⊢ ↑(Fintype.card ι) ≠ 0
      simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])
  · -- ⊢ ↑↑δᵣ'(w, C) ≠ ⊤ => trivial because δᵣ'(w, C) is a ℚ≥0
    simp only [ne_eq, ENNReal.coe_ne_top, not_false_eq_true]
  · -- ⊢ δᵣ(w, C).toNNReal = (↑↑δᵣ'(w, C)).toNNReal
    change δᵣ(w, C).toNNReal = (δᵣ'(w, C) : NNReal)
    -- 2. Prove the core equality in ENNReal: δᵣ(w, C) = δᵣ'(w, C)
    have h_eq : δᵣ(w, C) = (δᵣ'(w, C) : ENNReal) := by
      unfold relDistFromCode relDistFromCode'
      apply le_antisymm
      · -- Part A: sInf (LHS) ≤ min' (RHS)
        -- The minimum is achieved by some codeword c, which is in the set defining sInf
        apply sInf_le
        simp only [Set.mem_setOf_eq]
        -- Extract the witness c from the Finset minimum
        let S := Finset.univ.image (fun (c : C) => relHammingDist w c)
        have h_mem := Finset.min'_mem S (Finset.univ_nonempty.image _)
        rcases Finset.mem_image.mp h_mem with ⟨c, _, h_val⟩
        -- Use c as the witness. Note: c is a subtype element, c.prop is c ∈ C
        use c
        constructor
        · exact c.property
        · rw [←h_val]
      · -- Part B: min' (RHS) ≤ sInf (LHS)
        -- The minimum is a lower bound for all distances in the code
        apply le_sInf
        intro d hd
        rcases hd with ⟨v, hv_mem, h_dist_le⟩
        -- Transitivity: min' ≤ dist(w, v) ≤ d
        apply le_trans _ h_dist_le
        -- ⊢ ↑((Finset.image (fun c ↦ δᵣ(w, ↑c)) Finset.univ).min' ⋯) ≤ ↑δᵣ(w, v)
        apply ENNReal.coe_le_coe.mpr
        -- ⊢ ↑((Finset.image (fun c ↦ δᵣ(w, ↑c)) Finset.univ).min' ⋯) ≤ ↑δᵣ(w, v)
        simp only [NNRat.cast_le]
        apply Finset.min'_le
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop]
        -- ⊢ ∃ a ∈ C, δᵣ(w, a) = δᵣ(w, v)
        use v
    rw [h_eq] -- 3. Use the equality to close the goal
    rfl

@[simp]
lemma zero_mem_relHammingDistRange : 0 ∈ relHammingDistRange ι := by use 0; simp

-- /-- The relative Hamming distances between a vector and a codeword is in the
--   range of the relative Hamming distance function.
-- -/
-- @[simp]
-- lemma relHammingDistToCode_mem_relHammingDistRange [Nonempty ι] [DecidableEq F] :
--   δᵣ'(c, C) ∈ relHammingDistRange ι := by
--   unfold relDistFromCode
--   split_ifs with h
--   · exact Set.mem_of_subset_of_mem
--             (s₁ := (possibleDistsToCode c C relHammingDist).toFinset)
--             (by simp)
--             (by simp_rw [distToCode_of_nonempty (h₁ := by simp) (h₂ := h)]
--                 simp [←WithTop.some_eq_coe]
--                 have := Finset.min'_mem
--                           (s := (possibleDistsToCode c C relHammingDist).toFinset)
--                           (H := by simpa)
--                 simpa)
--   · simp
-- end


end

end Code
