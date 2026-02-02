/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.Fin.Basic
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Qify
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.Real.ENatENNReal
import ArkLib.Data.Nat.Bitwise

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some
  target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear
  code to be a linear subspace of `n → R`. We also define the notion of generator matrix and
  (parity) check matrix.

  ## Naming conventions
  1. suffix `'`: **computable/instantiation** of the corresponding
  mathematical generic definitions without such suffix (e.g. `Δ₀'(u, C)` vs `Δ₀(u, C)`,
  `δᵣ'(u, C)` vs `δᵣ(u, C)`, ...)
    - **NOTE**: The generic (non-suffixed) definitions (`Δ₀`, `δᵣ`, ...) are recommended
      to be used in generic security statements, and the suffixed definitions
      (`Δ₀'`, `δᵣ'`, ...) are used for proofs or in statements of lemmas that need
      smaller value range.
    - We usually prove the equality as a bridge from the suffixed definitions into the
      non-suffixed definitions (e.g. `distFromCode'_eq_distFromCode`, ...)

  ## Main Definitions
  1. Distance between two words:
    - `hammingDist u v (Δ₀(u, v))`: The Hamming distance between two words `u` and `v`
    - `relHammingDist u v (δᵣ(u, v))`: The relative Hamming distance between two words `u` and `v`
  2. Distance of code:
    - `dist C (‖"C‖₀)`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the
      Hamming distances between any two distinct elements of `C`. This is noncomputable.
      + `minDist C`: another statement of `dist C` using equality, we have `dist_eq_minDist`
    - `dist' C (‖C‖₀')`: A computable version of `dist C`, assuming `C` is a `Fintype`.
  3. Distance from a word to a code:
    - `distFromCode u C (Δ₀(u, C))`: The hamming distance from a word `u` to a code `C`
      + `distFromCode_of_empty`: `Δ₀(u, ∅) = ⊤`
      + `distFromCode_eq_top_iff_empty`: `Δ₀(u, C) = ⊤ ↔ C = ∅`
    - `distFromCode' u C (Δ₀'(u, C))`: A computable version of `distFromCode u C`,
      assuming `C` is a `Fintype`.
      + `distFromCode'_eq_distFromCode`: `Δ₀'(u, C) = Δ₀(u, C)`
    - `relDistFromCode u C (δᵣ(u, C))`: The relative Hamming distance from a word `u` to a code `C`
      + `relDistFromCode' u C (δᵣ'(u, C))`: A computable version of `relDistFromCode u C`,
      assuming `C` is a `Fintype` and `C` is **non-empty**.
      + `relDistFromCode'_eq_relDistFromCode`: `δᵣ'(u, C) = δᵣ(u, C)`
  4. Switching between different distance realms:
    - `relDistFromCode_eq_distFromCode_div`: `δᵣ(u, C) = Δ₀(u, C) / |ι|`
    - `pairDist_eq_distFromCode_iff_eq_relDistFromCode_div`:
      `Δ₀(u, v) = Δ₀(u, C) ↔ δᵣ(u, v) = δᵣ(u, C)`
    - `relDistFromCode_le_relDist_to_mem`: `δᵣ(u, C) ≤ δᵣ(u, v)`
    - `relCloseToCode_iff_relCloseToCodeword_of_minDist`: `δᵣ(u, C) ≤ δ ↔ ∃ v ∈ C, δᵣ(u, v) ≤ δ`
    - `pairRelDist_le_iff_pairDist_le`:
      `(δᵣ(u, v) ≤ δ) ↔ (Δ₀(u, v) ≤ Nat.floor (δ * Fintype.card ι))`
    - `distFromCode_le_iff_relDistFromCode_le`:
      `Δ₀(u, C) ≤ e ↔ δᵣ(u, C) ≤ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0)`
    - `relDistFromCode_le_iff_distFromCode_le`:
      `δᵣ(u, C) ≤ δ ↔ Δ₀(u, C) ≤ Nat.floor (δ * Fintype.card ι)`
    - `relCloseToWord_iff_exists_possibleDisagreeCols`
    - `relCloseToWord_iff_exists_agreementCols`
    - `relDist_floor_bound_iff_complement_bound`
    - `distFromCode_le_dist_to_mem`: `Δ₀(u, C) ≤ Δ₀(u, v), given v ∈ C`
    - `distFromCode_le_card_index_of_Nonempty`: `Δ₀(u, C) ≤ |ι|, given C is non-empty`
  5. Unique decoding radius:
    - `uniqueDecodingRadius C (UDR(C))`: The unique decoding radius of a code `C`
    - `relativeUniqueDecodingRadius C (relUDR(C))`:
      The relative unique decoding radius of a code `C`
    - `UDR_close_iff_exists_unique_close_codeword`:
      `Δ₀(u, C) ≤ UDR(C) ↔ ∃! v ∈ C, Δ₀(u, v) ≤ UDR(C)`
    - `UDRClose_iff_two_mul_proximity_lt_d_UDR`: `e ≤ UDR(C) ↔ 2 * e < ‖C‖₀`
    - `eq_of_le_uniqueDecodingRadius`
    - `UDR_close_iff_relURD_close`: `Δ₀(u, C) ≤ UDR(C) ↔ δᵣ(u, C) ≤ relUDR(C)`
    - `dist_le_UDR_iff_relDist_le_relUDR`:
      `e ≤ UDR(C) ↔ (e : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ relUDR(C)`

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes
  such as the singleton bound.

## TODOs
- Implement `ENNRat (ℚ≥0∞)`, for usage in `relDistFromCode` and `relDistFromCode'`,
  as counterpart of `ENat (ℕ∞)` in `distFromCode` and `distFromCode'`.
-/

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code
open NNReal

-- Notation for Hamming distance
notation "Δ₀(" u ", " v ")" => hammingDist u v

notation "‖" u "‖₀" => hammingNorm u

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct
  elements of the code.
We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the
code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`.
-/
noncomputable def dist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀( u, v ) ≤ d}

-- TODO: rewrite this file using existing `(e)infsep` definitions

instance : EDist (n → R) where
  edist := fun u v => hammingDist u v

instance : Dist (n → R) where
  dist := fun u v => hammingDist u v

noncomputable def eCodeDistNew (C : Set (n → R)) : ENNReal := C.einfsep

noncomputable def codeDistNew (C : Set (n → R)) : ℝ := C.infsep

notation "‖" C "‖₀" => dist C

/-- The distance from a vector `u` to a code `C` is the minimum Hamming distance between `u`
and any element of `C`. -/
noncomputable def distFromCode (u : n → R) (C : Set (n → R)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, hammingDist u v ≤ d}

notation "Δ₀(" u ", " C ")" => distFromCode u C

/-- The distance to a code is at most the distance to any specific codeword. -/
lemma distFromCode_le_dist_to_mem (u : n → R) {C : Set (n → R)} (v : n → R) (hv : v ∈ C) :
    Δ₀(u, C) ≤ Δ₀(u, v) := by
  apply csInf_le
  · -- Show the set is bounded below
    use 0
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    rcases hd with ⟨w, _, h_dist⟩
    exact bot_le
  · -- Show hammingDist u v is in the set
    simp only [Set.mem_setOf_eq]
    exact ⟨v, hv, le_refl _⟩

/-- If `u` and `v` are distinct members of a code `C`, their distance is at least `‖C‖₀`. -/
lemma pairDist_ge_code_mindist_of_ne {C : Set (n → R)} {u v : n → R}
    (hu : u ∈ C) (hv : v ∈ C) (h_ne : u ≠ v) :
    Δ₀(u, v) ≥ ‖C‖₀:= by
  unfold Code.dist -- We use the property of sInf: if `k` is in the set `S`, then `sInf S ≤ k`.
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq]
  exists u
  constructor
  · exact hu
  · exists v

noncomputable def minDist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}

@[simp]
theorem dist_empty : ‖ (∅ : Set (n → R) ) ‖₀ = 0 := by simp [dist]

@[simp]
theorem dist_subsingleton {C : Set (n → R)} [Subsingleton C] : ‖C‖₀ = 0 := by
  simp only [Code.dist]
  have {d : ℕ} : (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d) = False := by
    have h := @Subsingleton.allEq C _
    simp_all; intro a ha b hb hab
    have hEq : a = b := h a ha b hb
    simp_all
  have : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    simp [this]
  simp [this]

@[simp]
theorem dist_le_card (C : Set (n → R)) : dist C ≤ Fintype.card n := by
  by_cases h : Subsingleton C
  · simp
  · simp at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    refine Nat.sInf_le ?_
    simp
    refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, hammingDist_le_card_fintype⟩⟩⟩

lemma dist_eq_minDist {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] (C : Set (ι → F)) :
    Code.dist C = Code.minDist C := by
  -- 1. Define the sets
  let S_le : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}
  let S_eq : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}
  -- Apply antisymmetry
  apply le_antisymm
  · -- 2. Prove dist C ≤ minDist C (i.e., sInf S_le ≤ sInf S_eq)
    -- This relies on finding an element achieving Nat.sInf S_eq
    by_cases hS_eq_nonempty : S_eq.Nonempty
    · -- Case: S_eq is non-empty
      -- Get the minimum element d_min which exists and equals sInf S_eq
      obtain ⟨d_min, hd_min_in_Seq, hd_min_is_min⟩ := Nat.sInf_mem hS_eq_nonempty
      -- hd_min_is_min : ∃ v ∈ C, d_min ≠ v ∧ Δ₀(d_min, v) = sInf S_eq
      rcases hd_min_is_min with ⟨v, hv, hne, hdist_eq_dmin⟩
      dsimp only [S_eq] at hdist_eq_dmin
      dsimp only [Code.minDist, ne_eq]
      rw [←hdist_eq_dmin] -- Replace sInf S_eq with d_min
      -- Show d_min is in S_le
      have hd_min_in_Sle : Δ₀(d_min, v) ∈ S_le := by
        use d_min, hd_min_in_Seq, v, hv, hne
      -- Since d_min is in S_le, sInf S_le must be less than or equal to it
      apply Nat.sInf_le hd_min_in_Sle
    · -- Case: S_eq is empty
      simp only [Set.not_nonempty_iff_eq_empty, S_eq] at hS_eq_nonempty
      simp only [dist, ne_eq, Code.minDist, hS_eq_nonempty]
      rw [Nat.sInf_empty]
      have hS_le_empty : S_le = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro d hd_in_Sle
        rcases hd_in_Sle with ⟨u, hu, v, hv, hne, hdist_le_d⟩
        -- If such u,v,hne existed, then d' = hammingDist u v would be in S_eq.
        have hd'_in_Seq : hammingDist u v ∈ S_eq := ⟨u, hu, v, hv, hne, rfl⟩
        simp_rw [S_eq, hS_eq_nonempty] at hd'_in_Seq
        exact hd'_in_Seq -- mem ∅
      -- sInf of empty set is 0.
      simp_rw [S_le] at hS_le_empty
      rw [hS_le_empty, Nat.sInf_empty]
  · -- 3. Prove minDist C ≤ dist C (i.e., sInf S_eq ≤ sInf S_le)
    -- Show sInf S_le is a lower bound for S_eq
    by_cases hS_le_nonempty : S_le.Nonempty
    · -- Case: S_le is non-empty
      obtain ⟨d_min, hd_min_in_Seq, hd_min_is_min⟩ := Nat.sInf_mem hS_le_nonempty
      -- hd_min_is_min : ∃ v ∈ C, d_min ≠ v ∧ Δ₀(d_min, v) = sInf S_le
      rcases hd_min_is_min with ⟨v, hv, hne, hdist_le_dmin⟩
      dsimp only [S_le] at hdist_le_dmin
      dsimp only [dist]
      have h :  minDist C ≤ Δ₀(d_min, v) := by
        apply Nat.sInf_le
        use d_min, hd_min_in_Seq, v, hv, hne
      omega
    · -- Case: S_le is empty
      -- If S_le is empty, sInf S_le = 0
      -- ⊢ minDist C ≤ ‖C‖₀
      simp only [Set.nonempty_iff_ne_empty, ne_eq, not_not, S_le] at hS_le_nonempty
      rw [dist, hS_le_nonempty, Nat.sInf_empty]
      -- Goal: ⊢ minDist C ≤ 0
      -- Since minDist C is a Nat, this implies minDist C = 0
      rw [Nat.le_zero]
      -- Goal: ⊢ minDist C = 0
      rw [minDist]
      -- Goal: ⊢ sInf S_eq = 0
      have hS_eq_empty : S_eq = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr -- Prove by showing no element d is in S_eq
        intro d hd_in_Seq -- Assume d ∈ S_eq
        -- Unpack the definition of S_eq
        rcases hd_in_Seq with ⟨u, hu, v, hv, hne, hdist_eq_d⟩
        -- If such u, v, hne exist, then d = Δ₀(u, v) must be in S_le
        -- because Δ₀(u, v) ≤ d (as they are equal)
        have hd_in_Sle : d ∈ S_le := by
          use u, hu, v, hv, hne
          exact le_of_eq hdist_eq_d -- Use d' ≤ d where d' = Δ₀(u, v) = d
        -- But we know S_le is empty, so d cannot be in S_le
        simp_rw [S_le, hS_le_nonempty] at hd_in_Sle -- Rewrites the goal to `d ∈ ∅`
        exact hd_in_Sle -- This provides the contradiction (proof of False)
      simp_rw [S_eq] at hS_eq_empty
      rw [hS_eq_empty, Nat.sInf_empty]

/-- A non-trivial code (a code with at least two distinct codewords)
must have a minimum distance greater than 0.
-/
lemma dist_pos_of_Nontrivial {ι : Type*} [Fintype ι] {F : Type*} (C : Set (ι → F))
    [DecidableEq F] (hC : Set.Nontrivial C) : Code.dist C > 0 := by
  rw [Code.dist_eq_minDist]
  unfold Code.minDist
  let S_eq : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}
  -- 2. `hC : Set.Nontrivial C` means `∃ u ∈ C, ∃ v ∈ C, u ≠ v`
  rcases hC with ⟨u, hu, v, hv, hne⟩
  -- 3. This implies S_eq is non-empty, because the distance d' = Δ₀(u, v) is in it
  let d' := hammingDist u v
  have hd'_in_Seq : d' ∈ S_eq := ⟨u, hu, v, hv, hne, rfl⟩
  have hS_eq_nonempty : S_eq.Nonempty := ⟨d', hd'_in_Seq⟩
  -- 4. Get the minimum element d_min = sInf S_eq
  let d_min := sInf S_eq
  -- 5. By `Nat.sInf_mem_of_nonempty`, this minimum d_min is itself an element of S_eq
  have h_d_min_in_Seq : d_min ∈ S_eq := by
    exact Nat.sInf_mem hS_eq_nonempty
  -- 6. Unpack the proof that d_min ∈ S_eq
  --    This gives us a pair (u', v') that *achieves* this minimum distance
  rcases h_d_min_in_Seq with ⟨u', hu', v', hv', hne', hdist_eq_dmin⟩
  -- 7. The goal is to show d_min > 0.
  -- We know d_min = hammingDist u' v' from hdist_eq_dmin
  dsimp only [d_min, S_eq] at hdist_eq_dmin
  rw [←hdist_eq_dmin]
  exact hammingDist_pos.mpr hne'

lemma exists_closest_codeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) [Nonempty C] (u : ι → F) : ∃ M ∈ C, Δ₀(u, M) = Δ₀(u, C) := by
  set S := (fun (x : C) => Δ₀(u, x)) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  -- Use the fact that we can find a minimum element in S
  let SENat := (fun (g : C) => (Δ₀(u, g) : ENat)) '' Set.univ
    -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
    rw [ENat.coe_sInf (hs := hS_nonempty)]
    simp only [SENat, Set.image_univ, sInf_range]
    simp only [S, Set.image_univ, iInf_range]
  rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
  rcases g_subtype with ⟨M_closest, hg_mem⟩
  -- The distance `d` is exactly the Hamming distance of `U` to `M_closest` (lifted to `ℕ∞`).
  have h_dist_eq_hamming : Δ₀(u, C) = (hammingDist u M_closest) := by
    -- We found `M_closest` by taking the `sInf` of all distances, and `hg_min`
    -- shows that the distance to `M_closest` achieves this `sInf`.
    have h_distFromCode_eq_sInf : Δ₀(u, C) = sInf SENat := by
      apply le_antisymm
      · -- Part 1 : `d ≤ sInf ...`
        simp only [distFromCode]
        apply sInf_le_sInf
        intro a ha
        -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
        rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
        -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
        -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
        use g; simp only [Subtype.coe_prop, le_refl, and_self]
      · -- Part 2 : `sInf ... ≤ d`
        simp only [distFromCode]
        apply le_sInf
        -- Let `d'` be any element in the set that `d` is the infimum of.
        intro d' h_d'
        -- Unpack `h_d'` : there exists some `v` in the code such that
        -- `↑(hammingDist f v) ≤ d'`.
        rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
        -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
        -- The element `↑(hammingDist f v)` is in `SENat`.
        have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist u v) := by
          apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
          rw [Set.mem_image]
          -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
          simp only [Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
          -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
          use v -- exact And.symm ⟨rfl, hv_mem⟩
        -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
        exact h_sInf_le_dist_v.trans h_dist_v_le_d'
    rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
  use M_closest, hg_mem, h_dist_eq_hamming.symm

noncomputable def pickClosestCodeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) : C := by
  have h_exists := exists_closest_codeword_of_Nonempty_Code C u
  let M_val := Classical.choose h_exists
  have h_M_spec := Classical.choose_spec h_exists
  exact ⟨M_val, h_M_spec.1⟩

lemma distFromPickClosestCodeword_of_Nonempty_Code {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    Δ₀(u, C) = Δ₀(u, pickClosestCodeword_of_Nonempty_Code C u) := by
  have h_exists := exists_closest_codeword_of_Nonempty_Code C u
  have h_M_spec := Classical.choose_spec h_exists
  -- reapply the choose spec for definitional equality
  exact h_M_spec.2.symm

theorem closeToWord_iff_exists_possibleDisagreeCols
    {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] (u v : ι → F) (e : ℕ) :
    Δ₀(u, v) ≤ e ↔ ∃ (D : Finset ι),
      D.card ≤ e ∧ (∀ (colIdx : ι), colIdx ∉ D → u colIdx = v colIdx) := by
  constructor
  · -- Direction 1: Δ₀(u, v) ≤ e → ∃ D, ...
    intro h_dist_le_e
    -- Define D as the set of disagreeing columns
    let D : Finset ι := Finset.filter (fun colIdx => u colIdx ≠ v colIdx) Finset.univ
    use D
    constructor
    · -- Prove D.card ≤ e
      have hD_card_eq_dist : D.card = hammingDist u v := by
        simp only [hammingDist, ne_eq, D]
      rw [hD_card_eq_dist]
      -- Assume Δ₀(word, codeword) = hammingDist word codeword (perhaps needs coercion)
      -- Let's assume Δ₀ returns ℕ∞ and hammingDist returns ℕ for now
      apply ENat.coe_le_coe.mp -- Convert goal to ℕ ≤ ℕ
      -- Goal: ↑(hammingDist u ↑v) ≤ ↑e
      rw [Nat.cast_le (α := ENat)]
      exact h_dist_le_e
    · -- Prove agreement outside D
      intro colIdx h_colIdx_notin_D
      -- h_colIdx_notin_D means colIdx is not in the filter
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        ne_eq, not_not, D] at h_colIdx_notin_D
      -- Therefore, u colIdx = v.val colIdx
      exact h_colIdx_notin_D
  · -- Direction 2: (∃ D, ...) → Δ₀(u, v) ≤ e
    intro h_exists_D
    rcases h_exists_D with ⟨D, hD_card_le_e, h_agree_outside_D⟩
    -- Goal: Δ₀(u, v) ≤ e

    -- Consider the set where u and v differ
    let Diff_set := Finset.filter (fun colIdx => u colIdx ≠ v colIdx) Finset.univ
    -- Show that Diff_set is a subset of D
    have h_subset : Diff_set ⊆ D := by
      intro colIdx h_diff -- Assume colIdx is in Diff_set, i.e., u colIdx ≠ v.val colIdx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Diff_set] at h_diff
      -- We need to show colIdx ∈ D
      -- Suppose colIdx ∉ D for contradiction
      by_contra h_notin_D
      -- Then by h_agree_outside_D, u colIdx = v.val colIdx
      have h_eq := h_agree_outside_D colIdx h_notin_D
      -- This contradicts h_diff
      exact h_diff h_eq

    -- Use card_le_card and the properties
    have h_card_diff_le_card_D : Diff_set.card ≤ D.card := Finset.card_le_card h_subset
    have h_dist_eq_card_diff : hammingDist u v = Diff_set.card := by
      simp only [hammingDist, ne_eq, Diff_set]

    -- Combine the inequalities
    -- Assuming Δ₀(w, c) = ↑(hammingDist w c)
    rw [← ENat.coe_le_coe] -- Convert goal to ℕ∞ ≤ ℕ∞
    -- Goal: ↑(hammingDist u ↑v) ≤ ↑e
    apply le_trans (ENat.coe_le_coe.mpr (by rw [h_dist_eq_card_diff]))
    apply ENat.coe_le_coe.mpr
    exact Nat.le_trans h_card_diff_le_card_D hD_card_le_e

theorem closeToWord_iff_exists_agreementCols
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [DecidableEq F] (u v : ι → F) (e : ℕ) :
    Δ₀(u, v) ≤ e ↔ ∃ (S : Finset ι),
      Fintype.card ι - e ≤ S.card ∧ (∀ (colIdx : ι), (colIdx ∈ S → u colIdx = v colIdx)
        ∧ (u colIdx ≠ v colIdx → colIdx ∉ S)) := by
  rw [closeToWord_iff_exists_possibleDisagreeCols]
  constructor
  · -- Direction 1: (∃ D, D.card ≤ e ∧ ∀ colIdx ∉ D, u colIdx = v colIdx) → ∃ S, ...
    intro h_exists_D
    rcases h_exists_D with ⟨D, hD_card_le_e, h_agree_outside_D⟩
    -- Define S as the complement of D (the agreeing columns)
    let S : Finset ι := Finset.filter (fun colIdx => colIdx ∉ D) Finset.univ
    use S
    constructor
    · -- Prove Fintype.card ι - e ≤ S.card
      -- S is the complement of D, so S.card = Fintype.card ι - D.card
      have hS_card_eq : S.card = Fintype.card ι - D.card := by
        -- S is the complement of D in univ
        -- Use the fact that S = univ.filter (· ∉ D) and card of complement
        have h_compl : S = Finset.univ \ D := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          constructor
          · intro hx_S
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hx_S
            exact hx_S
          · intro hx_sdiff
            exact (Finset.mem_filter_univ x).mpr hx_sdiff
        rw [h_compl, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
      rw [hS_card_eq]
      omega
    · -- Prove agreement inside S
      intro colIdx
      constructor
      · intro h_colIdx_in_S
        have h_colIdx_notin_D : colIdx ∉ D := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at h_colIdx_in_S
          exact h_colIdx_in_S
        exact h_agree_outside_D colIdx h_colIdx_notin_D
      · intro h_colIdx_neq_v_colIdx
        by_contra h_colIdx_in_S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at h_colIdx_in_S
        have h_eq := h_agree_outside_D colIdx h_colIdx_in_S
        exact h_colIdx_neq_v_colIdx (h_agree_outside_D colIdx h_colIdx_in_S)
  · -- Direction 2: (∃ S, ...) → (∃ D, D.card ≤ e ∧ ∀ colIdx ∉ D, u colIdx = v colIdx)
    intro h_exists_S
    rcases h_exists_S with ⟨S, hS_card_ge, h_agree_inside_S⟩
    -- Define D as the complement of S (the disagreeing columns)
    let D : Finset ι := Finset.filter (fun colIdx => colIdx ∉ S) Finset.univ
    use D
    constructor
    · -- Prove D.card ≤ e
      -- D is the complement of S, so D.card = Fintype.card ι - S.card
      have hD_card_eq : D.card = Fintype.card ι - S.card := by
        -- D is the complement of S in univ
        have h_compl : D = Finset.univ \ S := by
          ext x
          simp only [Finset.mem_univ, true_and, Finset.mem_sdiff]
          constructor
          · intro hx_D
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, D] at hx_D
            exact hx_D
          · intro hx_sdiff
            exact (Finset.mem_filter_univ x).mpr hx_sdiff
        rw [h_compl, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
      rw [hD_card_eq]
      -- We are given: Fintype.card ι - e ≤ S.card
      -- This is equivalent to: Fintype.card ι - S.card ≤ e
      omega
    · -- Prove agreement outside D
      intro colIdx h_colIdx_notin_D
      -- colIdx ∉ D means colIdx is not in filter (fun colIdx => colIdx ∉ S) univ
      -- This means either colIdx ∉ univ (impossible) or colIdx ∈ S
      -- So colIdx ∈ S
      have h_colIdx_in_S : colIdx ∈ S := by
        by_contra h_notin_S
        have h_in_D : colIdx ∈ D := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not,
            D] at h_colIdx_notin_D
          exact False.elim (h_notin_S h_colIdx_notin_D)
        exact h_colIdx_notin_D h_in_D
      -- By h_agree_inside_S, if colIdx ∈ S, then u colIdx = v colIdx
      exact (h_agree_inside_S colIdx).1 h_colIdx_in_S

/-- If `u` and `v` are two codewords of `C` with distance less than `dist C`,
then they are the same. -/
theorem eq_of_lt_dist {C : Set (n → R)} {u v : n → R} (hu : u ∈ C) (hv : v ∈ C)
    (huv : Δ₀(u, v) < ‖C‖₀) : u = v := by
  simp only [dist] at huv
  by_contra hNe
  push_neg at hNe
  revert huv
  simp
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨hNe, le_rfl⟩⟩⟩

@[simp]
theorem distFromCode_of_empty (u : n → R) : Δ₀(u, (∅ : Set (n → R))) = ⊤ := by
  simp [distFromCode]

theorem distFromCode_eq_top_iff_empty (u : n → R) (C : Set (n → R)) : Δ₀(u, C) = ⊤ ↔ C = ∅ := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    apply sInf_eq_top.mp at h
    revert h
    simp
    refine ⟨Fintype.card n, v, And.intro hv ⟨?_, ?_⟩⟩
    · norm_num; exact hammingDist_le_card_fintype
    · norm_num
  · intro h; subst h; simp

lemma distFromCode_le_card_index_of_Nonempty (u : n → R) {C : Set (n → R)} [Nonempty C] :
    Δ₀(u, C) ≤ Fintype.card n := by
  -- exact an element from C since C is nonempty
  letI h_nonempty : Set.Nonempty C := by (expose_names; exact Set.nonempty_coe_sort.mp inst_2)
  let v : n → R := Classical.choose h_nonempty
  have hv : v ∈ C := Classical.choose_spec h_nonempty
  have h_dist_u_C_le_dist_u_v : Δ₀(u, C) ≤ Δ₀(u, v) := by
    apply distFromCode_le_dist_to_mem u v hv
  have h_dist_u_v_le_card_index : Δ₀(u, v) ≤ Fintype.card n := by
    exact hammingDist_le_card_fintype
  have h_dist_u_C_ne_top : Δ₀(u, C) ≠ ⊤ := by
    by_contra h_dist_u_C_eq_top
    rw [distFromCode_eq_top_iff_empty (n := n) (u := u) (C := C)] at h_dist_u_C_eq_top
    have h_C_ne_empty: C ≠ ∅ := by (expose_names; exact Set.nonempty_iff_ne_empty'.mp inst_2)
    exact h_C_ne_empty h_dist_u_C_eq_top
  lift Δ₀(u, C) to ℕ using h_dist_u_C_ne_top with d
  norm_cast at ⊢ h_dist_u_C_le_dist_u_v
  exact Nat.le_trans h_dist_u_C_le_dist_u_v h_dist_u_v_le_card_index

@[simp]
theorem distFromCode_of_mem (C : Set (n → R)) {u : n → R} (h : u ∈ C) : Δ₀(u, C) = 0 := by
  simp only [distFromCode]
  apply ENat.sInf_eq_zero.mpr
  simp [h]

theorem distFromCode_eq_zero_iff_mem (C : Set (n → R)) (u : n → R) : Δ₀(u, C) = 0 ↔ u ∈ C := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply ENat.sInf_eq_zero.mp at h
    revert h
    simp
  · intro h; exact distFromCode_of_mem C h

theorem distFromCode_eq_of_lt_half_dist (C : Set (n → R)) (u : n → R) {v w : n → R}
    (hv : v ∈ C) (hw : w ∈ C) (huv : Δ₀(u, v) < ‖C‖₀ / 2) (hvw : Δ₀(u, w) < ‖C‖₀ / 2) : v = w := by
  apply eq_of_lt_dist hv hw
  calc
    Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
    _ = Δ₀(u, v) + Δ₀(u, w) := by simp only [hammingDist_comm]
    _ < ‖C‖₀ / 2 + ‖C‖₀ / 2 := by omega
    _ ≤ ‖C‖₀ := by omega

lemma closeToCode_iff_closeToCodeword_of_minDist {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    {C : Set (ι → F)} (u : ι → F) (e : ℕ) : Δ₀(u, C) ≤ e ↔ ∃ v ∈ C, Δ₀(u, v) ≤ e := by
  constructor
  · -- Direction 1: (→)
    -- Assume: Δ₀(u, C) ≤ ↑e
    -- Goal: ∃ v ∈ C, Δ₀(u, v) ≤ e
    intro h_dist_le_e
    -- We need to handle two cases: the code C being empty or non-empty.
    by_cases hC_empty : C = ∅
    · -- Case 1: C is empty
      -- The goal is `∃ v ∈ ∅, ...`, which is `False`.
      -- We must show the assumption `h_dist_le_e` is also `False`.
      rw [hC_empty] at h_dist_le_e
      rw [distFromCode_of_empty] at h_dist_le_e
      -- h_dist_le_e is now `⊤ ≤ ↑e`.
      -- Since `e : ℕ`, `↑e` is finite (i.e., `↑e ≠ ⊤`).
      have h_e_ne_top : (e : ℕ∞) ≠ ⊤ := ENat.coe_ne_top e
      -- `⊤ ≤ ↑e` is only true if `↑e = ⊤`, so this is a contradiction.
      simp only [top_le_iff, ENat.coe_ne_top] at h_dist_le_e
    · -- Case 2: C is non-empty
      have hC_nonempty : Set.Nonempty C := Set.nonempty_iff_ne_empty.mpr hC_empty
      have hC_nonempty_instance : Nonempty C := Set.Nonempty.to_subtype hC_nonempty
      let v := pickClosestCodeword_of_Nonempty_Code C u
      use v; constructor
      · simp only [Subtype.coe_prop]
      · rw [distFromPickClosestCodeword_of_Nonempty_Code] at h_dist_le_e
        rw [ENat.coe_le_coe] at h_dist_le_e
        exact h_dist_le_e
  · -- Direction 2: (←)
    -- Assume: `∃ v ∈ C, Δ₀(u, v) ≤ e`
    -- Goal: `Δ₀(u, C) ≤ ↑e`
    intro h_exists
    -- Unpack the assumption
    rcases h_exists with ⟨v, hv_mem, h_dist_le_e⟩
    -- Goal is `sInf {d | ∃ w ∈ C, ↑(Δ₀(u, w)) ≤ d} ≤ ↑e`
    -- We can use the lemma `ENat.sInf_le` (or `sInf_le` for complete linear orders)
    -- which says `sInf S ≤ x` if `x ∈ S`.
    have h_sInf_le: Δ₀(u, C) ≤ Δ₀(u, v) := by
      apply sInf_le
      simp only [Set.mem_setOf_eq, Nat.cast_le]
      use v
    calc Δ₀(u, C) ≤ Δ₀(u, v) := h_sInf_le
    _ ≤ e := by exact ENat.coe_le_coe.mpr h_dist_le_e

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def dist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

notation "‖" C "‖₀'" => dist' C

variable {C : Set (n → R)} [Fintype C]

@[simp]
theorem dist'_empty : ‖(∅ : Set (n → R))‖₀' = ⊤ := by
  simp [dist']

@[simp]
theorem codeDist'_subsingleton [Subsingleton C] : ‖C‖₀' = ⊤ := by
  simp [dist']
  apply Finset.min_eq_top.mpr
  simp [Finset.filter_eq_empty_iff]
  have h := @Subsingleton.elim C _
  simp_all
  exact h

theorem dist'_eq_dist : ‖C‖₀'.toNat = ‖C‖₀ := by
  by_cases h : Subsingleton C
  · simp
  · -- Extract two distinct codewords u,v ∈ C
    simp at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    -- The filtered pair set is nonempty
    have hPairs_nonempty :
        (((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2))).Nonempty := by
      refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_⟩
      simp [huv]

    set pairs : Finset (C × C) :=
      ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)) with hpairs
    set vals : Finset ℕ :=
      pairs.image (fun ⟨u, v⟩ => hammingDist u.1 v.1) with hvals

    have hVals_nonempty : vals.Nonempty := by
      rcases hPairs_nonempty with ⟨p, hp⟩
      rcases p with ⟨u', v'⟩
      exact ⟨hammingDist u'.1 v'.1, Finset.mem_image.mpr ⟨(u', v'), hp, rfl⟩⟩

    -- Let d* be the minimum realized distance among distinct pairs
    set dStar : ℕ := vals.min' (by simpa [hvals] using hVals_nonempty) with hdstar

    -- Show the computable distance's toNat equals this minimum
    have h_toNat_eq_min' : ‖C‖₀'.toNat = dStar := by
      -- First, rewrite ‖C‖₀' as the minimum of `vals` in `ℕ∞`.
      have hmin_coe : ‖C‖₀' = (vals.min : ℕ∞) := by
        simp only [dist', hvals, hpairs]
      -- Next, show `(vals.min : ℕ∞) = dStar` by sandwiching with ≤.
      have hmem_min' : dStar ∈ vals := by
        simpa [hdstar] using
          (Finset.min'_mem (s := vals)
            (by simpa [hvals] using hVals_nonempty))
      -- `vals.min ≤ dStar` since `dStar ∈ vals`.
      have h_le : vals.min ≤ (dStar : ℕ∞) := by
        simpa using (Finset.min_le hmem_min')
      -- `dStar ≤ a` for all `a ∈ vals`, hence `dStar ≤ vals.min`.
      have h_ge : (dStar : ℕ∞) ≤ vals.min := by
        -- Use the universal lower-bound property of `min'`.
        refine Finset.le_min (s := vals) (m := (dStar : ℕ∞)) ?_;
        intro a ha; exact
          (show (dStar : ℕ∞) ≤ (a : ℕ∞) from
            by
              -- `dStar ≤ a` in `ℕ`, then coerce.
              have h' : dStar ≤ a := by
                -- `min' ≤ any element`.
                have hleast := (Finset.isLeast_min' (s := vals)
                                  (H := by simpa [hvals] using hVals_nonempty))
                exact hleast.2 ha
              simpa using h')
      -- Conclude equality in `ℕ∞` and take `toNat`.
      have : (vals.min : ℕ∞) = dStar := le_antisymm h_le h_ge
      simpa only [hmin_coe, this, hdstar]

    -- Now prove that the abstract distance equals the same minimum
    -- Define the set used in sInf
    let S : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}

    -- First inequality: dist C ≤ dStar using a minimizing pair
    have h_le_dStar : dist C ≤ dStar := by
      -- obtain a pair (u,v) attaining the minimum distance dStar
      have hmem_min : dStar ∈ vals := by
        simpa [hdstar] using
          (Finset.min'_mem (s := vals)
            (by simpa [hvals] using hVals_nonempty))
      rcases Finset.mem_image.mp hmem_min with ⟨p, hpairs_mem, hp_eq⟩
      rcases p with ⟨u', v'⟩
      have hneq_sub : u' ≠ v' := (Finset.mem_filter.mp hpairs_mem).2
      -- Lift inequality on subtypes to inequality on values
      have hneq : (↑u' : n → R) ≠ ↑v' := by
        intro h
        apply hneq_sub
        exact Subtype.ext (by simpa using h)
      -- Show dStar ∈ S using the minimizing pair
      have hdist_le_dstar : hammingDist u'.1 v'.1 ≤ dStar := by
        simp only [hp_eq, le_refl]
      have hmemS : dStar ∈ S := by
        change ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ dStar
        exact ⟨u'.1, u'.2, v'.1, v'.2, hneq, hdist_le_dstar⟩
      -- Therefore sInf S ≤ dStar
      have := Nat.sInf_le (s := S) hmemS
      simpa [Code.dist, S] using this

    -- Second inequality: dStar ≤ dist C using lower-bound argument
    have h_dStar_le : dStar ≤ dist C := by
      -- Show dStar is a lower bound of S
      have hLB : ∀ d ∈ S, dStar ≤ d := by
        intro d hd
        rcases hd with ⟨u, hu, v, hv, hne, hle⟩
        -- The realized distance appears in vals, hence ≥ dStar
        have hmem : hammingDist u v ∈ vals := by
          -- show (⟨u,hu⟩,⟨v,hv⟩) ∈ pairs
          have hp : (⟨⟨u, hu⟩, ⟨v, hv⟩⟩ : C × C) ∈ pairs := by
            simp [hpairs, hne]
          -- then its image is in vals
          exact Finset.mem_image.mpr ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, hp, rfl⟩
        -- min' ≤ any member of vals
        have : dStar ≤ hammingDist u v := by
          -- Using the `IsLeast` property of `min'`.
          have hleast := (Finset.isLeast_min' (s := vals)
                            (H := by simpa [hvals] using hVals_nonempty))
          have := hleast.2 hmem
          simpa [hdstar] using this
        exact le_trans this hle
      -- The set S is nonempty since C is non-subsingleton
      have hS_nonempty : S.Nonempty := by
        refine ⟨hammingDist u v, ?_⟩
        exact ⟨u, hu, v, hv, huv, le_rfl⟩
      -- Greatest lower bound property on ℕ
      have := sInf.le_sInf_of_LB (S := S) hS_nonempty hLB
      simpa [Code.dist, S] using this

    -- Assemble inequalities and replace toNat of ‖C‖₀' by dStar
    have : ‖C‖₀ = dStar := le_antisymm h_le_dStar h_dStar_le
    simp [this, h_toNat_eq_min']

section

/-
- TODO: We currently do not use `(E)Dist` as it forces the distance(s) into `ℝ`.
        Instead, we take some explicit notion of distance `δf`.
        Let us give this some thought.
-/

variable {α : Type*}
         {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- The set of possible distances `δf` from a vector `w` to a code `C`.
-/
def possibleDistsToCode (w : ι → F) (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ c ∈ C, c ≠ w ∧ δf w c = d}

lemma possibleDistsToCode_nonempty_iff
    {α : Type*} {F : Type*} {ι : Type*}
    {w : ι → F} {C : Set (ι → F)} {δf : (ι → F) → (ι → F) → α} :
    (possibleDistsToCode w C δf).Nonempty ↔ (C \ {w}).Nonempty := by
  -- 1. Unfold definitions
  unfold possibleDistsToCode
  simp only [Set.nonempty_def, Set.mem_setOf_eq]
  -- Goal: (∃ d, ∃ c ∈ C, c ≠ w ∧ δf w c = d) ↔ (∃ c, c ∈ C \ {w})

  -- 2. Unfold set difference on RHS
  simp only [Set.mem_diff, Set.mem_singleton_iff]
  -- Goal: (∃ d, ∃ c ∈ C, c ≠ w ∧ δf w c = d) ↔ (∃ c, c ∈ C ∧ c ≠ w)

  -- 3. Prove the iff
  constructor
  · -- (→) If a distance `d` exists from a `c ≠ w`, then that `c` exists.
    rintro ⟨d, c, hc_mem, hc_ne, rfl⟩
    use c, hc_mem, hc_ne
  · -- (←) If a `c ≠ w` exists in `C`, then its distance `δf w c` exists.
    rintro ⟨c, hc_mem, hc_ne⟩
    use δf w c, c, hc_mem, hc_ne

/-- The set of possible distances `δf` between distinct codewords in a code `C`.

  - TODO: This allows us to express distance in non-ℝ, which is quite convenient.
          Extending to `(E)Dist` forces this into `ℝ`; give some thought.
-/
def possibleDists (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ p ∈ Set.offDiag C, δf p.1 p.2 = d}

/-- A generalisation of `distFromCode` for an arbitrary distance function `δf`.
-/
noncomputable def distToCode [LinearOrder α] [Zero α]
                             (w : ι → F) (C : Set (ι → F))
                             (δf : (ι → F) → (ι → F) → α)
                             (h : (possibleDistsToCode w C δf).Finite) : WithTop α :=
  haveI := @Fintype.ofFinite _ h
  (possibleDistsToCode w C δf).toFinset.min

end

lemma distToCode_of_nonempty {α : Type*} [LinearOrder α] [Zero α]
                             {ι F : Type*}
                             {w : ι → F} {C : Set (ι → F)}
                             {δf : (ι → F) → (ι → F) → α}
                             (h₁ : (possibleDistsToCode w C δf).Finite)
                             (h₂ : (possibleDistsToCode w C δf).Nonempty) :
  haveI := @Fintype.ofFinite _ h₁
  distToCode w C δf h₁ = .some ((possibleDistsToCode w C δf).toFinset.min' (by simpa)) := by
  simp [distToCode, Finset.min'_eq_inf', Finset.min_eq_inf_withTop]
  rfl

/-- Computable version of the distance from a vector `u` to a finite code `C`. -/
def distFromCode' (C : Set (n → R)) [Fintype C] (u : n → R) : ℕ∞ :=
  Finset.min <| (@Finset.univ C _).image (fun v => hammingDist u v.1)

notation "Δ₀'(" u ", " C ")" => distFromCode' C u

/-- For finite nonempty codes, the computable distance equals the noncomputable distance. -/
lemma distFromCode'_eq_distFromCode (C : Set (n → R)) [Fintype C] (u : n → R) :
    Δ₀'(u, C) = Δ₀(u, C) := by
  by_cases hC_empty: C = ∅
  · subst hC_empty
    simp only [distFromCode', Finset.univ_eq_empty, Finset.image_empty, Finset.min_empty,
      distFromCode, Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false,
      _root_.sInf_empty]
  · have hC_nonempty : Nonempty C := Set.nonempty_iff_ne_empty'.mpr hC_empty
    unfold distFromCode distFromCode'
    -- The minimum equals the infimum for finite sets
    have h_nonempty : (@Finset.univ C _).image (fun v => hammingDist u v.1) |>.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.univ_nonempty
    apply le_antisymm
    · -- Show min ≤ inf
      apply le_csInf
      · -- The inf set is nonempty
        obtain ⟨c, hc⟩ := (inferInstance : Nonempty C)
        use (hammingDist u c : ℕ∞)
        simp only [Set.mem_setOf_eq]
        exact ⟨c, hc, le_refl _⟩
      · -- min is a lower bound
        intro d hd
        simp only [Set.mem_setOf_eq] at hd
        obtain ⟨v, hv, hdist⟩ := hd
        calc Finset.min ((@Finset.univ C _).image (fun v => hammingDist u v.1))
          _ ≤ hammingDist u v := by
            apply Finset.min_le
            apply Finset.mem_image.mpr
            refine ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩
          _ ≤ d := hdist
    · -- Show inf ≤ min
      apply csInf_le
      · -- The set is bounded below
        use 0
        intro d _
        exact bot_le
      · -- min is in the set of upper bounds
        simp only [Set.mem_setOf_eq]
        obtain ⟨min_val, hmin⟩ := Finset.min_of_nonempty h_nonempty
        -- 1. The minimum value must belong to the set
        have h_in_set : min_val ∈ (@Finset.univ C _).image (fun v => hammingDist u v.1) :=
          Finset.mem_of_min hmin
        -- 2. Unwrap the image definition to find the specific codeword `c`
        -- "There exists a c in C such that hammingDist(u, c) = min_val"
        rw [Finset.mem_image] at h_in_set
        obtain ⟨⟨c, hc_mem⟩, -, h_dist_eq⟩ := h_in_set
        -- 3. Provide `c` as the witness for the existential goal
        refine ⟨c, hc_mem, ?_⟩
        -- 4. Prove the inequality: we know `dist(u, c) = min_val`, and `result = min_val`
        rw [h_dist_eq, hmin]
        exact le_refl _

end Computable

noncomputable section

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
    let S_ham_range := (Finset.range (Fintype.card ι + 1)).toSet
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
        fun ⟨_, _, _, h₂⟩ ↦ by field_simp [h₂]; sorry,
        fun _ ↦ by simp
        ⟩⟩
      ⟩

/-- The set of pairs of distinct elements from a finite set is finite.
-/
@[simp]
lemma finite_offDiag [Finite F] : C.offDiag.Finite := Set.Finite.offDiag (Set.toFinite _)

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

instance [Nonempty ι] [DecidableEq F] : Fintype (possibleDistsToCode w C relHammingDist)
  := @Fintype.ofFinite _ finite_possibleRelHammingDistsToCode

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

lemma relDistFromCode'_eq_relDistFromCode {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type*} [DecidableEq F]
    (w : ι → F) (C : Set (ι → F)) [Fintype C] [Nonempty C] :
    (δᵣ(w, C)) = δᵣ'(w, C) := by
  -- 1. Identify the set of distances V
  let V : Finset ℚ≥0 := Finset.univ.image (fun (c : C) => relHammingDist w c)
  conv_rhs => rw [ENNReal.coe_NNRat_coe_NNReal]
  have h_C_ne_empty : C ≠ ∅ := by
    (expose_names; exact Set.nonempty_iff_ne_empty'.mp inst_5)
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

section DecodingRadius

/-- The unique decoding radius: `≤ ⌊(d-1)/2⌋` for any code `C`. -/
noncomputable def uniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) : ℕ := (‖C‖₀ - 1) / 2 -- Nat.division instead of Nat.floor

alias UDR := uniqueDecodingRadius

/-- The relative unique decoding radius, obtained from the absolute radius by normalizing with the
block length. This also works with `≤`. -/
noncomputable def relativeUniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) : ℝ≥0 :=
  (((‖C‖₀ : ℝ≥0) - 1) / 2) / (Fintype.card ι : ℝ≥0)
-- TODO: define `Johnson bound` radius, capacity bounds, etc for generic code `C`

alias relUDR := relativeUniqueDecodingRadius

@[simp]
lemma uniqueDecodingRadius_eq_floor_div_2 {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) :
  Code.uniqueDecodingRadius C = Nat.floor (((‖C‖₀ - 1) : ℝ≥0) / 2) := by
  rw [uniqueDecodingRadius]
  apply Eq.symm
  -- ⊢ ↑((‖C‖₀ - 1) / 2) ≤ (↑‖C‖₀ - 1) / 2 ∧ (↑‖C‖₀ - 1) / 2 < ↑((‖C‖₀ - 1) / 2) + 1
  set d := ‖C‖₀
  -- 4. Set up aliases for the real-valued numbers
  set x_nat : ℝ≥0 := ((d - 1 : ℕ) : ℝ≥0)
  set x_nnreal : ℝ≥0 := (((d : ℝ≥0) - 1) : ℝ≥0)
  -- 5. These two real numbers are actually equal
  have h_eq : x_nat = x_nnreal := by
    -- rw [NNReal.sub_eq_cast_sub, NNReal.coe_nat_cast]
    dsimp only [x_nat, x_nnreal]
    by_cases h_d_ge_1 : d ≥ 1
    · simp only [Nat.cast_tsub, Nat.cast_one]
    · have h_d_eq_0 : d = 0 := by omega
      rw [h_d_eq_0]
      simp only [zero_tsub, CharP.cast_eq_zero]
  rw [←h_eq]; dsimp [x_nat];
  stop
  let res := Nat.floor_div_eq_div  (K := ℝ≥0) (m := (‖C‖₀ - 1)) (n := 2)
  rw [Nat.cast_ofNat] at res
  exact res

/-- Given an error/proximity parameter `e` within the unique decoding radius of a code `C` where
`‖C‖₀ > 0`, this lemma proves the standard bound `2 * e < d`
(i.e. condition of `Code.eq_of_lt_dist`). -/
lemma UDRClose_iff_two_mul_proximity_lt_d_UDR {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) [NeZero (‖C‖₀)]
    {e : ℕ} : e ≤ Code.uniqueDecodingRadius (C := C) ↔ 2 * e < ‖C‖₀ :=
  (Nat.two_mul_lt_iff_le_half_of_sub_one (a := e) (b := ‖C‖₀)
    (h_b_pos := by exact Nat.pos_of_neZero ‖C‖₀)).symm

/-- A stronger version of `distFromCode_eq_of_lt_half_dist`:
If two codewords `v` and `w` are both within the `uniqueDecodingRadius` of
`u` (i.e. `2 * Δ₀(u, v) < ‖C‖₀ and 2 * Δ₀(u, w) < ‖C‖₀`), then they must be equal. -/
theorem eq_of_le_uniqueDecodingRadius {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) (u : ι → F) {v w : ι → F}
    (hv : v ∈ C) (hw : w ∈ C)
    (huv : Δ₀(u, v) ≤ Code.uniqueDecodingRadius C)
    (huw : Δ₀(u, w) ≤ Code.uniqueDecodingRadius C) : v = w := by
  -- Handle the edge case where distance is 0 (trivial code)
  by_cases hd : ‖C‖₀ = 0
  · simp only [uniqueDecodingRadius] at huv huw
    simp only [hd, zero_tsub, Nat.zero_div, nonpos_iff_eq_zero, hammingDist_eq_zero] at huv huw
    rw [←huv, ←huw]
  · -- Main Case: d > 0
    apply eq_of_lt_dist hv hw
    calc
      Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
      _ = Δ₀(u, v) + Δ₀(u, w)        := by simp only [hammingDist_comm]
      _ ≤ Code.uniqueDecodingRadius C + Code.uniqueDecodingRadius C := by gcongr
      _ < ‖C‖₀                          := by
        -- Proof that 2 * ⌊(d-1)/2⌋ < d
        simp only [uniqueDecodingRadius]
        -- 2 * ((d - 1) / 2) ≤ d - 1
        have h_div : 2 * ((‖C‖₀ - 1) / 2) ≤ ‖C‖₀ - 1 := by
          rw [mul_comm]
          apply Nat.div_mul_le_self (m := ‖C‖₀ - 1) (n := 2)
        -- Since d ≠ 0, d - 1 < d
        have h_sub : ‖C‖₀ - 1 < ‖C‖₀ := Nat.pred_lt hd
        omega

/--
A word `u` is within the `uniqueDecodingRadius` of a code `C` if and only if
there exists *exactly one* codeword `v` in `C` that is that close.
-/
theorem UDR_close_iff_exists_unique_close_codeword {ι : Type*} [Fintype ι] {F : Type*}
    [DecidableEq F] (C : Set (ι → F)) [Nonempty C] (u : ι → F) :
    Δ₀(u, C) ≤ Code.uniqueDecodingRadius C ↔ ∃! v ∈ C, Δ₀(u, v) ≤ Code.uniqueDecodingRadius C := by
  -- 1. Define t (radius) and d (distance) for brevity
  set t := Code.uniqueDecodingRadius C
  set d := ‖C‖₀
  constructor
  · -- (→) Direction 1: "Close" implies "Uniquely Close"
    intro h_dist_le_t
    -- 2. First, prove *existence*
    let v := pickClosestCodeword_of_Nonempty_Code (C := C) (u := u)
    have h_close_to_v : Δ₀(u, v) ≤ t := by
      rw [distFromPickClosestCodeword_of_Nonempty_Code (C := C) (u := u)] at h_dist_le_t
      simp only [Nat.cast_le] at h_dist_le_t
      exact h_dist_le_t
    have h_exists : ∃ v, v ∈ C ∧ Δ₀(u, v) ≤ t := by
      use v
      simp only [Subtype.coe_prop, true_and]
      exact h_close_to_v
    -- 3. Second, prove *uniqueness*
    have h_uniq : ∀ (v₁ : ι → F) (v₂ : ι → F),
      v₁ ∈ C → v₂ ∈ C → Δ₀(u, v₁) ≤ t → Δ₀(u, v₂) ≤ t → v₁ = v₂ := by
      intro v₁ v₂ hv₁_mem hv₂_mem h_dist_v₁ h_dist_v₂
      -- We will use the triangle inequality to bound the distance between v₁ and v₂
      have h_dist_v1_v2 : Δ₀(v₁, v₂) ≤ Δ₀(v₁, u) + Δ₀(u, v₂) := by
        exact hammingDist_triangle v₁ u v₂
      -- The distance is symmetric
      rw [hammingDist_comm v₁ u] at h_dist_v1_v2
      -- Substitute the known bounds `≤ t`
      have h_le_2t : Δ₀(v₁, v₂) ≤ t + t :=
        h_dist_v1_v2.trans (Nat.add_le_add h_dist_v₁ h_dist_v₂)
      rw [←Nat.two_mul] at h_le_2t
      -- 4. Now, we show that `2 * t < d`
      -- We handle the main case (d ≥ 2) and the trivial case (d < 2) separately
      by_cases h_d_ge_2 : d ≥ 2
      · -- Case 1: d ≥ 2 (the standard case)
        -- We have t = ⌊(d-1)/2⌋. We know 2 * ⌊(d-1)/2⌋ ≤ d-1
        have h_2t_le_d_minus_1 : 2 * t ≤ d - 1 := by
          dsimp only [d, t, uniqueDecodingRadius]
          rw [mul_comm]
          exact Nat.div_mul_le_self (‖C‖₀ - 1) 2
        -- Since d ≥ 2, we know d-1 < d
        have h_d_minus_1_lt_d : d - 1 < d := by
          apply Nat.sub_lt_of_pos_le
          · linarith -- d > 0
          · linarith -- 1 > 0
        -- Chain the inequalities: Δ₀(v₁, v₂) ≤ 2*t ≤ d-1 < d
        have h_dist_lt_d : Δ₀(v₁, v₂) < d := by omega
        -- By `eq_of_lt_dist`, if two codewords have a distance less than
        -- the minimum distance of the code, they must be equal.
        exact eq_of_lt_dist hv₁_mem hv₂_mem h_dist_lt_d
      · -- Case 2: d < 2 (i.e., d = 0 or d = 1)
        -- This means the code is trivial or has min distance 1
        have h_d_le_1 : d ≤ 1 := by omega
        -- If d ≤ 1, then t = ⌊(1-1)/2⌋ = 0 or ⌊(0-1)/2⌋ = 0
        have h_t_eq_0 : t = 0 := by
          dsimp only [t, d, uniqueDecodingRadius]
          apply Nat.le_zero.mp
          omega
        -- Our assumption `Δ₀(u, v₁) ≤ t` becomes `Δ₀(u, v₁) ≤ 0`
        rw [h_t_eq_0] at h_dist_v₁ h_dist_v₂
        rw [Nat.le_zero] at h_dist_v₁ h_dist_v₂
        -- If the distance is 0, the words are equal
        have h_u_eq_v1 : u = v₁ := by rw [←hammingDist_eq_zero]; exact h_dist_v₁
        have h_u_eq_v2 : u = v₂ := by rw [←hammingDist_eq_zero]; exact h_dist_v₂
        -- By transitivity, v₁ = u = v₂, so v₁ = v₂
        rw [←h_u_eq_v1, h_u_eq_v2]
    -- 5. Combine existence and uniqueness
    -- apply ExistsUnique.intro h_exists
    refine existsUnique_of_exists_of_unique h_exists ?_
    intro v₁ v₂ ⟨hv₁_mem, h_dist_v₁⟩ ⟨hv₂_mem, h_dist_v₂⟩
    exact h_uniq v₁ v₂ hv₁_mem hv₂_mem h_dist_v₁ h_dist_v₂
  · -- (←) Direction 2: "Uniquely Close" implies "Close"
    intro h_exists_unique
    rcases h_exists_unique with ⟨v, hv_mem, h_dist_le⟩
    rw [closeToCode_iff_closeToCodeword_of_minDist]
    use v

/--
A word `u` is close to a code `C` within the absolute unique decoding radius
if and only if it is close within the relative unique decoding radius.
-/
theorem UDR_close_iff_relURD_close {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F] [Nonempty ι]
    (C : Set (ι → F)) (u : ι → F) :
    Δ₀(u, C) ≤ uniqueDecodingRadius C ↔ δᵣ(u, C) ≤ relativeUniqueDecodingRadius C := by
  rw [closeToCode_iff_closeToCodeword_of_minDist, relCloseToCode_iff_relCloseToCodeword_of_minDist]
  -- Goal: (∃ v ∈ C, Δ₀(u, v) ≤ t) ↔ (∃ v ∈ C, δᵣ(u, v) ≤ τ)
  apply exists_congr
  intro v
  simp only [and_congr_right_iff]
  intro hv_mem
  -- ⊢ Δ₀(u, v) ≤ t ↔ δᵣ(u, v) ≤ τ
  rw [pairRelDist_le_iff_pairDist_le]
  set n := (Fintype.card ι : ℝ≥0)
  have h_n_pos : 0 < n := by exact NeZero.pos n
  conv_lhs => rw [uniqueDecodingRadius_eq_floor_div_2 (C := C)]
  dsimp only [relativeUniqueDecodingRadius]
  conv_rhs => rw [div_mul_cancel₀ (h := by rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero)]

@[simp]
theorem dist_le_UDR_iff_relDist_le_relUDR {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]
    [Nonempty ι] (C : Set (ι → F)) (e : ℕ) :
    e ≤ uniqueDecodingRadius C ↔
      (e : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤ relativeUniqueDecodingRadius C := by
    rw [uniqueDecodingRadius_eq_floor_div_2]
    unfold relativeUniqueDecodingRadius
    conv_rhs => rw [div_le_iff₀ (b := e) (c := Fintype.card ι)
      (a := ((‖C‖₀ : ℝ≥0) - 1) / 2 / (Fintype.card ι : ℝ≥0))
      (hc := by simp only [Nat.cast_pos, Fintype.zero_lt_card])]
    simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      IsUnit.div_mul_cancel]
    rw [Nat.le_floor_iff (ha := by simp only [zero_le])]

end DecodingRadius
section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]


open Finset

def wt [Zero F]
  (v : ι → F) : ℕ := #{i | v i ≠ 0}

lemma wt_eq_hammingNorm [Zero F] {v : ι → F} :
  wt v = hammingNorm v := rfl

lemma wt_eq_zero_iff [Zero F] {v : ι → F} :
  wt v = 0 ↔ Fintype.card ι = 0 ∨ ∀ i, v i = 0 := by
  by_cases IsEmpty ι <;>
  aesop (add simp [wt, Finset.filter_eq_empty_iff])

end

end
end Code

variable [Finite R]

open Fintype

def projection (S : Finset n) (w : n → R) : S → R :=
  fun i => w i.val

omit [Finite R] in
theorem projection_injective
    (C : Set (n → R))
    (nontriv : ‖C‖₀ ≥ 1)
    (S : Finset n)
    (hS : card S = card n - (‖C‖₀ - 1))
    (u v : n → R)
    (hu : u ∈ C)
    (hv : v ∈ C) : projection S u = projection S v → u = v := by
  intro proj_agree
  by_contra hne

  have hdiff : hammingDist u v ≥ ‖C‖₀ := by
    simp [Code.dist]
    refine Nat.sInf_le ?_
    refine Set.mem_setOf.mpr ?_
    use u
    refine exists_and_left.mp ?_
    use v

  let D := {i : n | u i ≠ v i}

  have hD : card D = hammingDist u v := by
    simp
    exact rfl

  have hagree : ∀ i ∈ S, u i = v i := by
    intros i hi
    let i' : {x // x ∈ S} := ⟨i, hi⟩
    have close: u i' = v i' := by
      apply congr_fun at proj_agree
      apply proj_agree
    exact close

  have hdisjoint : D ∩ S = ∅ := by
    by_contra hinter
    have hinter' : (D ∩ S).Nonempty := by
      exact Set.nonempty_iff_ne_empty.mpr hinter
    apply Set.inter_nonempty.1 at hinter'
    obtain ⟨x, hx_in_D, hx_in_S⟩ := hinter'
    apply hagree at hx_in_S
    contradiction

  let diff : Set n := {i : n | ¬i ∈ S}

  have hsub : D ⊆ diff  := by
    unfold diff
    refine Set.subset_setOf.mpr ?_
    intro x hxd
    solve_by_elim

  have hcard_compl : @card diff (ofFinite diff) = ‖C‖₀ - 1 := by
    unfold diff
    simp at *
    rw[hS]
    have stronger : ‖C‖₀ ≤ card n := by
      apply Code.dist_le_card
    omega

  have hsizes: card D ≤ @card diff (ofFinite diff) := by
    exact @Set.card_le_card _ _ _ _ (ofFinite diff) hsub

  rw[hcard_compl, hD] at hsizes
  omega

/-- **Singleton bound** for arbitrary codes -/
theorem singleton_bound (C : Set (n → R)) :
    (ofFinite C).card ≤ (ofFinite R).card ^ (card n - (‖C‖₀ - 1)) := by

  by_cases non_triv : ‖C‖₀ ≥ 1
  · -- there exists some projection S of the desired size
    have ax_proj: ∃ (S : Finset n), card S = card n - (‖C‖₀ - 1) := by
      let instexists := Finset.le_card_iff_exists_subset_card
         (α := n)
         (s := @Fintype.elems n _)
         (n := card n - (‖C‖₀ - 1))
      have some: card n - (‖C‖₀ - 1) ≤ card n := by
        omega
      obtain ⟨t, ht⟩ := instexists.1 some
      exists t
      simp
      exact And.right ht
    obtain ⟨S, hS⟩ := ax_proj

    -- project C by only looking at indices in S
    let Cproj := Set.image (projection S) C

    -- The size of C is upper bounded by the size of its projection,
    -- because the projection is injective
    have C_le_Cproj: @card C (ofFinite C) ≤ @card Cproj (ofFinite Cproj) := by
      apply @Fintype.card_le_of_injective C Cproj
        (ofFinite C)
        (ofFinite Cproj)
        (Set.imageFactorization (projection S) C)
      refine Set.imageFactorization_injective_iff.mpr ?_
      intro u hu v hv heq

      apply projection_injective (nontriv := non_triv) (S := S) (u := u) (v := v) <;>
        assumption

    -- The size of Cproj itself is sufficiently bounded by its type
    have Cproj_le_type_card :
    @card Cproj (ofFinite Cproj) ≤ @card R (ofFinite R) ^ (card n - (‖C‖₀ - 1)) := by
      let card_fun := @card_fun S R (Classical.typeDecidableEq S) _ (ofFinite R)
      rw[hS] at card_fun
      rw[← card_fun]

      let huniv := @set_fintype_card_le_univ (S → R) ?_ Cproj (ofFinite Cproj)
      exact huniv

    apply le_trans (b := @card Cproj (ofFinite Cproj)) <;>
      assumption
  · simp at non_triv
    rw[non_triv]
    simp only [zero_tsub, tsub_zero]

    let card_fun := @card_fun n R (Classical.typeDecidableEq n) _ (ofFinite R)
    rw[← card_fun]

    let huniv := @set_fintype_card_le_univ (n → R) ?_ C (ofFinite C)
    exact huniv

/-- A `ModuleCode ι F A` is an `F`-linear code of length indexed by `ι` over the alphabet `A`,
defined as an `F`-submodule of `ι → A`. -/
@[simp]
abbrev ModuleCode.{u, v, w} (ι : Type u) (F : Type v) [Semiring F] -- ModuleCode ι F A
    (A : Type w) [AddCommMonoid A] [Module F A] : Type (max u w) := Submodule F (ι → A)

abbrev LinearCode.{u, v} (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] : Type (max u v) :=
  Submodule F (ι → F)

lemma LinearCode_is_ModuleCode.{u, v} {ι : Type u} [Fintype ι] {F : Type v} [Semiring F]
    : LinearCode ι F = ModuleCode ι F F := by rfl

-- TODO: MDS code

namespace LinearCode

section

variable {F : Type*} {A : Type*} [AddCommMonoid A]
         {ι : Type*} [Fintype ι]
         {κ : Type*} [Fintype κ]


/-- Module code defined by left multiplication by its generator matrix.
  For a matrix G : Matrix κ ι F (over field F) and module A over F, this generates
  the F-submodule of (ι → A) spanned by the rows of G acting on (κ → A).
  The matrix acts on vectors v : κ → A by: (G • v)(i) = ∑ k, G k i • v k
  where G k i : F is the scalar and v k : A is the module element.
-/
noncomputable def fromRowGenMat [Semiring F] (G : Matrix κ ι F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/-- Linear code defined by right multiplication by a generator matrix.
-/
noncomputable def fromColGenMat [CommRing F] (G : Matrix ι κ F) : LinearCode ι F :=
  LinearMap.range G.mulVecLin

/-- Define a linear code from its (parity) check matrix -/
noncomputable def byCheckMatrix [CommRing F] (H : Matrix ι κ F) : LinearCode κ F :=
  LinearMap.ker H.mulVecLin

/-- The Hamming distance of a linear code can also be defined as the minimum Hamming norm of a
  non-zero vector in the code -/
noncomputable def disFromHammingNorm [Semiring F] [DecidableEq F] (LC : LinearCode ι F) : ℕ :=
  sInf {d | ∃ u ∈ LC, u ≠ 0 ∧ hammingNorm u ≤ d}

theorem dist_eq_dist_from_HammingNorm [CommRing F] [DecidableEq F] (LC : LinearCode ι F) :
    Code.dist LC.carrier = disFromHammingNorm LC := by
  simp only [Code.dist, Submodule.carrier_eq_coe, SetLike.mem_coe, ne_eq, disFromHammingNorm]
  congr; funext d
  apply propext
  constructor
  · intro h
    rcases h with ⟨u, hu, v, hv, huv, hle⟩
    -- Consider the difference w = u - v ∈ LC, w ≠ 0, and ‖w‖₀ = Δ₀(u,v)
    refine ⟨u - v, ?_, ?_, ?_⟩
    · -- membership
      have : (u - v) ∈ LC := by
        simpa [sub_eq_add_neg] using LC.add_mem hu (LC.neg_mem hv)
      simpa using this
    · -- nonzero
      intro hzero
      have : u = v := sub_eq_zero.mp hzero
      exact huv this
    · -- norm bound via `hammingDist_eq_hammingNorm`
      have hEq : hammingNorm (u - v) = hammingDist u v := by
        simpa using (hammingDist_eq_hammingNorm u v).symm
      simpa [hEq] using hle
  · intro h
    rcases h with ⟨w, hw, hw_ne, hle⟩
    -- Take v = 0, u = w
    refine ⟨w, hw, (0 : ι → F), LC.zero_mem, ?_, ?_⟩
    · exact by simpa using hw_ne
    · -- Δ₀(w, 0) = ‖w‖₀
      have hEq : hammingDist w 0 = hammingNorm w := by
        simp [hammingDist, hammingNorm]
      simpa [hEq] using hle

/--
The dimension of a linear code.
-/
noncomputable def dim [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) : ℕ := Module.finrank F MC

/-- The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma rank_eq_dim_fromColGenMat [CommRing F] {G : Matrix κ ι F} :
  G.rank = dim (fromColGenMat G) := rfl

/--
The length of a linear code.
-/
def length [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A] (_ : ModuleCode ι F A) : ℕ
    := Fintype.card ι

/--
The rate of a linear code.
-/
noncomputable def rate [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) : ℚ≥0 :=
  (dim MC : ℚ≥0) / length MC

/--
  `ρ LC` is the rate of the linear code `LC`.

  Uses `&` to make the notation non-reserved, allowing `ρ` to also be used as a variable name.
-/
scoped syntax &"ρ" term : term

scoped macro_rules
  | `(ρ $t:term) => `(LinearCode.rate $t)

end

section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]
         {A : Type*} [AddCommMonoid A] [DecidableEq A]

/-- The minimum taken over the weight of codewords in a linear code.
-/
noncomputable def minWtCodewords [Semiring F] [Module F A] (MC : ModuleCode ι F A) : ℕ :=
  sInf {w | ∃ c ∈ MC, c ≠ 0 ∧ Code.wt c = w}

/--
The Hamming distance between codewords equals to the weight of their difference.
-/
lemma hammingDist_eq_wt_sub [AddCommGroup F] {u v : ι → F} : hammingDist u v = Code.wt (u - v) := by
  aesop (add simp [hammingDist, Code.wt, sub_eq_zero])

omit [DecidableEq F] in
/-- The min distance of a linear code equals the minimum of the weights of non-zero codewords.
-/
lemma dist_eq_minWtCodewords [Ring F] {A : Type*} [DecidableEq A] [AddCommGroup A] [Module F A]
    {MC : ModuleCode ι F A} :
  Code.minDist (MC : Set (ι → A)) = minWtCodewords MC := by
    unfold Code.minDist minWtCodewords
    refine congrArg _ (Set.ext fun _ ↦ ⟨fun ⟨u, _, v, _⟩ ↦ ⟨u - v, ?p₁⟩, fun _ ↦ ⟨0, ?p₂⟩⟩) <;>
    rename_i u hu v u_sub_v_weight hvv h_u_mem hv_u_v_rel
    -- aesop (add simp [hammingDist_eq_wt_sub, sub_eq_zero])
    constructor
    · rcases hv_u_v_rel with ⟨h_v_mem, h_u_ne_v, h_dist⟩
      apply Submodule.sub_mem
      · exact h_u_mem
      · exact h_v_mem
    · -- case p₂
      rcases hv_u_v_rel with ⟨h_v_mem, h_u_ne_v, h_dist⟩
      constructor
      · rw [sub_ne_zero]; exact h_u_ne_v
      · -- ⊢ Code.wt (u - v) = hv
        -- We know `Code.wt c = h_u_mem`, so we show `Δ₀(0, c) = Code.wt c`
        rw [← h_dist]
        simp [Code.wt, hammingDist, sub_eq_zero]
    · simp only [SetLike.mem_coe, ne_eq, hammingDist_zero_left]
      rcases hv_u_v_rel with ⟨c, h_c_mem, h_c_ne, h_c_wt⟩
      -- We need to prove the conjunction
      constructor
      · -- 1. Prove `0 ∈ MC`
        let res := Submodule.zero_mem (p := MC)
        exact res
      · -- 2. Prove `∃ v_1 ...`
        refine ⟨c, h_c_mem, ?_, ?_⟩
        · -- Prove `¬0 = c` (which is `0 ≠ c`)
          exact h_c_ne.symm
        · -- Prove `‖c‖₀ = h_u_mem`
          rw [←h_c_wt]
          simp only [hammingNorm, ne_eq, Code.wt]

open Finset in

omit [DecidableEq F] in
lemma dist_UB [Ring F] {A : Type*} [DecidableEq A] [AddCommGroup A] [Module F A]
    {MC : ModuleCode ι F A} : Code.minDist (MC : Set (ι → A)) ≤ length MC := by
  rw [dist_eq_minWtCodewords, minWtCodewords]
  exact sInf.sInf_UB_of_le_UB fun s ⟨_, _, _, s_def⟩ ↦
          s_def ▸ le_trans (card_le_card (subset_univ _)) (le_refl _)

-- Restriction to a finite set of coordinates as a linear map
noncomputable def restrictLinear [Semiring F] [Module F A] (S : Finset ι) :
  (ι → A) →ₗ[F] (S → A) :=
{ toFun := fun f i => f i.1,
  map_add' := by intro f g; ext i; simp,
  map_smul' := by intro a f; ext i; simp }

theorem singletonBound [CommRing F] [StrongRankCondition F]
  (LC : LinearCode ι F) :
  dim LC ≤ length LC - Code.minDist (LC : Set (ι → F)) + 1 := by
  classical
  -- abbreviations
  set d := Code.minDist (LC : Set (ι → F)) with hd
  -- trivial case when d = 0
  by_cases h0 : d = 0
  · -- dim LC ≤ card ι ≤ card ι - 0 + 1
    have h_le_top : Module.finrank F LC ≤ Module.finrank F (ι → F) :=
      (Submodule.finrank_le (R := F) (M := (ι → F)) LC)
    have h_top : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_pi (R := F)
    have hfin : Module.finrank F LC ≤ Fintype.card ι := by simpa [h_top] using h_le_top
    have hfin' : Module.finrank F LC ≤ Fintype.card ι + 1 := hfin.trans (Nat.le_add_right _ _)
    have : Module.finrank F LC ≤ 1 + (Fintype.card ι - d) := by
      simpa [h0, Nat.sub_zero, Nat.add_comm] using hfin'
    simpa [dim, length, hd, Nat.add_comm] using this
  -- main case: d ≥ 1
  · have hd_pos : 1 ≤ d := by omega
    -- choose a set S of coordinates with |S| = |ι| - (d - 1)
    have h_le : Fintype.card ι - (d - 1) ≤ Fintype.card ι := by
      exact Nat.sub_le _ _
    obtain ⟨S, -, hScard⟩ :=
      (Finset.le_card_iff_exists_subset_card (α := ι) (s := (Finset.univ : Finset ι))
        (n := Fintype.card ι - (d - 1))).1 h_le
    -- restriction linear map to S, restricted to the code LC
    let res : LC →ₗ[F] (S → F) := (restrictLinear (F := F) (ι := ι) S).comp LC.subtype
    -- show ker res = ⊥ via the minimum distance property
    have hker : LinearMap.ker res = ⊥ := by
      classical
      refine LinearMap.ker_eq_bot'.2 ?_
      intro x hx
      -- x : LC, `res x = 0` hence all S-coordinates vanish
      have hxS : ∀ i ∈ S, (x : ι → F) i = 0 := by
        intro i hi
        have := congrArg (fun (f : (S → F)) => f ⟨i, hi⟩) (by simpa using hx)
        -- simp at this
        simpa using this
      -- bound the weight of x by |Sᶜ|
      let A : Finset ι := Finset.univ.filter (fun i => (x : ι → F) i ≠ 0)
      have hA_subset_compl : A ⊆ Sᶜ := by
        intro i hi
        rcases Finset.mem_filter.mp hi with ⟨-, hne⟩
        have : i ∉ S := by
          intro hiS; have := hxS i hiS; exact hne (by simpa using this)
        simpa [Finset.mem_compl] using this
      have h_wt_le : Code.wt (x : ι → F) ≤ (Sᶜ).card := by
        have : Code.wt (x : ι → F) = A.card := by
          simp [Code.wt, A]
        simpa [this] using (Finset.card_le_card hA_subset_compl)
      -- and |Sᶜ| = d - 1 using the chosen size of S
      have hS_card : S.card = Fintype.card ι - (d - 1) := by simpa using hScard
      have h_wt_le' : Code.wt (x : ι → F) ≤ d - 1 := by
        -- (Sᶜ).card = card ι - S.card = d - 1
        have hcardcompl : (Sᶜ : Finset ι).card = Fintype.card ι - S.card := by
          simpa using (Finset.card_compl (s := S))
        -- compute |Sᶜ| from hS_card
        have h_d_le_len : d ≤ Fintype.card ι := by
          have h := (dist_UB (MC := LC)); simpa [hd, length] using h
        have h_d1_le_len : d - 1 ≤ Fintype.card ι :=
          le_trans (Nat.sub_le d 1) h_d_le_len
        have hlen_sub : Fintype.card ι - S.card = d - 1 := by
          have : Fintype.card ι - S.card = Fintype.card ι - (Fintype.card ι - (d - 1)) := by
            simp [hS_card]
          simpa [Nat.sub_sub_self h_d1_le_len] using this
        have hcompl_le : (Sᶜ : Finset ι).card ≤ d - 1 := by simp [hcardcompl, hlen_sub]
        exact h_wt_le.trans hcompl_le
      -- if x ≠ 0 then d ≤ wt x, contradiction
      have hx0 : (x : ι → F) = 0 := by
        by_contra hx0
        have hx_mem : Code.wt (x : ι → F) ∈ {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w} := by
          exact ⟨x, x.property, by simpa using hx0, rfl⟩
        have hmin_le : d ≤ Code.wt (x : ι → F) := by
          -- d = sInf of weights of nonzero codewords
          have hmin_eq : Code.minDist (LC : Set (ι → F)) = minWtCodewords LC :=
            dist_eq_minWtCodewords (MC := LC)
          have hsInf : sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w} ≤ Code.wt (x : ι → F) :=
            Nat.sInf_le (s := {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w}) hx_mem
          have hd_def : d = sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w} := by
            simp [hd, minWtCodewords, hmin_eq]
          simpa [hd_def] using hsInf
        have hcontra : d ≤ d - 1 := le_trans hmin_le h_wt_le'
        have hsucc_le : d + 1 ≤ d := by
          have := Nat.add_le_add_right hcontra 1
          simp [Nat.sub_add_cancel hd_pos, Nat.add_comm] at this
        exact (Nat.not_succ_le_self d) hsucc_le
      -- conclude x = 0 in LC
      apply Subtype.ext
      simpa using hx0
    -- Using injectivity, compare finranks
    have hinj : Function.Injective res := by
      simpa [LinearMap.ker_eq_bot] using hker
    have hrange : Module.finrank F (LinearMap.range res) = Module.finrank F LC :=
      LinearMap.finrank_range_of_inj hinj
    have hcod_le : Module.finrank F (LinearMap.range res) ≤ Module.finrank F (S → F) :=
      Submodule.finrank_le (LinearMap.range res)
    have hcod : Module.finrank F (S → F) = S.card := by
      simp [Module.finrank_pi (R := F) (ι := {x // x ∈ S})]
    have : Module.finrank F LC ≤ S.card := by
      simpa [hrange, hcod] using hcod_le
    -- turn S.card bound into the target bound via arithmetic: a - (d - 1) ≤ 1 + (a - d)
    have hS_to_target : S.card ≤ 1 + (Fintype.card ι - d) := by
      simpa [hScard] using (by omega : Fintype.card ι - (d - 1) ≤ 1 + (Fintype.card ι - d))
    have hfin : Module.finrank F LC ≤ 1 + (Fintype.card ι - d) := this.trans hS_to_target
    simpa [dim, length, hd, Nat.add_comm] using hfin

/-- **Singleton bound** for linear codes -/
theorem singleton_bound_linear [CommRing F] [StrongRankCondition F]
    (LC : LinearCode ι F) :
    Module.finrank F LC ≤ card ι - (Code.dist LC.carrier) + 1 := by
  classical
  -- From the min-distance version and `Code.dist ≤ Code.minDist`.
  have h1 : Module.finrank F LC ≤ card ι - Code.minDist (LC : Set (ι → F)) + 1 :=
    singletonBound (LC := LC)
  -- `dist ≤ minDist` since `= d` implies `≤ d` for witnesses
  have hdist_le_min : Code.dist LC.carrier ≤ Code.minDist (LC : Set (ι → F)) := by
    classical
    let S₁ : Set ℕ := {d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d}
    let S₂ : Set ℕ := {d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v = d}
    have hsub : S₂ ⊆ S₁ := by
      intro d hd; rcases hd with ⟨u, hu, v, hv, hne, heq⟩; exact ⟨u, hu, v, hv, hne, by simp [heq]⟩
    by_cases hne : (S₂ : Set ℕ).Nonempty
    · have hLB : ∀ m ∈ S₂, sInf S₁ ≤ m := fun m hm => Nat.sInf_le (s := S₁) (hsub hm)
      have := sInf.le_sInf_of_LB (S := S₂) hne hLB
      simpa [Code.dist, Code.minDist, S₁, S₂] using this
    · -- S₂ empty ⇒ S₁ empty as well
      have hS₂empty : S₂ = (∅ : Set ℕ) := (Set.not_nonempty_iff_eq_empty).1 (by simpa using hne)
      have hS₁empty : S₁ = (∅ : Set ℕ) := by
        apply (Set.eq_empty_iff_forall_notMem).2
        intro m hm
        rcases hm with ⟨u, hu, v, hv, hne, hle⟩
        have : hammingDist u v ∈ S₂ := ⟨u, hu, v, hv, hne, rfl⟩
        simpa [hS₂empty, this]
      simp [Code.dist, Code.minDist, S₁, S₂, hS₁empty, hS₂empty, Nat.sInf_empty]
  -- Since a - b is antitone in b, add 1 afterwards
  have hmono' : card ι - Code.minDist (LC : Set (ι → F)) + 1 ≤
                 card ι - (Code.dist LC.carrier) + 1 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.add_le_add_right (Nat.sub_le_sub_left hdist_le_min _) 1)
  exact h1.trans hmono'

end

section Computable

/-- A computable version of the Hamming distance of a module code `MC`. -/
def moduleCodeDist' {F A} {ι} [Fintype ι] [Semiring F] [Fintype A] [DecidableEq ι] [DecidableEq A]
    [AddCommMonoid A] [Module F A]
 (MC : ModuleCode ι F A) [DecidablePred (· ∈ MC)] : ℕ∞ :=
  Finset.min <| ((Finset.univ (α := MC)).filter (fun v => v ≠ 0)).image (fun v => hammingNorm v.1)

end Computable

end LinearCode

lemma poly_eq_zero_of_dist_lt {n k : ℕ} {F : Type*} [DecidableEq F] [CommRing F] [IsDomain F]
  {p : Polynomial F} {ωs : Fin n → F}
  (h_deg : p.natDegree < k)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_dist : Δ₀(p.eval ∘ ωs, 0) < n - k + 1)
  : p = 0 := by
  by_cases hk : k = 0
  · simp [hk] at h_deg
  · have h_n_k_1 : n - k + 1 = n - (k - 1) := by omega
    rw [h_n_k_1] at h_dist
    simp [hammingDist] at *
    rw [←Finset.compl_filter, Finset.card_compl] at h_dist
    simp at h_dist
    have hk : 1 ≤ k := by omega
    rw [←Finset.card_image_of_injective _ h_inj
    ] at h_dist
    have h_dist_p : k  ≤
      (@Finset.image (Fin n) F _ ωs {i | Polynomial.eval (ωs i) p = 0} : Finset F).card
        := by omega
    by_cases heq_0 : p = 0 <;> try simp [heq_0]
    have h_dist := Nat.le_trans h_dist_p (by {
      apply Polynomial.card_le_degree_of_subset_roots (p := p)
      intro x hx
      aesop
    })
    omega
