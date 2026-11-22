/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen, Elias Judin,
  Aristotle (Harmonic)
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.AHIV22Support
public import ArkLib.Data.Probability.Uniform

/-!
## Main Definitions
Statements of proximity results for Reed--Solomon codes ([AHIV22], Lemmas 4.3--4.5).

## References

* [Ames, S., Hazay, C., Ishai, Y., and Venkitasubramaniam, M., *Ligero: Lightweight
    sublinear arguments without a trusted setup*][AHIV22], version 20221118:030830
-/

@[expose] public section

noncomputable section

open Code ProbabilityTheory
open scoped ProbabilityTheory

-- `Pr{...}[...]` notation is universe-restricted (requires `F : Type`).
variable {F : Type} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ]
         {ι : Type} [Fintype ι]

local instance : Fintype F := Fintype.ofFinite F

namespace ProximityToRS
open ReedSolomon NNReal

omit [Finite F] [DecidableEq F] in
private lemma direction_eq_of_two_affine_values
    {u v c₀ c₁ r₀ r₁ : F}
    (h₀ : u + r₀ * v = c₀) (h₁ : u + r₁ * v = c₁) (hr : r₁ ≠ r₀) :
    v = (r₁ - r₀)⁻¹ * (c₁ - c₀) := by
  rw [← h₀, ← h₁]
  field_simp [sub_ne_zero.mpr hr]
  ring

omit [Finite F] [DecidableEq F] in
private lemma directions_eq_of_two_affine_values
    {u v c w r s : F}
    (hr : u + r * v = c + r * w) (hs : u + s * v = c + s * w) (hrs : r ≠ s) :
    v = w := by
  have hzero : (r - s) * (v - w) = 0 := by
    calc
      (r - s) * (v - w) =
          (u + r * v - (c + r * w)) - (u + s * v - (c + s * w)) := by ring
      _ = 0 := by rw [hr, hs]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hrs))

omit [DecidableEq F] in
private lemma three_mul_lt_of_lt_div_three {e d : ℕ} (he : (e : ℚ≥0) < d / 3) : 3 * e < d := by
  have h : (e : ℚ≥0) * 3 < d := (lt_div_iff₀ (by norm_num)).1 he
  rw [mul_comm] at h
  exact_mod_cast h

/-- Every close point on the affine line `u + r • v` comes from some close scalar `r`. -/
private lemma numberOfClosePts_le_natCard_close_scalars
    {deg : ℕ} {α : ι ↪ F} {e : ℕ} {u v : ι → F} :
    numberOfClosePts u v deg α e ≤
      Nat.card {r : F // Δ₀(u + r • v, (ReedSolomon.code α deg : Set (ι → F))) ≤ e} := by
  rw [number_of_close_pts_eq_nat_card]
  refine Nat.card_le_card_of_surjective
    (fun r ↦ ⟨u + r.1 • v,
      (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) _).2 ⟨r.1, rfl⟩,
      r.2⟩) ?_
  intro x
  obtain ⟨r, hr⟩ :=
    (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) x.1).1 x.2.1
  exact ⟨⟨r, hr ▸ x.2.2⟩, Subtype.ext hr.symm⟩

/-- Core of Lemma 4.4: if more than `‖C‖₀` scalars `r` put `u + r • v` within distance `e` of
the linear code `C`, and `3e < ‖C‖₀`, then `u` and `v` agree with codewords outside a common set
of at most `e` coordinates. -/
private lemma exists_codewords_agree_of_many_close_scalars
    (CRS : Submodule F (ι → F)) {e : ℕ} {u v : ι → F}
    (h3e_lt : 3 * e < ‖(CRS : Set (ι → F))‖₀)
    (hRS_gt' : ‖(CRS : Set (ι → F))‖₀ <
      Nat.card {r : F // Δ₀(u + r • v, (CRS : Set (ι → F))) ≤ e}) :
    ∃ cBase ∈ CRS, ∃ w ∈ CRS, ∃ D : Finset ι, D.card ≤ e ∧
      ∀ j ∉ D, u j = cBase j ∧ v j = w j := by
  classical
  set C : Set (ι → F) := (CRS : Set (ι → F))
  let RS : Type := {r : F // Δ₀(u + r • v, C) ≤ e}
  have hRS_gt : ‖C‖₀ < Fintype.card RS := by
    rw [← Nat.card_eq_fintype_card]
    exact hRS_gt'
  have huniv_one_lt : 1 < (Finset.univ : Finset RS).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨r0, -, r1, -, hr01⟩ := Finset.one_lt_card.mp huniv_one_lt
  -- Decode each good scalar to a codeword and a disagreement set of size at most `e`.
  have h_close_codeword (r : RS) : ∃ c ∈ C, Δ₀(u + r.1 • v, c) ≤ e :=
    (Code.closeToCode_iff_closeToCodeword_of_minDist (u := u + r.1 • v) (C := C) (e := e)).1
      r.2
  choose c hc_mem hc_dist using h_close_codeword
  have h_disagree (r : RS) :
      ∃ D : Finset ι, D.card ≤ e ∧ ∀ j, j ∉ D → (u + r.1 • v) j = c r j :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols (u := u + r.1 • v) (v := c r) (e := e)).1
      (hc_dist r)
  choose E hE_card hE_agree using h_disagree
  have hE_agree' (r : RS) (j : ι) (hj : j ∉ E r) : u j + r.1 * v j = c r j :=
    hE_agree r j hj
  -- The direction codeword `w` and the base codeword `cBase`, read off from `r0` and `r1`.
  let w : ι → F := (r1.1 - r0.1)⁻¹ • (c r1 - c r0)
  let cBase : ι → F := c r0 - r0.1 • w
  have hw_mem : w ∈ CRS := CRS.smul_mem _ (CRS.sub_mem (hc_mem r1) (hc_mem r0))
  have hcBase_mem : cBase ∈ CRS := CRS.sub_mem (hc_mem r0) (CRS.smul_mem _ hw_mem)
  have h_base (j : ι) (h0 : j ∉ E r0) (h1 : j ∉ E r1) : u j = cBase j ∧ v j = w j := by
    have hv : v j = w j :=
      direction_eq_of_two_affine_values (hE_agree' r0 j h0) (hE_agree' r1 j h1)
        fun h ↦ hr01 (Subtype.ext h.symm)
    refine ⟨?_, hv⟩
    simp only [cBase, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv, ← hE_agree' r0 j h0]
    ring
  -- Every decoded codeword lies on the line `cBase + r • w`: the two codewords agree outside
  -- `E r0 ∪ E r1 ∪ E r`, which has fewer than `‖C‖₀` elements.
  have h_codeword_eq (r : RS) : c r = cBase + r.1 • w := by
    refine Code.eq_of_lt_dist (C := C) (hc_mem r) (CRS.add_mem hcBase_mem (CRS.smul_mem _ hw_mem))
      (lt_of_le_of_lt (hamming_dist_le_of_subset_disagree (E r0 ∪ E r1 ∪ E r) fun j hj ↦ ?_) ?_)
    · by_contra hU
      simp only [Finset.mem_union, not_or] at hU
      obtain ⟨hu, hv⟩ := h_base j hU.1.1 hU.1.2
      refine hj ?_
      rw [← hE_agree' r j hU.2]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu, hv]
    · have h3 := (Finset.card_union_le (E r0 ∪ E r1) (E r)).trans
        (Nat.add_le_add_right (Finset.card_union_le (E r0) (E r1)) _)
      have := hE_card r0
      have := hE_card r1
      have := hE_card r
      omega
  have h_line (r : RS) (j : ι) (hj : j ∉ E r) : u j + r.1 * v j = cBase j + r.1 * w j := by
    rw [hE_agree' r j hj, h_codeword_eq r]
    rfl
  -- The global disagreement set where `u` or `v` fail to match `cBase`/`w`.
  let D : Finset ι := {j | u j ≠ cBase j ∨ v j ≠ w j}
  -- At a coordinate of `D`, at most one good scalar avoids its disagreement set.
  have h_err_ge (j : ι) (hj : j ∈ D) :
      Fintype.card RS - 1 ≤ (Finset.univ.filter fun r : RS ↦ j ∈ E r).card := by
    have hclean_le1 : (Finset.univ.filter fun r : RS ↦ j ∉ E r).card ≤ 1 := by
      refine Finset.card_le_one.2 fun r hr s hs ↦ Subtype.ext ?_
      by_contra hrs
      have hr' : j ∉ E r := (Finset.mem_filter.mp hr).2
      have hs' : j ∉ E s := (Finset.mem_filter.mp hs).2
      have hv : v j = w j :=
        directions_eq_of_two_affine_values (h_line r j hr') (h_line s j hs') hrs
      have hu : u j = cBase j := add_right_cancel (hv ▸ h_line r j hr')
      exact (Finset.mem_filter.mp hj).2.elim (· hu) (· hv)
    have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset RS))
      (p := fun r : RS ↦ j ∈ E r)
    rw [Finset.card_univ] at hpart
    omega
  -- Count the incidences `j ∈ E r` over `j ∈ D` from both sides.
  have h_incidences : ∑ j, (Finset.univ.filter fun r : RS ↦ j ∈ E r).card = ∑ r, (E r).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h_pairs : D.card * (Fintype.card RS - 1) ≤ Fintype.card RS * e :=
    calc
      D.card * (Fintype.card RS - 1)
          ≤ ∑ j ∈ D, (Finset.univ.filter fun r : RS ↦ j ∈ E r).card :=
        smul_eq_mul D.card _ ▸ Finset.card_nsmul_le_sum D _ _ h_err_ge
      _ ≤ ∑ j, (Finset.univ.filter fun r : RS ↦ j ∈ E r).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ D)
      _ = ∑ r, (E r).card := h_incidences
      _ ≤ ∑ _r : RS, e := Finset.sum_le_sum fun r _ ↦ hE_card r
      _ = Fintype.card RS * e := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hD_card : D.card ≤ e := by
    by_contra hD_gt
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card RS = m + 1 := ⟨Fintype.card RS - 1, by omega⟩
    have hle : (e + 1) * m ≤ (m + 1) * e := by
      rw [hm, Nat.add_sub_cancel] at h_pairs
      exact (Nat.mul_le_mul_right m (by omega)).trans h_pairs
    rw [add_mul, one_mul, add_mul, one_mul, mul_comm m e] at hle
    omega
  exact ⟨cBase, hcBase_mem, w, hw_mem, D, hD_card, fun j hj ↦ by simpa [D, not_or] using hj⟩

-- Distance-bound form, proved first; the mutual-exclusion corollary `e_le_dist_over_3` follows.
/-- **Lemma 4.4, [AHIV22] (strong form).**

Either all points on the affine line are `e`-close to the Reed–Solomon code, or at most
`‖RS‖₀` points are.
-/
lemma e_le_dist_over_3_strong
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3) :
    (∀ x ∈ Affine.affineLineAtOrigin (F := F) u v, Δ₀(x, ReedSolomon.code α deg) ≤ e)
      ∨ numberOfClosePts u v deg α e ≤ ‖(RScodeSet α deg)‖₀ := by
  refine or_iff_not_imp_right.2 fun h_card x hx ↦ ?_
  obtain ⟨cBase, hcBase_mem, w, hw_mem, D, hD_card, hagree⟩ :=
    exists_codewords_agree_of_many_close_scalars (ReedSolomon.code α deg)
      (three_mul_lt_of_lt_div_three he)
      (lt_of_lt_of_le (not_le.1 h_card) numberOfClosePts_le_natCard_close_scalars)
  obtain ⟨r, rfl⟩ :=
    (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) x).1 hx
  have hdist : Δ₀(u + r • v, cBase + r • w) ≤ D.card :=
    hamming_dist_le_of_subset_disagree D fun j hj ↦ by
      by_contra hjD
      obtain ⟨huj, hvj⟩ := hagree j hjD
      exact hj (by simp only [Pi.add_apply, Pi.smul_apply, huj, hvj])
  exact le_trans
    (Code.distFromCode_le_dist_to_mem _ _
      (Submodule.add_mem _ hcBase_mem (Submodule.smul_mem _ r hw_mem)))
    (by exact_mod_cast le_trans hdist hD_card)

/-- If more than `‖RS‖₀` scalars `r` put `u + r • v` within distance `e` of the Reed–Solomon
code, then the direction `v` is itself `e`-close to the code. -/
private lemma dir_close_of_many_close_scalars
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
    (h_many : ‖(RScodeSet α deg)‖₀ <
      Nat.card {r : F // Δ₀(u + r • v, (ReedSolomon.code α deg : Set (ι → F))) ≤ e}) :
    Δ₀(v, ReedSolomon.code α deg) ≤ e := by
  obtain ⟨_, _, w, hw_mem, D, hD_card, hagree⟩ :=
    exists_codewords_agree_of_many_close_scalars (ReedSolomon.code α deg)
      (three_mul_lt_of_lt_div_three he) h_many
  have hdist_vw : Δ₀(v, w) ≤ D.card :=
    hamming_dist_le_of_subset_disagree D fun j hj ↦ by
      by_contra hjD
      exact hj (hagree j hjD).2
  exact le_trans (Code.distFromCode_le_dist_to_mem _ _ hw_mem)
    (by exact_mod_cast le_trans hdist_vw hD_card)

/-- If an affine line has too many `e`-close points to the Reed–Solomon code, then its direction
is itself `e`-close to the code. -/
lemma dir_close_of_many_close_pts
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
    (h_many : numberOfClosePts u v deg α e > ‖(RScodeSet α deg)‖₀) :
    Δ₀(v, ReedSolomon.code α deg) ≤ e :=
  dir_close_of_many_close_scalars he
    (lt_of_lt_of_le h_many numberOfClosePts_le_natCard_close_scalars)

/-- If every point on a nondegenerate affine line is close and the field is larger than the
Reed-Solomon minimum distance, then the line cannot have only few close points. -/
private lemma all_close_not_few_close_pts
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (hv : v ≠ 0)
    (hFd : ‖(RScodeSet α deg)‖₀ < Fintype.card F)
    (h_all :
      ∀ x ∈ Affine.affineLineAtOrigin (F := F) u v, Δ₀(x, ReedSolomon.code α deg) ≤ e) :
    ¬numberOfClosePts u v deg α e ≤ ‖(RScodeSet α deg)‖₀ := by
  intro h_few
  have hnum_ge : Fintype.card F ≤ numberOfClosePts (F := F) (ι := ι) u v deg α e := by
    have hex : ∃ j, v j ≠ 0 := by
      by_contra h
      apply hv
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    rcases hex with ⟨j, hj⟩
    let g : F → closePtsOnAffineLine (F := F) (u := u) (v := v)
        (deg := deg) (α := α) (e := e) :=
      fun r ↦
        ⟨u + r • v, by
            refine ⟨?_, ?_⟩
            · refine
                (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) _).2 ?_
              exact ⟨r, rfl⟩
            · apply h_all
              refine
                (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u) (direction := v) _).2 ?_
              exact ⟨r, rfl⟩⟩
    have hg_inj : Function.Injective g := by
      intro r₁ r₂ hr
      have hval : u + r₁ • v = u + r₂ • v := congrArg Subtype.val hr
      have hmul : r₁ * v j = r₂ * v j := by
        have := congrArg (fun f : ι → F ↦ f j) hval
        simpa [Pi.add_apply, Pi.smul_apply] using add_left_cancel this
      exact mul_right_cancel₀ hj hmul
    have hnat :
        Nat.card F ≤ Nat.card
          (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
      Nat.card_le_card_of_injective g hg_inj
    have hnum :
        numberOfClosePts (F := F) (ι := ι) u v deg α e =
          Nat.card
            (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
      number_of_close_pts_eq_nat_card (F := F) (ι := ι) u v deg α e
    have hcardF : Fintype.card F = Nat.card F := by
      exact (Fintype.card_eq_nat_card (α := F))
    calc
      Fintype.card F = Nat.card F := hcardF
      _ ≤ Nat.card
            (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
        hnat
      _ = numberOfClosePts (F := F) (ι := ι) u v deg α e := hnum.symm
  have hcardF_le : Fintype.card F ≤ ‖(RScodeSet α deg)‖₀ := le_trans hnum_ge h_few
  exact (not_lt_of_ge hcardF_le) hFd

/-- **Lemma 4.4, [AHIV22] (mutual-exclusion corollary).**

Either all points on the affine line are `e`-close to the Reed–Solomon code, or at most
`‖RS‖₀` points are.

The assumptions `v ≠ 0` and `‖RS‖₀ < |F|` are necessary for mutual exclusion:
if `v = 0`, the affine line degenerates to a singleton and the two branches can hold
simultaneously.
-/
lemma e_le_dist_over_3
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
    (hv : v ≠ 0)
    (hFd : ‖(RScodeSet α deg)‖₀ < Fintype.card F) :
    Xor
      (∀ x ∈ Affine.affineLineAtOrigin (F := F) u v, Δ₀(x, ReedSolomon.code α deg) ≤ e)
      (numberOfClosePts u v deg α e ≤ ‖(RScodeSet α deg)‖₀) := by
  classical
  have hline :
      (∀ x ∈ Affine.affineLineAtOrigin (F := F) u v, Δ₀(x, ReedSolomon.code α deg) ≤ e)
        ∨ numberOfClosePts u v deg α e ≤ ‖(RScodeSet α deg)‖₀ :=
    e_le_dist_over_3_strong (F := F) (ι := ι) (α := α) (e := e) (u := u) (v := v) he
  rcases hline with h_all | h_few
  · exact Or.inl
      ⟨h_all,
        all_close_not_few_close_pts (F := F) (ι := ι) (hv := hv) (hFd := hFd) h_all⟩
  · exact Or.inr
      ⟨h_few, fun h_all ↦
        all_close_not_few_close_pts (F := F) (ι := ι) (hv := hv) (hFd := hFd) h_all
          h_few⟩

/-- **Lemma 4.5, [AHIV22].**

If the interleaved word `U⋆` is far from the interleaved Reed–Solomon code, then a uniformly
random word in the row-span is `e`-close to the code with probability at most
`‖RS‖₀ / |F|`. -/
lemma prob_of_bad_pts
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {U_star : WordStack (A := F) κ ι}
    [SampleableType (Matrix.rowSpan U_star)]
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
    (hU : e < Δ₀(⋈|U_star, (ReedSolomon.code α deg)^⋈κ)) :
    Pr{let w_star ← $ᵗ (Matrix.rowSpan U_star)}[
        Δ₀(w_star, RScodeSet α deg) ≤ e]
      ≤ (‖(RScodeSet α deg)‖₀ : ENNReal) / Fintype.card F := by
  classical
  set RS : Set (ι → F) := RScodeSet α deg
  set d : ℕ := ‖RS‖₀
  have h3e_lt_d : 3 * e < d := three_mul_lt_of_lt_div_three he
  have hF : e < Fintype.card F :=
    calc
      e < d := by omega
      _ ≤ Fintype.card ι := Code.dist_le_card (C := RS)
      _ ≤ Fintype.card F := Fintype.card_le_of_embedding α
  obtain ⟨v_star, hv_mem, hv_far⟩ :=
    dist_interleaved_code_to_code_lb (F := F) (ι := ι) (κ := κ) (L := ReedSolomon.code α deg)
      (U_star := U_star) hF he hU
  -- Every affine line in direction `v_star` has at most `d` points close to the code.
  have hline_le (u : ι → F) : Nat.card {r : F // Δ₀(u + r • v_star, RS) ≤ e} ≤ d :=
    le_of_not_gt fun h_many ↦ not_lt_of_ge (dir_close_of_many_close_scalars he h_many) hv_far
  -- Double count the pairs `(w, r)` with `w + r • v_star` close to the code.
  let S : Submodule F (ι → F) := Matrix.rowSpan U_star
  let vDir : S := ⟨v_star, hv_mem⟩
  let Pbad : S → Prop := fun w ↦ Δ₀((w : ι → F), RS) ≤ e
  let bad : Finset S := Finset.filter Pbad Finset.univ
  have htranslate (r : F) :
      (Finset.univ.filter fun w : S ↦ Pbad (w + r • vDir)).card = bad.card :=
    Finset.card_equiv (Equiv.addRight (r • vDir)) fun w ↦ by simp [bad]
  have hcount : bad.card * Fintype.card F ≤ Fintype.card S * d :=
    calc
      bad.card * Fintype.card F
          = ∑ r : F, (Finset.univ.filter fun w : S ↦ Pbad (w + r • vDir)).card := by
        rw [Finset.sum_congr rfl fun r _ ↦ htranslate r, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
      _ = ∑ w : S, (Finset.univ.filter fun r : F ↦ Pbad (w + r • vDir)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      _ ≤ ∑ _w : S, d := Finset.sum_le_sum fun w _ ↦ by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact hline_le w
      _ = Fintype.card S * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hprob :
      Pr{let w_star ← $ᵗ (Matrix.rowSpan U_star)}[Δ₀(w_star, RS) ≤ e] =
        (bad.card : ENNReal) / Fintype.card S := by
    rw [SampleableType.prEvent_uniformSample]
  rw [hprob]
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm, ← mul_div_assoc, ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast Fintype.card_ne_zero)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast hcount
end ProximityToRS
end
