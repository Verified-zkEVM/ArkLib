/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen, Elias Judin,
  Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Quotient.Card

/-!
## Main Definitions
- AHIV22 support material for the row-span bound and affine-line counting setup used by
  `ArkLib.Data.CodingTheory.ProximityGap.AHIV22`

## References

* [Ames, S., Hazay, C., Ishai, Y., and Venkitasubramaniam, M., *Ligero: Lightweight sublinear
    arguments without a trusted setup*][AHIV22]
      * NB we use version 20221118:030830
-/

noncomputable section

open Code ProbabilityTheory

-- `Pr_{...}[...]` notation is universe-restricted (requires `F : Type`).
variable {F : Type} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ]
         {ι : Type} [Fintype ι]

local instance : Fintype F := Fintype.ofFinite F

/-- The finite support of a vector over `F`. -/
private def vecSupport (u : ι → F) : Finset ι :=
  Finset.filter (fun j ↦ u j ≠ 0) Finset.univ

omit [Finite F] in
/-- Membership in `vecSupport` is exactly nonvanishing at that coordinate. -/
private lemma mem_vecSupport {u : ι → F} {j : ι} :
    j ∈ vecSupport (F := F) u ↔ u j ≠ 0 := by
  simp [vecSupport]

omit [Finite F] in
/-- Non-membership in `vecSupport` is exactly vanishing at that coordinate. -/
private lemma not_mem_vecSupport {u : ι → F} {j : ι} :
    j ∉ vecSupport (F := F) u ↔ u j = 0 := by
  simp [vecSupport]

omit [Finite F] in
/-- The support of a difference is the set of coordinates where the two words disagree. -/
private lemma vecSupport_sub (u v : ι → F) :
    vecSupport (F := F) (u - v) = Finset.filter (fun j ↦ u j ≠ v j) Finset.univ := by
  ext j
  simp [vecSupport, Pi.sub_apply, sub_ne_zero]

/-- If every coordinate where two words disagree lies in `D`, then their Hamming distance is at
most `D.card`. -/
lemma hamming_dist_le_of_subset_disagree
    {α : Type*} [DecidableEq α] {u v : ι → α}
    (D : Finset ι) (hD : ∀ j, u j ≠ v j → j ∈ D) :
    Δ₀(u, v) ≤ D.card := by
  classical
  unfold hammingDist
  refine Finset.card_le_card ?_
  intro j hj
  have : u j ≠ v j := by
    simpa [Finset.mem_filter] using hj
  exact hD j this

/-- A finite-dimensional submodule whose vectors all have support size at most `e` over a field
with more than `e` elements has a common support of size at most `e`. -/
private lemma exists_common_support_of_wt_le
    (E : Submodule F (ι → F)) (e : ℕ)
    (hE : ∀ x : E, (vecSupport (F := F) (x : ι → F)).card ≤ e)
    (hF : Fintype.card F > e) :
    ∃ D : Finset ι, D.card ≤ e ∧ ∀ x : E, ∀ j, j ∉ D → (x : ι → F) j = 0 := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let f : E → ℕ := fun x ↦ (vecSupport (F := F) (x : ι → F)).card
  have huniv : (Finset.univ : Finset E).Nonempty := Finset.univ_nonempty
  obtain ⟨x0, hx0⟩ := Finset.exists_maximalFor (f := f) (s := (Finset.univ : Finset E)) huniv
  have hx0_max : ∀ x : E, f x ≤ f x0 := by
    intro x
    by_contra hx
    have hxlt : f x0 < f x := lt_of_not_ge hx
    have : f x ≤ f x0 := hx0.2 (by simp) (le_of_lt hxlt)
    exact (not_lt_of_ge this) hxlt
  let D : Finset ι := vecSupport (F := F) (x0 : ι → F)
  refine ⟨D, ?_, ?_⟩
  · exact hE x0
  · intro x i hi
    by_contra hxi0
    have hxi : (x : ι → F) i ≠ 0 := by simpa using hxi0
    have hx0i : (x0 : ι → F) i = 0 := by
      have : i ∉ D := hi
      simpa [D, not_mem_vecSupport] using this
    let S : Finset ι := D.filter (fun j ↦ (x : ι → F) j ≠ 0)
    let bad : Finset F := S.image (fun j ↦ - (x0 : ι → F) j / (x : ι → F) j)
    let bad0 : Finset F := insert 0 bad
    have hS_subset : S ⊆ vecSupport (F := F) (x : ι → F) := by
      intro j hj
      have hxj : (x : ι → F) j ≠ 0 := by
        simpa [S] using (Finset.mem_filter.mp hj).2
      simpa [mem_vecSupport] using hxj
    have hi_mem_supportx : i ∈ vecSupport (F := F) (x : ι → F) := by
      simpa [mem_vecSupport] using hxi
    have hi_not_mem_S : i ∉ S := by
      intro hiS
      have hiD : i ∈ D := (Finset.mem_filter.mp hiS).1
      exact hi hiD
    have hS_card_lt_supportx : S.card < (vecSupport (F := F) (x : ι → F)).card := by
      apply Finset.card_lt_card
      refine ⟨hS_subset, ?_⟩
      intro hSubset
      exact hi_not_mem_S (hSubset hi_mem_supportx)
    have h_supportx_le_D : (vecSupport (F := F) (x : ι → F)).card ≤ D.card := by
      simpa [D, f] using hx0_max x
    have hS_card_lt_D : S.card < D.card :=
      lt_of_lt_of_le hS_card_lt_supportx h_supportx_le_D
    have hS_succ_le_D : S.card + 1 ≤ D.card := Nat.succ_le_of_lt hS_card_lt_D
    have hbad_card_le : bad.card ≤ S.card := Finset.card_image_le
    have h0_not_mem_bad : (0 : F) ∉ bad := by
      intro h0
      rcases Finset.mem_image.mp h0 with ⟨j, hjS, hj0⟩
      have hxj : (x : ι → F) j ≠ 0 := by
        have := (Finset.mem_filter.mp hjS).2
        simpa [S] using this
      have hx0j : (x0 : ι → F) j ≠ 0 := by
        have hjD : j ∈ D := (Finset.mem_filter.mp hjS).1
        simpa [D, mem_vecSupport] using hjD
      have : - (x0 : ι → F) j = (0 : F) := by
        have : - (x0 : ι → F) j / (x : ι → F) j = 0 := by simpa [bad] using hj0
        rcases (div_eq_zero_iff).1 this with h | h
        · exact h
        · exact False.elim (hxj h)
      have : (x0 : ι → F) j = 0 := by
        simpa using (neg_eq_zero.mp this)
      exact hx0j this
    have hbad0_card : bad0.card = bad.card + 1 := by
      simp [bad0, h0_not_mem_bad]
    have hbad0_card_le_D : bad0.card ≤ D.card := by
      calc
        bad0.card = bad.card + 1 := hbad0_card
        _         ≤ S.card + 1 := Nat.add_le_add_right hbad_card_le 1
        _         ≤ D.card := hS_succ_le_D
    have hD_lt_cardF : D.card < Fintype.card F := lt_of_le_of_lt (hE x0) hF
    have hbad0_lt_cardF : bad0.card < Fintype.card F :=
      lt_of_le_of_lt hbad0_card_le_D hD_lt_cardF
    have h_nonempty : (Finset.univ \ bad0 : Finset F).Nonempty := by
      have : 0 < (Finset.univ \ bad0 : Finset F).card := by
        simpa [Finset.card_univ_diff] using Nat.sub_pos_of_lt hbad0_lt_cardF
      exact Finset.card_pos.mp this
    rcases h_nonempty with ⟨a, ha⟩
    have ha_not_bad0 : a ∉ bad0 := (Finset.mem_sdiff.mp ha).2
    have ha_ne_zero : a ≠ 0 := by
      intro h
      apply ha_not_bad0
      simp [bad0, h]
    have ha_not_bad : a ∉ bad := by
      intro hab
      apply ha_not_bad0
      simp [bad0, hab]
    have hD_subset :
        D ⊆ vecSupport (F := F) ((x0 : ι → F) + a • (x : ι → F)) := by
      intro j hjD
      have hx0j : (x0 : ι → F) j ≠ 0 := by
        simpa [D, mem_vecSupport] using hjD
      by_cases hxj : (x : ι → F) j = 0
      · have : ((x0 : ι → F) + a • (x : ι → F)) j ≠ 0 := by
          simp [Pi.add_apply, Pi.smul_apply, hxj, hx0j]
        simpa [mem_vecSupport] using this
      · have hxj' : (x : ι → F) j ≠ 0 := hxj
        have hjS : j ∈ S := by
          have : j ∈ D ∧ (x : ι → F) j ≠ 0 := ⟨hjD, hxj'⟩
          simpa [S] using this
        have hneq : a ≠ - (x0 : ι → F) j / (x : ι → F) j := by
          intro hEq
          apply ha_not_bad
          exact Finset.mem_image.mpr ⟨j, hjS, hEq.symm⟩
        have : ((x0 : ι → F) + a • (x : ι → F)) j ≠ 0 := by
          intro hsum
          apply hneq
          have h' : a * (x : ι → F) j = - (x0 : ι → F) j := by
            have : (x0 : ι → F) j + a * (x : ι → F) j = 0 := by
              simpa [Pi.add_apply, Pi.smul_apply] using hsum
            simpa [mul_comm] using (eq_neg_of_add_eq_zero_right this)
          calc
            a = (a * (x : ι → F) j) / (x : ι → F) j := by
              simpa [mul_assoc] using (mul_div_cancel_right₀ a hxj').symm
            _ = - (x0 : ι → F) j / (x : ι → F) j := by
              simp [h']
        simpa [mem_vecSupport] using this
    have hi_mem :
        i ∈ vecSupport (F := F) ((x0 : ι → F) + a • (x : ι → F)) := by
      have : ((x0 : ι → F) + a • (x : ι → F)) i ≠ 0 := by
        simp [Pi.add_apply, Pi.smul_apply, hx0i, ha_ne_zero, hxi]
      simpa [mem_vecSupport] using this
    have hi_not_mem_D : i ∉ D := hi
    have hlt : D.card < (vecSupport (F := F) ((x0 : ι → F) + a • (x : ι → F))).card := by
      apply Finset.card_lt_card
      refine ⟨hD_subset, ?_⟩
      intro hSubset
      exact hi_not_mem_D (hSubset hi_mem)
    have hx0_ge :
        (vecSupport (F := F) ((x0 : ι → F) + a • (x : ι → F))).card ≤ D.card := by
      have hx_in : x0 + a • x ∈ (Finset.univ : Finset E) := by simp
      simpa [D, f] using hx0_max (x0 + a • x)
    exact (not_lt_of_ge hx0_ge) hlt

/-- **Lemma 4.3, [AHIV22]** (row-span lower bound).

If the interleaved word `U⋆` is more than `e` far from the interleaved code `L^⋈κ`, then the
row-span of `U⋆` contains a word more than `e` far from `L`.

The additional field-size assumption `|F| > e` is needed: for small fields one can have a linear
subspace of `F^ι` consisting entirely of `e`-sparse vectors whose supports are not aligned, making
`⋈|U⋆` column-wise far while every row-span vector stays `e`-close. -/
lemma dist_interleaved_code_to_code_lb
    {L : LinearCode ι F} {U_star : WordStack (A := F) κ ι}
    {e : ℕ}
    (hF : Fintype.card F > e)
    (he : (e : ℚ≥0) < ‖(L : Set (ι → F))‖₀ / 3)
    (hU : e < Δ₀(⋈|U_star, L^⋈κ)) :
    ∃ v ∈ Matrix.rowSpan U_star, e < Δ₀(v, L) := by
  classical
  have h3e_lt_d : 3 * e < ‖(L : Set (ι → F))‖₀ := by
    have h3pos : (0 : ℚ≥0) < 3 := by norm_num
    have h' : (3 : ℚ≥0) * (e : ℚ≥0) < (‖(L : Set (ι → F))‖₀ : ℚ≥0) := by
      have hmul := mul_lt_mul_of_pos_left he h3pos
      have h3ne : (3 : ℚ≥0) ≠ 0 := by norm_num
      have h3mul :
          (3 : ℚ≥0) * (‖(L : Set (ι → F))‖₀ : ℚ≥0) / 3 =
            ‖(L : Set (ι → F))‖₀ := by
        simp [h3ne]
      have : (3 : ℚ≥0) * (‖(L : Set (ι → F))‖₀ : ℚ≥0) / 3 =
          (3 : ℚ≥0) * ((‖(L : Set (ι → F))‖₀ : ℚ≥0) / 3) := by
        simpa [mul_div_assoc] using
          (mul_div_assoc (3 : ℚ≥0) (‖(L : Set (ι → F))‖₀ : ℚ≥0) (3 : ℚ≥0))
      have h3mul' :
          (3 : ℚ≥0) * ((‖(L : Set (ι → F))‖₀ : ℚ≥0) / 3) =
            ‖(L : Set (ι → F))‖₀ := by
        simpa [this] using h3mul
      simpa [h3mul'] using hmul
    exact_mod_cast h'
  have h2e_lt_d : 2 * e < ‖(L : Set (ι → F))‖₀ := by omega
  by_contra h_contra
  push Not at h_contra
  have h_close (v : Matrix.rowSpan U_star) :
      Δ₀((v : ι → F), (L : Set (ι → F))) ≤ e :=
    h_contra v v.property
  have h_exists_codeword (v : Matrix.rowSpan U_star) :
      ∃ c ∈ (L : Set (ι → F)), Δ₀((v : ι → F), c) ≤ e := by
    simpa using
      (Code.closeToCode_iff_closeToCodeword_of_minDist (u := (v : ι → F))
        (C := (L : Set (ι → F))) (e := e)).1 (h_close v)
  choose dec hdec_mem hdec_dist using h_exists_codeword
  have hdec_add (v w : Matrix.rowSpan U_star) : dec (v + w) = dec v + dec w := by
    apply Code.eq_of_lt_dist (C := (L : Set (ι → F)))
    · exact hdec_mem (v + w)
    · exact Submodule.add_mem _ (hdec_mem v) (hdec_mem w)
    · have h1 : Δ₀(dec (v + w), (v + w : ι → F)) ≤ e := by
        simpa [hammingDist_comm] using hdec_dist (v + w)
      have h2 : Δ₀((v + w : ι → F), dec v + dec w) ≤ 2 * e := by
        have hv :
            Δ₀((v + w : ι → F), (v : ι → F) + dec w) = Δ₀((w : ι → F), dec w) := by
          simpa [Pi.add_apply] using
            (hammingDist_comp (f := fun i ↦ fun t : F ↦ (v : ι → F) i + t)
              (x := (w : ι → F)) (y := dec w)
              (hf := fun _ ↦ by
                intro a b hab
                exact add_left_cancel hab))
        have hw :
            Δ₀((v : ι → F) + dec w, dec v + dec w) = Δ₀((v : ι → F), dec v) := by
          simpa [Pi.add_apply] using
            (hammingDist_comp (f := fun i ↦ fun t : F ↦ t + dec w i)
              (x := (v : ι → F)) (y := dec v)
              (hf := fun _ ↦ by
                intro a b hab
                exact add_right_cancel hab))
        have : Δ₀((v + w : ι → F), dec v + dec w)
            ≤ Δ₀((v + w : ι → F), (v : ι → F) + dec w)
              + Δ₀((v : ι → F) + dec w, dec v + dec w) := by
          exact hammingDist_triangle (v + w : ι → F) ((v : ι → F) + dec w) (dec v + dec w)
        calc
          Δ₀((v + w : ι → F), dec v + dec w)
              ≤ Δ₀((v + w : ι → F), (v : ι → F) + dec w)
                + Δ₀((v : ι → F) + dec w, dec v + dec w) := this
          _   = Δ₀((w : ι → F), dec w) + Δ₀((v : ι → F), dec v) := by
              simp [hv, hw, add_comm]
          _   ≤ e + e := Nat.add_le_add (hdec_dist w) (hdec_dist v)
          _   = 2 * e := by ring
      have h3 : Δ₀(dec (v + w), dec v + dec w) ≤ 3 * e := by
        calc
          Δ₀(dec (v + w), dec v + dec w)
              ≤ Δ₀(dec (v + w), (v + w : ι → F))
                + Δ₀((v + w : ι → F), dec v + dec w) := by
                  exact
                    hammingDist_triangle (dec (v + w)) (v + w : ι → F) (dec v + dec w)
          _   ≤ e + 2 * e := Nat.add_le_add h1 h2
          _   = 3 * e := by ring
      exact lt_of_le_of_lt h3 h3e_lt_d
  have hdec_smul (a : F) (v : Matrix.rowSpan U_star) : dec (a • v) = a • dec v := by
    apply Code.eq_of_lt_dist (C := (L : Set (ι → F)))
    · exact hdec_mem (a • v)
    · exact Submodule.smul_mem _ a (hdec_mem v)
    · have h1 : Δ₀(dec (a • v), (a • v : ι → F)) ≤ e := by
        simpa [hammingDist_comm] using hdec_dist (a • v)
      have h2 : Δ₀((a • v : ι → F), a • dec v) ≤ e := by
        have := hammingDist_smul_le_hammingDist (k := a) (x := (v : ι → F)) (y := dec v)
        exact le_trans this (hdec_dist v)
      have h3 : Δ₀(dec (a • v), a • dec v) ≤ 2 * e := by
        calc
          Δ₀(dec (a • v), a • dec v)
              ≤ Δ₀(dec (a • v), (a • v : ι → F))
                  + Δ₀((a • v : ι → F), a • dec v) := by
                exact hammingDist_triangle (dec (a • v)) (a • v : ι → F) (a • dec v)
          _   ≤ e + e := Nat.add_le_add h1 h2
          _   = 2 * e := by ring
      exact lt_of_le_of_lt h3 h2e_lt_d
  let decLin : Matrix.rowSpan U_star →ₗ[F] (ι → F) :=
    { toFun := dec, map_add' := hdec_add, map_smul' := hdec_smul }
  let err : Matrix.rowSpan U_star →ₗ[F] (ι → F) :=
    Submodule.subtype (Matrix.rowSpan U_star) - decLin
  have herr_wt (x : LinearMap.range err) :
      (vecSupport (F := F) (x : ι → F)).card ≤ e := by
    rcases x.property with ⟨v, hv⟩
    have h_supp :
        (vecSupport (F := F) ((err v) : ι → F)).card = Δ₀((v : ι → F), dec v) := by
      simp [err, decLin, vecSupport_sub, hammingDist]
    simpa [hv.symm, h_supp] using hdec_dist v
  obtain ⟨D, hD_card, hD_zero⟩ :=
    exists_common_support_of_wt_le (F := F) (ι := ι) (E := LinearMap.range err) (e := e)
      herr_wt hF
  have h_row_in_span (k : κ) : U_star k ∈ Matrix.rowSpan U_star := by
    unfold Matrix.rowSpan
    exact Submodule.subset_span ⟨k, rfl⟩
  let V : WordStack (A := F) κ ι := fun k ↦ dec ⟨U_star k, h_row_in_span k⟩
  have hV_mem : (⋈|V) ∈ (L^⋈κ) := by
    refine (Code.mem_moduleInterleavedCode_iff (F := F) (A := F) (κ := κ) (ι := ι) (MC := L)
      (v := (⋈|V))).2 ?_
    intro k
    simpa [V] using hdec_mem ⟨U_star k, h_row_in_span k⟩
  have h_dist_rows : ∀ k j, j ∉ D → U_star k j = V k j := by
    intro k j hj
    have hz :
        (err ⟨U_star k, h_row_in_span k⟩ : ι → F) j = 0 := by
      have : (err ⟨U_star k, h_row_in_span k⟩) ∈ LinearMap.range err :=
        ⟨⟨U_star k, h_row_in_span k⟩, rfl⟩
      exact hD_zero ⟨err ⟨U_star k, h_row_in_span k⟩, this⟩ j hj
    have : (U_star k j : F) - V k j = 0 := by
      simpa [err, decLin, V, Pi.sub_apply] using hz
    exact sub_eq_zero.mp this
  have hUV_le : Δ₀(⋈|U_star, ⋈|V) ≤ e := by
    refine le_trans
      (hamming_dist_le_of_subset_disagree (ι := ι) (u := (⋈|U_star)) (v := (⋈|V))
        (D := D) ?_)
      hD_card
    intro j hj
    by_contra hjD
    apply hj
    funext k
    have := h_dist_rows k j hjD
    simpa [V] using this
  have h_dist_to_code : Δ₀(⋈|U_star, (L^⋈κ)) ≤ e := by
    exact le_trans
      (Code.distFromCode_le_dist_to_mem (C := (L^⋈κ)) (u := (⋈|U_star)) (v := (⋈|V))
        hV_mem)
      (by exact_mod_cast hUV_le)
  exact (not_lt_of_ge h_dist_to_code) hU

namespace ProximityToRS

open ReedSolomon NNReal

/-- The set of points on an affine line, which are within distance `e` from a Reed-Solomon code.
-/
def closePtsOnAffineLine {ι : Type*} [Fintype ι]
    (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : Set (ι → F) :=
  {x : ι → F | x ∈ Affine.affineLineAtOrigin (F := F) (origin := u) (direction := v)
    ∧ Δ₀(x, ReedSolomon.code α deg) ≤ e}

/-- The number of points on an affine line between, which are within distance `e` from a
Reed-Solomon code.
-/
def numberOfClosePts (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : ℕ := by
  classical
  letI :
      Fintype
        (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) :=
    Fintype.ofFinite _
  exact
    Fintype.card
      (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e))

/-- The explicit finite-cardinality definition of `numberOfClosePts` agrees with `Nat.card` of
the corresponding close-point subtype. -/
lemma number_of_close_pts_eq_nat_card (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) :
    numberOfClosePts (F := F) (ι := ι) u v deg α e =
      Nat.card
        (closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)) := by
  classical
  unfold numberOfClosePts
  exact
    (Fintype.card_eq_nat_card
      (α :=
        closePtsOnAffineLine (F := F) (u := u) (v := v) (deg := deg) (α := α) (e := e)))

end ProximityToRS
