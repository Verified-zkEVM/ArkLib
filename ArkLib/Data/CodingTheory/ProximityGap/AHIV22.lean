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
  have hRS_gt : Fintype.card RS > ‖C‖₀ := by
    rw [← Nat.card_eq_fintype_card]
    exact hRS_gt'
  have hdist_pos : 0 < ‖C‖₀ := by
    exact lt_of_le_of_lt (Nat.zero_le (3 * e)) h3e_lt
  have hRS_one_lt : 1 < Fintype.card RS := by
    have : 1 ≤ ‖C‖₀ := Nat.succ_le_of_lt hdist_pos
    exact lt_of_le_of_lt this hRS_gt
  have huniv_one_lt : 1 < (Finset.univ : Finset RS).card := by
    rwa [Finset.card_univ]
  obtain ⟨r0, -, r1, -, hr01⟩ := Finset.one_lt_card.mp huniv_one_lt
  have : Nonempty RS := ⟨r0⟩
  -- Define codewords and disagreement sets for each good scalar.
  have h_close_codeword (r : RS) : ∃ c ∈ C, Δ₀(u + r.1 • v, c) ≤ e :=
    (Code.closeToCode_iff_closeToCodeword_of_minDist (u := u + r.1 • v) (C := C) (e := e)).1
      r.2
  choose c hc_mem hc_dist using h_close_codeword
  have h_disagree (r : RS) :
      ∃ D : Finset ι, D.card ≤ e ∧ ∀ j, j ∉ D → (u + r.1 • v) j = c r j :=
    (Code.closeToWord_iff_exists_possibleDisagreeCols (u := u + r.1 • v) (v := c r) (e := e)).1
      (hc_dist r)
  choose E hE_card hE_agree using h_disagree
  -- The direction codeword `w`.
  have hr10 : (r1.1 - r0.1) ≠ 0 := sub_ne_zero.mpr (by
    intro h
    apply hr01
    ext
    exact h.symm)
  let w : ι → F := (r1.1 - r0.1)⁻¹ • (c r1 - c r0)
  have hw_mem : w ∈ CRS := by
    have hc1 : c r1 ∈ CRS := hc_mem r1
    have hc0 : c r0 ∈ CRS := hc_mem r0
    exact Submodule.smul_mem CRS _ (Submodule.sub_mem CRS hc1 hc0)
  have hv_eq_w_of_notin (j : ι) (hj0 : j ∉ E r0) (hj1 : j ∉ E r1) : v j = w j := by
    have h1 : (u + r1.1 • v) j = c r1 j := hE_agree r1 j hj1
    have h0 : (u + r0.1 • v) j = c r0 j := hE_agree r0 j hj0
    simpa [w, Pi.smul_apply, Pi.sub_apply] using
      direction_eq_of_two_affine_values
        (by simpa [Pi.add_apply, Pi.smul_apply] using h0)
        (by simpa [Pi.add_apply, Pi.smul_apply] using h1) (sub_ne_zero.mp hr10)
  -- Define the base codeword so that `c r = cBase + r•w`.
  let cBase : ι → F := c r0 - r0.1 • w
  have hcBase_mem : cBase ∈ CRS := by
    have hc0 : c r0 ∈ CRS := hc_mem r0
    exact Submodule.sub_mem CRS hc0 (Submodule.smul_mem CRS _ hw_mem)
  -- Rewrite each decoded codeword in affine form and show agreement outside its disagreement set.
  have h_codeword_eq (r : RS) : c r = cBase + r.1 • w := by
    by_cases hr0 : r = r0
    · subst hr0
      simp [cBase]
    · have hneq : (r.1 - r0.1) ≠ 0 := sub_ne_zero.mpr (by
        intro h
        apply hr0
        ext
        exact h)
      let w0r : ι → F := (r.1 - r0.1)⁻¹ • (c r - c r0)
      have hw0r_mem : w0r ∈ CRS := by
        have hcr : c r ∈ CRS := hc_mem r
        have hc0 : c r0 ∈ CRS := hc_mem r0
        exact Submodule.smul_mem CRS _ (Submodule.sub_mem CRS hcr hc0)
      have hw0r_eq : w0r = w := by
        apply Code.eq_of_lt_dist (C := C)
        · exact hw0r_mem
        · exact hw_mem
        · have hdist : Δ₀(w0r, w) ≤ (E r0 ∪ E r1 ∪ E r).card := by
            refine hamming_dist_le_of_subset_disagree (ι := ι) (u := w0r) (v := w)
              (D := E r0 ∪ E r1 ∪ E r) ?_
            intro i hi
            by_contra hiU
            have hi0 : i ∉ E r0 := by
              intro hi0
              apply hiU
              exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hi0)))
            have hi1 : i ∉ E r1 := by
              intro hi1
              apply hiU
              exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hi1)))
            have hir : i ∉ E r := by
              intro hir
              apply hiU
              exact Finset.mem_union.2 (Or.inr hir)
            have hvw : v i = w i := hv_eq_w_of_notin (j := i) hi0 hi1
            have hv0r : v i = w0r i := by
              have hr_eq : (u + r.1 • v) i = c r i := hE_agree r i hir
              have hr0_eq : (u + r0.1 • v) i = c r0 i := hE_agree r0 i hi0
              simpa [w0r, Pi.smul_apply, Pi.sub_apply] using
                direction_eq_of_two_affine_values
                  (by simpa [Pi.add_apply, Pi.smul_apply] using hr0_eq)
                  (by simpa [Pi.add_apply, Pi.smul_apply] using hr_eq) (sub_ne_zero.mp hneq)
            exact hi (hv0r.symm.trans hvw)
          have hcard_le : (E r0 ∪ E r1 ∪ E r).card ≤ 3 * e := by
            have h01 :
                (E r0 ∪ E r1).card ≤ (E r0).card + (E r1).card :=
              Finset.card_union_le _ _
            have hUnion : (E r0 ∪ E r1 ∪ E r).card ≤ (E r0 ∪ E r1).card + (E r).card :=
              Finset.card_union_le _ _
            have hUnion' :
                (E r0 ∪ E r1 ∪ E r).card ≤
                  (E r0).card + (E r1).card + (E r).card := by
              calc
                (E r0 ∪ E r1 ∪ E r).card ≤ (E r0 ∪ E r1).card + (E r).card := hUnion
                _ ≤ ((E r0).card + (E r1).card) + (E r).card := Nat.add_le_add_right h01 _
                _ = (E r0).card + (E r1).card + (E r).card := by omega
            have hE0 : (E r0).card ≤ e := hE_card r0
            have hE1 : (E r1).card ≤ e := hE_card r1
            have hEr : (E r).card ≤ e := hE_card r
            have hSum : (E r0).card + (E r1).card + (E r).card ≤ e + e + e :=
              Nat.add_le_add (Nat.add_le_add hE0 hE1) hEr
            have : (E r0 ∪ E r1 ∪ E r).card ≤ e + e + e := le_trans hUnion' hSum
            have : (E r0 ∪ E r1 ∪ E r).card ≤ 3 * e := by omega
            exact this
          have : Δ₀(w0r, w) ≤ 3 * e := le_trans hdist hcard_le
          exact lt_of_le_of_lt this h3e_lt
      have hdiff : c r - c r0 = (r.1 - r0.1) • w := by
        have hsmul : (r.1 - r0.1) • w0r = (r.1 - r0.1) • w := by simp [hw0r_eq]
        simpa [w0r, smul_smul, hneq] using hsmul
      ext i
      have hdiff_i : c r i - c r0 i = (r.1 - r0.1) * w i := by
        have := congrArg (fun f ↦ f i) hdiff
        simpa [Pi.sub_apply, Pi.smul_apply] using this
      have hcri : c r i = (r.1 - r0.1) * w i + c r0 i := (sub_eq_iff_eq_add).1 hdiff_i
      simp [hcri, cBase, Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
      ring
  have h_line_eq (r : RS) (j : ι) (hj : j ∉ E r) :
      (u + r.1 • v) j = (cBase + r.1 • w) j := by
    have hu : (u + r.1 • v) j = c r j := hE_agree r j hj
    have hc : c r j = (cBase + r.1 • w) j := by
      simp [h_codeword_eq (r := r), Pi.add_apply, Pi.smul_apply]
    simpa [hc] using hu
  -- The global disagreement set where `u` or `v` fail to match `cBase`/`w`.
  let D : Finset ι := Finset.filter (fun j ↦ u j ≠ cBase j ∨ v j ≠ w j) Finset.univ
  have hD_card : D.card ≤ e := by
    -- For `j ∈ D`, at most one good scalar can avoid `E r` at coordinate `j`.
    have h_err_ge (j : ι) (hj : j ∈ D) :
        (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card ≥ Fintype.card RS - 1 := by
      have hclean_le1 : (Finset.filter (fun r : RS ↦ j ∉ E r) Finset.univ).card ≤ 1 := by
        by_contra hgt
        have hone :
            1 < (Finset.filter (fun r : RS ↦ j ∉ E r) Finset.univ).card :=
          lt_of_not_ge hgt
        rcases Finset.one_lt_card.mp hone with ⟨r, hr, s, hs, hrs⟩
        have hr' : j ∉ E r := (Finset.mem_filter.mp hr).2
        have hs' : j ∉ E s := (Finset.mem_filter.mp hs).2
        have hr_eq : (u + r.1 • v) j = (cBase + r.1 • w) j := h_line_eq r j hr'
        have hs_eq : (u + s.1 • v) j = (cBase + s.1 • w) j := h_line_eq s j hs'
        have hrs_val : r.1 ≠ s.1 := by
          intro h
          apply hrs
          ext
          exact h
        -- Solve the two linear equations to get `u j = cBase j` and `v j = w j`.
        have hvw : v j = w j := by
          have hrj : u j + r.1 * v j = cBase j + r.1 * w j := by
            simpa [Pi.add_apply, Pi.smul_apply] using hr_eq
          have hsj : u j + s.1 * v j = cBase j + s.1 * w j := by
            simpa [Pi.add_apply, Pi.smul_apply] using hs_eq
          exact directions_eq_of_two_affine_values hrj hsj hrs_val
        have hu_eq : u j = cBase j := by
          have hrj : u j + r.1 * v j = cBase j + r.1 * w j := by
            simpa [Pi.add_apply, Pi.smul_apply] using hr_eq
          have : u j + r.1 * v j = cBase j + r.1 * v j := by simpa [hvw] using hrj
          exact add_right_cancel this
        have hjD : u j ≠ cBase j ∨ v j ≠ w j := by
          have : j ∈ D := hj
          have : u j ≠ cBase j ∨ v j ≠ w j := by simpa [D] using (Finset.mem_filter.mp this).2
          exact this
        cases hjD with
        | inl hu_ne => exact (hu_ne hu_eq).elim
        | inr hv_ne => exact (hv_ne hvw).elim
      have hclean :
          (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card =
            Fintype.card RS - (Finset.filter (fun r : RS ↦ j ∉ E r) Finset.univ).card := by
        classical
        set a : ℕ := (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card
        set b : ℕ := (Finset.filter (fun r : RS ↦ j ∉ E r) Finset.univ).card
        have hpart : a + b = Fintype.card RS := by
          simpa [a, b, Finset.card_univ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset RS))
              (p := fun r : RS ↦ j ∈ E r))
        have hab : a = Fintype.card RS - b := by
          -- Subtract `b` from both sides of `hpart`.
          have := congrArg (fun t ↦ t - b) hpart
          simpa [Nat.add_sub_cancel] using this
        simpa [a, b] using hab
      have h_err :
          (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card ≥ Fintype.card RS - 1 := by
        have hle := hclean_le1
        have hsub :
            Fintype.card RS - (Finset.filter (fun r : RS ↦ j ∉ E r) Finset.univ).card ≥
              Fintype.card RS - 1 := by
          have : (Finset.filter (fun r : RS ↦ j ∉ E r) Finset.univ).card ≤ 1 := hle
          exact Nat.sub_le_sub_left this _
        simpa [hclean] using hsub
      exact h_err
    have h_pairs_le :
        (∑ j ∈ D, (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card) ≤
          Fintype.card RS * e := by
      -- Each `E r` has size `≤ e`, so sum over `r` bounds the total incidence count.
      have h_pairs_le' :
          (∑ j ∈ (Finset.univ : Finset ι),
                (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card) ≤
            Fintype.card RS * e := by
        classical
        -- Count pairs `(r,j)` with `j ∈ E r` in two ways.
        let pairs : Finset (Sigma (fun _ : RS ↦ ι)) :=
          Finset.filter (fun p : Sigma (fun _ : RS ↦ ι) ↦ p.2 ∈ E p.1) Finset.univ
        have h_pairs_ge :
            pairs.card =
              ∑ j ∈ (Finset.univ : Finset ι),
                (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card := by
          classical
          -- Use fiberwise counting on `p ↦ p.2`.
          let f : (Sigma (fun _ : RS ↦ ι)) → ι := fun p ↦ p.2
          have hf :
              (pairs : Set (Sigma (fun _ : RS ↦ ι))).MapsTo f
                (Finset.univ : Finset ι) := by
            intro _ _; simp
          have hcard_fiber := Finset.card_eq_sum_card_fiberwise (f := f) (s := pairs)
            (t := (Finset.univ : Finset ι)) hf
          have hfiber (j : ι) :
              {p ∈ pairs | f p = j}.card =
                (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card := by
            classical
            let emb : RS ↪ Sigma (fun _ : RS ↦ ι) :=
              ⟨fun r ↦ ⟨r, j⟩, by
                intro a b h
                simpa using congrArg Sigma.fst h⟩
            have :
                Finset.filter (fun p : Sigma (fun _ : RS ↦ ι) ↦ p.2 = j) pairs =
                  (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).map emb := by
              ext p
              rcases p with ⟨r, i⟩
              have h :
                  (i ∈ E r ∧ i = j) ↔ (j ∈ E r ∧ j = i) := by
                constructor
                · intro h
                  refine ⟨?_, h.2.symm⟩
                  simpa [h.2] using h.1
                · intro h
                  refine ⟨?_, h.2.symm⟩
                  simpa [h.2] using h.1
              simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_map, emb]
              constructor
              · rintro ⟨hir, rfl⟩
                exact ⟨r, hir, rfl⟩
              · rintro ⟨a, hja, ha⟩
                have har : a = r := congrArg Sigma.fst ha
                have hji : j = i := congrArg Sigma.snd ha
                subst a
                subst i
                exact ⟨hja, rfl⟩
            have hmap :
                {p ∈ pairs | f p = j} =
                  Finset.filter (fun p : Sigma (fun _ : RS ↦ ι) ↦ p.2 = j) pairs := by
              ext p
              simp [f]
            simp [hmap, this]
          have hpairs_sum :
              pairs.card = ∑ j ∈ (Finset.univ : Finset ι),
                (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card := by
            classical
            simpa [hfiber] using hcard_fiber
          simp [hpairs_sum]
        -- Bound `pairs.card` by summing `|E r|`.
        have h_pairs_card :
            pairs.card ≤ ∑ r : RS, (E r).card := by
          classical
          -- Fiberwise count on `p ↦ p.1`.
          let g : (Sigma (fun _ : RS ↦ ι)) → RS := fun p ↦ p.1
          have hg :
              (pairs : Set (Sigma (fun _ : RS ↦ ι))).MapsTo g
                (Finset.univ : Finset RS) := by
            intro _ _; simp
          have hcard_fiber := Finset.card_eq_sum_card_fiberwise (f := g) (s := pairs)
            (t := (Finset.univ : Finset RS)) hg
          have hfiber (r : RS) :
              {p ∈ pairs | g p = r}.card = (E r).card := by
            classical
            let emb : ι ↪ Sigma (fun _ : RS ↦ ι) :=
              ⟨fun j ↦ ⟨r, j⟩, by
                intro a b h
                simpa using congrArg Sigma.snd h⟩
            have :
                Finset.filter (fun p : Sigma (fun _ : RS ↦ ι) ↦ p.1 = r) pairs =
                  (E r).map emb := by
              ext p
              rcases p with ⟨r', i⟩
              by_cases hrr : r' = r
              · subst hrr
                simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and,
                  Finset.mem_map, emb]
                constructor
                · rintro ⟨hi, _⟩
                  exact ⟨i, hi, rfl⟩
                · rintro ⟨a, ha, hai⟩
                  have hia : a = i := congrArg Sigma.snd hai
                  subst a
                  exact ⟨ha, trivial⟩
              · constructor
                · intro hp
                  exfalso
                  exact hrr (Finset.mem_filter.mp hp).2
                · intro hp
                  exfalso
                  rcases Finset.mem_map.1 hp with ⟨j, hj, hjp⟩
                  have : r = r' := congrArg Sigma.fst hjp
                  exact hrr this.symm
            have hmap :
                {p ∈ pairs | g p = r} =
                  Finset.filter (fun p : Sigma (fun _ : RS ↦ ι) ↦ p.1 = r) pairs := by
              ext p
              simp [g]
            simp [hmap, this]
          -- Replace the sum of fiber cards by `∑ r, |E r|`.
          have hpairs_sum :
              pairs.card = ∑ r ∈ (Finset.univ : Finset RS), (E r).card := by
            classical
            simpa [hfiber] using hcard_fiber
          -- Drop the membership binder.
          simp [hpairs_sum]
        have hsumE : (∑ r : RS, (E r).card) ≤ Fintype.card RS * e := by
          classical
          have : ∀ r : RS, (E r).card ≤ e := fun r ↦ hE_card r
          calc
            (∑ r : RS, (E r).card) ≤ ∑ r : RS, e := by
              exact Finset.sum_le_sum (by intro r _; exact this r)
            _ = Fintype.card RS * e := by
              simp [Finset.card_univ]
        have hpairs_le : pairs.card ≤ Fintype.card RS * e := le_trans h_pairs_card hsumE
        -- Rewrite the LHS using the alternate counting of `pairs`.
        simpa [h_pairs_ge] using hpairs_le
      -- Restricting the sum to `D` only decreases it.
      have hsum_le :
          (∑ j ∈ D, (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card)
            ≤ ∑ j ∈ (Finset.univ : Finset ι),
              (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card := by
        refine
          Finset.sum_le_sum_of_subset_of_nonneg (s := D) (t := (Finset.univ : Finset ι)) ?_ ?_
        · intro j hj
          simp
        · intro _ _ _
          exact Nat.zero_le _
      exact le_trans hsum_le h_pairs_le'
    have h_pairs_ge :
        (∑ j ∈ D, (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card) ≥
          D.card * (Fintype.card RS - 1) := by
      classical
      -- Each term is at least `card RS - 1`.
      have hterm : ∀ j ∈ D,
          (Fintype.card RS - 1) ≤ (Finset.filter (fun r : RS ↦ j ∈ E r) Finset.univ).card :=
        fun j hj ↦ by simpa using (h_err_ge j hj)
      have := Finset.sum_le_sum hterm
      -- Rewrite the LHS as `D.card * (card RS - 1)`.
      simpa [Finset.sum_const_nat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    -- Conclude `D.card ≤ e` by arithmetic.
    by_contra hD_gt
    have hD_ge : e + 1 ≤ D.card := Nat.succ_le_of_lt (lt_of_not_ge hD_gt)
    have hRS_one_le : 1 ≤ Fintype.card RS := Nat.one_le_of_lt hRS_one_lt
    have hdist_le : ‖C‖₀ ≤ Fintype.card RS - 1 := by
      have : ‖C‖₀ ≤ (Fintype.card RS).pred := Nat.le_pred_of_lt hRS_gt
      simpa [Nat.pred_eq_sub_one] using this
    have h3e_lt_RS : 3 * e < Fintype.card RS - 1 := lt_of_lt_of_le h3e_lt hdist_le
    have he_le_3e : e ≤ 3 * e := Nat.le_mul_of_pos_left (n := 3) e (by decide)
    have he_lt_RS : e < Fintype.card RS - 1 := lt_of_le_of_lt he_le_3e h3e_lt_RS
    have hmul_lt : Fintype.card RS * e < (e + 1) * (Fintype.card RS - 1) := by
      have hmulRS : e * (Fintype.card RS) = e * (Fintype.card RS - 1) + e := by
        have h :
            (Fintype.card RS) = Fintype.card RS - 1 + 1 := (Nat.sub_add_cancel hRS_one_le).symm
        rw [h]
        simp [Nat.mul_add]
      have hmulS :
          (e + 1) * (Fintype.card RS - 1) =
            e * (Fintype.card RS - 1) + (Fintype.card RS - 1) := by
        rw [Nat.add_one]
        simpa using Nat.succ_mul e (Fintype.card RS - 1)
      have hlt :
          e * (Fintype.card RS - 1) + e <
            e * (Fintype.card RS - 1) + (Fintype.card RS - 1) :=
        Nat.add_lt_add_left he_lt_RS _
      have : e * (Fintype.card RS) < (e + 1) * (Fintype.card RS - 1) := by
        have hlt' :
            e * (Fintype.card RS - 1) + e < (e + 1) * (Fintype.card RS - 1) := by
          simpa [hmulS] using hlt
        simpa [hmulRS] using hlt'
      simpa [Nat.mul_comm] using this
    have hle : (e + 1) * (Fintype.card RS - 1) ≤ Fintype.card RS * e := by
      have h1 : (e + 1) * (Fintype.card RS - 1) ≤ D.card * (Fintype.card RS - 1) :=
        Nat.mul_le_mul_right _ hD_ge
      have h2 : D.card * (Fintype.card RS - 1) ≤ Fintype.card RS * e := by
        exact le_trans h_pairs_ge h_pairs_le
      exact le_trans h1 h2
    exact (not_lt_of_ge hle) hmul_lt
  refine ⟨cBase, hcBase_mem, w, hw_mem, D, hD_card, fun j hj ↦ ?_⟩
  simpa [D, not_or] using hj

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

/-- If an affine line has too many `e`-close points to the Reed–Solomon code, then its direction
is itself `e`-close to the code. -/
lemma dir_close_of_many_close_pts
    {deg : ℕ}
    {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
    (h_many : numberOfClosePts u v deg α e > ‖(RScodeSet α deg)‖₀) :
    Δ₀(v, ReedSolomon.code α deg) ≤ e := by
  obtain ⟨_, _, w, hw_mem, D, hD_card, hagree⟩ :=
    exists_codewords_agree_of_many_close_scalars (ReedSolomon.code α deg)
      (three_mul_lt_of_lt_div_three he)
      (lt_of_lt_of_le h_many numberOfClosePts_le_natCard_close_scalars)
  have hdist_vw : Δ₀(v, w) ≤ D.card :=
    hamming_dist_le_of_subset_disagree D fun j hj ↦ by
      by_contra hjD
      exact hj (hagree j hjD).2
  exact le_trans (Code.distFromCode_le_dist_to_mem _ _ hw_mem)
    (by exact_mod_cast le_trans hdist_vw hD_card)

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
  -- If `d = |F|`, the RHS is `1`, so the bound is trivial.
  by_cases hd : d = Fintype.card F
  · have h_triv :
        Pr{let w_star ← $ᵗ (Matrix.rowSpan U_star)}[Δ₀(w_star, RS) ≤ e] ≤ 1 :=
      prEvent_le_one ($ᵗ (Matrix.rowSpan U_star))
        (fun w_star ↦ Δ₀(w_star, RS) ≤ e)
    have hF_ne_zero : (Fintype.card F : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := F))
    have hRHS : (d : ENNReal) / Fintype.card F = 1 := by
      simpa [d, hd, hF_ne_zero] using (ENNReal.div_self hF_ne_zero)
    simpa [hRHS, d, RS] using h_triv
  -- Otherwise, `d < |F|`. We count bad points by partitioning the row-span into affine lines.
  have hd_le_n : d ≤ Fintype.card ι := by
    calc
      d = ‖RScodeSet α deg‖₀ := by simp [d, RS]
      _ ≤ Fintype.card ι := Code.dist_le_card (C := RScodeSet α deg)
  have hd_le : d ≤ Fintype.card F := by
    exact le_trans hd_le_n (Fintype.card_le_of_embedding α)
  have hd_lt : d < Fintype.card F := lt_of_le_of_ne hd_le hd
  have h3e_lt_d : 3 * e < d := three_mul_lt_of_lt_div_three he
  have he_lt_d : e < d := by
    have he_le_3e : e ≤ 3 * e := Nat.le_mul_of_pos_left (n := 3) e (by decide)
    exact lt_of_le_of_lt he_le_3e h3e_lt_d
  have hF : Fintype.card F > e := lt_of_lt_of_le he_lt_d hd_le
  obtain ⟨v_star, hv_mem, hv_far⟩ :=
    dist_interleaved_code_to_code_lb (F := F) (ι := ι) (κ := κ) (L := ReedSolomon.code α deg)
      (U_star := U_star) hF (by simpa [RS, RScodeSet] using he) hU
  have hv_ne_zero : v_star ≠ 0 := by
    intro hv0
    have h0_in : (0 : ι → F) ∈ (ReedSolomon.code α deg : Set (ι → F)) :=
      Submodule.zero_mem (ReedSolomon.code α deg)
    have hdist0 : Δ₀(v_star, (ReedSolomon.code α deg : Set (ι → F))) = 0 := by
      rw [hv0]
      exact (Code.distFromCode_eq_zero_iff_mem _ _).2 h0_in
    have hv_far' : ((e : ℕ∞) < 0) := by
      rwa [hdist0] at hv_far
    exact (not_lt_zero (a := (e : ℕ∞))) hv_far'
  let S : Submodule F (ι → F) := Matrix.rowSpan U_star
  let vDir : S := ⟨v_star, hv_mem⟩
  have hvDir_ne_zero : vDir ≠ 0 := by
    intro h
    apply hv_ne_zero
    have : (vDir : ι → F) = 0 := congrArg Subtype.val h
    simpa [vDir] using this
  -- Partition `S` into cosets of the 1D submodule `V = span{vDir}`.
  let V : Submodule F S := Submodule.span F ({vDir} : Set S)
  let Q : Type := S ⧸ V
  let π : S → Q := fun w ↦ V.mkQ w
  have hπ_surj : Function.Surjective π := by
    intro q
    rcases V.mkQ_surjective q with ⟨w, hw⟩
    exact ⟨w, hw⟩
  classical
  choose rep hrep using hπ_surj
  have hcardV : Fintype.card V = Fintype.card F := by
    classical
    -- `r ↦ r • vDir` is a bijection `F ≃ V` because `vDir ≠ 0`.
    let g : F → V :=
      fun r ↦
        ⟨r • vDir,
          Submodule.smul_mem V r (Submodule.subset_span (by simp))⟩
    have hg_surj : Function.Surjective g := by
      intro x
      rcases (Submodule.mem_span_singleton.mp x.property) with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      apply Subtype.ext
      exact hr
    have hg_inj : Function.Injective g := by
      intro r₁ r₂ hr
      have hmul : r₁ • vDir = r₂ • vDir := congrArg Subtype.val hr
      have hsub : (r₁ - r₂) • vDir = 0 := by
        have : r₁ • vDir - r₂ • vDir = 0 := sub_eq_zero.mpr hmul
        calc
          (r₁ - r₂) • vDir = r₁ • vDir - r₂ • vDir := sub_smul r₁ r₂ vDir
          _ = 0 := this
      -- Pick a coordinate where `v_star` is nonzero and cancel.
      have hex : ∃ j, v_star j ≠ 0 := by
        by_contra h
        apply hv_ne_zero
        funext j
        by_contra hj
        exact h ⟨j, hj⟩
      rcases hex with ⟨j, hj⟩
      have hj' : (vDir : ι → F) j ≠ 0 := by simpa [vDir] using hj
      have : (r₁ - r₂) = 0 := by
        have hcoord :
            ((r₁ - r₂) • (vDir : S) : ι → F) j = ((0 : S) : ι → F) j := by
          simpa using congrArg (fun f : S ↦ (f : ι → F) j) hsub
        have hmul0 : (r₁ - r₂) * (vDir : ι → F) j = 0 := by
          simpa [Pi.smul_apply] using hcoord
        have hmul' : (r₁ - r₂) * (vDir : ι → F) j = 0 * (vDir : ι → F) j := by
          simpa using hmul0
        exact mul_right_cancel₀ hj' hmul'
      exact sub_eq_zero.mp this
    have hg_bij : Function.Bijective g := ⟨hg_inj, hg_surj⟩
    -- Convert bijection to a card equality.
    simpa using (Fintype.card_congr (Equiv.ofBijective g hg_bij)).symm
  have hcardS : Fintype.card S = Fintype.card V * Fintype.card Q := by
    simpa [Q] using (Submodule.card_eq_card_quotient_mul_card (S := V) (M := S) (R := F))
  -- Count bad points fiberwise over the quotient map `π`.
  let Pbad : S → Prop := fun w ↦ Δ₀((w : ι → F), RS) ≤ e
  let bad : Finset S := Finset.filter Pbad Finset.univ
  have hbad_sum :
      bad.card =
        ∑ q ∈ (Finset.univ : Finset Q), (Finset.filter (fun w : S ↦ π w = q) bad).card := by
    classical
    have hmaps : (bad : Set S).MapsTo π (Finset.univ : Finset Q) := by
      intro _ _
      simp
    simpa using
      (Finset.card_eq_sum_card_fiberwise (f := π) (s := bad) (t := (Finset.univ : Finset Q)) hmaps)
  have hfiber_le : ∀ q : Q, (Finset.filter (fun w : S ↦ π w = q) bad).card ≤ d := by
    intro q
    -- Compare the fiber to close points on the affine line through `rep q` in direction `v_star`.
    let u0 : ι → F := (rep q : S)
    have hu0 : π (rep q) = q := hrep q
    have hclose_le :
        (Finset.filter (fun w : S ↦ π w = q) bad).card ≤
          numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e := by
      -- Inject the fiber into `closePtsOnAffineLine`.
      let fiber : Type := {w : S // Pbad w ∧ π w = q}
      have hfiber_card :
          (Finset.filter (fun w : S ↦ π w = q) bad).card = Fintype.card fiber := by
        classical
        -- Turn nested filters into one filter on `Finset.univ`.
        have hfilter :
            Finset.filter (fun w : S ↦ π w = q) bad =
              Finset.filter (fun w : S ↦ Pbad w ∧ π w = q) Finset.univ := by
          ext w
          constructor
          · intro hw
            have hw_bad : w ∈ bad := (Finset.mem_filter.mp hw).1
            have hw_pi : π w = q := (Finset.mem_filter.mp hw).2
            have hw_Pbad : Pbad w := (Finset.mem_filter.mp hw_bad).2
            refine Finset.mem_filter.mpr ?_
            refine ⟨by simp, ?_⟩
            exact ⟨hw_Pbad, hw_pi⟩
          · intro hw
            have hwP : Pbad w ∧ π w = q := (Finset.mem_filter.mp hw).2
            have hw_Pbad : Pbad w := hwP.1
            have hw_pi : π w = q := hwP.2
            refine Finset.mem_filter.mpr ?_
            refine ⟨?_, hw_pi⟩
            refine Finset.mem_filter.mpr ?_
            exact ⟨by simp, hw_Pbad⟩
        rw [hfilter]
        exact (Fintype.card_subtype (α := S) (p := fun w : S ↦ Pbad w ∧ π w = q)).symm
      have hcard_le_nat :
          Fintype.card fiber ≤ numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e := by
        -- Use `Nat.card` to avoid choosing a `Fintype` instance for the close-point set.
        let f : fiber → closePtsOnAffineLine (F := F) (u := u0) (v := v_star)
            (deg := deg) (α := α) (e := e) :=
          fun w ↦
            ⟨(w.1 : ι → F), by
                refine ⟨?_, ?_⟩
                · -- membership in the affine line: `w - rep q ∈ V`.
                  have hwq : π w.1 = π (rep q) := by
                    calc
                      π w.1 = q := w.2.2
                      _ = π (rep q) := hu0.symm
                  have hdiff_mem : w.1 - rep q ∈ V := by
                    have :
                        (Submodule.Quotient.mk w.1 : S ⧸ V) = Submodule.Quotient.mk (rep q) := by
                      simpa [π, Submodule.mkQ_apply] using hwq
                    exact (Submodule.Quotient.eq (p := V)).1 this
                  rcases (Submodule.mem_span_singleton.mp hdiff_mem) with ⟨r, hr⟩
                  refine
                    (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u0) (direction := v_star)
                        (x := (w.1 : ι → F))).2 ?_
                  refine ⟨r, ?_⟩
                  have hw1 : w.1 = rep q + r • vDir := by
                    have hsub : w.1 - rep q = r • vDir := hr.symm
                    have hw1' : w.1 = r • vDir + rep q := (sub_eq_iff_eq_add.mp hsub)
                    simpa [add_comm, add_left_comm, add_assoc] using hw1'
                  -- Coerce the equality in `S` to an equality in `ι → F`.
                  ext i
                  have := congrArg (fun x : S ↦ (x : ι → F) i) hw1
                  simpa [u0, vDir, Pi.add_apply, Pi.smul_apply] using this
                · -- closeness to the code.
                  simpa [Pbad, RS] using w.2.1⟩
        have hf_inj : Function.Injective f := by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg
            (fun x :
                closePtsOnAffineLine (F := F) (u := u0) (v := v_star) (deg := deg) (α := α)
                  (e := e) ↦
              (x : ι → F))
            hab
        have hnat :
            Nat.card fiber ≤ Nat.card (closePtsOnAffineLine (F := F) (u := u0) (v := v_star)
              (deg := deg) (α := α) (e := e)) :=
          Nat.card_le_card_of_injective f hf_inj
        have hnum :
            numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e =
              Nat.card
                (closePtsOnAffineLine (F := F) (u := u0) (v := v_star) (deg := deg) (α := α)
                  (e := e)) := by
          exact number_of_close_pts_eq_nat_card (F := F) (ι := ι) u0 v_star deg α e
        have hcard_fiber : Fintype.card fiber = Nat.card fiber := by
          exact (Fintype.card_eq_nat_card (α := fiber))
        -- Convert back to `Fintype.card` / `numberOfClosePts`.
        calc
          Fintype.card fiber = Nat.card fiber := hcard_fiber
          _ ≤ Nat.card
                (closePtsOnAffineLine (F := F) (u := u0) (v := v_star) (deg := deg) (α := α)
                  (e := e)) :=
            hnat
          _ = numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e := hnum.symm
      -- Convert to the `Finset` fiber count.
      rw [hfiber_card]
      exact hcard_le_nat
    have hclose_bd : numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e ≤ d := by
      have hline :=
        e_le_dist_over_3_strong (F := F) (ι := ι) (deg := deg) (α := α)
          (e := e) (u := u0) (v := v_star) (by simpa [d, RS, RScodeSet] using he)
      rcases hline with h_all | h_few
      · exfalso
        -- All points close implies `numberOfClosePts > d`, hence `v_star` is close,
        -- contradicting `hv_far`.
        have hnum_ge :
            Fintype.card F ≤ numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e := by
          -- Inject `F` into close points on the line (direction is nonzero).
          have hex : ∃ j, v_star j ≠ 0 := by
            by_contra h
            apply hv_ne_zero
            funext j
            by_contra hj
            exact h ⟨j, hj⟩
          rcases hex with ⟨j, hj⟩
          let g : F → closePtsOnAffineLine (F := F) (u := u0) (v := v_star)
              (deg := deg) (α := α) (e := e) :=
            fun r ↦
              ⟨u0 + r • v_star, by
                  refine ⟨?_, ?_⟩
                  · refine
                      (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u0)
                        (direction := v_star) _).2 ?_
                    exact ⟨r, rfl⟩
                  · apply h_all
                    · refine
                        (Affine.mem_affineLineAtOrigin_iff (F := F) (origin := u0)
                          (direction := v_star) _).2 ?_
                      exact ⟨r, rfl⟩⟩
          have hg_inj : Function.Injective g := by
            intro r₁ r₂ hr
            have hval : u0 + r₁ • v_star = u0 + r₂ • v_star := congrArg Subtype.val hr
            have hmul : r₁ * v_star j = r₂ * v_star j := by
              have := congrArg (fun f : ι → F ↦ f j) hval
              simpa [Pi.add_apply, Pi.smul_apply] using add_left_cancel this
            exact mul_right_cancel₀ hj hmul
          have hnat :
              Nat.card F ≤ Nat.card (closePtsOnAffineLine (F := F) (u := u0) (v := v_star)
                (deg := deg) (α := α) (e := e)) :=
            Nat.card_le_card_of_injective g hg_inj
          have hnum :
              numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e =
                Nat.card
                  (closePtsOnAffineLine (F := F) (u := u0) (v := v_star) (deg := deg) (α := α)
                    (e := e)) := by
            exact number_of_close_pts_eq_nat_card (F := F) (ι := ι) u0 v_star deg α e
          have hcardF : Fintype.card F = Nat.card F := by
            exact (Fintype.card_eq_nat_card (α := F))
          calc
            Fintype.card F = Nat.card F := hcardF
            _ ≤ Nat.card
                  (closePtsOnAffineLine (F := F) (u := u0) (v := v_star) (deg := deg) (α := α)
                    (e := e)) :=
              hnat
            _ = numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e := hnum.symm
        have hnum_gt : numberOfClosePts (F := F) (ι := ι) u0 v_star deg α e > d :=
          lt_of_lt_of_le hd_lt hnum_ge
        have hv_close :
            Δ₀(v_star, ReedSolomon.code α deg) ≤ e :=
          dir_close_of_many_close_pts (F := F) (ι := ι) (deg := deg) (α := α)
            (e := e) (u := u0) (v := v_star) (by simpa [d, RS, RScodeSet] using he)
            (by simpa [d] using hnum_gt)
        exact (not_lt_of_ge hv_close) hv_far
      · simpa [d, RS, RScodeSet] using h_few
    exact le_trans hclose_le hclose_bd
  have hbad_card : (bad.card : ENNReal) ≤ (d * Fintype.card Q : ENNReal) := by
    have hbad_nat : bad.card ≤ d * Fintype.card Q := by
      classical
      -- Sum of fiber sizes.
      have :=
        calc
          bad.card =
              ∑ q ∈ (Finset.univ : Finset Q),
                (Finset.filter (fun w : S ↦ π w = q) bad).card := by
            exact hbad_sum
          _ ≤ ∑ q ∈ (Finset.univ : Finset Q), d := by
            refine Finset.sum_le_sum ?_
            intro q hq
            exact hfiber_le q
          _ = (Finset.univ : Finset Q).card * d := by
            simp
      simpa [Finset.card_univ, Nat.mul_comm] using this
    exact_mod_cast hbad_nat
  -- Convert to a probability bound using native uniformity.
  have hprob :
      Pr{let w_star ← $ᵗ (Matrix.rowSpan U_star)}[Δ₀(w_star, RS) ≤ e] =
        (bad.card : ENNReal) / Fintype.card S := by
    rw [SampleableType.prEvent_uniformSample]
  -- Combine the counting bound with the cardinality decomposition `|S| = |V| * |Q|`.
  have hQ_pos : 0 < Fintype.card Q := by
    have : Nonempty Q := ⟨0⟩
    exact (Fintype.card_pos_iff.mpr this)
  have hQ_ne_zero : (Fintype.card Q : ENNReal) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hQ_pos)
  have hQ_ne_top : (Fintype.card Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top (Fintype.card Q)
  -- `Pr[bad] = |bad|/|S| ≤ (d*|Q|)/(|V|*|Q|) = d/|F|`.
  calc
    Pr{let w_star ← $ᵗ (Matrix.rowSpan U_star)}[Δ₀(w_star, RS) ≤ e] =
        (bad.card : ENNReal) / Fintype.card S := hprob
    _ ≤ (d * Fintype.card Q : ENNReal) / Fintype.card S := by
      exact ENNReal.div_le_div_right hbad_card (Fintype.card S)
    _ = (d * Fintype.card Q : ENNReal) / (Fintype.card V * Fintype.card Q : ℕ) := by
      -- rewrite `|S| = |V| * |Q|`.
      rw [hcardS]
    _ = (d : ENNReal) / Fintype.card V := by
      -- cancel the common factor `|Q|`.
      rw [Nat.cast_mul]
      exact ENNReal.mul_div_mul_right (a := (d : ENNReal)) (b := (Fintype.card V : ENNReal))
        (c := (Fintype.card Q : ENNReal)) hQ_ne_zero hQ_ne_top
    _ = (d : ENNReal) / Fintype.card F := by rw [hcardV]
    _ = (‖RS‖₀ : ENNReal) / Fintype.card F := by rfl
end ProximityToRS
end
