/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.Probability.Notation
/-! # BCIKS20 Reed-Solomon Proximity Gaps -/


namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].
Let `C` be a collection of affine spaces. Then `C` displays a `(δ, ε)`-proximity gap with respect to
a Reed-Solomon code, where `(δ, ε)` are the proximity and error parameters defined up to the
Johnson bound.

The `hε : errorBound δ deg domain < 1` hypothesis is required for the `Xor'` exclusivity in
`δ_ε_proximityGap`: without `ε < 1`, the two branches `Pr = 1` and `Pr ≤ ε` could both hold
when `ε = 1`, violating `Xor'`.

This proof depends on `correlatedAgreement_affine_spaces` (Theorem 1.7) in `AffineSpaces.lean`. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
    (hdeg : 0 < deg)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0}
    (_hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C)
      δ
      (errorBound δ deg domain) := by
  classical
  intro S hS _inst
  obtain ⟨i, rfl⟩ := hS
  -- Let `S` abbreviate the affine-span finset; use for cleaner case analysis.
  set S : Finset (ι → F) := Affine.AffSpanFinset (C i) with hS_def
  -- Case split on whether the proximity probability is ≤ ε.
  by_cases hcase :
      Pr_{let x ← $ᵖ S}[δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ] ≤
        (errorBound δ deg domain : ℝ≥0)
  · -- Right Xor' branch: `Pr ≤ ε ∧ ¬(Pr = 1)`.
    refine Or.inr ⟨hcase, ?_⟩
    intro hPeq1
    rw [hPeq1] at hcase
    -- `hcase : 1 ≤ ε` contradicts `hε : ε < 1`.
    have hε_lt_one_ENN : (errorBound δ deg domain : ENNReal) < (1 : ENNReal) := by
      exact_mod_cast hε
    exact (not_lt_of_ge hcase) hε_lt_one_ENN
  · -- Left Xor' branch: `Pr = 1 ∧ ¬(Pr ≤ ε)`.
    push Not at hcase
    refine Or.inl ⟨?_, not_le.mpr hcase⟩
    -- Goal: `Pr = 1`. Suffices every point of `S` is δ-close to the RS code.
    suffices h_all : ∀ x : ↥S,
        δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ by
      rw [prob_uniform_eq_card_filter_div_card (F := ↥S)
            (P := fun x => δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ)]
      have hfilter :
          Finset.filter (fun x : ↥S =>
              δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ) Finset.univ =
            (Finset.univ : Finset ↥S) := by
        ext x; simpa using h_all x
      rw [hfilter, Finset.card_univ]
      have hcard_pos : (Fintype.card ↥S : ℝ≥0) ≠ 0 := by
        have : Nonempty ↥S := inferInstance
        exact_mod_cast Fintype.card_ne_zero
      exact_mod_cast div_self hcard_pos
    intro xS
    -- Step 1: membership in AffSpanFinset ⇒ membership in linear span of word stack.
    have hx_mem_aff : xS.val ∈ Affine.AffSpanSet (C i) :=
      (Affine.AffSpanSet.instFinite (u := C i)).mem_toFinset.mp xS.property
    -- Step 2: suffices jointAgreement from which #461 concludes proximity.
    suffices hja :
        jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F)))
          (δ := δ) (W := C i) by
      -- `affineSpan_subset_span` + #461 give δ-closeness in the code.
      have hx_in_span : xS.val ∈ (Submodule.span F (Set.range (C i)) : Set (ι → F)) := by
        have : (Finset.univ.image (C i) : Set (ι → F)) = Set.range (C i) := by
          simp [Set.range, Finset.coe_image, Finset.coe_univ]
        rw [← this]
        exact affineSpan_subset_span hx_mem_aff
      have h_prox := jointAgreement_implies_linSpan_proximity
        (C := ReedSolomon.code domain deg) hja xS.val hx_in_span
      -- `toFinset` coerces to the same Set.
      convert h_prox using 2
      simp [ReedSolomon.toFinset]
    -- Step 3: obtain jointAgreement from Thm 1.7 via sampling bridge.
    -- Case split: k = 1 (singleton, direct) vs k ≥ 2 (Thm 1.7 chain).
    by_cases hk1 : k = 1
    · -- k = 1: AffSpanFinset is a singleton {C i 0}. Pr > ε forces the event,
      -- giving individual δ-closeness → jointAgreement for a Fin 1 word stack.
      subst hk1
      -- Every element of AffSpanSet (C i) equals C i 0 when k = 1 (affine span of singleton).
      have himg : (Finset.univ : Finset (Fin 1)).image (C i) = {C i 0} := by
        ext y; simp [Fin.eq_zero]
      have hmem_eq : ∀ x ∈ Affine.AffSpanSet (C i), x = C i 0 := by
        intro x (hx : x ∈ (affineSpan F (↑(Finset.univ.image (C i)))).carrier)
        rw [himg, Finset.coe_singleton] at hx
        change x ∈ affineSpan F ({C i 0} : Set (ι → F)) at hx
        rwa [AffineSubspace.mem_affineSpan_singleton] at hx
      -- C i 0 is δ-close to the RS code: extract from hcase via Pr > 0 on singleton.
      have hCi0_close :
          δᵣ(C i 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
        by_contra hnotclose
        push Not at hnotclose
        -- All elements of S equal C i 0, which is NOT δ-close, so Pr = 0.
        have hPr_eq :
            Pr_{let x ← $ᵖ S}[δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ] = 0 := by
          rw [prob_uniform_eq_card_filter_div_card (F := ↥S)
            (P := fun x => δᵣ(x.val, (ReedSolomon.toFinset domain deg : Set _)) ≤ δ)]
          have : (Finset.univ : Finset ↥S).filter
              (fun x : ↥S => δᵣ(x.val,
                (ReedSolomon.toFinset domain deg : Set _)) ≤ δ) = ∅ := by
            apply Finset.filter_false_of_mem
            intro ⟨x, hx⟩ _
            have hx_eq := hmem_eq x
              ((Affine.AffSpanSet.instFinite (u := C i)).mem_toFinset.mp hx)
            subst hx_eq
            intro hclose
            exact absurd (by convert hclose using 2; simp [ReedSolomon.toFinset])
              (not_le.mpr hnotclose)
          rw [this, Finset.card_empty, Nat.cast_zero]
          simp
        rw [hPr_eq] at hcase
        exact absurd hcase (not_lt.mpr (zero_le _))
      -- Construct jointAgreement from the close codeword witness.
      obtain ⟨v₀, hv₀_mem, hv₀_dist⟩ :=
        (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (C i 0) δ).mp hCi0_close
      obtain ⟨S', hS'_card, hS'_agree⟩ :=
        (Code.relCloseToWord_iff_exists_agreementCols (C i 0) v₀ δ).mp hv₀_dist
      exact ⟨S',
        (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S'.card δ).mp hS'_card,
        fun _ => v₀, fun j => ⟨hv₀_mem, fun col hcol =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [show j = 0 from Fin.eq_zero j]
            exact ((hS'_agree col).1 hcol).symm⟩⟩⟩
    · -- k ≥ 2: Apply Thm 1.7 via reindexing + sampling bridge.
      -- Write k = m + 2 so that k - 1 = m + 1 avoids Fin casting.
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by have := NeZero.pos k; omega⟩
      -- Reindex: u' 0 = C i 0, u' j.succ = C i j.succ - C i 0.
      -- This makes u' 0 + ∑ r j • u' j.succ parametrize affineSpan F (range (C i)).
      let u' : Fin (m + 2) → ι → F := fun j =>
        if j = 0 then C i 0 else C i j - C i 0
      -- Sampling bridge: convert Pr on AffSpanFinset S to Pr on affineSubspaceAtOrigin.
      -- Both are uniform distributions over the same affine subspace, just presented
      -- as different Lean types (Finset subtype vs AffineSubspace subtype).
      -- Step 1: Show the two affine subspaces have the same carrier set.
      -- Sampling bridge: show affineSubspaceAtOrigin = affineSpan, then transfer Pr.
      -- Step 1: AffineSubspace equality.
      have haff_eq : Affine.affineSubspaceAtOrigin (F := F) (u' 0) (Fin.tail u') =
          affineSpan F (↑(Finset.univ.image (C i)) : Set (ι → F)) := by
        unfold Affine.affineSubspaceAtOrigin u'
        simp only [ite_true]
        have hp0 : C i 0 ∈ affineSpan F
            (↑(Finset.univ.image (C i)) : Set (ι → F)) := by
          apply subset_affineSpan; simp
        rw [← AffineSubspace.mk'_eq hp0, direction_affineSpan,
          vectorSpan_eq_span_vsub_set_right (k := F)
            (by simp : C i 0 ∈ ↑(Finset.univ.image (C i)))]
        congr 1
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
          Finset.coe_image, Finset.coe_univ, Set.image_univ]
        have hvsub : (· -ᵥ C i 0) '' Set.range (C i) =
            Set.range (fun j : Fin (m + 2) => C i j - C i 0) := by
          ext v; simp [vsub_eq_sub]
        rw [hvsub]
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro v hv; obtain ⟨j, rfl⟩ := hv
          exact Submodule.subset_span ⟨j.succ,
            by simp [Fin.tail]⟩
        · apply Submodule.span_le.mpr
          intro v hv; obtain ⟨j, rfl⟩ := hv
          by_cases hj0 : j = 0
          · simp only [hj0, sub_self]; exact Submodule.zero_mem _
          · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
            apply Submodule.subset_span
            exact ⟨j', by simp [Fin.tail]⟩
      -- Step 2: Transfer the probability.
      have hPr_aff :
          Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F)
            (u' 0) (Fin.tail u'))}[
            δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] >
          (errorBound δ deg domain : ℝ≥0) := by
        have hcase_code : (errorBound δ deg domain : ℝ≥0) <
            Pr_{let x ← $ᵖ S}[δᵣ(x.val,
              (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] := by
          convert hcase using 3; simp [ReedSolomon.toFinset]
        -- haff_eq + hS_def give: the carrier of affineSubspaceAtOrigin = ↑S
        have hcarrier_eq : (Affine.affineSubspaceAtOrigin (F := F)
            (u' 0) (Fin.tail u') : Set (ι → F)) = ↑S := by
          rw [haff_eq, hS_def]; unfold Affine.AffSpanFinset
          exact (Affine.AffSpanSet.instFinite (u := C i)).coe_toFinset.symm
        -- Transfer probability via carrier set equality.
        rw [prob_uniform_eq_card_filter_div_card] at hcase_code
        rw [prob_uniform_eq_card_filter_div_card
          (F := ↥(Affine.affineSubspaceAtOrigin (F := F) (u' 0) (Fin.tail u')))]
        let e := Equiv.setCongr hcarrier_eq
        have hcard : Fintype.card ↥(Affine.affineSubspaceAtOrigin (F := F)
            (u' 0) (Fin.tail u')) = Fintype.card ↥S :=
          Fintype.card_of_bijective e.bijective
        have hfilt : (Finset.univ.filter (fun (y : ↥(Affine.affineSubspaceAtOrigin
            (F := F) (u' 0) (Fin.tail u'))) =>
            δᵣ(y.1, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ)).card =
          (Finset.univ.filter (fun (x : ↥S) =>
            δᵣ(x.val, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ)).card :=
          Finset.card_bij (fun a _ => e a)
            (fun a ha => by simpa using ha)
            (fun a₁ _ a₂ _ h => e.injective h)
            (fun b hb => ⟨e.symm b, by simpa using hb, e.apply_symm_apply b⟩)
        rw [hcard, hfilt]; exact hcase_code
      -- Apply Thm 1.7 at k := m + 1 to get jointAgreement (W := u').
      have hja_u' : jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F)))
          (δ := δ) (W := u') :=
        correlatedAgreement_affine_spaces (k := m + 1) hdeg _hδ_pos hδ hRS hε u' hPr_aff
      -- Convert jointAgreement (W := u') → jointAgreement (W := C i).
      -- Witnesses: v_0 for C i 0 stays, v_{j+1} + v_0 ∈ RS.code (submodule closure)
      -- agrees with C i (j+1) on S because v_{j+1} agrees with u'(j+1) = C i (j+1) - C i 0
      -- and v_0 agrees with C i 0 on S.
      obtain ⟨S_ja, hS_card, v', hv'⟩ := hja_u'
      refine ⟨S_ja, hS_card, fun j => if j = 0 then v' 0 else v' j + v' 0, fun j => ?_⟩
      by_cases hj0 : j = 0
      · subst hj0
        simp only [ite_true]
        exact hv' 0
      · simp only [hj0, ite_false]
        constructor
        · -- v' j + v' 0 ∈ RS.code (submodule: closed under addition)
          exact (ReedSolomon.code domain deg).add_mem (hv' j).1 (hv' 0).1
        · -- Agreement: v' j + v' 0 agrees with C i j on S_ja.
          intro col hcol
          have hv'j := (Finset.mem_filter.mp ((hv' j).2 hcol)).2
          have hv'0 := (Finset.mem_filter.mp ((hv' 0).2 hcol)).2
          have hu'0 : u' 0 = C i 0 := if_pos rfl
          rw [hu'0] at hv'0
          simp only [u', hj0, ite_false, Pi.sub_apply] at hv'j
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [Pi.add_apply, hv'j, hv'0, sub_add_cancel]⟩

end CoreResults

end ProximityGap
