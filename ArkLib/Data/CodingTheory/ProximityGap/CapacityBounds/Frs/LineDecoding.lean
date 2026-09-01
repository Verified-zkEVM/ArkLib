/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.SubspaceDesign
import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding

/-!
# Affine-line decoding infrastructure for the FRS capacity bound

This internal module develops the affine-line collision, list-decoding, and subspace-design
ingredients used by the folded Reed--Solomon capacity bound. The pinning induction and public
capacity theorem live in downstream modules.

## References

- [GG25] Goyal and Guruswami, *Optimal Proximity Gaps for Subspace-Design Codes and (Random)
  Reed-Solomon Codes*, ePrint 2025/2054. Corollary 4.10.
-/

namespace CodingTheory.FrsInternal

open scoped NNReal
open CoreDefinitions ProximityGap

private noncomputable def affineLineCollisionSeeds
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (u₀ u₁ v₀ v₁ : ι → A) : Finset F :=
  Finset.univ.filter (fun γ => u₀ + γ • u₁ = v₀ + γ • v₁)

private theorem affineLineCollisionSeeds_card_le_one
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (u₀ u₁ v₀ v₁ : ι → A)
    (hne : u₀ ≠ v₀ ∨ u₁ ≠ v₁) :
    (affineLineCollisionSeeds (F := F) u₀ u₁ v₀ v₁).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro α hα β hβ
  have ha : u₀ + α • u₁ = v₀ + α • v₁ :=
    (Finset.mem_filter.mp hα).2
  have hb : u₀ + β • u₁ = v₀ + β • v₁ :=
    (Finset.mem_filter.mp hβ).2
  by_cases hs : u₁ = v₁
  · have hi : u₀ ≠ v₀ := hne.resolve_right (fun h => h hs)
    exfalso
    apply hi
    calc
      u₀ = (u₀ + α • u₁) - α • u₁ := by abel
      _ = (v₀ + α • v₁) - α • u₁ := by rw [ha]
      _ = v₀ := by rw [hs]; abel
  · have hea : α • (u₁ - v₁) = v₀ - u₀ := by
      calc
        α • (u₁ - v₁) = α • u₁ - α • v₁ := smul_sub α u₁ v₁
        _ = (u₀ + α • u₁) - (u₀ + α • v₁) := by abel
        _ = (v₀ + α • v₁) - (u₀ + α • v₁) := by rw [ha]
        _ = v₀ - u₀ := by abel
    have heb : β • (u₁ - v₁) = v₀ - u₀ := by
      calc
        β • (u₁ - v₁) = β • u₁ - β • v₁ := smul_sub β u₁ v₁
        _ = (u₀ + β • u₁) - (u₀ + β • v₁) := by abel
        _ = (v₀ + β • v₁) - (u₀ + β • v₁) := by rw [hb]
        _ = v₀ - u₀ := by abel
    have hz : (α - β) • (u₁ - v₁) = 0 := by
      rw [sub_smul, hea, heb, sub_self]
    rcases smul_eq_zero.mp hz with hab | hv
    · exact sub_eq_zero.mp hab
    · exact (hs (sub_eq_zero.mp hv)).elim

theorem boosted_frs_radius_le_list_radius
    (s t : ℕ) (R : ℝ) (ht : 3 ≤ t)
    (hs : 4 * t ^ 2 < s) (hR0 : 0 ≤ R) :
    (1 - R - 2 / (t : ℝ)) * (((2 * t : ℕ) : ℝ)) /
        (((2 * t - 1 : ℕ) : ℝ)) ≤
      (t : ℝ) / (t + 1) *
        (1 - (s : ℝ) * R / ((s : ℝ) - t + 1)) := by
  have hsub : 1 ≤ 2 * t := by omega
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hsub, Nat.cast_one]
  have htR3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have htR : (0 : ℝ) < t := by nlinarith
  have hsR : (4 : ℝ) * (t : ℝ) ^ 2 < s := by exact_mod_cast hs
  have ha : (0 : ℝ) < 2 * t - 1 := by nlinarith only [htR3]
  have hb : (0 : ℝ) < t + 1 := by positivity
  have hd : (0 : ℝ) < (s : ℝ) - t + 1 := by nlinarith only [hsR, htR3]
  rw [div_le_iff₀ ha]
  rw [div_mul_eq_mul_div]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ hb]
  field_simp
  have hgap : (0 : ℝ) ≤ s - 4 * (t : ℝ) ^ 2 := by linarith
  have hgap_t : (0 : ℝ) ≤ (s - 4 * (t : ℝ) ^ 2) * t :=
    mul_nonneg hgap htR.le
  have ht2 : (0 : ℝ) ≤ (t : ℝ) ^ 2 := sq_nonneg (t : ℝ)
  have ht3nonneg : (0 : ℝ) ≤ (t : ℝ) ^ 3 := by positivity
  have hc : (0 : ℝ) ≤ 3 * s * t - 2 * (t : ℝ) ^ 3 + 2 * t := by
    nlinarith only [hgap_t, ht3nonneg, htR.le]
  have hbse : (0 : ℝ) ≤ s * t + 4 * s - (t : ℝ) ^ 2 - 3 * t + 4 := by
    nlinarith only [mul_nonneg hgap (show (0 : ℝ) ≤ t + 4 by positivity), ht2, htR3]
  nlinarith only [mul_nonneg hR0 hc, hbse]

private theorem exists_finset_lift_image_eq_injOn
    {α β : Type} [DecidableEq β]
    (f : α → β) (s : Set α) (t : Finset β)
    (h : (↑t : Set β) ⊆ f '' s) :
    ∃ u : Finset α, (↑u : Set α) ⊆ s ∧ Set.InjOn f (↑u : Set α) ∧
      u.image f = t := by
  classical
  apply Finset.exists_subset_injOn_image_eq_of_surjOn s t
  intro y hy
  exact h hy

open scoped BigOperators in
private theorem exists_seed_pairwise_distinct_affine_lines
    {ι : Type} [Finite ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [Finite A] [AddCommGroup A] [Module F A]
    (P : Finset ((ι → A) × (ι → A)))
    (hcard : P.card ^ 2 < Fintype.card F) :
    ∃ γ : F,
      Set.InjOn (fun p : (ι → A) × (ι → A) => p.1 + γ • p.2)
        (↑P : Set ((ι → A) × (ι → A))) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite A
  let Q := (P.product P).filter (fun pq => pq.1 ≠ pq.2)
  let B := Q.biUnion (fun pq =>
    affineLineCollisionSeeds (F := F) pq.1.1 pq.1.2 pq.2.1 pq.2.2)
  have hBcard : B.card ≤ P.card ^ 2 := by
    calc
      B.card ≤ ∑ pq ∈ Q,
          (affineLineCollisionSeeds (F := F)
            pq.1.1 pq.1.2 pq.2.1 pq.2.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _pq ∈ Q, 1 := by
        apply Finset.sum_le_sum
        intro pq hpq
        have hne : pq.1.1 ≠ pq.2.1 ∨ pq.1.2 ≠ pq.2.2 := by
          have hpne : pq.1 ≠ pq.2 := (Finset.mem_filter.mp hpq).2
          by_contra h
          push Not at h
          exact hpne (Prod.ext h.1 h.2)
        exact affineLineCollisionSeeds_card_le_one
          pq.1.1 pq.1.2 pq.2.1 pq.2.2 hne
      _ = Q.card := by simp
      _ ≤ (P.product P).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = P.card ^ 2 := by simp [pow_two]
  have hBlt : B.card < Fintype.card F := hBcard.trans_lt hcard
  obtain ⟨γ, _hγuniv, hγB⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := B) (t := (Finset.univ : Finset F)) (by simpa using hBlt)
  refine ⟨γ, ?_⟩
  intro p hp q hq heq
  by_contra hpq
  apply hγB
  apply Finset.mem_biUnion.mpr
  refine ⟨(p, q), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, heq⟩

open scoped BigOperators in
private theorem finset_card_sdiff_biUnion_ge
    {α β : Type} [DecidableEq β]
    (P : Finset α) (T : Finset β) (K : α → Finset β)
    (n L a : ℕ)
    (hsub : ∀ p ∈ P, K p ⊆ T)
    (hP : P.card ≤ L)
    (hK : ∀ p ∈ P, (K p).card ≤ n)
    (hT : n * L + a ≤ T.card) :
    a ≤ (T \ P.biUnion K).card := by
  classical
  let B : Finset β := P.biUnion K
  have hBT : B ⊆ T := by
    intro x hx
    obtain ⟨p, hpP, hxp⟩ := Finset.mem_biUnion.mp hx
    exact hsub p hpP hxp
  have hBcard0 : B.card ≤ P.card * n := by
    dsimp only [B]
    exact Finset.card_biUnion_le_card_mul P K n hK
  have hPmul : P.card * n ≤ L * n := Nat.mul_le_mul_right n hP
  have hBcard : B.card ≤ n * L := by
    calc
      B.card ≤ P.card * n := hBcard0
      _ ≤ L * n := hPmul
      _ = n * L := Nat.mul_comm _ _
  have hdiff : (T \ B).card + B.card = T.card :=
    Finset.card_sdiff_add_card_eq_card hBT
  change a ≤ (T \ B).card
  omega

open scoped NNReal in
private noncomputable def globallyCloseAffinePairs
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (C : Set (ι → Fin s → F))
    (f₀ f₁ : ι → Fin s → F) (δ : ℝ) :
    Finset ((ι → Fin s → F) × (ι → Fin s → F)) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.1 ∈ C ∧ p.2 ∈ C ∧
      ∀ γ : F,
        (Code.relHammingDist (f₀ + γ • f₁) (p.1 + γ • p.2) : ℝ) ≤ δ)

open scoped NNReal in
private theorem globallyCloseAffinePairs_card_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s L : ℕ} (C : Set (ι → Fin s → F))
    (hclosed : ∀ u₀ ∈ C, ∀ u₁ ∈ C, ∀ γ : F, u₀ + γ • u₁ ∈ C)
    (f₀ f₁ : ι → Fin s → F) (δ : ℝ)
    (hLambda : Code.Lambda C δ ≤ (L : ℕ∞))
    (hcard : (L + 1) ^ 2 < Fintype.card F) :
    (globallyCloseAffinePairs C f₀ f₁ δ).card ≤ L := by
  classical
  let P := globallyCloseAffinePairs C f₀ f₁ δ
  by_contra hnot
  change ¬ P.card ≤ L at hnot
  have hbig : L + 1 ≤ P.card := by omega
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hbig
  have hQsq : Q.card ^ 2 < Fintype.card F := by
    rw [hQcard]
    exact hcard
  obtain ⟨γ, hinj⟩ := exists_seed_pairwise_distinct_affine_lines Q hQsq
  let V : Finset (ι → Fin s → F) := Q.image (fun p => p.1 + γ • p.2)
  have hVcard : V.card = L + 1 := by
    calc
      V.card = Q.card := Finset.card_image_of_injOn hinj
      _ = L + 1 := hQcard
  have hVsub : (↑V : Set (ι → Fin s → F)) ⊆
      Code.closeCodewordsRel C (f₀ + γ • f₁) δ := by
    intro c hc
    obtain ⟨p, hpQ, rfl⟩ := Finset.mem_image.mp hc
    have hpP : p ∈ P := hQP hpQ
    have hpdata := (Finset.mem_filter.mp hpP).2
    apply Code.mem_closeCodewordsRel_iff.mpr
    exact ⟨hclosed p.1 hpdata.1 p.2 hpdata.2.1 γ, hpdata.2.2 γ⟩
  have hpoint := (Code.Lambda_le_iff_forall_ncard_le.mp hLambda) (f₀ + γ • f₁)
  have hVle : V.card ≤
      (Code.closeCodewordsRel C (f₀ + γ • f₁) δ).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hVsub hpoint.1
  omega

noncomputable def lineAgreementSeeds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (T : Finset F) (i : ι) : Finset F :=
  T.filter (fun γ => U γ i = f₀ i + γ • f₁ i)

private theorem lineAgreementSeeds_card_le_one_of_ne_at
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (f₀ f₁ u₀ u₁ : ι → Fin s → F)
    (T : Finset F) (i : ι) (γ : F)
    (hne : f₀ i + γ • f₁ i ≠ u₀ i + γ • u₁ i) :
    (lineAgreementSeeds f₀ f₁ (fun α => u₀ + α • u₁) T i).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro α hα β hβ
  have ha : u₀ i + α • u₁ i = f₀ i + α • f₁ i := by
    have := (Finset.mem_filter.mp hα).2
    simpa only [Pi.add_apply, Pi.smul_apply] using this
  have hb : u₀ i + β • u₁ i = f₀ i + β • f₁ i := by
    have := (Finset.mem_filter.mp hβ).2
    simpa only [Pi.add_apply, Pi.smul_apply] using this
  by_cases hs : u₁ i = f₁ i
  · have hi : u₀ i ≠ f₀ i := by
      intro h
      apply hne
      rw [h, hs]
    exfalso
    apply hi
    calc
      u₀ i = (u₀ i + α • u₁ i) - α • u₁ i := by abel
      _ = (f₀ i + α • f₁ i) - α • u₁ i := by rw [ha]
      _ = f₀ i := by rw [hs]; abel
  · have hea : α • (u₁ i - f₁ i) = f₀ i - u₀ i := by
      calc
        α • (u₁ i - f₁ i) = α • u₁ i - α • f₁ i := smul_sub α _ _
        _ = (u₀ i + α • u₁ i) - (u₀ i + α • f₁ i) := by abel
        _ = (f₀ i + α • f₁ i) - (u₀ i + α • f₁ i) := by rw [ha]
        _ = f₀ i - u₀ i := by abel
    have heb : β • (u₁ i - f₁ i) = f₀ i - u₀ i := by
      calc
        β • (u₁ i - f₁ i) = β • u₁ i - β • f₁ i := smul_sub β _ _
        _ = (u₀ i + β • u₁ i) - (u₀ i + β • f₁ i) := by abel
        _ = (f₀ i + β • f₁ i) - (u₀ i + β • f₁ i) := by rw [hb]
        _ = f₀ i - u₀ i := by abel
    have hz : (α - β) • (u₁ i - f₁ i) = 0 := by
      rw [sub_smul, hea, heb, sub_self]
    rcases smul_eq_zero.mp hz with hab | hv
    · exact sub_eq_zero.mp hab
    · exact (hs (sub_eq_zero.mp hv)).elim

private theorem lineAgreement_span_finrank_le_two
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (T : Finset F) (i : ι) :
    Module.finrank F
      (Submodule.span F
        ((fun γ : F => U γ i) ''
          (↑(lineAgreementSeeds f₀ f₁ U T i) : Set F))) ≤ 2 := by
  classical
  let P : Submodule F (Fin s → F) :=
    Submodule.span F (↑({f₀ i, f₁ i} : Finset (Fin s → F)) : Set (Fin s → F))
  have hle : Submodule.span F
      ((fun γ : F => U γ i) ''
        (↑(lineAgreementSeeds f₀ f₁ U T i) : Set F)) ≤ P := by
    rw [Submodule.span_le]
    rintro x ⟨γ, hγ, rfl⟩
    have hagree : U γ i = f₀ i + γ • f₁ i := by
      have hmem : γ ∈ T ∧ U γ i = f₀ i + γ • f₁ i := by
        simpa only [lineAgreementSeeds, Finset.mem_coe, Finset.mem_filter] using hγ
      exact hmem.2
    change U γ i ∈ P
    rw [hagree]
    apply P.add_mem
    · change f₀ i ∈ Submodule.span F
        (↑({f₀ i, f₁ i} : Finset (Fin s → F)) : Set (Fin s → F))
      apply Submodule.subset_span
      simp
    · apply P.smul_mem
      change f₁ i ∈ Submodule.span F
        (↑({f₀ i, f₁ i} : Finset (Fin s → F)) : Set (Fin s → F))
      apply Submodule.subset_span
      simp
  calc
    Module.finrank F
        (Submodule.span F
          ((fun γ : F => U γ i) ''
            (↑(lineAgreementSeeds f₀ f₁ U T i) : Set F)))
        ≤ Module.finrank F P := Submodule.finrank_mono hle
    _ ≤ ({f₀ i, f₁ i} : Finset (Fin s → F)).card := by
      change Set.finrank F
          (↑({f₀ i, f₁ i} : Finset (Fin s → F)) : Set (Fin s → F)) ≤
        ({f₀ i, f₁ i} : Finset (Fin s → F)).card
      exact finrank_span_finset_le_card
        ({f₀ i, f₁ i} : Finset (Fin s → F))
    _ ≤ 2 := Finset.card_le_two

private theorem lineAgreementSeeds_card_le_kernel_finrank_add_two
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (T : Finset F) (hlin : LinearIndepOn F U (↑T : Set F)) (i : ι) :
    (lineAgreementSeeds f₀ f₁ U T i).card ≤
      Module.finrank F ↥(Submodule.span F (U '' (↑T : Set F)) ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) + 2 := by
  classical
  let Ti : Finset F := lineAgreementSeeds f₀ f₁ U T i
  let B : Submodule F (ι → Fin s → F) :=
    Submodule.span F (U '' (↑Ti : Set F))
  let A : Submodule F (ι → Fin s → F) :=
    Submodule.span F (U '' (↑T : Set F))
  let p : (ι → Fin s → F) →ₗ[F] (Fin s → F) :=
    LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i
  have hTiT : (↑Ti : Set F) ⊆ (↑T : Set F) := by
    intro γ hγ
    have hmem : γ ∈ T ∧ U γ i = f₀ i + γ • f₁ i := by
      simpa only [Ti, lineAgreementSeeds, Finset.mem_coe, Finset.mem_filter] using hγ
    exact hmem.1
  have hlinTi : LinearIndepOn F U (↑Ti : Set F) := hlin.mono hTiT
  have himage : U '' (↑Ti : Set F) = (↑(Ti.image U) : Set (ι → Fin s → F)) := by
    ext x
    simp only [Finset.coe_image, Set.mem_image]
  have hdimB : Module.finrank F B = Ti.card := by
    change Module.finrank F (Submodule.span F (U '' (↑Ti : Set F))) = Ti.card
    rw [himage]
    calc
      Module.finrank F (Submodule.span F (↑(Ti.image U) : Set (ι → Fin s → F))) =
          (Ti.image U).card := by
        apply finrank_span_finset_eq_card
        simpa only [← himage] using hlinTi.id_image
      _ = Ti.card := Finset.card_image_of_injOn hlinTi.injOn
  have hrange_eq : LinearMap.range (p.domRestrict B) =
      Submodule.span F
        ((fun γ : F => U γ i) '' (↑Ti : Set F)) := by
    rw [LinearMap.range_domRestrict]
    change (Submodule.span F (U '' (↑Ti : Set F))).map p = _
    rw [Submodule.map_span]
    congr 1
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
      exact ⟨γ, hγ, by simp only [p, LinearMap.proj_apply]⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨U γ, ⟨γ, hγ, rfl⟩, by simp only [p, LinearMap.proj_apply]⟩
  have hrange : Module.finrank F (LinearMap.range (p.domRestrict B)) ≤ 2 := by
    rw [hrange_eq]
    simpa only [Ti] using lineAgreement_span_finrank_le_two f₀ f₁ U T i
  have hker_map :
      (LinearMap.ker (p.domRestrict B)).map B.subtype =
        B ⊓ LinearMap.ker p := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨y.2, LinearMap.mem_ker.mpr ?_⟩
      exact LinearMap.mem_ker.mp hy
    · rintro ⟨hxB, hxp⟩
      refine ⟨⟨x, hxB⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      exact LinearMap.mem_ker.mp hxp
  have hker_finrank : Module.finrank F (LinearMap.ker (p.domRestrict B)) =
      Module.finrank F ↥(B ⊓ LinearMap.ker p) := by
    calc
      Module.finrank F (LinearMap.ker (p.domRestrict B)) =
          Module.finrank F ((LinearMap.ker (p.domRestrict B)).map B.subtype) :=
        (Submodule.finrank_map_subtype_eq B (LinearMap.ker (p.domRestrict B))).symm
      _ = Module.finrank F ↥(B ⊓ LinearMap.ker p) := by rw [hker_map]
  have hBA : B ≤ A := by
    change Submodule.span F (U '' (↑Ti : Set F)) ≤
      Submodule.span F (U '' (↑T : Set F))
    exact Submodule.span_mono (Set.image_mono hTiT)
  have hker_le : Module.finrank F ↥(B ⊓ LinearMap.ker p) ≤
      Module.finrank F ↥(A ⊓ LinearMap.ker p) :=
    Submodule.finrank_mono (inf_le_inf hBA le_rfl)
  have hnull := LinearMap.finrank_range_add_finrank_ker (p.domRestrict B)
  have hfinal : Ti.card ≤ Module.finrank F ↥(A ⊓ LinearMap.ker p) + 2 := by
    rw [← hdimB]
    omega
  simpa only [Ti, A, p] using hfinal

open scoped NNReal in
noncomputable def lineCloseSeeds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ) : Finset F :=
  Finset.univ.filter (fun γ => (δᵣ(f₀ + γ • f₁, U γ) : ℝ) ≤ δ)

open scoped NNReal in
def StrongLineDecodable
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (C : Set (ι → Fin s → F)) (δ : NNReal) (a b : ℕ) : Prop :=
  ∀ f₀ f₁ : ι → Fin s → F, ∀ U : F → ι → Fin s → F,
    (∀ γ : F, U γ ∈ C) →
    ∀ T : Finset F, T ⊆ lineCloseSeeds f₀ f₁ U (δ : ℝ) → a ≤ T.card →
      ∃ u₀ ∈ C, ∃ u₁ ∈ C,
        b ≤ (T.filter (fun γ => U γ = u₀ + γ • u₁)).card

open scoped NNReal in
noncomputable def lineCloseSpan
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ) :
    Submodule F (ι → Fin s → F) :=
  Submodule.span F (U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F))

private theorem exists_lineCloseSeeds_linearIndepOn_card_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ)
    (hr : r ≤ Module.finrank F (lineCloseSpan f₀ f₁ U δ)) :
    ∃ T : Finset F, T ⊆ lineCloseSeeds f₀ f₁ U δ ∧ T.card = r ∧
      LinearIndepOn F U (↑T : Set F) := by
  classical
  let G : Set (ι → Fin s → F) :=
    U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F)
  have hrG : r ≤ Module.finrank F (Submodule.span F G) := by
    change r ≤ Module.finrank F
      (Submodule.span F (U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F))) at hr
    exact hr
  obtain ⟨W₀, hW₀G, hW₀card, _hW₀span, hW₀lin⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn F G
  have hrW₀ : r ≤ W₀.card := by
    rw [hW₀card]
    exact hrG
  obtain ⟨W, hWW₀, hWcard⟩ := Finset.exists_subset_card_eq hrW₀
  have hWG : (↑W : Set (ι → Fin s → F)) ⊆ G := by
    intro x hx
    exact hW₀G (hWW₀ hx)
  have hWlin : LinearIndepOn F id (↑W : Set (ι → Fin s → F)) := by
    exact hW₀lin.mono (by
      intro x hx
      exact hWW₀ hx)
  obtain ⟨T, hTclose, hUinj, himage⟩ :=
    exists_finset_lift_image_eq_injOn U
      (↑(lineCloseSeeds f₀ f₁ U δ) : Set F) W hWG
  have hlinT : LinearIndepOn F U (↑T : Set F) := by
    apply (linearIndepOn_iff_image hUinj).2
    have hset : U '' (↑T : Set F) = (↑W : Set (ι → Fin s → F)) := by
      rw [← Finset.coe_image, himage]
    rw [hset]
    exact hWlin
  refine ⟨T, ?_, ?_, hlinT⟩
  · intro γ hγ
    exact hTclose hγ
  · calc
      T.card = (T.image U).card := (Finset.card_image_of_injOn hUinj).symm
      _ = W.card := by rw [himage]
      _ = r := hWcard

open scoped NNReal in
theorem lineCloseSpan_le_code
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (C : Submodule F (ι → Fin s → F))
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ)
    (hU : ∀ γ : F, U γ ∈ C) :
    lineCloseSpan f₀ f₁ U δ ≤ C := by
  rw [lineCloseSpan, Submodule.span_le]
  rintro x ⟨γ, _hγ, rfl⟩
  exact hU γ

open scoped NNReal in
theorem lineClose_sum_agreement_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ : ℝ) (T : Finset F)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ) :
    (T.card : ℝ) * Fintype.card ι * (1 - δ) ≤
      ∑ i : ι, ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hγ : ∀ γ ∈ T,
      (Fintype.card ι : ℝ) * (1 - δ) ≤
        (Code.agree (f₀ + γ • f₁) (U γ) : ℝ) := by
    intro γ hγT
    have hd := hclose γ hγT
    rw [Code.relHammingDist_coe, div_le_iff₀ hn] at hd
    have ha := Code.agree_add_hammingDist
      (u := f₀ + γ • f₁) (v := U γ)
    have haR : (Code.agree (f₀ + γ • f₁) (U γ) : ℝ) +
        (hammingDist (f₀ + γ • f₁) (U γ) : ℝ) = Fintype.card ι := by
      exact_mod_cast ha
    nlinarith
  have hsum : ∑ γ ∈ T, ((Fintype.card ι : ℝ) * (1 - δ)) ≤
      ∑ γ ∈ T, (Code.agree (f₀ + γ • f₁) (U γ) : ℝ) :=
    Finset.sum_le_sum fun γ hγT => hγ γ hγT
  have hagree_sum (γ : F) :
      (Code.agree (f₀ + γ • f₁) (U γ) : ℝ) =
        ∑ i : ι, if U γ i = (f₀ + γ • f₁) i then (1 : ℝ) else 0 := by
    rw [Code.agree]
    have hfilter :
        (Finset.univ.filter (fun i : ι => (f₀ + γ • f₁) i = U γ i)) =
          Finset.univ.filter (fun i : ι => U γ i = (f₀ + γ • f₁) i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
    rw [hfilter]
    exact (Finset.sum_boole
      (R := ℝ) (fun i : ι => U γ i = (f₀ + γ • f₁) i) Finset.univ).symm
  have hseed_sum (i : ι) :
      (∑ γ ∈ T, if U γ i = (f₀ + γ • f₁) i then (1 : ℝ) else 0) =
        ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) := by
    exact Finset.sum_boole
      (R := ℝ) (fun γ : F => U γ i = (f₀ + γ • f₁) i) T
  have hdouble : (∑ γ ∈ T, (Code.agree (f₀ + γ • f₁) (U γ) : ℝ)) =
      ∑ i : ι, ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun γ _ => hagree_sum γ), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Pi.add_apply, Pi.smul_apply] using hseed_sum i
  calc
    (T.card : ℝ) * Fintype.card ι * (1 - δ) =
        ∑ γ ∈ T, ((Fintype.card ι : ℝ) * (1 - δ)) := by
          simp [mul_assoc]
    _ ≤ ∑ γ ∈ T, (Code.agree (f₀ + γ • f₁) (U γ) : ℝ) := hsum
    _ = ∑ i : ι, ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) := hdouble

open scoped BigOperators in
open scoped NNReal in
open Code in
private theorem aligned_affineLine_global_close
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F] [DecidableEq F]
    {s b : ℕ} (hb : 1 < b)
    (f₀ f₁ u₀ u₁ : ι → Fin s → F) (T : Finset F)
    (hTcard : T.card = b) (δ : ℝ)
    (hclose : ∀ α ∈ T,
      (Code.relHammingDist (f₀ + α • f₁) (u₀ + α • u₁) : ℝ) ≤ δ)
    (γ : F) :
    (Code.relHammingDist (f₀ + γ • f₁) (u₀ + γ • u₁) : ℝ) ≤
      δ * (b : ℝ) / ((b : ℝ) - 1) := by
  classical
  let _ := Fintype.ofFinite F
  let U : F → ι → Fin s → F := fun α => u₀ + α • u₁
  have hlower := lineClose_sum_agreement_lower f₀ f₁ U δ T (by
    intro α hα
    simpa only [U] using hclose α hα)
  rw [hTcard] at hlower
  let D : Finset ι := Code.disagreementCols (f₀ + γ • f₁) (u₀ + γ • u₁)
  have hlocal : ∀ i : ι,
      ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) +
          ((b : ℝ) - 1) * (if i ∈ D then 1 else 0) ≤ (b : ℝ) := by
    intro i
    by_cases hi : i ∈ D
    · rw [if_pos hi]
      have hne : f₀ i + γ • f₁ i ≠ u₀ i + γ • u₁ i := by
        simpa only [D, Code.mem_disagreementCols, Pi.add_apply, Pi.smul_apply] using hi
      have hone := lineAgreementSeeds_card_le_one_of_ne_at
        f₀ f₁ u₀ u₁ T i γ hne
      have honeR : ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) ≤ 1 := by
        simpa only [U] using (show
          (((lineAgreementSeeds f₀ f₁ (fun α => u₀ + α • u₁) T i).card : ℕ) : ℝ) ≤ 1 by
            exact_mod_cast hone)
      have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (le_of_lt hb)
      nlinarith
    · rw [if_neg hi]
      have hcardNat : (lineAgreementSeeds f₀ f₁ U T i).card ≤ T.card :=
        Finset.card_filter_le _ _
      have hcardR : ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) ≤ b := by
        rw [hTcard] at hcardNat
        exact_mod_cast hcardNat
      norm_num at hcardR ⊢
      exact hcardR
  have hindicator :
      (∑ i : ι, if i ∈ D then (1 : ℝ) else 0) = (D.card : ℝ) := by
    rw [Finset.sum_boole]
    rw [show Finset.univ.filter (fun i : ι => i ∈ D) = D by
      ext i
      simp]
  have hupper :
      (∑ i : ι, ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ)) +
          ((b : ℝ) - 1) * (D.card : ℝ) ≤
        (b : ℝ) * Fintype.card ι := by
    calc
      (∑ i : ι, ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ)) +
          ((b : ℝ) - 1) * (D.card : ℝ) =
          ∑ i : ι, (((lineAgreementSeeds f₀ f₁ U T i).card : ℝ) +
            ((b : ℝ) - 1) * (if i ∈ D then 1 else 0)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
      _ ≤ ∑ _i : ι, (b : ℝ) := Finset.sum_le_sum fun i _ => hlocal i
      _ = (b : ℝ) * Fintype.card ι := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hcount : ((b : ℝ) - 1) * (D.card : ℝ) ≤
      (b : ℝ) * δ * Fintype.card ι := by
    nlinarith
  have hDcard : D.card =
      hammingDist (f₀ + γ • f₁) (u₀ + γ • u₁) := by
    simpa only [D] using
      (hammingDist_eq_disagreementCols_card
        (f₀ + γ • f₁) (u₀ + γ • u₁)).symm
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  rw [Code.relHammingDist_coe, div_le_iff₀ hn]
  rw [div_mul_eq_mul_div, le_div_iff₀ hb1]
  rw [← hDcard]
  nlinarith

noncomputable def linePinnedSeedsOn
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (S : Finset ι) : Finset F :=
  T.filter (fun γ => ∀ i ∈ S, U γ i = f₀ i + γ • f₁ i)

theorem linePinnedSeedsOn_empty
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) :
    linePinnedSeedsOn T f₀ f₁ U ∅ = T := by
  classical
  ext γ
  simp [linePinnedSeedsOn]

theorem linePinnedSeedsOn_insert
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (S : Finset ι) (i : ι) :
    linePinnedSeedsOn T f₀ f₁ U (insert i S) =
      lineAgreementSeeds f₀ f₁ U (linePinnedSeedsOn T f₀ f₁ U S) i := by
  classical
  ext γ
  simp only [linePinnedSeedsOn, lineAgreementSeeds, Finset.mem_filter,
    Finset.mem_insert]
  aesop

private theorem linePinnedSeedsOn_insert_subset
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (S : Finset ι) (i : ι) :
    linePinnedSeedsOn T f₀ f₁ U (insert i S) ⊆
      linePinnedSeedsOn T f₀ f₁ U S := by
  classical
  intro γ hγ
  have hdata : γ ∈ T ∧
      ∀ j ∈ insert i S, U γ j = f₀ j + γ • f₁ j := by
    simpa only [linePinnedSeedsOn, Finset.mem_filter] using hγ
  apply Finset.mem_filter.mpr
  refine ⟨hdata.1, ?_⟩
  intro j hj
  exact hdata.2 j (Finset.mem_insert_of_mem hj)

theorem linePinnedSeedsOn_insert_card_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (S : Finset ι) (i : ι) :
    (linePinnedSeedsOn T f₀ f₁ U (insert i S)).card ≤
      (linePinnedSeedsOn T f₀ f₁ U S).card :=
  Finset.card_le_card (linePinnedSeedsOn_insert_subset T f₀ f₁ U S i)

open _root_.CoreDefinitions in
open _root_.ProximityGap in
theorem mcaError_affineLine_zero_le_inv_card
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [Finite A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) :
    mcaError (AffineLineGenerator F) C 0 ≤
      ENNReal.ofReal (1 / (Fintype.card F : ℝ)) := by
  classical
  let _ := Fintype.ofFinite A
  have mem_of_proj_univ (w : ι → A)
      (h : LinearCode.projectedWord w Finset.univ ∈
        LinearCode.projectedCodeSubmod C Finset.univ) : w ∈ C := by
    rw [LinearCode.mem_projectedCodeSubmod_iff] at h
    rcases h with ⟨c, hc, heq⟩
    have hwc : w = c := by
      funext i
      simpa [LinearCode.projectedWord] using
        congrFun heq ⟨i, Finset.mem_univ i⟩
    rw [hwc]
    exact hc
  unfold mcaError
  refine iSup_le fun U => ?_
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (show (Finset.univ.filter (fun x : F =>
        IsMCA (AffineLineGenerator F) C x U 0)).card ≤ 1 by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      rcases hx with ⟨Tx, hTxcard, hvx, hbadx⟩
      rcases hy with ⟨Ty, hTycard, hvy, hbady⟩
      have hTxle : Fintype.card ι ≤ Tx.card := by
        exact_mod_cast (show (Fintype.card ι : ℝ) ≤ Tx.card by
          simpa using hTxcard)
      have hTyle : Fintype.card ι ≤ Ty.card := by
        exact_mod_cast (show (Fintype.card ι : ℝ) ≤ Ty.card by
          simpa using hTycard)
      have hTx : Tx = Finset.univ := (Finset.card_eq_iff_eq_univ Tx).mp
        (le_antisymm (Finset.card_le_univ Tx) hTxle)
      have hTy : Ty = Finset.univ := (Finset.card_eq_iff_eq_univ Ty).mp
        (le_antisymm (Finset.card_le_univ Ty) hTyle)
      rw [hTx] at hvx hbadx
      rw [hTy] at hvy hbady
      have hvxC : (fun i => U 0 i + x • U 1 i) ∈ C := by
        apply mem_of_proj_univ
        simpa [AffineLineGenerator, Fin.sum_univ_two] using hvx
      have hvyC : (fun i => U 0 i + y • U 1 i) ∈ C := by
        apply mem_of_proj_univ
        simpa [AffineLineGenerator, Fin.sum_univ_two] using hvy
      by_contra hxy
      have hU1C : U 1 ∈ C := by
        have hm := C.smul_mem ((x - y)⁻¹) (C.sub_mem hvxC hvyC)
        have hd :
            ((fun i => U 0 i + x • U 1 i) -
              (fun i => U 0 i + y • U 1 i)) =
              (x - y) • U 1 := by
          funext i
          change U 0 i + x • U 1 i - (U 0 i + y • U 1 i) =
            (x - y) • U 1 i
          rw [sub_smul]
          exact add_sub_add_left_eq_sub (x • U 1 i) (y • U 1 i) (U 0 i)
        rw [hd, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hxy), one_smul] at hm
        exact hm
      have hU0C : U 0 ∈ C := by
        have hm := C.sub_mem hvxC (C.smul_mem x hU1C)
        convert hm using 1
        funext i
        simp
      rcases hbadx with ⟨j, hj⟩
      have hUjC : U j ∈ C := by
        fin_cases j
        · exact hU0C
        · exact hU1C
      apply hj
      rw [LinearCode.mem_projectedCodeSubmod_iff]
      exact ⟨U j, hUjC, rfl⟩)
  · positivity

theorem mcaError_eq_zero_of_neg_radius
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
    {ℓ : Type} [Fintype ℓ]
    {S : Type} [Fintype S] [Nonempty S]
    {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (C : ModuleCode ι F A)
    {δ : ℝ} (hδ : δ < 0) :
    mcaError G C δ = 0 := by
  classical
  unfold mcaError
  apply le_antisymm
  · refine iSup_le fun U => ?_
    rw [Probability.prob_uniform_eq_ofReal]
    have hempty : Finset.univ.filter (fun x : S => IsMCA G C x U δ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      rcases hx with ⟨T, hT, -⟩
      have hcard : (T.card : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast Finset.card_le_univ T
      have hlarge : (Fintype.card ι : ℝ) < Fintype.card ι * (1 - δ) := by
        have hone : (1 : ℝ) < 1 - δ := by linarith
        have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
        nlinarith
      linarith
    rw [hempty]
    norm_num
  · exact bot_le

theorem pinning_potential_compose
    (A B C d d' ε : ℝ) (hd : 0 ≤ d) (hd' : 0 ≤ d') (hε : 0 < ε)
    (hstep : A * (d' + ε) ≤ B * (d + ε))
    (hterminal : B * ε ≤ C * (d' + ε)) :
    A * ε ≤ C * (d + ε) := by
  have hp : 0 < d' + ε := by linarith
  have hde : 0 ≤ d + ε := by linarith
  have h1 := mul_le_mul_of_nonneg_right hstep hε.le
  have h2 := mul_le_mul_of_nonneg_right hterminal hde
  apply le_of_mul_le_mul_right _ hp
  nlinarith

noncomputable def sharpSubspaceProfile
    {ι : Type} [Fintype ι] (s : ℕ) (R : ℝ) : ℕ → ℝ :=
  fun r => if r ∈ Finset.Icc 1 s then
    (s * R - 1 / Fintype.card ι) / (s - r + 1)
  else 1

theorem isSubspaceDesign_frsCode_sharpProfile
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hFn : Fintype.card ι < Fintype.card F)
    (hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (hω : ω ≠ 0)
    (hωgen : orderOf ω = Fintype.card F - 1)
    (hk : k ≤ s * Fintype.card ι) :
    IsSubspaceDesign s
      (sharpSubspaceProfile (ι := ι) s
        ((k : ℝ) / (s * Fintype.card ι)))
      (ReedSolomon.Folded.frsCode domain k s ω) := by
  classical
  have hrate : (LinearCode.alphabetRate
      (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) =
      (k : ℝ) / (s * Fintype.card ι) := by
    rw [ReedSolomon.Folded.alphabetRate_frsCode domain k s ω hadm hω hk]
  have hdesign := isSubspaceDesign_frsCode_sub_one domain k s ω hFn hadm hωgen
  rw [hrate] at hdesign
  refine hdesign.mono_tau fun r => ?_
  rw [sharpSubspaceProfile]

theorem sharpSubspaceProfile_eq_fun
    {ι : Type} [Fintype ι] (s : ℕ) (R : ℝ) :
    sharpSubspaceProfile (ι := ι) s R =
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) := by
  rfl

theorem sharpSubspaceProfile_two_mul_le_rate_add
    {ι : Type} [Fintype ι] [Nonempty ι]
    (s t : ℕ) (R : ℝ)
    (ht : 0 < t) (hs : 4 * t ^ 2 < s)
    (_hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    sharpSubspaceProfile (ι := ι) s R (2 * t) ≤
      R + 1 / (2 * (t : ℝ)) := by
  classical
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1R : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hsR : (4 : ℝ) * (t : ℝ) ^ 2 < s := by exact_mod_cast hs
  have h2ts : 2 * t ≤ s := by nlinarith
  have hmem : 2 * t ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨by omega, h2ts⟩
  have hval : sharpSubspaceProfile (ι := ι) s R (2 * t) =
      ((s : ℝ) * R - 1 / Fintype.card ι) /
        ((s : ℝ) - 2 * t + 1) := by
    simp only [sharpSubspaceProfile, hmem, if_true]
    congr 1
    push_cast
    ring
  have hden_pos : (0 : ℝ) < (s : ℝ) - 2 * t + 1 := by nlinarith
  have hfac_nonneg : (0 : ℝ) ≤ 2 * t - 1 := by nlinarith
  have haux : (2 : ℝ) * t - 1 ≤
      (1 / (2 * t)) * ((s : ℝ) - 2 * t + 1) := by
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hRt : R * (2 * (t : ℝ) - 1) ≤ 2 * t - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR1) hfac_nonneg]
  have hinv_nonneg : (0 : ℝ) ≤ 1 / Fintype.card ι := by positivity
  rw [hval, div_le_iff₀ hden_pos]
  nlinarith

open scoped NNReal in
open scoped BigOperators in
open Code in
theorem strongLineDecodable_boost_of_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s a b L : ℕ} {δ : NNReal}
    (C : Submodule F (ι → Fin s → F))
    (hweak : StrongLineDecodable (C : Set (ι → Fin s → F)) δ a b)
    (hb : 1 < b)
    (hLambda : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (b : ℝ) / ((b : ℝ) - 1)) ≤ (L : ℕ∞))
    (hfield : (L + 1) ^ 2 < Fintype.card F) :
    StrongLineDecodable (C : Set (ι → Fin s → F)) δ
      (Fintype.card ι * L + a) (Fintype.card ι + 1) := by
  classical
  intro f₀ f₁ U hU T hTclose hTcard
  let δ' : ℝ := (δ : ℝ) * (b : ℝ) / ((b : ℝ) - 1)
  let P : Finset ((ι → Fin s → F) × (ι → Fin s → F)) :=
    globallyCloseAffinePairs (C : Set (ι → Fin s → F)) f₀ f₁ δ'
  let K : ((ι → Fin s → F) × (ι → Fin s → F)) → Finset F :=
    fun p => T.filter (fun γ => U γ = p.1 + γ • p.2)
  have hclosed : ∀ u₀ ∈ (C : Set (ι → Fin s → F)),
      ∀ u₁ ∈ (C : Set (ι → Fin s → F)), ∀ γ : F,
        u₀ + γ • u₁ ∈ (C : Set (ι → Fin s → F)) := by
    intro u₀ hu₀ u₁ hu₁ γ
    exact C.add_mem hu₀ (C.smul_mem γ hu₁)
  have hPcard : P.card ≤ L := by
    dsimp only [P, δ']
    exact globallyCloseAffinePairs_card_le C hclosed f₀ f₁
      ((δ : ℝ) * (b : ℝ) / ((b : ℝ) - 1)) hLambda hfield
  by_cases hlarge : ∃ p ∈ P, Fintype.card ι + 1 ≤ (K p).card
  · obtain ⟨p, hpP, hpK⟩ := hlarge
    have hpdata : p.1 ∈ (C : Set (ι → Fin s → F)) ∧
        p.2 ∈ (C : Set (ι → Fin s → F)) ∧
        ∀ γ : F,
          (Code.relHammingDist (f₀ + γ • f₁) (p.1 + γ • p.2) : ℝ) ≤ δ' := by
      simpa only [P, globallyCloseAffinePairs, Finset.mem_filter,
        Finset.mem_univ, true_and] using hpP
    refine ⟨p.1, hpdata.1, p.2, hpdata.2.1, ?_⟩
    simpa only [K] using hpK
  · push Not at hlarge
    have hKcard : ∀ p ∈ P, (K p).card ≤ Fintype.card ι := by
      intro p hpP
      have hnot := hlarge p hpP
      omega
    let B : Finset F := P.biUnion K
    let R : Finset F := T \ B
    have haR : a ≤ R.card := by
      dsimp only [R, B]
      exact finset_card_sdiff_biUnion_ge P T K (Fintype.card ι) L a
        (by
          intro p hpP
          exact Finset.filter_subset _ _)
        hPcard hKcard hTcard
    have hRT : R ⊆ T := by
      dsimp only [R]
      exact Finset.sdiff_subset
    have hRclose : R ⊆ lineCloseSeeds f₀ f₁ U (δ : ℝ) := by
      intro γ hγ
      exact hTclose (hRT hγ)
    obtain ⟨u₀, hu₀, u₁, hu₁, halign⟩ :=
      hweak f₀ f₁ U hU R hRclose haR
    let A : Finset F := R.filter (fun γ => U γ = u₀ + γ • u₁)
    have hbA : b ≤ A.card := by simpa only [A] using halign
    obtain ⟨Q, hQA, hQcard⟩ := Finset.exists_subset_card_eq hbA
    have hQclose : ∀ α ∈ Q,
        (Code.relHammingDist (f₀ + α • f₁) (u₀ + α • u₁) : ℝ) ≤ (δ : ℝ) := by
      intro α hαQ
      have hαA := hQA hαQ
      have hαdata : α ∈ R ∧ U α = u₀ + α • u₁ := by
        simpa only [A, Finset.mem_filter] using hαA
      have hclosemem := hRclose hαdata.1
      have hclose :
          (Code.relHammingDist (f₀ + α • f₁) (U α) : ℝ) ≤ (δ : ℝ) := by
        simpa only [lineCloseSeeds, Finset.mem_filter, Finset.mem_univ,
          true_and] using hclosemem
      simpa only [hαdata.2] using hclose
    have hglobal : ∀ γ : F,
        (Code.relHammingDist (f₀ + γ • f₁) (u₀ + γ • u₁) : ℝ) ≤ δ' := by
      intro γ
      dsimp only [δ']
      exact aligned_affineLine_global_close hb f₀ f₁ u₀ u₁ Q hQcard
        (δ : ℝ) hQclose γ
    have hpP : (u₀, u₁) ∈ P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hu₀, hu₁, ?_⟩
      exact hglobal
    have hQpos : 0 < Q.card := by rw [hQcard]; omega
    obtain ⟨α, hαQ⟩ := Finset.card_pos.mp hQpos
    have hαA := hQA hαQ
    have hαdata : α ∈ R ∧ U α = u₀ + α • u₁ := by
      simpa only [A, Finset.mem_filter] using hαA
    have hαR : α ∈ T \ B := by simpa only [R] using hαdata.1
    have hαB : α ∈ B := by
      apply Finset.mem_biUnion.mpr
      refine ⟨(u₀, u₁), hpP, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_sdiff.mp hαR).1, hαdata.2⟩
    exact ((Finset.mem_sdiff.mp hαR).2 hαB).elim

open scoped NNReal in
open scoped ProbabilityTheory in
theorem strongLineDecodable_to_isLineDecodable
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s a b : ℕ} (C : Set (ι → Fin s → F)) (δ : NNReal)
    (hstrong : StrongLineDecodable C δ a b) :
    IsLineDecodable (F := F) C δ a b := by
  classical
  intro f₀ f₁ U hU hprob
  let T : Finset F := lineCloseSeeds f₀ f₁ U (δ : ℝ)
  have hclose_iff (γ : F) :
      (δᵣ(f₀ + γ • f₁, U γ) ≤ δ) ↔
        ((δᵣ(f₀ + γ • f₁, U γ) : ℝ) ≤ (δ : ℝ)) := by
    norm_cast
  have hfilter :
      (Finset.univ.filter fun γ : F => δᵣ(f₀ + γ • f₁, U γ) ≤ δ) = T := by
    ext γ
    simp only [T, lineCloseSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      hclose_iff]
  rw [Probability.prob_uniform_eq_card_filter_div_card, hfilter] at hprob
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  have haT : a ≤ T.card := by
    by_contra hnot
    have hltNat : T.card < a := Nat.lt_of_not_ge hnot
    have hlt : (T.card : ENNReal) < (a : ENNReal) := by exact_mod_cast hltNat
    have hdiv := ENNReal.div_lt_div_right hq0 hqtop hlt
    exact (not_lt_of_ge hprob) hdiv
  obtain ⟨u₀, hu₀, u₁, hu₁, halign⟩ :=
    hstrong f₀ f₁ U hU T (by
      intro γ hγ
      simpa only [T] using hγ) haT
  refine ⟨u₀, hu₀, u₁, hu₁, ?_⟩
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  have hevent :
      (Finset.univ.filter fun γ : F =>
        δᵣ(f₀ + γ • f₁, U γ) ≤ δ ∧ U γ = u₀ + γ • u₁) =
      T.filter (fun γ => U γ = u₀ + γ • u₁) := by
    ext γ
    simp only [T, lineCloseSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      hclose_iff]
  rw [hevent]
  exact_mod_cast halign

open scoped BigOperators in
open scoped NNReal in
theorem subspaceDesign_lineCloseSpan_finrank_lt
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (hU : ∀ γ : F, U γ ∈ C) (δ ε : ℝ) (r : ℕ)
    (hr : 0 < r) (hδ : δ ≤ 1 - τ r - ε)
    (hε : 2 / (r : ℝ) < ε) :
    Module.finrank F (lineCloseSpan f₀ f₁ U δ) < r := by
  classical
  by_contra hnot
  have hrle : r ≤ Module.finrank F (lineCloseSpan f₀ f₁ U δ) := by omega
  obtain ⟨T, hTclose, hTcard, hlinT⟩ :=
    exists_lineCloseSeeds_linearIndepOn_card_eq f₀ f₁ U δ hrle
  let A : Submodule F (ι → Fin s → F) :=
    Submodule.span F (U '' (↑T : Set F))
  have himage : U '' (↑T : Set F) =
      (↑(T.image U) : Set (ι → Fin s → F)) := by
    ext x
    simp only [Finset.coe_image, Set.mem_image]
  have hdimA : Module.finrank F A = r := by
    change Module.finrank F (Submodule.span F (U '' (↑T : Set F))) = r
    rw [himage]
    calc
      Module.finrank F (Submodule.span F
          (↑(T.image U) : Set (ι → Fin s → F))) = (T.image U).card := by
        apply finrank_span_finset_eq_card
        simpa only [← himage] using hlinT.id_image
      _ = T.card := Finset.card_image_of_injOn hlinT.injOn
      _ = r := hTcard
  have hAC : A ≤ C := by
    change Submodule.span F (U '' (↑T : Set F)) ≤ C
    rw [Submodule.span_le]
    rintro x ⟨γ, _hγ, rfl⟩
    exact hU γ
  have hdes := hdesign r A hAC (by rw [hdimA])
  have hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ := by
    intro γ hγ
    have hc := hTclose hγ
    have hm : γ ∈ (Finset.univ : Finset F) ∧
        (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ := by
      simpa only [lineCloseSeeds, Finset.mem_filter] using hc
    exact hm.2
  have hlower := lineClose_sum_agreement_lower f₀ f₁ U δ T hclose
  rw [hTcard] at hlower
  let d : ι → ℕ := fun i => Module.finrank F
    ↥(A ⊓ LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))
  have hlocal : ∀ i : ι,
      (lineAgreementSeeds f₀ f₁ U T i).card ≤ d i + 2 := by
    intro i
    simpa only [d, A] using
      lineAgreementSeeds_card_le_kernel_finrank_add_two f₀ f₁ U T hlinT i
  have hupper : (∑ i : ι,
      ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ)) ≤
      (∑ i : ι, (d i : ℝ)) + 2 * Fintype.card ι := by
    calc
      (∑ i : ι, ((lineAgreementSeeds f₀ f₁ U T i).card : ℝ)) ≤
          ∑ i : ι, ((d i + 2 : ℕ) : ℝ) := by
        exact Finset.sum_le_sum fun i _ => by exact_mod_cast hlocal i
      _ = (∑ i : ι, (d i : ℝ)) + 2 * Fintype.card ι := by
        push_cast
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hdes' : (∑ i : ι, (d i : ℝ)) / Fintype.card ι ≤
      (r : ℝ) * τ r := by
    rw [hdimA] at hdes
    simpa only [d, A] using hdes
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hksum : (∑ i : ι, (d i : ℝ)) ≤
      (Fintype.card ι : ℝ) * (r : ℝ) * τ r := by
    rw [div_le_iff₀ hn] at hdes'
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hdes'
  have htotal : (r : ℝ) * Fintype.card ι * (1 - δ) ≤
      (Fintype.card ι : ℝ) * (r : ℝ) * τ r +
        2 * Fintype.card ι := by
    exact hlower.trans (hupper.trans (add_le_add hksum le_rfl))
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hreps : (2 : ℝ) < (r : ℝ) * ε := by
    rw [div_lt_iff₀ hrR] at hε
    simpa only [mul_comm] using hε
  have hδ' : τ r + ε ≤ 1 - δ := by linarith
  have hn0 : (0 : ℝ) < Fintype.card ι := hn
  have hscaled := mul_le_mul_of_nonneg_left hδ' (mul_nonneg hrR.le hn0.le)
  have heps_scaled : 2 * Fintype.card ι <
      (Fintype.card ι : ℝ) * ((r : ℝ) * ε) := by
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hreps hn0
  have hcontra : (Fintype.card ι : ℝ) * (r : ℝ) * τ r +
      2 * Fintype.card ι < (r : ℝ) * Fintype.card ι * (1 - δ) := by
    calc
      (Fintype.card ι : ℝ) * (r : ℝ) * τ r + 2 * Fintype.card ι <
          (Fintype.card ι : ℝ) * (r : ℝ) * τ r +
            Fintype.card ι * ((r : ℝ) * ε) := by
              simpa only [add_comm] using
                add_lt_add_left heps_scaled ((Fintype.card ι : ℝ) * r * τ r)
      _ = ((r : ℝ) * Fintype.card ι) * (τ r + ε) := by ring
      _ ≤ ((r : ℝ) * Fintype.card ι) * (1 - δ) := hscaled
  exact (not_lt_of_ge htotal) hcontra

noncomputable def vanishOnCoordinates
    {ι : Type} {F : Type} [Field F] {s : ℕ} (S : Finset ι) :
    Submodule F (ι → Fin s → F) :=
  LinearMap.ker
    (LinearMap.funLeft F (Fin s → F) (Subtype.val : S → ι))

noncomputable def pinnedSubspace
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) :
    Submodule F (ι → Fin s → F) :=
  H ⊓ vanishOnCoordinates (F := F) (s := s) S

end CodingTheory.FrsInternal
