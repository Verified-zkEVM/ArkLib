/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.SubspaceDesign
import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding

set_option linter.style.longFile 2200

/-!
# MCA bound for folded Reed-Solomon codes up to capacity

This file proves the affine-line MCA bound for admissibly folded Reed--Solomon codes in the
capacity regime, via an affine-line collision-counting argument and a subspace-design
"pinning"/rank-drop induction.

## Main result

- `frs_mcaError_le` — ABF26 T4.14 [GG25 Cor 4.10]: folded RS up to capacity has the
  integer-native bound `ε_mca(C, 1 - ρ - 2/t) ≤ (nt + 3t³)/|F|`.

## References

- [GG25] Goyal and Guruswami, *Optimal Proximity Gaps for Subspace-Design Codes and (Random)
  Reed-Solomon Codes*, ePrint 2025/2054. Corollary 4.10.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

private noncomputable def affineLineCollisionSeeds
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (u₀ u₁ v₀ v₁ : ι → A) : Finset F :=
  Finset.univ.filter (fun γ => u₀ + γ • u₁ = v₀ + γ • v₁)

private noncomputable def affineLineCollisionSeeds_card_le_one
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

private noncomputable def boosted_frs_radius_le_list_radius
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
  have ha : (0 : ℝ) < 2 * t - 1 := by nlinarith
  have hb : (0 : ℝ) < t + 1 := by positivity
  have hd : (0 : ℝ) < (s : ℝ) - t + 1 := by nlinarith
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
    nlinarith
  have hbse : (0 : ℝ) ≤ s * t + 4 * s - (t : ℝ) ^ 2 - 3 * t + 4 := by
    nlinarith [mul_nonneg hgap (show (0 : ℝ) ≤ t + 4 by positivity)]
  nlinarith [mul_nonneg hR0 hc]

private noncomputable def exists_finset_lift_image_eq_injOn
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Set α) (t : Finset β)
    (h : (↑t : Set β) ⊆ f '' s) :
    ∃ u : Finset α, (↑u : Set α) ⊆ s ∧ Set.InjOn f (↑u : Set α) ∧
      u.image f = t := by
  classical
  apply Finset.exists_subset_injOn_image_eq_of_surjOn s t
  intro y hy
  exact h hy

open scoped BigOperators in
private noncomputable def exists_seed_pairwise_distinct_affine_lines
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (P : Finset ((ι → A) × (ι → A)))
    (hcard : P.card ^ 2 < Fintype.card F) :
    ∃ γ : F,
      Set.InjOn (fun p : (ι → A) × (ι → A) => p.1 + γ • p.2)
        (↑P : Set ((ι → A) × (ι → A))) := by
  classical
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
private noncomputable def finset_card_sdiff_biUnion_ge
    {α β : Type} [DecidableEq α] [DecidableEq β]
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
private noncomputable def globallyCloseAffinePairs_card_le
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

private noncomputable def lineAgreementSeeds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (T : Finset F) (i : ι) : Finset F :=
  T.filter (fun γ => U γ i = f₀ i + γ • f₁ i)

private noncomputable def lineAgreementSeeds_card_le_one_of_ne_at
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

private noncomputable def lineAgreement_span_finrank_le_two
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

private noncomputable def lineAgreementSeeds_card_le_kernel_finrank_add_two
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
private noncomputable def lineCloseSeeds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ) : Finset F :=
  Finset.univ.filter (fun γ => (δᵣ(f₀ + γ • f₁, U γ) : ℝ) ≤ δ)

open scoped NNReal in
private def StrongLineDecodable
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (C : Set (ι → Fin s → F)) (δ : NNReal) (a b : ℕ) : Prop :=
  ∀ f₀ f₁ : ι → Fin s → F, ∀ U : F → ι → Fin s → F,
    (∀ γ : F, U γ ∈ C) →
    ∀ T : Finset F, T ⊆ lineCloseSeeds f₀ f₁ U (δ : ℝ) → a ≤ T.card →
      ∃ u₀ ∈ C, ∃ u₁ ∈ C,
        b ≤ (T.filter (fun γ => U γ = u₀ + γ • u₁)).card

open scoped NNReal in
private noncomputable def lineCloseSpan
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ) :
    Submodule F (ι → Fin s → F) :=
  Submodule.span F (U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F))

private noncomputable def exists_lineCloseSeeds_linearIndepOn_card_eq
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
private noncomputable def lineCloseSpan_le_code
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
private noncomputable def lineClose_sum_agreement_lower
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
private noncomputable def aligned_affineLine_global_close
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s b : ℕ} (hb : 1 < b)
    (f₀ f₁ u₀ u₁ : ι → Fin s → F) (T : Finset F)
    (hTcard : T.card = b) (δ : ℝ)
    (hclose : ∀ α ∈ T,
      (Code.relHammingDist (f₀ + α • f₁) (u₀ + α • u₁) : ℝ) ≤ δ)
    (γ : F) :
    (Code.relHammingDist (f₀ + γ • f₁) (u₀ + γ • u₁) : ℝ) ≤
      δ * (b : ℝ) / ((b : ℝ) - 1) := by
  classical
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

private noncomputable def linePinnedSeedsOn
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (S : Finset ι) : Finset F :=
  T.filter (fun γ => ∀ i ∈ S, U γ i = f₀ i + γ • f₁ i)

private noncomputable def linePinnedSeedsOn_empty
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) :
    linePinnedSeedsOn T f₀ f₁ U ∅ = T := by
  classical
  ext γ
  simp [linePinnedSeedsOn]

private noncomputable def linePinnedSeedsOn_insert
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

private noncomputable def linePinnedSeedsOn_insert_subset
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

private noncomputable def linePinnedSeedsOn_insert_card_le
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
private noncomputable def mcaError_affineLine_zero_le_inv_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) :
    mcaError (AffineLineGenerator F) C 0 ≤
      ENNReal.ofReal (1 / (Fintype.card F : ℝ)) := by
  classical
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

private noncomputable def mcaError_eq_zero_of_neg_radius
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
    {ℓ : Type} [Fintype ℓ]
    {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]
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

private noncomputable def pinning_potential_compose
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

private noncomputable def sharpSubspaceProfile
    {ι : Type} [Fintype ι] (s : ℕ) (R : ℝ) : ℕ → ℝ :=
  fun r => if r ∈ Finset.Icc 1 s then
    (s * R - 1 / Fintype.card ι) / (s - r + 1)
  else 1

private noncomputable def isSubspaceDesign_frsCode_sharpProfile
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
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
  have hrate : (LinearCode.alphabetRate
      (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) =
      (k : ℝ) / (s * Fintype.card ι) := by
    rw [ReedSolomon.Folded.alphabetRate_frsCode domain k s ω hadm hω hk]
  have hdesign := isSubspaceDesign_frsCode_sub_one domain k s ω hFn hadm hωgen
  rw [hrate] at hdesign
  refine hdesign.mono_tau fun r => ?_
  rw [sharpSubspaceProfile]

private noncomputable def sharpSubspaceProfile_eq_fun
    {ι : Type} [Fintype ι] (s : ℕ) (R : ℝ) :
    sharpSubspaceProfile (ι := ι) s R =
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) := by
  rfl

private noncomputable def sharpSubspaceProfile_two_mul_le_rate_add
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
private noncomputable def strongLineDecodable_boost_of_lambda_le
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
private noncomputable def strongLineDecodable_to_isLineDecodable
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
private noncomputable def subspaceDesign_lineCloseSpan_finrank_lt
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
    nlinarith
  have htotal : (r : ℝ) * Fintype.card ι * (1 - δ) ≤
      (Fintype.card ι : ℝ) * (r : ℝ) * τ r +
        2 * Fintype.card ι := by
    exact le_trans hlower (hupper.trans (by nlinarith))
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hreps : (2 : ℝ) < (r : ℝ) * ε := by
    rw [div_lt_iff₀ hrR] at hε
    nlinarith
  have hδ' : τ r + ε ≤ 1 - δ := by linarith
  have hn0 : (0 : ℝ) < Fintype.card ι := hn
  nlinarith [mul_le_mul_of_nonneg_left hδ'
    (mul_nonneg hrR.le hn0.le)]

private noncomputable def vanishOnCoordinates
    {ι : Type} {F : Type} [Field F] {s : ℕ} (S : Finset ι) :
    Submodule F (ι → Fin s → F) :=
  LinearMap.ker
    (LinearMap.funLeft F (Fin s → F) (Subtype.val : S → ι))

private noncomputable def pinnedSubspace
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) :
    Submodule F (ι → Fin s → F) :=
  H ⊓ vanishOnCoordinates (F := F) (s := s) S

private noncomputable def pinnedSubspace_empty
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) :
    pinnedSubspace H (∅ : Finset ι) = H := by
  rw [pinnedSubspace]
  apply le_antisymm inf_le_left
  intro x hx
  refine ⟨hx, ?_⟩
  apply LinearMap.mem_ker.mpr
  exact Subsingleton.elim _ _

private noncomputable def pinned_lineSeeds_lie_on_affine_codeword_line
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s : ℕ} (C : Submodule F (ι → Fin s → F))
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ : ℝ) (T : Finset F)
    (hTclose : T ⊆ lineCloseSeeds f₀ f₁ U δ)
    (hU : ∀ γ : F, U γ ∈ C)
    (S : Finset ι)
    (hterminal : lineCloseSpan f₀ f₁ U δ ⊓
      vanishOnCoordinates (F := F) (s := s) S = ⊥)
    (hcard : 2 ≤ (linePinnedSeedsOn T f₀ f₁ U S).card) :
    ∃ u₀ ∈ C, ∃ u₁ ∈ C,
      ∀ γ ∈ linePinnedSeedsOn T f₀ f₁ U S,
        U γ = u₀ + γ • u₁ := by
  classical
  let A := linePinnedSeedsOn T f₀ f₁ U S
  have hAone : 1 < A.card := by dsimp [A]; omega
  obtain ⟨α, hαA, β, hβA, hαβ⟩ := Finset.one_lt_card.mp hAone
  have hα : α ∈ linePinnedSeedsOn T f₀ f₁ U S := by simpa only [A] using hαA
  have hβ : β ∈ linePinnedSeedsOn T f₀ f₁ U S := by simpa only [A] using hβA
  have hαdata : α ∈ T ∧ ∀ i ∈ S, U α i = f₀ i + α • f₁ i := by
    simpa only [linePinnedSeedsOn, Finset.mem_filter] using hα
  have hβdata : β ∈ T ∧ ∀ i ∈ S, U β i = f₀ i + β • f₁ i := by
    simpa only [linePinnedSeedsOn, Finset.mem_filter] using hβ
  let u₁ : ι → Fin s → F := (β - α)⁻¹ • (U β - U α)
  let u₀ : ι → Fin s → F := U α - α • u₁
  have hu₁C : u₁ ∈ C := by
    exact C.smul_mem _ (C.sub_mem (hU β) (hU α))
  have hu₀C : u₀ ∈ C := by
    exact C.sub_mem (hU α) (C.smul_mem α hu₁C)
  have hUαH : U α ∈ lineCloseSpan f₀ f₁ U δ := by
    change U α ∈ Submodule.span F
      (U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F))
    apply Submodule.subset_span
    exact ⟨α, hTclose hαdata.1, rfl⟩
  have hUβH : U β ∈ lineCloseSpan f₀ f₁ U δ := by
    change U β ∈ Submodule.span F
      (U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F))
    apply Submodule.subset_span
    exact ⟨β, hTclose hβdata.1, rfl⟩
  have hu₁H : u₁ ∈ lineCloseSpan f₀ f₁ U δ := by
    exact (lineCloseSpan f₀ f₁ U δ).smul_mem _
      ((lineCloseSpan f₀ f₁ U δ).sub_mem hUβH hUαH)
  have hu₀H : u₀ ∈ lineCloseSpan f₀ f₁ U δ := by
    exact (lineCloseSpan f₀ f₁ U δ).sub_mem hUαH
      ((lineCloseSpan f₀ f₁ U δ).smul_mem α hu₁H)
  refine ⟨u₀, hu₀C, u₁, hu₁C, ?_⟩
  intro γ hγ
  have hγdata : γ ∈ T ∧ ∀ i ∈ S, U γ i = f₀ i + γ • f₁ i := by
    simpa only [linePinnedSeedsOn, Finset.mem_filter] using hγ
  have hUγH : U γ ∈ lineCloseSpan f₀ f₁ U δ := by
    change U γ ∈ Submodule.span F
      (U '' (↑(lineCloseSeeds f₀ f₁ U δ) : Set F))
    apply Submodule.subset_span
    exact ⟨γ, hTclose hγdata.1, rfl⟩
  let w : ι → Fin s → F := U γ - (u₀ + γ • u₁)
  have hwH : w ∈ lineCloseSpan f₀ f₁ U δ := by
    exact (lineCloseSpan f₀ f₁ U δ).sub_mem hUγH
      ((lineCloseSpan f₀ f₁ U δ).add_mem hu₀H
        ((lineCloseSpan f₀ f₁ U δ).smul_mem γ hu₁H))
  have hwV : w ∈ vanishOnCoordinates (F := F) (s := s) S := by
    apply LinearMap.mem_ker.mpr
    funext i j
    have ha := congrFun (hαdata.2 i i.property) j
    have hb := congrFun (hβdata.2 i i.property) j
    have hg := congrFun (hγdata.2 i i.property) j
    simp only [Pi.add_apply, Pi.smul_apply] at ha hb hg
    dsimp [w, u₀, u₁]
    rw [ha, hb, hg]
    field_simp [sub_ne_zero.mpr (Ne.symm hαβ)]
    ring
  have hwK : w ∈ lineCloseSpan f₀ f₁ U δ ⊓
      vanishOnCoordinates (F := F) (s := s) S := ⟨hwH, hwV⟩
  rw [hterminal] at hwK
  have hw0 : w = 0 := (Submodule.mem_bot F).mp hwK
  exact sub_eq_zero.mp hw0

private noncomputable def pinningActiveCoordinates
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i =>
    Module.finrank F (pinnedSubspace H (insert i S)) <
      Module.finrank F (pinnedSubspace H S))

private noncomputable def pinningInactiveCoordinates
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i =>
    pinnedSubspace H (insert i S) = pinnedSubspace H S)

private noncomputable def pinningActiveCoordinates_disjoint_inactive
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) :
    Disjoint (pinningActiveCoordinates H S)
      (pinningInactiveCoordinates H S) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiE hiZ
  have hlt : Module.finrank F (pinnedSubspace H (insert i S)) <
      Module.finrank F (pinnedSubspace H S) := by
    simpa only [pinningActiveCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] using hiE
  have heq : pinnedSubspace H (insert i S) = pinnedSubspace H S := by
    simpa only [pinningInactiveCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] using hiZ
  rw [heq] at hlt
  exact (lt_irrefl _ hlt).elim

open scoped BigOperators in
private noncomputable def pinning_tau_nonneg
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F) (δ : ℝ)
    (hU : ∀ γ : F, U γ ∈ C)
    (hspan : Module.finrank F (lineCloseSpan f₀ f₁ U δ) ≤ r)
    (S : Finset ι)
    (hK : lineCloseSpan f₀ f₁ U δ ⊓
      vanishOnCoordinates (F := F) (s := s) S ≠ ⊥) :
    0 ≤ τ r := by
  classical
  let K : Submodule F (ι → Fin s → F) :=
    lineCloseSpan f₀ f₁ U δ ⊓
      vanishOnCoordinates (F := F) (s := s) S
  have hKC : K ≤ C :=
    le_trans inf_le_left (lineCloseSpan_le_code C f₀ f₁ U δ hU)
  have hKr : Module.finrank F K ≤ r :=
    le_trans (Submodule.finrank_mono inf_le_left) hspan
  have hdes := hdesign r K hKC hKr
  have hdposNat : 0 < Module.finrank F K := by
    by_contra h
    have hz : Module.finrank F K = 0 := by omega
    exact hK ((Submodule.finrank_eq_zero).mp hz)
  have hdpos : (0 : ℝ) < Module.finrank F K := by exact_mod_cast hdposNat
  have hsum : (0 : ℝ) ≤
      ∑ i : ι,
        (Module.finrank F ↥(K ⊓
          LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ) := by
    exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hleft : (0 : ℝ) ≤
      (∑ i : ι,
        (Module.finrank F ↥(K ⊓
          LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) /
        Fintype.card ι := div_nonneg hsum hn
  have hprod : (0 : ℝ) ≤ Module.finrank F K * τ r := hleft.trans hdes
  nlinarith

private noncomputable def vanishOnCoordinates_insert
    {ι : Type} [DecidableEq ι] {F : Type} [Field F] {s : ℕ}
    (S : Finset ι) (i : ι) :
    vanishOnCoordinates (F := F) (s := s) (insert i S) =
      vanishOnCoordinates (F := F) (s := s) S ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
  classical
  ext x
  constructor
  · intro hx
    have hall := LinearMap.mem_ker.mp hx
    constructor
    · apply LinearMap.mem_ker.mpr
      funext j
      have hj := congrFun hall
        (⟨j, Finset.mem_insert_of_mem j.property⟩ : ↥(insert i S))
      simpa [vanishOnCoordinates] using hj
    · apply LinearMap.mem_ker.mpr
      have hi := congrFun hall
        (⟨i, Finset.mem_insert_self i S⟩ : ↥(insert i S))
      simpa [vanishOnCoordinates, LinearMap.proj_apply] using hi
  · rintro ⟨hxS, hxi⟩
    apply LinearMap.mem_ker.mpr
    funext j
    rcases Finset.mem_insert.mp j.property with hji | hjS
    · change x (j : ι) = 0
      rw [hji]
      have hi := LinearMap.mem_ker.mp hxi
      simpa [LinearMap.proj_apply] using hi
    · have hallS := LinearMap.mem_ker.mp hxS
      have hj := congrFun hallS (⟨j, hjS⟩ : ↥S)
      simpa [vanishOnCoordinates] using hj

private noncomputable def pinnedSubspace_insert_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) (i : ι) :
    pinnedSubspace H (insert i S) ≤ pinnedSubspace H S := by
  rw [pinnedSubspace, pinnedSubspace, vanishOnCoordinates_insert, ← inf_assoc]
  exact inf_le_left

private noncomputable def pinningActiveCoordinates_nonempty
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι)
    (hK : pinnedSubspace H S ≠ ⊥) :
    (pinningActiveCoordinates H S).Nonempty := by
  classical
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  obtain ⟨i, hi⟩ : ∃ i : ι, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hproper : pinnedSubspace H (insert i S) < pinnedSubspace H S := by
    apply lt_of_le_of_ne (pinnedSubspace_insert_le H S i)
    intro heq
    have hxchild : x ∈ pinnedSubspace H (insert i S) := by
      rw [heq]
      exact hxK
    apply hi
    have hall := LinearMap.mem_ker.mp hxchild.2
    have hzero := congrFun hall
      (⟨i, Finset.mem_insert_self i S⟩ : ↥(insert i S))
    simpa [vanishOnCoordinates] using hzero
  refine ⟨i, ?_⟩
  simp only [pinningActiveCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Submodule.finrank_lt_finrank_of_lt hproper

private noncomputable def pinning_active_or_inactive
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) (i : ι) :
    i ∈ pinningActiveCoordinates H S ∨
      i ∈ pinningInactiveCoordinates H S := by
  classical
  by_cases heq : pinnedSubspace H (insert i S) = pinnedSubspace H S
  · right
    simp only [pinningInactiveCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact heq
  · left
    simp only [pinningActiveCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (pinnedSubspace_insert_le H S i) heq)

private noncomputable def pinningActiveCoordinates_union_inactive
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) :
    pinningActiveCoordinates H S ∪ pinningInactiveCoordinates H S =
      (Finset.univ : Finset ι) := by
  classical
  ext i
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  exact pinning_active_or_inactive H S i

open scoped BigOperators in
open scoped NNReal in
private noncomputable def pinned_child_card_sum_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r : ℕ} (τ : ℕ → ℝ)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ ε : ℝ) (T : Finset F)
    (hTclose : T ⊆ lineCloseSeeds f₀ f₁ U δ)
    (hδ : δ ≤ 1 - τ r - ε) (S : Finset ι) :
    ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) *
        ((Fintype.card ι : ℝ) * (τ r + ε) -
          ((pinningInactiveCoordinates (lineCloseSpan f₀ f₁ U δ) S).card : ℝ)) ≤
      ∑ i ∈ pinningActiveCoordinates (lineCloseSpan f₀ f₁ U δ) S,
        ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ) := by
  classical
  let H := lineCloseSpan f₀ f₁ U δ
  let A := linePinnedSeedsOn T f₀ f₁ U S
  have hclose : ∀ γ ∈ A,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ := by
    intro γ hγ
    have hdata : γ ∈ T ∧ ∀ i ∈ S, U γ i = f₀ i + γ • f₁ i := by
      simpa only [A, linePinnedSeedsOn, Finset.mem_filter] using hγ
    have hm := hTclose hdata.1
    have hm' : γ ∈ (Finset.univ : Finset F) ∧
        (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ := by
      simpa only [lineCloseSeeds, Finset.mem_filter] using hm
    exact hm'.2
  have hlower := lineClose_sum_agreement_lower f₀ f₁ U δ A hclose
  have hrad : τ r + ε ≤ 1 - δ := by linarith
  have htotal :
      (A.card : ℝ) * Fintype.card ι * (τ r + ε) ≤
        ∑ i : ι,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ) := by
    calc
      (A.card : ℝ) * Fintype.card ι * (τ r + ε) ≤
          (A.card : ℝ) * Fintype.card ι * (1 - δ) := by
            exact mul_le_mul_of_nonneg_left hrad
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ ≤ ∑ i : ι, ((lineAgreementSeeds f₀ f₁ U A i).card : ℝ) := hlower
      _ = ∑ i : ι,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [linePinnedSeedsOn_insert]
  have hsplit :
      (∑ i : ι,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) =
        (∑ i ∈ pinningActiveCoordinates H S,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) +
        (∑ i ∈ pinningInactiveCoordinates H S,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) := by
    rw [← pinningActiveCoordinates_union_inactive H S,
      Finset.sum_union (pinningActiveCoordinates_disjoint_inactive H S)]
  have hZupper :
      (∑ i ∈ pinningInactiveCoordinates H S,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) ≤
        ((pinningInactiveCoordinates H S).card : ℝ) * (A.card : ℝ) := by
    calc
      (∑ i ∈ pinningInactiveCoordinates H S,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) ≤
          ∑ _i ∈ pinningInactiveCoordinates H S, (A.card : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact_mod_cast linePinnedSeedsOn_insert_card_le T f₀ f₁ U S i
      _ = ((pinningInactiveCoordinates H S).card : ℝ) * (A.card : ℝ) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hsplit] at htotal
  dsimp only [H, A] at htotal hZupper ⊢
  nlinarith

open scoped BigOperators in
private noncomputable def pinning_weight_sum_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] {s r : ℕ}
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C)
    (hHr : Module.finrank F H ≤ r)
    (ε : ℝ) (hε : 0 < ε) (hτ : 0 ≤ τ r)
    (S : Finset ι) (hK : pinnedSubspace H S ≠ ⊥) :
    (∑ i ∈ pinningActiveCoordinates H S,
        ((Module.finrank F (pinnedSubspace H (insert i S)) : ℝ) + ε)) ≤
      ((Module.finrank F (pinnedSubspace H S) : ℝ) + ε) *
        ((Fintype.card ι : ℝ) * (τ r + ε) -
          ((pinningInactiveCoordinates H S).card : ℝ)) := by
  classical
  have hKC : pinnedSubspace H S ≤ C := by
    apply le_trans _ hHC
    rw [pinnedSubspace]
    exact inf_le_left
  have hKr : Module.finrank F (pinnedSubspace H S) ≤ r :=
    le_trans (Submodule.finrank_mono (by
      rw [pinnedSubspace]
      exact inf_le_left)) hHr
  have hchild (i : ι) :
      pinnedSubspace H S ⊓
          LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) =
        pinnedSubspace H (insert i S) := by
    rw [pinnedSubspace, pinnedSubspace, vanishOnCoordinates_insert, inf_assoc]
  have hdes := hdesign r (pinnedSubspace H S) hKC hKr
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at hdes
  have hsum_le :
      (∑ i : ι,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) ≤
        (Fintype.card ι : ℝ) *
          (Module.finrank F (pinnedSubspace H S) : ℝ) * τ r := by
    calc
      (∑ i : ι,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) =
          ∑ i : ι, (Module.finrank F
            ↥(pinnedSubspace H S ⊓
              LinearMap.ker
                (LinearMap.proj (R := F)
                  (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hchild i]
      _ ≤ (Module.finrank F (pinnedSubspace H S) : ℝ) * τ r *
          Fintype.card ι := hdes
      _ = (Fintype.card ι : ℝ) *
          (Module.finrank F (pinnedSubspace H S) : ℝ) * τ r := by ring
  have hsplit :
      (∑ i : ι,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) =
        (∑ i ∈ pinningActiveCoordinates H S,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) +
        (∑ i ∈ pinningInactiveCoordinates H S,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) := by
    rw [← pinningActiveCoordinates_union_inactive H S,
      Finset.sum_union (pinningActiveCoordinates_disjoint_inactive H S)]
  have hsumZ :
      (∑ i ∈ pinningInactiveCoordinates H S,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) =
        ((pinningInactiveCoordinates H S).card : ℝ) *
          (Module.finrank F (pinnedSubspace H S) : ℝ) := by
    calc
      (∑ i ∈ pinningInactiveCoordinates H S,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) =
          ∑ _i ∈ pinningInactiveCoordinates H S,
            (Module.finrank F (pinnedSubspace H S) : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              have heq : pinnedSubspace H (insert i S) = pinnedSubspace H S := by
                simpa only [pinningInactiveCoordinates, Finset.mem_filter,
                  Finset.mem_univ, true_and] using hi
              rw [heq]
      _ = ((pinningInactiveCoordinates H S).card : ℝ) *
          (Module.finrank F (pinnedSubspace H S) : ℝ) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
  have hcardNat :
      (pinningActiveCoordinates H S).card +
        (pinningInactiveCoordinates H S).card = Fintype.card ι := by
    have hc := Finset.card_union_of_disjoint
      (pinningActiveCoordinates_disjoint_inactive H S)
    rw [pinningActiveCoordinates_union_inactive H S, Finset.card_univ] at hc
    omega
  have hcardR :
      ((pinningActiveCoordinates H S).card : ℝ) +
        ((pinningInactiveCoordinates H S).card : ℝ) = Fintype.card ι := by
    exact_mod_cast hcardNat
  have hdposNat : 0 < Module.finrank F (pinnedSubspace H S) := by
    by_contra h
    have hz : Module.finrank F (pinnedSubspace H S) = 0 := by omega
    exact hK ((Submodule.finrank_eq_zero).mp hz)
  have hdge : (1 : ℝ) ≤ Module.finrank F (pinnedSubspace H S) := by
    exact_mod_cast hdposNat
  have hsumE :
      (∑ i ∈ pinningActiveCoordinates H S,
          (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)) +
        ((pinningInactiveCoordinates H S).card : ℝ) *
          (Module.finrank F (pinnedSubspace H S) : ℝ) ≤
        (Fintype.card ι : ℝ) *
          (Module.finrank F (pinnedSubspace H S) : ℝ) * τ r := by
    rw [hsplit, hsumZ] at hsum_le
    exact hsum_le
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hfac : (0 : ℝ) ≤ τ r +
      Module.finrank F (pinnedSubspace H S) + ε - 1 := by linarith
  have hprod : (0 : ℝ) ≤
      (Fintype.card ι : ℝ) * ε *
        (τ r + Module.finrank F (pinnedSubspace H S) + ε - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hε.le) hfac
  nlinarith

open scoped BigOperators in
private noncomputable def shared_pinning_step
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ ε : ℝ) (hU : ∀ γ : F, U γ ∈ C)
    (hspan : Module.finrank F (lineCloseSpan f₀ f₁ U δ) ≤ r)
    (hε : 0 < ε) (T : Finset F)
    (hTclose : T ⊆ lineCloseSeeds f₀ f₁ U δ)
    (hδ : δ ≤ 1 - τ r - ε) (S : Finset ι)
    (hK : pinnedSubspace (lineCloseSpan f₀ f₁ U δ) S ≠ ⊥) :
    ∃ i ∈ pinningActiveCoordinates (lineCloseSpan f₀ f₁ U δ) S,
      Module.finrank F
          (pinnedSubspace (lineCloseSpan f₀ f₁ U δ) (insert i S)) <
        Module.finrank F
          (pinnedSubspace (lineCloseSpan f₀ f₁ U δ) S) ∧
      ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) *
          ((Module.finrank F
            (pinnedSubspace (lineCloseSpan f₀ f₁ U δ) (insert i S)) : ℝ) + ε) ≤
        ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ) *
          ((Module.finrank F
            (pinnedSubspace (lineCloseSpan f₀ f₁ U δ) S) : ℝ) + ε) := by
  classical
  let H := lineCloseSpan f₀ f₁ U δ
  let E := pinningActiveCoordinates H S
  let A : ℝ := (linePinnedSeedsOn T f₀ f₁ U S).card
  let d : ℝ := Module.finrank F (pinnedSubspace H S)
  let B : ℝ := (Fintype.card ι : ℝ) * (τ r + ε) -
    ((pinningInactiveCoordinates H S).card : ℝ)
  have hHC : H ≤ C := by
    dsimp only [H]
    exact lineCloseSpan_le_code C f₀ f₁ U δ hU
  have hτ : 0 ≤ τ r := by
    exact pinning_tau_nonneg τ C hdesign f₀ f₁ U δ hU hspan S (by
      simpa only [H, pinnedSubspace] using hK)
  have hw := pinning_weight_sum_le τ C hdesign H hHC hspan ε hε hτ S hK
  have hc := pinned_child_card_sum_lower τ f₀ f₁ U δ ε T hTclose hδ S
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hd : 0 < d + ε := by
    dsimp only [d]
    have : (0 : ℝ) ≤ Module.finrank F (pinnedSubspace H S) := Nat.cast_nonneg _
    linarith
  have htotal :
      (∑ i ∈ E,
          A * ((Module.finrank F (pinnedSubspace H (insert i S)) : ℝ) + ε)) ≤
        ∑ i ∈ E,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ) * (d + ε) := by
    have hw' : A *
        (∑ i ∈ E,
          ((Module.finrank F (pinnedSubspace H (insert i S)) : ℝ) + ε)) ≤
        A * ((d + ε) * B) := by
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [H, E, d, B] using hw
    have hc' : A * B * (d + ε) ≤
        (∑ i ∈ E,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) * (d + ε) := by
      apply mul_le_mul_of_nonneg_right _ hd.le
      simpa only [H, E, A, B] using hc
    calc
      (∑ i ∈ E,
          A * ((Module.finrank F (pinnedSubspace H (insert i S)) : ℝ) + ε)) =
          A * (∑ i ∈ E,
            ((Module.finrank F (pinnedSubspace H (insert i S)) : ℝ) + ε)) := by
              rw [Finset.mul_sum]
      _ ≤ A * ((d + ε) * B) := hw'
      _ = A * B * (d + ε) := by ring
      _ ≤ (∑ i ∈ E,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)) * (d + ε) := hc'
      _ = ∑ i ∈ E,
          ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ) * (d + ε) := by
            rw [Finset.sum_mul]
  obtain ⟨i, hiE, hi⟩ := Finset.exists_le_of_sum_le
    (pinningActiveCoordinates_nonempty H S hK) htotal
  refine ⟨i, ?_, ?_, ?_⟩
  · simpa only [E] using hiE
  · simpa only [E, pinningActiveCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] using hiE
  · simpa only [H, A, d] using hi

open scoped BigOperators in
private noncomputable def exists_terminal_line_pinning
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ ε : ℝ) (hU : ∀ γ : F, U γ ∈ C)
    (hspan : Module.finrank F (lineCloseSpan f₀ f₁ U δ) ≤ r)
    (hε : 0 < ε) (T : Finset F)
    (hTclose : T ⊆ lineCloseSeeds f₀ f₁ U δ)
    (hδ : δ ≤ 1 - τ r - ε) (S : Finset ι) :
    ∃ S' : Finset ι,
      pinnedSubspace (lineCloseSpan f₀ f₁ U δ) S' = ⊥ ∧
      ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) * ε ≤
        ((linePinnedSeedsOn T f₀ f₁ U S').card : ℝ) *
          ((Module.finrank F
            (pinnedSubspace (lineCloseSpan f₀ f₁ U δ) S) : ℝ) + ε) := by
  classical
  let H := lineCloseSpan f₀ f₁ U δ
  have hrec : ∀ d : ℕ, ∀ S : Finset ι,
      Module.finrank F (pinnedSubspace H S) = d →
      ∃ S' : Finset ι,
        pinnedSubspace H S' = ⊥ ∧
        ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) * ε ≤
          ((linePinnedSeedsOn T f₀ f₁ U S').card : ℝ) *
            ((d : ℝ) + ε) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro S hd
        by_cases hbot : pinnedSubspace H S = ⊥
        · refine ⟨S, hbot, ?_⟩
          have hd0 : d = 0 := by
            rw [← hd, hbot]
            exact finrank_bot F _
          rw [hd0]
          norm_num
        · obtain ⟨i, hiE, hlt, hstep⟩ := shared_pinning_step τ C hdesign
            f₀ f₁ U δ ε hU hspan hε T hTclose hδ S (by
              simpa only [H] using hbot)
          have hlt' : Module.finrank F (pinnedSubspace H (insert i S)) < d := by
            simpa only [H, hd] using hlt
          obtain ⟨S', hterm, hind⟩ :=
            ih (Module.finrank F (pinnedSubspace H (insert i S))) hlt'
              (insert i S) rfl
          refine ⟨S', hterm, ?_⟩
          apply pinning_potential_compose
            ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ)
            ((linePinnedSeedsOn T f₀ f₁ U (insert i S)).card : ℝ)
            ((linePinnedSeedsOn T f₀ f₁ U S').card : ℝ)
            (d : ℝ)
            (Module.finrank F (pinnedSubspace H (insert i S)) : ℝ)
            ε (Nat.cast_nonneg _) (Nat.cast_nonneg _) hε
          · simpa only [H, hd] using hstep
          · exact hind
  obtain ⟨S', hterm, hpot⟩ :=
    hrec (Module.finrank F (pinnedSubspace H S)) S rfl
  refine ⟨S', ?_, ?_⟩
  · simpa only [H] using hterm
  · simpa only [H] using hpot

open scoped NNReal in
open scoped BigOperators in
private noncomputable def strongLineDecodable_of_subspaceDesign
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s r a b : ℕ} (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (hr : 0 < r) (ε : ℝ) (hε : 2 / (r : ℝ) < ε)
    (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 - τ r - ε)
    (hb : 2 ≤ b)
    (hretain : (b : ℝ) * ((r : ℝ) + ε) ≤ (a : ℝ) * ε) :
    StrongLineDecodable (C : Set (ι → Fin s → F)) δ a b := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hεpos : 0 < ε := lt_trans (by positivity : (0 : ℝ) < 2 / (r : ℝ)) hε
  intro f₀ f₁ U hU T hTclose ha
  have hspanlt := subspaceDesign_lineCloseSpan_finrank_lt τ C hdesign
    f₀ f₁ U hU (δ : ℝ) ε r hr hδ hε
  have hspanle : Module.finrank F (lineCloseSpan f₀ f₁ U (δ : ℝ)) ≤ r :=
    Nat.le_of_lt hspanlt
  obtain ⟨S, hterm, hpot⟩ := exists_terminal_line_pinning τ C hdesign
    f₀ f₁ U (δ : ℝ) ε hU hspanle hεpos T hTclose hδ ∅
  rw [linePinnedSeedsOn_empty,
    pinnedSubspace_empty (lineCloseSpan f₀ f₁ U (δ : ℝ))] at hpot
  have haR : (a : ℝ) ≤ T.card := by exact_mod_cast ha
  have haeps : (a : ℝ) * ε ≤ (T.card : ℝ) * ε :=
    mul_le_mul_of_nonneg_right haR hεpos.le
  have hdR : (Module.finrank F (lineCloseSpan f₀ f₁ U (δ : ℝ)) : ℝ) < r := by
    exact_mod_cast hspanlt
  have hA0 : (0 : ℝ) ≤ (linePinnedSeedsOn T f₀ f₁ U S).card := Nat.cast_nonneg _
  have hdim :
      ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) *
          ((Module.finrank F (lineCloseSpan f₀ f₁ U (δ : ℝ)) : ℝ) + ε) ≤
        ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) * ((r : ℝ) + ε) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    linarith
  have hchain : (b : ℝ) * ((r : ℝ) + ε) ≤
      ((linePinnedSeedsOn T f₀ f₁ U S).card : ℝ) * ((r : ℝ) + ε) :=
    hretain.trans (haeps.trans (hpot.trans hdim))
  have hden : 0 < (r : ℝ) + ε := by linarith
  have hbR : (b : ℝ) ≤ (linePinnedSeedsOn T f₀ f₁ U S).card :=
    le_of_mul_le_mul_right hchain hden
  have hbNat : b ≤ (linePinnedSeedsOn T f₀ f₁ U S).card := by
    exact_mod_cast hbR
  have hterm' : lineCloseSpan f₀ f₁ U (δ : ℝ) ⊓
      vanishOnCoordinates (F := F) (s := s) S = ⊥ := by
    simpa only [pinnedSubspace] using hterm
  obtain ⟨u₀, hu₀, u₁, hu₁, halign⟩ :=
    pinned_lineSeeds_lie_on_affine_codeword_line C f₀ f₁ U (δ : ℝ)
      T hTclose hU S hterm' (hb.trans hbNat)
  refine ⟨u₀, hu₀, u₁, hu₁, hbNat.trans (Finset.card_le_card ?_)⟩
  intro γ hγ
  have hdata : γ ∈ T ∧ ∀ i ∈ S, U γ i = f₀ i + γ • f₁ i := by
    simpa only [linePinnedSeedsOn, Finset.mem_filter] using hγ
  apply Finset.mem_filter.mpr
  exact ⟨hdata.1, halign γ hγ⟩

open scoped NNReal in
private noncomputable def strongLineDecodable_two_mul_of_profile_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {s t : ℕ} (τ : ℕ → ℝ) (R : ℝ)
    (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (ht : 3 ≤ t)
    (δ : NNReal)
    (hprofile : τ (2 * t) ≤ R + 1 / (2 * (t : ℝ)))
    (hδ : (δ : ℝ) ≤ 1 - R - 2 / (t : ℝ)) :
    StrongLineDecodable (C : Set (ι → Fin s → F)) δ
      (3 * t ^ 3) (2 * t) := by
  have htpos : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have htR3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hden : (0 : ℝ) < 2 * (t : ℝ) := by positivity
  have hrad : (δ : ℝ) ≤
      1 - τ (2 * t) - 3 / (2 * (t : ℝ)) := by
    have hid : 1 / (2 * (t : ℝ)) + 3 / (2 * (t : ℝ)) = 2 / (t : ℝ) := by
      field_simp
      ring
    nlinarith
  have heps : 2 / (((2 * t : ℕ) : ℝ)) < 3 / (2 * (t : ℝ)) := by
    push_cast
    exact div_lt_div_of_pos_right (by norm_num) hden
  have hret : (((2 * t : ℕ) : ℝ)) *
        ((((2 * t : ℕ) : ℝ)) + 3 / (2 * (t : ℝ))) ≤
      (((3 * t ^ 3 : ℕ) : ℝ)) * (3 / (2 * (t : ℝ))) := by
    have hsq : (9 : ℝ) ≤ (t : ℝ) ^ 2 := by
      have hmul : (0 : ℝ) ≤ ((t : ℝ) - 3) * ((t : ℝ) + 3) :=
        mul_nonneg (sub_nonneg.mpr htR3) (by linarith)
      nlinarith
    push_cast
    field_simp
    nlinarith
  exact strongLineDecodable_of_subspaceDesign τ C hdesign (by omega)
    (3 / (2 * (t : ℝ))) heps δ hrad (by omega) hret

open scoped NNReal in
open Code in
private noncomputable def frs_mcaError_le_proof
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hω : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hcard : s * Fintype.card ι < Fintype.card F)
    (t : ℕ) (_ht_pos : 0 < t)
    (_hs_gt : 4 * t ^ 2 < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - ρ - 2 / (t : ℝ)) ≤
      ENNReal.ofReal ((n * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) := by
  dsimp
  classical
  let R : ℝ := (k : ℝ) / ((s : ℝ) * Fintype.card ι)
  let δr : ℝ := 1 - R - 2 / (t : ℝ)
  change mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω) δr ≤
    ENNReal.ofReal (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F)
  by_cases hδneg : δr < 0
  · rw [mcaError_eq_zero_of_neg_radius _ _ hδneg]
    exact bot_le
  have hδ0 : 0 ≤ δr := le_of_not_gt hδneg
  by_cases hδzero : δr = 0
  · rw [hδzero]
    calc
      mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω) 0
          ≤ ENNReal.ofReal (1 / (Fintype.card F : ℝ)) :=
        mcaError_affineLine_zero_le_inv_card _
      _ ≤ ENNReal.ofReal
          (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) := by
        apply ENNReal.ofReal_le_ofReal
        have hqR : (0 : ℝ) < Fintype.card F := by positivity
        rw [div_le_div_iff₀ hqR hqR]
        have hntNat : 1 ≤ Fintype.card ι * t := by
          apply Nat.one_le_iff_ne_zero.mpr
          exact mul_ne_zero (Nat.ne_of_gt Fintype.card_pos) (Nat.ne_of_gt _ht_pos)
        have hnumNat : 1 ≤ Fintype.card ι * t + 3 * t ^ 3 := by omega
        have hnum : (1 : ℝ) ≤ (Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3 := by
          exact_mod_cast hnumNat
        exact mul_le_mul_of_nonneg_right hnum hqR.le
  have hδpos : 0 < δr := lt_of_le_of_ne hδ0 (Ne.symm hδzero)
  by_cases htsmall : t ≤ 2
  · have htR0 : (0 : ℝ) < t := by exact_mod_cast _ht_pos
    have hR0' : 0 ≤ R := by dsimp [R]; positivity
    dsimp [δr] at hδpos
    interval_cases t <;> norm_num at hδpos ⊢ <;> nlinarith
  have ht3 : 3 ≤ t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hs_pos : 0 < s := by nlinarith [_hs_gt]
  have hFn : Fintype.card ι < Fintype.card F := by
    have hnpos : 0 < Fintype.card ι := Fintype.card_pos
    nlinarith [_hcard]
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    dsimp [δr] at hδ0
    nlinarith [div_pos (show (0 : ℝ) < 2 by norm_num) htR]
  have hRlt : R < 1 := by
    dsimp [δr] at hδ0
    nlinarith [div_pos (show (0 : ℝ) < 2 by norm_num) htR]
  have hsn_pos : (0 : ℝ) < (s : ℝ) * Fintype.card ι := by positivity
  have hkR : (k : ℝ) < (s : ℝ) * Fintype.card ι := by
    rw [← div_lt_one hsn_pos]
    exact hRlt
  have hk : k ≤ s * Fintype.card ι := by exact_mod_cast hkR.le
  let C := ReedSolomon.Folded.frsCode domain k s ω
  have hdesign := isSubspaceDesign_frsCode_sharpProfile domain k s ω hFn _hadm _hω _hω_gen hk
  have hprof : sharpSubspaceProfile (ι := ι) s R (2 * t) ≤ R + 1 / (2 * (t : ℝ)) :=
    sharpSubspaceProfile_two_mul_le_rate_add s t R _ht_pos _hs_gt hR0 hR1
  let δ : NNReal := ⟨δr, hδ0⟩
  have hweak : StrongLineDecodable (C : Set (ι → Fin s → F)) δ
      (3 * t ^ 3) (2 * t) := by
    apply strongLineDecodable_two_mul_of_profile_le
      (sharpSubspaceProfile (ι := ι) s R) R C hdesign ht3 δ hprof
    change δr ≤ δr
    exact le_rfl
  have hrate : (LinearCode.alphabetRate C : ℝ) = R := by
    simpa only [C, R, Nat.cast_mul] using
      (ReedSolomon.Folded.alphabetRate_frsCode domain k s ω _hadm _hω hk)
  have h2tle : 2 * t ≤ s := by nlinarith [_hs_gt, sq_nonneg ((t : ℝ) - 1)]
  have ht_le_s : t ≤ s := le_trans (by omega : t ≤ 2 * t) h2tle
  change IsSubspaceDesign s (sharpSubspaceProfile (ι := ι) s R) C at hdesign
  have hdesignList := hdesign
  rw [sharpSubspaceProfile_eq_fun s R] at hdesignList
  have hlist0 := subspaceDesign_lambda_le s R C hrate hdesignList
    t (by omega) ht_le_s
  have hboostrad : (δ : ℝ) * (((2 * t : ℕ) : ℝ)) / (((2 * t - 1 : ℕ) : ℝ)) ≤
      (t : ℝ) / (t + 1) * (1 - (s : ℝ) * R / ((s : ℝ) - t + 1)) := by
    change δr * (((2 * t : ℕ) : ℝ)) / (((2 * t - 1 : ℕ) : ℝ)) ≤ _
    exact boosted_frs_radius_le_list_radius s t R ht3 _hs_gt hR0
  have hlist : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (((2 * t : ℕ) : ℝ)) / (((2 * t - 1 : ℕ) : ℝ))) ≤ (t : ℕ∞) := by
    exact (Code.Lambda_mono hboostrad).trans hlist0
  have hsub : 1 ≤ 2 * t := by omega
  have hlist' : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (((2 * t : ℕ) : ℝ)) / ((((2 * t : ℕ) : ℝ)) - 1)) ≤ (t : ℕ∞) := by
    simpa only [Nat.cast_sub hsub, Nat.cast_one] using hlist
  by_cases hfield : (t + 1) ^ 2 < Fintype.card F
  · have hstrong : StrongLineDecodable (C : Set (ι → Fin s → F)) δ
        (Fintype.card ι * t + 3 * t ^ 3) (Fintype.card ι + 1) :=
      strongLineDecodable_boost_of_lambda_le C hweak (by omega) hlist' hfield
    have hline := strongLineDecodable_to_isLineDecodable
      (F := F) (C : Set (ι → Fin s → F)) δ hstrong
    have hδlt : δ < 1 := by
      rw [← NNReal.coe_lt_coe]
      change δr < (1 : ℝ)
      dsimp [δr]
      have htwo : (0 : ℝ) < 2 / t := div_pos (by norm_num) htR
      nlinarith
    have hmca := IsLineDecodable.mcaError_le C δ
      (Fintype.card ι * t + 3 * t ^ 3)
      (by exact_mod_cast hδpos) hδlt hline
    change mcaError (AffineLineGenerator F) C δr ≤ _ at hmca
    have hnorm : ENNReal.ofReal
        (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) =
        ((Fintype.card ι * t + 3 * t ^ 3 : ℕ) : ENNReal) /
          (Fintype.card F : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity)]
      have hnum : (Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3 =
          ((Fintype.card ι * t + 3 * t ^ 3 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hnum, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [hnorm]
    exact hmca
  · have hq : Fintype.card F ≤ (t + 1) ^ 2 := by omega
    have hqP : Fintype.card F ≤ Fintype.card ι * t + 3 * t ^ 3 := by
      have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
      nlinarith [sq_nonneg (t - 1)]
    refine (mcaError_le_one (AffineLineGenerator F) C δr).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by positivity)]
    norm_num only [one_mul]
    exact_mod_cast hqP

set_option linter.unusedDecidableInType false in
/-- A capacity-regime MCA bound for an admissibly folded Reed--Solomon code. For an integer
`t > 0` and folding parameter `s > 4t²`,

  `ε_mca(C, 1 - ρ - 2/t) ≤ (nt + 3t³)/|F|`

The rate is alphabet-normalized as `ρ = k/(s·n)`. The hypotheses require a generator of
`Fˣ`, an admissible folding domain, and `s·n < |F|`; these are the conditions used by the
subspace-design argument. The integer parameter is kept explicit rather than replaced by an
unrounded real expression. -/
theorem frs_mcaError_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hω : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hcard : s * Fintype.card ι < Fintype.card F)
    (t : ℕ) (_ht_pos : 0 < t)
    (_hs_gt : 4 * t ^ 2 < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - ρ - 2 / (t : ℝ)) ≤
      ENNReal.ofReal ((n * t + 3 * (t : ℝ) ^ 3) / Fintype.card F) := by
  exact frs_mcaError_le_proof domain k s ω _hω _hω_gen _hadm _hcard t _ht_pos _hs_gt

/-- Threshold form of `frs_mcaError_le`: any target `ε_star` that the explicit
`(nt + 3t³)/|F|` budget clears at the instantiated parameters is a genuine affine-line MCA
bound for the folded Reed-Solomon code. The numeric budget check is a hypothesis, so the
contentful-range condition is discharged at the use site rather than assumed by the reader. -/
theorem frs_mcaError_le_of_budget
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hω : ω ≠ 0)
    (hω_gen : orderOf ω = Fintype.card F - 1)
    (hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (hcard : s * Fintype.card ι < Fintype.card F)
    (t : ℕ) (ht_pos : 0 < t)
    (hs_gt : 4 * t ^ 2 < s)
    (ε_star : ℝ≥0)
    (hbudget :
      ENNReal.ofReal (((Fintype.card ι : ℝ) * t + 3 * (t : ℝ) ^ 3) / Fintype.card F)
        ≤ (ε_star : ENNReal)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - (k : ℝ) / (s * (Fintype.card ι : ℝ)) - 2 / (t : ℝ)) ≤ (ε_star : ENNReal) := by
  classical
  exact le_trans (frs_mcaError_le domain k s ω hω hω_gen hadm hcard t ht_pos hs_gt) hbudget

end CodingTheory
