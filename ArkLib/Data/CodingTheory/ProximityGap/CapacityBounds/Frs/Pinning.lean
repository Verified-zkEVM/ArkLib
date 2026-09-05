/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Frs.LineDecoding

/-!
# Pinning induction for the folded Reed--Solomon capacity bound

Internal pinning and rank-drop infrastructure used by the public FRS capacity theorem.
-/

namespace CodingTheory.FrsInternal

open scoped NNReal
open CoreDefinitions ProximityGap

theorem pinnedSubspace_empty
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

theorem pinned_lineSeeds_lie_on_affine_codeword_line
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

private theorem pinningActiveCoordinates_disjoint_inactive
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
private theorem pinning_tau_nonneg
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

private theorem vanishOnCoordinates_insert
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

private theorem pinnedSubspace_insert_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ}
    (H : Submodule F (ι → Fin s → F)) (S : Finset ι) (i : ι) :
    pinnedSubspace H (insert i S) ≤ pinnedSubspace H S := by
  rw [pinnedSubspace, pinnedSubspace, vanishOnCoordinates_insert, ← inf_assoc]
  exact inf_le_left

private theorem pinningActiveCoordinates_nonempty
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

private theorem pinning_active_or_inactive
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

private theorem pinningActiveCoordinates_union_inactive
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
private theorem pinned_child_card_sum_lower
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
private theorem pinning_weight_sum_le
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
private theorem shared_pinning_step
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
theorem exists_terminal_line_pinning
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

end CodingTheory.FrsInternal
