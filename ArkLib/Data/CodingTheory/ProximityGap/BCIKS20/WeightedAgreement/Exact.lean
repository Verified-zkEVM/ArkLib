/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Coordinate weights and exact agreement

Equality of the entire agreement set preserves its weighted size for arbitrary coordinate
weights. In particular, an exact-agreement decomposition of a chosen weighted decoder gives
weighted common agreement without a denominator or a rounding loss.
-/

@[expose] public section

namespace ProximityGap.WeightedAgreement

open scoped BigOperators
open scoped ProbabilityTheory
open CoreDefinitions LinearCode

variable {ι κ F : Type} [Fintype ι] [DecidableEq F]

open Classical in
/-- Exact equality of agreement predicates preserves every coordinate-weighted measure. -/
theorem agree_eq_mu_set_of_exact_agreement
    (μ : ι → Set.Icc (0 : ℚ) 1) {u v : ι → F} {U V : κ → ι → F}
    (hexact : ∀ i, u i = v i ↔ ∀ j, U j i = V j i) :
    agree μ u v = mu_set μ {i | ∀ j, U j i = V j i} := by
  classical
  have hset : ({i | u i = v i} : Finset ι) = ({i | ∀ j, U j i = V j i} : Finset ι) := by
    ext i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hexact i
  simp only [agree, mu_set, hset]

/-- A finite nonempty code has a decoder attaining its weighted agreement. -/
theorem exists_agree_eq_agree_set (μ : ι → Set.Icc (0 : ℚ) 1)
    (u : ι → F) (C : Finset (ι → F)) [Nonempty C] :
    ∃ v ∈ C, agree μ u v = agree_set μ u C := by
  classical
  exact Finset.mem_image.mp (Finset.max'_mem _ _)

/-- Coordinate weights at most one cannot increase the number of agreements. -/
theorem agree_mul_card_le_card [Nonempty ι] (μ : ι → Set.Icc (0 : ℚ) 1) (u v : ι → F) :
    agree μ u v * Fintype.card ι ≤ ({i | u i = v i} : Finset ι).card := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hs : (∑ i ∈ ({i | u i = v i} : Finset ι), ((μ i).1 : ℝ)) ≤
      ({i | u i = v i} : Finset ι).card := by
    calc
      _ ≤ ∑ _i ∈ ({i | u i = v i} : Finset ι), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast (μ i).property.2
      _ = _ := by simp
  unfold agree
  rw [mul_comm (1 / _), mul_assoc, one_div, inv_mul_cancel₀ hn, mul_one]
  exact_mod_cast hs

/-- Weighted agreement is at most one, since every coordinate weight is at most one. -/
theorem agree_le_one [Nonempty ι] (μ : ι → Set.Icc (0 : ℚ) 1) (u v : ι → F) :
    agree μ u v ≤ 1 := by
  classical
  have h := (agree_mul_card_le_card μ u v).trans
    (Nat.cast_le.mpr (Finset.card_le_univ _))
  have hn : (0 : ℝ) < Fintype.card ι := by positivity
  nlinarith

/-- The maximum weighted agreement with a finite code is at most one. -/
theorem agree_set_le_one [Nonempty ι] (μ : ι → Set.Icc (0 : ℚ) 1)
    (u : ι → F) (C : Finset (ι → F)) [Nonempty C] : agree_set μ u C ≤ 1 := by
  obtain ⟨v, _, hv⟩ := exists_agree_eq_agree_set μ u C
  rw [← hv]
  exact agree_le_one μ u v

/-- Nonnegative coordinate weights make weighted size monotone under inclusion. -/
theorem mu_set_mono (μ : ι → Set.Icc (0 : ℚ) 1) {S T : Finset ι} (h : S ⊆ T) :
    mu_set μ S ≤ mu_set μ T := by
  unfold mu_set
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (Finset.sum_le_sum_of_subset_of_nonneg h
    (fun i _ _ ↦ (μ i).property.1))

open Classical in
/-- An exact decomposition transfers the chosen decoder's weighted agreement to its
constituents. The coordinate weights are unrelated to interpolation weights. -/
theorem exists_weighted_common_agreement_of_hasExactAgreement
    [Field F] [Fintype κ] {S : Type} (μ : ι → Set.Icc (0 : ℚ) 1)
    {G : S → κ → F} {C : ModuleCode ι F F} {x : S} {U : κ → ι → F} {c : ι → F}
    (h : Code.HasExactAgreement G C x U c) :
    ∃ V : κ → ι → F, (∀ j, V j ∈ C) ∧
      mu_set μ {i | ∀ j, U j i = V j i} =
        agree μ (fun i ↦ ∑ j, G x j • U j i) c := by
  classical
  obtain ⟨V, hV, _, hexact⟩ := h
  refine ⟨V, hV, ?_⟩
  have hset : ({i | ∀ j, U j i = V j i} : Finset ι) =
      ({i | (∑ j, G x j • U j i) = c i} : Finset ι) := by
    ext i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm] using
      (hexact i).symm
  simp only [mu_set, agree, hset]

open Classical in
/-- A weighted decoder outside the MCA event extends every constituent on that decoder's
entire agreement set. Weights bounded by one supply the ordinary cardinality threshold. -/
theorem exists_weighted_agreement_of_not_isMCA
    [Nonempty ι] [Field F] [Fintype κ] {S : Type} [Nonempty S] [Fintype S]
    (μ : ι → Set.Icc (0 : ℚ) 1) {G : Generator S κ F} {C : ModuleCode ι F F}
    {x : S} {U : κ → ι → F} {c : ι → F} {α : ℝ}
    (hc : c ∈ C) (hα : α ≤ agree μ (fun i ↦ ∑ j, G x j • U j i) c)
    (hgood : ¬ IsMCA G C x U (1 - α)) :
    ∃ T : Finset ι, ∃ V : κ → ι → F, (∀ j, V j ∈ C) ∧
      α ≤ mu_set μ T ∧ ∀ j i, i ∈ T → U j i = V j i := by
  classical
  let T : Finset ι := {i | (∑ j, G x j • U j i) = c i}
  have hT : (T.card : ℝ) ≥ Fintype.card ι * (1 - (1 - α)) := by
    have ha := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (Fintype.card ι))
    have hb := agree_mul_card_le_card μ (fun i ↦ ∑ j, G x j • U j i) c
    dsimp only [T]
    nlinarith
  have hmem : projectedWord (fun i ↦ ∑ j, G x j • U j i) T ∈
      projectedCodeSubmod C T := by
    apply (mem_projectedCodeSubmod_iff C T _).mpr
    refine ⟨c, hc, ?_⟩
    funext i
    exact (Finset.mem_filter.mp i.property).2
  obtain ⟨V, hV⟩ := (not_isMCA_iff_forall_exists_codewords G C x U (1 - α)).mp
    hgood T hT hmem
  exact ⟨T, fun j ↦ V j, fun j ↦ (V j).property, hα,
    fun j i hi ↦ (hV j i hi).symm⟩

open Classical in
/-- A weighted proximity event with probability above the MCA error forces weighted
correlated agreement for any generator and any finite code carrier. -/
theorem exists_weighted_agreement_of_prob_gt_mcaError
    [Nonempty ι] [Field F] [Fintype κ] {S : Type} [Nonempty S] [Fintype S]
    [SampleableType S] (μ : ι → Set.Icc (0 : ℚ) 1)
    (G : Generator S κ F) (C : ModuleCode ι F F) (carrier : Finset (ι → F))
    [Nonempty carrier] (hcarrier : ∀ c ∈ carrier, c ∈ C)
    (U : κ → ι → F) (α : ℝ)
    (hprob : Pr{let x ← $ᵗ S}[agree_set μ (fun i ↦ ∑ j, G x j • U j i) carrier ≥ α] >
      mcaError G C (1 - α)) :
    ∃ T : Finset ι, ∃ V : κ → ι → F, (∀ j, V j ∈ C) ∧
      α ≤ mu_set μ T ∧ ∀ j i, i ∈ T → U j i = V j i := by
  classical
  by_contra hnot
  have hle : Pr{let x ← $ᵗ S}[agree_set μ (fun i ↦ ∑ j, G x j • U j i) carrier ≥ α] ≤
      Pr{let x ← $ᵗ S}[IsMCA G C x U (1 - α)] := by
    apply prEvent_mono
    intro x hx
    by_contra hgood
    obtain ⟨c, hc, heq⟩ := exists_agree_eq_agree_set μ
      (fun i ↦ ∑ j, G x j • U j i) carrier
    exact hnot (exists_weighted_agreement_of_not_isMCA μ (hcarrier c hc)
      (by simpa only [heq] using hx) hgood)
  have hU : Pr{let x ← $ᵗ S}[IsMCA G C x U (1 - α)] ≤ mcaError G C (1 - α) := by
    unfold mcaError
    exact le_iSup (fun V ↦ Pr{let x ← $ᵗ S}[IsMCA G C x V (1 - α)]) U
  exact (not_lt_of_ge (hle.trans hU)) hprob

end ProximityGap.WeightedAgreement
