/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
import Mathlib.LinearAlgebra.Dimension.Free
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.DivergenceOfSets
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Trivariate
import ArkLib.Data.CodingTheory.Basic.DecodingRadius

/-!
# Foundations for affine-space proximity bounds

This module contains the BCIKS20 Section 6 averaging argument, the finite representation of
affine spaces, scaling invariance, and the theorem that upgrades random-line proximity to
proximity of every element in the affine space. Bucketing and the core result remain in
`BCIKS20.AffineSpaces`.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory ReedSolomon Code
open scoped BigOperators LinearCode ProbabilityTheory
open Probability

section BCIKS20ProximityGapSection6

open scoped ReedSolomon

variable {l : ℕ} [NeZero l]
variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem exists_of_weighted_avg_gt {α : Type} (p : PMF α) (f : α → ENNReal) (ε : ENNReal) :
    (∑' a, p a * f a) > ε → ∃ a, f a > ε := by
  intro hgt
  by_contra hno
  have hle : ∀ a, f a ≤ ε := by
    intro a
    have : ¬ f a > ε := by
      intro ha
      exact hno ⟨a, ha⟩
    exact le_of_not_gt this
  have hmul : ∀ a, p a * f a ≤ p a * ε := by
    intro a
    exact mul_le_mul_of_nonneg_left (hle a) (zero_le)
  have htsum : (∑' a, p a * f a) ≤ ∑' a, p a * ε := by
    exact ENNReal.tsum_le_tsum hmul
  have htsum' : (∑' a, p a * f a) ≤ ε := by
    refine le_trans htsum ?_
    simp [ENNReal.tsum_mul_right, p.tsum_coe]
  exact (not_lt_of_ge htsum') hgt

theorem jointAgreement_implies_second_proximity {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [DecidableEq F] {C : Set (ι → F)} {δ : ℝ≥0} {W : Fin 2 → ι → F} :
    jointAgreement (C := C) (δ := δ) (W := W) → δᵣ(W 1, C) ≤ δ := by
  intro h
  rcases h with ⟨S, hS_card, v, hv⟩
  have hv1 : v 1 ∈ C := (hv 1).1
  have hSsub : S ⊆ Finset.filter (fun j => v 1 j = W 1 j) Finset.univ := (hv 1).2
  have hdist : δᵣ(W 1, v 1) ≤ δ := by
    rw [Code.relCloseToWord_iff_exists_agreementCols (u := W 1) (v := v 1) (δ := δ)]
    refine ⟨S, ?_, ?_⟩
    · have hS' : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
        simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using hS_card
      exact (Code.relDist_floor_bound_iff_complement_bound (n := Fintype.card ι)
        (upperBound := S.card) (δ := δ)).2 hS'
    · intro j
      constructor
      · intro hj
        have hj' : j ∈ Finset.filter (fun j => v 1 j = W 1 j) Finset.univ := hSsub hj
        have : v 1 j = W 1 j := by
          simpa [Finset.mem_filter] using hj'
        exact this.symm
      · intro hj_ne hj
        have hj' : j ∈ Finset.filter (fun j => v 1 j = W 1 j) Finset.univ := hSsub hj
        have : v 1 j = W 1 j := by
          simpa [Finset.mem_filter] using hj'
        exact hj_ne this.symm
  have hclose : ∃ v' ∈ C, δᵣ(W 1, v') ≤ δ := by
    exact ⟨v 1, hv1, hdist⟩
  exact
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist (u := W 1) (C := C) (δ := δ)).2 hclose

/-- Generalisation of `jointAgreement_implies_second_proximity` to an arbitrary word stack over a
submodule code. If a stack `W : Fin k → ι → F` jointly agrees with a submodule `C ⊆ ι → F`, then
every element of the linear span of the stack is `δ`-close to `C`. The pointwise case
`W i ∈ C` is the special case `x = W i` (choose coefficients `c` to be the i-th basis vector);
the original `Fin 2` lemma is the case `k = 2`, `x = W 1`.

The proof bounds the linear combination against the matching linear combination of the agreement
witnesses: on each agreement column `j ∈ S`, `v i j = W i j` for every `i`, so `∑ cᵢ • vᵢ` and
`∑ cᵢ • Wᵢ` agree on `S`; `v'` is a codeword by submodule closure; lift via
`relCloseToCode_iff_relCloseToCodeword_of_minDist`. -/
theorem jointAgreement_implies_linSpan_proximity {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [DecidableEq F] {k : ℕ}
    (C : Submodule F (ι → F)) {δ : ℝ≥0} {W : Fin k → ι → F}
    (h : jointAgreement (C := (C : Set (ι → F))) (δ := δ) (W := W)) :
    ∀ x ∈ Submodule.span F (Set.range W), δᵣ(x, (C : Set (ι → F))) ≤ δ := by
  rcases h with ⟨S, hS_card, v, hv⟩
  intro x hx
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  rcases hx with ⟨c, rfl⟩
  set v' : ι → F := ∑ i : Fin k, c i • v i with hv'_def
  have hv'_mem : v' ∈ C := by
    refine Submodule.sum_mem C (fun i _ => ?_)
    exact Submodule.smul_mem C (c i) (hv i).1
  have hagree : ∀ j ∈ S, (∑ i, c i • v i) j = (∑ i, c i • W i) j := by
    intro j hj
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_j_in_filter : j ∈ Finset.filter (fun j => v i j = W i j) Finset.univ :=
      (hv i).2 hj
    have : v i j = W i j := by simpa [Finset.mem_filter] using h_j_in_filter
    rw [this]
  have hdist : δᵣ(∑ i, c i • W i, v') ≤ δ := by
    rw [Code.relCloseToWord_iff_exists_agreementCols
      (u := ∑ i, c i • W i) (v := v') (δ := δ)]
    refine ⟨S, ?_, ?_⟩
    · have hS' : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
        simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using hS_card
      exact (Code.relDist_floor_bound_iff_complement_bound (n := Fintype.card ι)
        (upperBound := S.card) (δ := δ)).2 hS'
    · intro j
      constructor
      · intro hj
        exact (hagree j hj).symm
      · intro hj_ne hj
        exact hj_ne (hagree j hj).symm
  exact
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist
      (u := ∑ i, c i • W i) (C := (C : Set (ι → F))) (δ := δ)).2
      ⟨v', hv'_mem, hdist⟩

theorem prob_uniform_shift_invariant {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [DecidableEq F]
    {U : Finset (ι → F)} [Nonempty U]
    (dir : ι → F)
    (hshift : ∀ a ∈ (U : Finset (ι → F)), ∀ z : F, a + z • dir ∈ (U : Finset (ι → F)))
    {V : Set (ι → F)} {δ : ℝ≥0} :
    ∀ z : F,
      Pr_{let a ←$ᵖ U}[δᵣ(a.1 + z • dir, V) ≤ δ] =
        Pr_{let a ←$ᵖ U}[δᵣ(a.1, V) ≤ δ] := by
  intro z
  classical
  let shiftEquiv : (U : Type) ≃ (U : Type) :=
    { toFun := fun a => ⟨a.1 + z • dir, hshift a.1 a.2 z⟩
      invFun := fun a => ⟨a.1 + (-z) • dir, hshift a.1 a.2 (-z)⟩
      left_inv := by
        intro a
        apply Subtype.ext
        ext i
        simp [add_left_comm, add_comm]
      right_inv := by
        intro a
        apply Subtype.ext
        ext i
        simp [add_comm] }
  simpa [shiftEquiv] using
    (ProbabilityTheory.Pr_uniform_equiv (α := (U : Type)) (β := (U : Type)) (e := shiftEquiv)
      (P := fun a : (U : Type) => δᵣ(a.1, V) ≤ δ))

theorem exists_basepoint_with_large_line_prob_aux {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {U : Finset (ι → F)} [Nonempty U]
    (dir : ι → F)
    (hshift : ∀ a ∈ (U : Finset (ι → F)), ∀ z : F, a + z • dir ∈ (U : Finset (ι → F)))
    {V : Set (ι → F)} {δ ε : ℝ≥0} :
    Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε →
      ∃ a : U, Pr_{let z ←$ᵖ F}[δᵣ(a.1 + z • dir, V) ≤ δ] > ε := by
  intro hprob
  classical
  let good : (ι → F) → Prop := fun w => δᵣ(w, V) ≤ δ
  let lineProb (a : U) : ENNReal := Pr_{let z ←$ᵖ F}[good (a.1 + z • dir)]
  let P2 : ENNReal := Pr_{let a ←$ᵖ U; let z ←$ᵖ F}[good (a.1 + z • dir)]
  -- Expand the joint probability as an average over basepoints.
  have hP2 : P2 = ∑' a : U, ($ᵖ U) a * lineProb a := by
    simpa [P2, lineProb] using
      (prob_tsum_form_split_first (D := ($ᵖ U))
        (D_rest := fun a : U => (do
          let z ← $ᵖ F
          return good (a.1 + z • dir))))
  -- Swap the order of sampling the basepoint and line parameter.
  have hswap :
      (do
          let a ← $ᵖ U
          let z ← $ᵖ F
          return good (a.1 + z • dir) : PMF Prop) =
        (do
          let z ← $ᵖ F
          let a ← $ᵖ U
          return good (a.1 + z • dir) : PMF Prop) := by
    simpa [Bind.bind, PMF.bind] using
      (PMF.bind_comm ($ᵖ U) ($ᵖ F) (fun a z => (pure (good (a.1 + z • dir)) : PMF Prop)))
  -- Turn the swapped bind identity into an equality of probabilities.
  have hP2_swap : P2 = Pr_{let z ←$ᵖ F; let a ←$ᵖ U}[good (a.1 + z • dir)] := by
    have hswap' := congrArg (fun p : PMF Prop => (p True : ENNReal)) hswap
    simpa [P2] using hswap'
  -- Reduce the shifted average back to the original uniform probability.
  have hP2_eq : P2 = Pr_{let u ←$ᵖ U}[good u.1] := by
    rw [hP2_swap]
    have hsplit :
        Pr_{let z ←$ᵖ F; let a ←$ᵖ U}[good (a.1 + z • dir)] =
          ∑' z : F, ($ᵖ F) z * Pr_{let a ←$ᵖ U}[good (a.1 + z • dir)] := by
      simpa using
        (prob_tsum_form_split_first (D := ($ᵖ F))
          (D_rest := fun z : F => (do
            let a ← $ᵖ U
            return good (a.1 + z • dir))))
    rw [hsplit]
    have hconst :
        ∀ z : F, Pr_{let a ←$ᵖ U}[good (a.1 + z • dir)] = Pr_{let a ←$ᵖ U}[good a.1] := by
      intro z
      simpa [good] using
        (prob_uniform_shift_invariant (U := U) (dir := dir) (hshift := hshift)
          (V := V) (δ := δ) (z := z))
    have :
        (∑' z : F, ($ᵖ F) z * Pr_{let a ←$ᵖ U}[good (a.1 + z • dir)]) =
          ∑' z : F, ($ᵖ F) z * Pr_{let a ←$ᵖ U}[good a.1] := by
      refine tsum_congr ?_
      intro z
      congr 1
      exact hconst z
    rw [this]
    simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  -- Rewrite the original hypothesis as a lower bound on `P2`.
  have hP2_gt : P2 > ε := by
    simpa [hP2_eq] using hprob
  -- Rewrite that lower bound using the weighted-sum formula for `P2`.
  have hsum_gt : (∑' a : U, ($ᵖ U) a * lineProb a) > ε := by
    simpa [hP2] using hP2_gt
  -- Choose a basepoint whose line probability exceeds the threshold.
  rcases exists_of_weighted_avg_gt ($ᵖ U) lineProb (ε : ENNReal) hsum_gt with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [lineProb] using ha

theorem exists_basepoint_with_large_line_prob {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {U'_sub : Submodule F (ι → F)} {u0 dir : ι → F} (hdir : dir ∈ U'_sub)
    {V : Set (ι → F)} {δ ε : ℝ≥0} :
    letI U' : Finset (ι → F) := (U'_sub : Set (ι → F)).toFinset
    letI U : Finset (ι → F) := U'.image (fun x => u0 + x)
    haveI : Nonempty U := by
      classical
      apply Finset.Nonempty.to_subtype
      refine ⟨u0, ?_⟩
      refine Finset.mem_image.2 ?_
      refine ⟨0, ?_, by simp⟩
      change (0 : ι → F) ∈ ((U'_sub : Set (ι → F)).toFinset)
      rw [Set.mem_toFinset]
      exact U'_sub.zero_mem
    Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε →
      ∃ a : U, Pr_{let z ←$ᵖ F}[δᵣ(a.1 + z • dir, V) ≤ δ] > ε := by
  classical
  let U' : Finset (ι → F) := (U'_sub : Set (ι → F)).toFinset
  let U : Finset (ι → F) := U'.image (fun x => u0 + x)
  have : Nonempty U := by
    classical
    apply Finset.Nonempty.to_subtype
    refine ⟨u0, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨0, ?_, by simp⟩
    change (0 : ι → F) ∈ ((U'_sub : Set (ι → F)).toFinset)
    rw [Set.mem_toFinset]
    exact U'_sub.zero_mem
  intro hprob
  have hshift : ∀ a ∈ (U : Finset (ι → F)), ∀ z : F, a + z • dir ∈ (U : Finset (ι → F)) := by
    intro a ha z
    rcases Finset.mem_image.1 ha with ⟨x, hxU', rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨x + z • dir, ?_, ?_⟩
    · have hxsub : x ∈ U'_sub := by
        simpa [U', Set.mem_toFinset] using hxU'
      have hxzsub : x + z • dir ∈ U'_sub := by
        exact U'_sub.add_mem hxsub (U'_sub.smul_mem z hdir)
      simpa [U', Set.mem_toFinset] using hxzsub
    · simp [add_assoc]
  have :=
    exists_basepoint_with_large_line_prob_aux (U := U) (dir := dir) hshift
      (V := V) (δ := δ) (ε := ε)
  simpa [U, U'] using (this (by simpa [U, U'] using hprob))

omit [NeZero l] in
theorem average_proximity_implies_proximity_of_linear_subspace
    {u : Fin (l + 2) → ι → F} {k : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ∈ Set.Ioo 0 (1 - ReedSolomon.sqrtRate (k + 1) domain)) :
    letI U'_submodule : Submodule F (ι → F) :=
      Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F))
    letI U' : Finset (ι → F) := (U'_submodule : Set (ι → F)).toFinset
    letI U : Finset (ι → F) := U'.image (fun x => u 0 + x)
    haveI : Nonempty U := by
      classical
      apply Finset.Nonempty.to_subtype
      refine ⟨u 0, ?_⟩
      refine Finset.mem_image.2 ?_
      refine ⟨0, ?_, by simp⟩
      change (0 : ι → F) ∈ ((U'_submodule : Set (ι → F)).toFinset)
      rw [Set.mem_toFinset]
      exact U'_submodule.zero_mem
    letI ε : ℝ≥0 := ProximityGap.errorBound δ (k + 1) domain
    letI V := ReedSolomon.code domain (k + 1)
    Pr_{let u ←$ᵖ U}[δᵣ(u.1, V) ≤ δ] > ε → ∀ u' ∈ U', δᵣ(u', V) ≤ δ := by
  classical
  intro hprob u' hu'
  have hu'_sub :
      u' ∈ (Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)) :
        Submodule F (ι → F)) := by
    simpa [Set.mem_toFinset] using hu'
  have hδ_le : δ ≤ 1 - ReedSolomon.sqrtRate (k + 1) domain :=
    le_of_lt hδ.2
  rcases
      (exists_basepoint_with_large_line_prob
        (ι := ι) (F := F)
        (U'_sub :=
          (Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)) :
            Submodule F (ι → F)))
        (u0 := u 0) (dir := u') (hdir := hu'_sub)
        (V := ReedSolomon.code domain (k + 1))
        (δ := δ) (ε := ProximityGap.errorBound δ (k + 1) domain)
        hprob)
    with ⟨a, hline⟩
  have hCA :
      δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
        (C := ReedSolomon.code domain (k + 1)) (δ := δ)
        (ε := ProximityGap.errorBound δ (k + 1) domain) :=
    RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := k + 1) (domain := domain)
      (δ := δ) hδ_le
  have hJA :
      jointAgreement (C := ReedSolomon.code domain (k + 1)) (δ := δ)
        (W := Code.finMapTwoWords a.1 u') := by
    apply hCA
    simpa [Code.finMapTwoWords] using hline
  have :
      δᵣ((Code.finMapTwoWords a.1 u') 1, ReedSolomon.code domain (k + 1)) ≤ δ :=
    jointAgreement_implies_second_proximity
      (ι := ι) (F := F) (C := ReedSolomon.code domain (k + 1))
      (δ := δ) (W := Code.finMapTwoWords a.1 u') hJA
  simpa [Code.finMapTwoWords] using this

end BCIKS20ProximityGapSection6

section AffineFinsetBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/- The two bridge declarations below are shared with the bucketing module. -/
namespace AffineSpacesInternal

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- The AffineSubspace and Finset.image representations of an affine subspace
have the same membership. -/
theorem affine_mem_iff_finset_mem [Finite F] {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) (x : ι → F) :
    x ∈ (Affine.affineSubspaceAtOrigin (F := F) u0 dirs : Set (ι → F)) ↔
    x ∈ (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)).toFinset.image
      (fun d => u0 + d) := by
  classical
  simp only [Affine.affineSubspaceAtOrigin,
    Finset.mem_image, Set.mem_toFinset]
  constructor
  · intro h; exact ⟨x - u0, h, by abel⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

noncomputable abbrev affineFinset {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) : Finset (ι → F) :=
  (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)).toFinset.image
    (fun d => u0 + d)

end AffineSpacesInternal

open AffineSpacesInternal

private noncomputable def affineFinsetEquiv {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) :
    (Affine.affineSubspaceAtOrigin (F := F) u0 dirs) ≃ (affineFinset u0 dirs) :=
  Equiv.subtypeEquiv (Equiv.refl _) (affine_mem_iff_finset_mem u0 dirs)

omit [Nonempty ι] [DecidableEq ι] in
theorem affine_finset_card_eq {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) :
    (affineFinset u0 dirs).card =
    Fintype.card F ^
      Module.finrank F ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F))) := by
  let S := (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)).toFinset
  have h1 : (affineFinset u0 dirs).card = S.card :=
    Finset.card_image_of_injective S (add_right_injective u0)
  rw [h1, Set.toFinset_card]
  exact Module.card_eq_pow_finrank

omit [Nonempty ι] in
/-- The coefficient-parameterised probability equals the subtype probability.
The map `r ↦ u₀ + ∑ rᵢ • dᵢ` has constant-cardinality fibers (cosets of the
kernel of the linear part), so pushforward of uniform gives uniform. -/
theorem prob_coeff_eq_prob_affine {k : ℕ} [NeZero k]
    (u0 : ι → F) (dirs : Fin k → ι → F)
    (P : (ι → F) → Prop) :
    Pr_{let r ← $ᵖ (Fin k → F)}[P (u0 + ∑ i : Fin k, r i • dirs i)] =
    Pr_{let y ← $ᵖ (Affine.affineSubspaceAtOrigin (F := F) u0 dirs)}[P ↑y] := by
  classical
  -- Reduce both sides to cardinality fractions via prob_uniform_eq_card_filter_div_card.
  rw [prob_uniform_eq_card_filter_div_card (fun r : Fin k → F => P (u0 + ∑ i, r i • dirs i))]
  rw [prob_uniform_eq_card_filter_div_card
    (fun y : ↥(Affine.affineSubspaceAtOrigin (F := F) u0 dirs) => P ↑y)]
  -- Define the map g : (Fin k → F) → affineSubspaceAtOrigin
  set A := Affine.affineSubspaceAtOrigin (F := F) u0 dirs with hA_def
  have hg_mem : ∀ r : Fin k → F, u0 + ∑ i, r i • dirs i ∈ A := fun r =>
    (Affine.mem_affineSubspaceFrom_iff (F := F) u0 dirs _).mpr ⟨r, rfl⟩
  let g : (Fin k → F) → A := fun r => ⟨u0 + ∑ i, r i • dirs i, hg_mem r⟩
  -- Key: g r₁ = g r₂ ↔ linear parts equal
  have hg_eq : ∀ r₁ r₂ : Fin k → F,
      g r₁ = g r₂ ↔ ∑ i, r₁ i • dirs i = ∑ i, r₂ i • dirs i := by
    intro r₁ r₂
    constructor
    · intro h; exact add_left_cancel (congrArg Subtype.val h)
    · intro h; exact Subtype.ext (congrArg (u0 + ·) h)
  -- Auxiliary: linear part of (r - r₀)
  have hlin_sub : ∀ (r r₀ : Fin k → F),
      ∑ i, (r - r₀) i • dirs i = ∑ i, r i • dirs i - ∑ i, r₀ i • dirs i := by
    intro r r₀; simp [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  -- g is surjective
  have hg_surj : Function.Surjective g := by
    intro ⟨y, hy⟩
    obtain ⟨β, rfl⟩ := (Affine.mem_affineSubspaceFrom_iff (F := F) u0 dirs y).mp hy
    exact ⟨β, rfl⟩
  -- Fiber cardinality is constant: use translation r ↦ r - r₀ to biject fibers.
  set K := ((Finset.univ : Finset (Fin k → F)).filter (g · = g 0)).card with hK_def
  have hg_fib : ∀ b ∈ Finset.univ.image g,
      ((Finset.univ : Finset (Fin k → F)).filter (g · = b)).card = K := by
    intro b hb
    obtain ⟨r₀, _, hr₀⟩ := Finset.mem_image.mp hb
    subst hr₀
    -- Bijection: fiber(g r₀) ≃ fiber(g 0) via r ↦ r - r₀
    apply Finset.card_equiv (Equiv.subRight r₀)
    intro r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subRight_apply]
    constructor
    · intro h
      rw [hg_eq] at h ⊢; rw [hlin_sub]
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      rw [h]; abel
    · intro h
      rw [hg_eq] at h ⊢; rw [hlin_sub] at h
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h
      have := sub_eq_zero.mp h; rw [this]
  -- K > 0 since fibers are nonempty
  have hK_pos : 0 < K := by
    rw [hK_def]
    exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  -- Step 1: |Fin k → F| = K * |A|
  have hcard_eq : Fintype.card (Fin k → F) = K * Fintype.card A := by
    rw [show Fintype.card (Fin k → F) = (Finset.univ : Finset (Fin k → F)).card from rfl]
    rw [Finset.card_eq_sum_card_image g Finset.univ, Finset.sum_const_nat hg_fib,
        Finset.image_univ_of_surjective hg_surj, Finset.card_univ, mul_comm]
  -- Step 2: LHS filter = K * RHS filter
  have hfilt_eq :
      (Finset.filter (fun r : Fin k → F => P (u0 + ∑ i, r i • dirs i)) Finset.univ).card =
      K * (Finset.filter (fun y : A => P ↑y) Finset.univ).card := by
    -- Rewrite LHS as filter by g
    have hfilt_rw :
        (Finset.filter (fun r : Fin k → F => P (u0 + ∑ i, r i • dirs i)) Finset.univ) =
        (Finset.filter (fun r => P (g r).val) Finset.univ) := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    rw [hfilt_rw, Finset.card_eq_sum_card_image g _]
    -- For each b in image of the filter, inner filter card = K
    have hfib_K : ∀ b ∈ (Finset.filter (fun r => P (g r).val) Finset.univ).image g,
        ((Finset.filter (fun r => P (g r).val) Finset.univ).filter (g · = b)).card = K := by
      intro b hb
      obtain ⟨r₀, hr₀_mem, hr₀_eq⟩ := Finset.mem_image.mp hb
      have hPb : P (g r₀).val := (Finset.mem_filter.mp hr₀_mem).2
      subst hr₀_eq
      have : (Finset.filter (fun r => P (g r).val) Finset.univ).filter (g · = g r₀) =
          Finset.univ.filter (g · = g r₀) := by
        ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hr; exact ⟨by rwa [show (g r).val = (g r₀).val from congrArg Subtype.val hr], hr⟩
      rw [this]
      exact hg_fib (g r₀) (Finset.mem_image_of_mem g (Finset.mem_univ r₀))
    rw [Finset.sum_const_nat hfib_K]
    -- Show: image of {r | P(g r)} under g = {y ∈ A | P ↑y}
    have himg : (Finset.filter (fun r => P (g r).val) Finset.univ).image g =
        Finset.filter (fun y : A => P ↑y) Finset.univ := by
      ext ⟨y, hy⟩
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨r, hPr, hr_eq⟩
        rwa [show (g r).val = y from congrArg Subtype.val hr_eq] at hPr
      · intro hPy
        obtain ⟨r, hr⟩ := hg_surj ⟨y, hy⟩
        exact ⟨r, by rwa [show (g r).val = y from congrArg Subtype.val hr], hr⟩
    rw [himg]; ring
  -- Step 3: The probabilities are card fractions that simplify.
  simp only [hfilt_eq, hcard_eq]
  push_cast
  exact ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hK_pos.ne') (ENNReal.natCast_ne_top K)

omit [Nonempty ι] in
theorem affine_prob_eq_finset_prob {k : ℕ} [NeZero k]
    (u0 : ι → F) (dirs : Fin k → ι → F)
    (P : (ι → F) → Prop)
    [Nonempty (affineFinset u0 dirs)] :
    Pr_{let y ← $ᵖ (Affine.affineSubspaceAtOrigin (F := F) u0 dirs)}[P ↑y] =
    Pr_{let y ← $ᵖ (affineFinset u0 dirs)}[P ↑y] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card
    (fun y : ↥(Affine.affineSubspaceAtOrigin (F := F) u0 dirs) => P ↑y)]
  rw [prob_uniform_eq_card_filter_div_card
    (fun y : ↥(affineFinset u0 dirs) => P ↑y)]
  have hcard : Fintype.card ↥(Affine.affineSubspaceAtOrigin (F := F) u0 dirs) =
      Fintype.card ↥(affineFinset u0 dirs) :=
    Fintype.card_congr (affineFinsetEquiv u0 dirs)
  have hfilt : (Finset.filter
      (fun y : ↥(Affine.affineSubspaceAtOrigin (F := F) u0 dirs) => P ↑y)
      Finset.univ).card =
    (Finset.filter (fun y : ↥(affineFinset u0 dirs) => P ↑y) Finset.univ).card := by
    apply Finset.card_equiv (affineFinsetEquiv u0 dirs)
    intro ⟨x, hx⟩
    simp [affineFinsetEquiv, Equiv.subtypeEquiv]
  simp only [hfilt, hcard]

omit [Nonempty ι] [DecidableEq ι] in
theorem proper_affine_sub_card_le {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F)
    (S : Finset (ι → F)) (hS : ↑S ⊆ (Affine.affineSubspaceAtOrigin (F := F) u0 dirs : Set (ι → F)))
    (hS_aff : ∃ (m : ℕ) (u0' : ι → F) (dirs' : Fin m → ι → F),
      S = affineFinset u0' dirs' ∧
      (Submodule.span F (Finset.univ.image dirs' : Set (ι → F)) :
        Submodule F (ι → F)) <
      Submodule.span F (Finset.univ.image dirs : Set (ι → F))) :
    S.card ≤ Fintype.card F ^ (Module.finrank F
      ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F))) - 1) := by
  obtain ⟨m, u0', dirs', rfl, hlt⟩ := hS_aff
  rw [affine_finset_card_eq]
  apply Nat.pow_le_pow_right (Fintype.card_pos)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end AffineFinsetBridge

open AffineSpacesInternal

section ScalingInvariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Hamming distance is invariant under scaling by a unit:
`hammingDist (z • u) (z • v) = hammingDist u v` for `z ≠ 0`. -/
theorem hammingDist_smul_eq {z : F} (hz : z ≠ 0) (u v : ι → F) :
    hammingDist (z • u) (z • v) = hammingDist u v := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Pi.smul_apply, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  exact not_congr (IsUnit.smul_left_cancel (IsUnit.mk0 z hz))

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Relative Hamming distance is invariant under scaling by a unit. -/
theorem relHammingDist_smul_eq {z : F} (hz : z ≠ 0) (u v : ι → F) :
    Code.relHammingDist (z • u) (z • v) = Code.relHammingDist u v := by
  unfold Code.relHammingDist
  rw [hammingDist_smul_eq hz]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Relative distance to a submodule is invariant under scaling by a unit:
`δᵣ(z • u, V) = δᵣ(u, V)` for `z ≠ 0` and `V` a submodule.
Key step in BCIKS20 §6.3 (Step 1c). -/
theorem relDistFromCode_smul_eq (V : Submodule F (ι → F))
    {z : F} (hz : z ≠ 0) (u : ι → F) :
    δᵣ(z • u, (V : Set (ι → F))) = δᵣ(u, (V : Set (ι → F))) := by
  unfold Code.relDistFromCode
  congr 1
  ext d
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, hle⟩
    refine ⟨z⁻¹ • v, V.smul_mem z⁻¹ hv, ?_⟩
    rwa [← relHammingDist_smul_eq hz, smul_inv_smul₀ hz]
  · rintro ⟨w, hw, hle⟩
    exact ⟨z • w, V.smul_mem z hw, by rw [relHammingDist_smul_eq hz]; exact hle⟩

end ScalingInvariance

section AllClose

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- When `u₀ ∉ U'`, `span(range u) = span {u₀} ⊔ U'`. -/
private lemma spanU_eq_sup {k : ℕ} (u : Fin (k + 1) → ι → F)
    (U' : Submodule F (ι → F))
    (hU' : U' = Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)))
    (hU'_le : U' ≤ Submodule.span F (Set.range u)) :
    Submodule.span F (Set.range u) = Submodule.span F {u 0} ⊔ U' := by
  apply le_antisymm
  · apply Submodule.span_le.mpr; rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Submodule.mem_sup_left (Submodule.subset_span rfl)
    · exact Submodule.mem_sup_right (hU' ▸ Submodule.subset_span
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  · exact sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.subset_span ⟨0, rfl⟩))) hU'_le

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Every element of `span(range u)` decomposes as `c • u₀ + d` with `d ∈ U'`. -/
private lemma mem_spanU_decomp {k : ℕ} (u : Fin (k + 1) → ι → F)
    (U' : Submodule F (ι → F))
    (hU' : U' = Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F)))
    (hU'_le : U' ≤ Submodule.span F (Set.range u))
    {x : ι → F} (hx : x ∈ Submodule.span F (Set.range u)) :
    ∃ c : F, ∃ d ∈ U', x = c • u 0 + d := by
  rw [spanU_eq_sup u U' hU' hU'_le, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  exact ⟨c, b, hb, rfl⟩

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- If `u₀ ∉ U'` and `a • u₀ + d₁ = b • u₀ + d₂` with `d₁ d₂ ∈ U'`, then `a = b`. -/
private lemma coset_scalar_eq {u₀ : ι → F} {U' : Submodule F (ι → F)}
    (hu0 : u₀ ∉ U') {a b : F} {d₁ d₂ : ι → F} (hd₁ : d₁ ∈ U') (hd₂ : d₂ ∈ U')
    (h : a • u₀ + d₁ = b • u₀ + d₂) : a = b := by
  by_contra hab
  apply hu0
  have h1 : (a - b) • u₀ = d₂ - d₁ := by
    rw [sub_smul]
    calc a • u₀ - b • u₀
        = (a • u₀ + d₁) - d₁ - b • u₀ := by abel
      _ = (b • u₀ + d₂) - d₁ - b • u₀ := by rw [h]
      _ = d₂ - d₁ := by abel
  rw [show u₀ = (a - b)⁻¹ • ((a - b) • u₀) from by
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul], h1]
  exact U'.smul_mem _ (U'.sub_mem hd₂ hd₁)



/-- Every element of an affine subspace U is δ-close to a RS code V,
given Pr_{x∈U}[δᵣ(x,V) ≤ δ] > ε (BCIKS20 §6.3, Step 1).

Proof strategy:
1. Apply Lemma 6.3 to U → all directions in U' are δ-close to V.
2. Scaling invariance: δᵣ(z·x, V) = δᵣ(x, V) for z ≠ 0, V a submodule.
3. Probability transfer: Pr[close on span(U)] > ε.
   Key: all |U'| direction elements are close (step 1) + scaling gives
   Pr_Ū ≥ 1/|F| + (1-1/|F|)·Pr_U > ε since ε < 1.
4. Apply Lemma 6.3 to span(U) → all elements of span(U) are close.
   Since U ⊆ span(U), all elements of U are close. -/
theorem all_affine_elements_close {k : ℕ} [NeZero k]
    (u : Fin (k + 1) → ι → F) {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hPr : Pr_{
      let y ← $ᵖ (Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[δᵣ(↑y,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] >
      ProximityGap.errorBound δ deg domain) :
    ∀ x ∈ (Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u) : Set (ι → F)),
      δᵣ(x, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
  classical
  set V := ReedSolomon.code domain deg
  set U'_sub := Submodule.span F (Finset.univ.image (Fin.tail u) : Set (ι → F))
  -- Convert probability to finset form
  have hU_ne : Nonempty (affineFinset (u 0) (Fin.tail u)) := by
    apply Finset.Nonempty.to_subtype
    exact ⟨u 0, Finset.mem_image.2 ⟨0, by simp [Set.mem_toFinset],
      by simp⟩⟩
  have hPr_fin : Pr_{let y ← $ᵖ (affineFinset (u 0) (Fin.tail u))}[
      δᵣ(↑y, (V : Set (ι → F))) ≤ δ] > ProximityGap.errorBound δ deg domain := by
    rw [← affine_prob_eq_finset_prob (u 0) (Fin.tail u)
      (fun w => δᵣ(w, (V : Set (ι → F))) ≤ δ)]
    exact hPr
  -- Step 1: All directions in U' are δ-close to V (Lemma 6.3 on U)
  have h_dirs_close : ∀ dir, dir ∈ U'_sub →
    δᵣ(dir, (V : Set (ι → F))) ≤ δ := by
    intro dir hdir
    rcases exists_basepoint_with_large_line_prob
      (U'_sub := U'_sub) (u0 := u 0) (dir := dir) (hdir := hdir)
      (V := (V : Set (ι → F))) (δ := δ)
      (ε := ProximityGap.errorBound δ deg domain)
      hPr_fin with ⟨a, hline⟩
    have hJA : Code.jointAgreement (C := (V : Set (ι → F))) (δ := δ)
        (W := Code.finMapTwoWords a.1 dir) := by
      apply RS_correlatedAgreement_affineLines hδ
      simpa [Code.finMapTwoWords] using hline
    exact jointAgreement_implies_second_proximity
      (ι := ι) (F := F) (C := (V : Set (ι → F)))
      (δ := δ) (W := Code.finMapTwoWords a.1 dir) hJA
  -- Steps 2-4: span(U) argument
  set spanU := Submodule.span F (Set.range u)
  have hU'_le_spanU : U'_sub ≤ spanU := by
    apply Submodule.span_le.mpr
    intro x hx; rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact Submodule.subset_span ⟨i.succ, rfl⟩
  have h_spanU_close : ∀ x ∈ spanU, δᵣ(x, (V : Set (ι → F))) ≤ δ := by
    set spanU_fin := (spanU : Set (ι → F)).toFinset
    set spanU_aff := spanU_fin.image (fun y => (0 : ι → F) + y)
    have hne : Nonempty spanU_aff := by
      apply Finset.Nonempty.to_subtype
      exact ⟨0, Finset.mem_image.2 ⟨0, Set.mem_toFinset.mpr spanU.zero_mem, by simp⟩⟩
    have hPr_span : Pr_{let y ← $ᵖ spanU_aff}[
        δᵣ(↑y, (V : Set (ι → F))) ≤ δ] >
        ProximityGap.errorBound δ deg domain := by
      by_cases hε_lt : ProximityGap.errorBound δ deg domain < 1
      · by_cases hu0_in : u 0 ∈ U'_sub
        · -- u₀ ∈ U': spanU = U', all close, Pr = 1 > ε
          have hspan_eq : spanU = U'_sub := by
            apply le_antisymm
            · apply Submodule.span_le.mpr; rintro x ⟨i, rfl⟩
              refine Fin.cases hu0_in (fun j => Submodule.subset_span ?_) i
              exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
            · exact hU'_le_spanU
          have hall : ∀ y : spanU_aff, δᵣ(↑y, (V : Set (ι → F))) ≤ δ := by
            intro ⟨y, hy⟩
            simp only [spanU_aff, Finset.mem_image] at hy
            obtain ⟨x, hx, rfl⟩ := hy; simp only [zero_add]
            exact h_dirs_close x (by rw [← hspan_eq]; exact Set.mem_toFinset.mp hx)
          calc Pr_{let y ← $ᵖ spanU_aff}[δᵣ(↑y, (V : Set (ι → F))) ≤ δ]
              = 1 := by
                rw [prob_uniform_eq_card_filter_div_card]
                rw [Finset.filter_true_of_mem (fun y _ => hall y), Finset.card_univ]
                exact_mod_cast div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            _ > _ := by exact_mod_cast hε_lt
        · -- u₀ ∉ U': Pr_spanU > ε via coset counting.
          -- Pr = Pr_U + (1-Pr_U)/|F| > ε, using:
          --   0-coset (U'): all |U'| elements close (h_dirs_close)
          --   z-cosets (z≠0): #{close} = #{close in U} by scaling invariance
          --   |spanU| = |F|·|U'| (disjoint cosets, u₀∉U')
          have hU'_sub_span : ∀ d ∈ U'_sub, d ∈ spanU := fun d hd =>
            hU'_le_spanU hd
          -- affineFinset ⊆ spanU_aff: every u₀+d (d∈U') is 0+(u₀+d) ∈ spanU_aff
          have haff_sub_span : affineFinset (u 0) (Fin.tail u) ⊆ spanU_aff := by
            intro x hx
            simp only [affineFinset, spanU_aff, spanU_fin, Finset.mem_image,
              Set.mem_toFinset] at hx ⊢
            obtain ⟨d, hd, rfl⟩ := hx
            exact ⟨u 0 + d, ⟨Submodule.add_mem _
              (Submodule.subset_span ⟨0, rfl⟩) (hU'_le_spanU hd), by simp⟩⟩
          -- U'_sub elements embed into spanU_aff (0-coset)
          have hU'_sub_aff : (U'_sub : Set (ι → F)).toFinset ⊆ spanU_aff := by
            intro x hx
            simp only [spanU_aff, spanU_fin, Finset.mem_image, Set.mem_toFinset] at hx ⊢
            exact ⟨x, ⟨hU'_le_spanU hx, by simp⟩⟩
          -- All U' elements are close
          have hU'_all_close : ∀ x ∈ (U'_sub : Set (ι → F)).toFinset,
              δᵣ(x, (V : Set (ι → F))) ≤ δ := by
            intro x hx; exact h_dirs_close x (Set.mem_toFinset.mp hx)
          -- For c ≠ 0: c • w ∈ spanU for w ∈ affineFinset, and δᵣ(c•w,V) = δᵣ(w,V)
          have hscale_in_span : ∀ (c : F) (_ : c ≠ 0) (w : ι → F),
              w ∈ affineFinset (u 0) (Fin.tail u) → c • w ∈ (spanU : Set (ι → F)) := by
            intro c _ w hw
            simp only [affineFinset, Finset.mem_image, Set.mem_toFinset] at hw
            obtain ⟨d, hd, rfl⟩ := hw
            exact spanU.smul_mem c (Submodule.add_mem _
              (Submodule.subset_span ⟨0, rfl⟩) (hU'_le_spanU hd))
          -- Coset counting: Pr_aff ≤ Pr_span via cross-multiply
          apply lt_of_lt_of_le hPr_fin
          simp only [prob_uniform_eq_card_filter_div_card]
          rw [← ENNReal.coe_div', ← ENNReal.coe_div', ENNReal.coe_le_coe]
          have : Nonempty ↥(affineFinset (u 0) (Fin.tail u)) :=
            Finset.Nonempty.to_subtype ⟨u 0, Finset.mem_image.2
              ⟨0, Set.mem_toFinset.mpr (Submodule.zero_mem _), add_zero _⟩⟩
          rw [div_le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)
            (Nat.cast_pos.mpr (Fintype.card_pos (α := ↥spanU_aff)))]
          -- Goal in NNReal: ↑ca * ↑|span| ≤ ↑cs * ↑|aff|
          -- Coset counting: build injection F × {close in aff} → {close in spanU_aff}
          -- via (c, x) ↦ c • x. Since u₀ ∉ U', each element of aff is nonzero,
          -- so different (c₁,x₁),(c₂,x₂) give different c•x by coset_scalar_eq.
          -- Then |F| * ca ≤ cs, and |span| = |F| * |aff| gives the result.
          norm_cast
          simp only [Fintype.card_coe]
          -- Goal: #{r : aff | close} * #spanU_aff ≤ #{r : spanU_aff | close} * #aff
          -- Build the coset equiv to get |spanU_aff| = |F| * |aff|
          have hspan_card : #spanU_aff = Fintype.card F * #(affineFinset (u 0) (Fin.tail u)) := by
            have hbij_0 : Function.Injective (fun y : ι → F => (0 : ι → F) + y) :=
              fun a b h => by simpa using h
            rw [Finset.card_image_of_injective _ hbij_0]
            have h_aff_card : #(affineFinset (u 0) (Fin.tail u)) =
                #((U'_sub : Set (ι → F)).toFinset) := by
              dsimp only [affineFinset]
              exact Finset.card_image_of_injective _ (add_right_injective (u 0))
            rw [h_aff_card, show Fintype.card F = #(Finset.univ : Finset F) from
              Finset.card_univ.symm, ← Finset.card_product]
            set prod := (Finset.univ : Finset F) ×ˢ (U'_sub : Set (ι → F)).toFinset
            suffices h : prod.image (fun p : F × (ι → F) => p.1 • u 0 + p.2) = spanU_fin by
              rw [← h]; apply Finset.card_image_of_injOn
              intro ⟨c₁, d₁⟩ h₁ ⟨c₂, d₂⟩ h₂ heq
              dsimp at heq
              have hd₁ : d₁ ∈ U'_sub := by
                rw [Finset.mem_coe, Finset.mem_product] at h₁
                exact Set.mem_toFinset.mp h₁.2
              have hd₂ : d₂ ∈ U'_sub := by
                rw [Finset.mem_coe, Finset.mem_product] at h₂
                exact Set.mem_toFinset.mp h₂.2
              have hc := coset_scalar_eq hu0_in hd₁ hd₂ heq
              have hd : d₁ = d₂ := by rw [hc] at heq; exact add_left_cancel heq
              exact Prod.ext hc hd
            ext x; simp only [Finset.mem_image, prod, Finset.mem_product, Finset.mem_univ,
              true_and, Set.mem_toFinset, spanU_fin]
            constructor
            · rintro ⟨⟨c, d⟩, hd, rfl⟩
              dsimp
              exact spanU.add_mem (spanU.smul_mem c (Submodule.subset_span ⟨0, rfl⟩))
                (hU'_le_spanU hd)
            · intro hx
              obtain ⟨c, d, hd, rfl⟩ := mem_spanU_decomp u U'_sub rfl hU'_le_spanU hx
              exact ⟨⟨c, d⟩, hd, rfl⟩
          have haff_decomp : ∀ x ∈ affineFinset (u 0) (Fin.tail u),
              ∃ d ∈ U'_sub, x = u 0 + d := by
            intro x hx
            simp only [affineFinset, Finset.mem_image, Set.mem_toFinset] at hx
            obtain ⟨d, hd, rfl⟩ := hx; exact ⟨d, hd, rfl⟩
          have hd_mem : ∀ x ∈ affineFinset (u 0) (Fin.tail u),
              x - u 0 ∈ U'_sub := by
            intro x hx; obtain ⟨d, hd, rfl⟩ := haff_decomp x hx
            simp only [add_sub_cancel_left]; exact hd
          have hspan_mem' : ∀ y ∈ (spanU : Set (ι → F)),
              y ∈ spanU_aff := by
            intro y hy
            exact Finset.mem_image.mpr ⟨y, Set.mem_toFinset.mpr hy, zero_add y⟩
          rw [hspan_card, ← mul_assoc]
          apply mul_le_mul_left
          rw [mul_comm]
          simp only [← Fintype.card_subtype]
          rw [← Fintype.card_prod]
          apply Fintype.card_le_of_injective
            (fun ⟨c, ⟨⟨x, hx_mem⟩, hx_close⟩⟩ =>
              if hc : c = 0 then
                ⟨⟨x - u 0, hspan_mem' _ (hU'_le_spanU (hd_mem x hx_mem))⟩,
                 h_dirs_close _ (hd_mem x hx_mem)⟩
              else
                ⟨⟨c • x, hspan_mem' _ (hscale_in_span c hc x hx_mem)⟩,
                 by rw [relDistFromCode_smul_eq V hc]; exact hx_close⟩)
          intro ⟨c₁, ⟨⟨x₁, hx₁_mem⟩, hx₁_close⟩⟩ ⟨c₂, ⟨⟨x₂, hx₂_mem⟩, hx₂_close⟩⟩ heq
          obtain ⟨d₁, hd₁, hx₁_eq⟩ := haff_decomp x₁ hx₁_mem
          obtain ⟨d₂, hd₂, hx₂_eq⟩ := haff_decomp x₂ hx₂_mem
          by_cases hc₁ : c₁ = 0 <;> by_cases hc₂ : c₂ = 0
          · -- c₁ = 0, c₂ = 0
            simp only [dif_pos hc₁, dif_pos hc₂] at heq
            have heq' : x₁ - u 0 = x₂ - u 0 :=
              congrArg Subtype.val (congrArg Subtype.val heq)
            have hx_eq : x₁ = x₂ := sub_left_injective heq'
            exact Prod.ext (by rw [hc₁, hc₂])
              (Subtype.ext (Subtype.ext hx_eq))
          · -- c₁ = 0, c₂ ≠ 0
            exfalso; apply hu0_in
            simp only [dif_pos hc₁, dif_neg hc₂] at heq
            have heq' : x₁ - u 0 = c₂ • x₂ :=
              congrArg Subtype.val (congrArg Subtype.val heq)
            rw [hx₁_eq, add_sub_cancel_left, hx₂_eq, smul_add] at heq'
            have hc₂u₀ : c₂ • u 0 = d₁ - c₂ • d₂ := eq_sub_of_add_eq heq'.symm
            rw [show u 0 = c₂⁻¹ • (c₂ • u 0) from by
              rw [smul_smul, inv_mul_cancel₀ hc₂, one_smul], hc₂u₀]
            exact U'_sub.smul_mem c₂⁻¹ (U'_sub.sub_mem hd₁ (U'_sub.smul_mem _ hd₂))
          · -- c₁ ≠ 0, c₂ = 0
            exfalso; apply hu0_in
            simp only [dif_neg hc₁, dif_pos hc₂] at heq
            have heq' : c₁ • x₁ = x₂ - u 0 :=
              congrArg Subtype.val (congrArg Subtype.val heq)
            rw [hx₂_eq, add_sub_cancel_left, hx₁_eq, smul_add] at heq'
            have hc₁u₀ : c₁ • u 0 = d₂ - c₁ • d₁ := eq_sub_of_add_eq heq'
            rw [show u 0 = c₁⁻¹ • (c₁ • u 0) from by
              rw [smul_smul, inv_mul_cancel₀ hc₁, one_smul], hc₁u₀]
            exact U'_sub.smul_mem c₁⁻¹ (U'_sub.sub_mem hd₂ (U'_sub.smul_mem _ hd₁))
          · -- c₁ ≠ 0, c₂ ≠ 0
            simp only [dif_neg hc₁, dif_neg hc₂] at heq
            have heq' : c₁ • x₁ = c₂ • x₂ :=
              congrArg Subtype.val (congrArg Subtype.val heq)
            rw [hx₁_eq, hx₂_eq, smul_add, smul_add] at heq'
            have hc_eq := coset_scalar_eq hu0_in
              (U'_sub.smul_mem c₁ hd₁) (U'_sub.smul_mem c₂ hd₂) heq'
            have hd_eq : d₁ = d₂ := by
              rw [← hc_eq] at heq'
              have h1 : c₁ • d₁ = c₁ • d₂ := add_left_cancel heq'
              ext i; exact mul_left_cancel₀ hc₁ (congr_fun h1 i)
            have hx_eq : x₁ = x₂ := by rw [hx₁_eq, hx₂_eq, hd_eq]
            exact Prod.ext hc_eq (Subtype.ext (Subtype.ext hx_eq))
      · push Not at hε_lt
        exact absurd hPr_fin (not_lt.mpr (le_trans (PMF.coe_le_one _ _)
          (by exact_mod_cast hε_lt)))
    intro x hx
    rcases exists_basepoint_with_large_line_prob (U'_sub := spanU) (u0 := 0)
      (dir := x) (hdir := hx) (V := (V : Set (ι → F))) (δ := δ)
      (ε := ProximityGap.errorBound δ deg domain) hPr_span with ⟨a, hline⟩
    have hJA : Code.jointAgreement (C := (V : Set (ι → F))) (δ := δ)
        (W := Code.finMapTwoWords a.1 x) := by
      apply RS_correlatedAgreement_affineLines hδ
      simpa [Code.finMapTwoWords] using hline
    exact jointAgreement_implies_second_proximity
      (ι := ι) (F := F) (C := (V : Set (ι → F)))
      (δ := δ) (W := Code.finMapTwoWords a.1 x) hJA
  intro x hx
  apply h_spanU_close
  change x ∈ Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u) at hx
  rw [Affine.mem_affineSubspaceFrom_iff] at hx
  obtain ⟨β, rfl⟩ := hx
  exact Submodule.add_mem _
    (Submodule.subset_span ⟨0, rfl⟩)
    (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, rfl⟩))

end AllClose


end ProximityGap
