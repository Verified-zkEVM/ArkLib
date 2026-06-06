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

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory ReedSolomon Code
open scoped BigOperators LinearCode ProbabilityTheory

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
    exact mul_le_mul_of_nonneg_left (hle a) (zero_le (p a))
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

theorem prob_uniform_congr_equiv {α : Type} [Fintype α] [Nonempty α]
    (e : α ≃ α) (P : α → Prop) :
    Pr_{let x ←$ᵖ α}[P (e x)] = Pr_{let x ←$ᵖ α}[P x] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card (F := α) (P := fun x => P (e x))]
  rw [prob_uniform_eq_card_filter_div_card (F := α) (P := P)]
  have hcard : (Finset.filter (fun x : α => P (e x)) Finset.univ).card =
      (Finset.filter (fun x : α => P x) Finset.univ).card := by
    classical
    refine Finset.card_bij (s := Finset.filter (fun x : α => P (e x)) Finset.univ)
      (t := Finset.filter (fun x : α => P x) Finset.univ)
      (i := fun a ha => e a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp [Finset.mem_filter, ha]
    · intro a1 ha1 a2 ha2 h
      exact e.injective h
    · intro b hb
      refine ⟨e.symm b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        simp [Finset.mem_filter, hb]
      · simp
  simp [hcard]

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
    (prob_uniform_congr_equiv (α := (U : Type)) (e := shiftEquiv)
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
  haveI : Nonempty U := by
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

omit [Nonempty ι] [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- The AffineSubspace and Finset.image representations of an affine subspace
have the same membership. -/
private theorem affine_mem_iff_finset_mem {k : ℕ}
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

private noncomputable abbrev affineFinset {k : ℕ}
    (u0 : ι → F) (dirs : Fin k → ι → F) : Finset (ι → F) :=
  (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)).toFinset.image
    (fun d => u0 + d)

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
  simp only [Set.mem_setOf_eq]
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
  haveI hU_ne : Nonempty (affineFinset (u 0) (Fin.tail u)) := by
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
    haveI hne : Nonempty spanU_aff := by
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
          haveI : Nonempty ↥(affineFinset (u 0) (Fin.tail u)) :=
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

private theorem exists_large_of_finset_cover' {α : Type}
    {U : Finset α} {L : ℕ} {buckets : Fin L → Finset α}
    (hcover : ∀ x ∈ U, ∃ i, x ∈ buckets i)
    {B : ℕ} (hLB : L * B < U.card) :
    ∃ i, B < (buckets i).card := by
  classical
  by_contra hall
  push Not at hall
  have hle : U.card ≤ L * B := by
    calc U.card
        ≤ (Finset.univ.biUnion buckets).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, hi⟩ := hcover x hx
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      _ ≤ ∑ i : Fin L, (buckets i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin L, B := Finset.sum_le_sum (fun i _ => hall i)
      _ = L * B := by simp [Finset.sum_const]
  exact absurd hle (not_le.mpr hLB)


section Bucketing

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedDecidableInType false in
/-- BCIKS20 §6.3 bucketing: given an affine subspace U whose elements are all δ-close
to a linear code V, there exist a codeword v₀ and agreement set D' of size ≥ (1-δ)|ι|
such that the basepoint agrees with v₀ on D' and every generator direction agrees with
some codeword on D'. -/
theorem bucket_exists_common_codeword
    {k : ℕ} [NeZero k] (V : Submodule F (ι → F)) (u₀ : ι → F) (dirs : Fin k → ι → F)
    {δ : ℝ≥0}
    (h_elem_ja : ∀ x ∈ (Affine.affineSubspaceAtOrigin (F := F) u₀ dirs : Set (ι → F)),
        jointAgreement (C := (V : Set (ι → F))) (δ := δ)
          (W := finMapTwoWords u₀ (x - u₀)))
    (h_pair_ja : ∀ j : Fin k,
        jointAgreement (C := (V : Set (ι → F))) (δ := δ)
          (W := finMapTwoWords u₀ (dirs j)))
    (h_list_bound : ∀ (w : ι → F) (close : Finset (ι → F)),
        (∀ v ∈ close, v ∈ (V : Set (ι → F)) ∧ δᵣ(w, v) ≤ δ) →
        close.card < Fintype.card F)
    (hδ_exact : ∀ v ∈ (V : Set (ι → F)), δᵣ(u₀, v) ≤ δ → (δᵣ(u₀, v) : ℝ≥0) ≥ δ) :
    ∃ (v₀ : ι → F) (D' : Finset ι),
      v₀ ∈ (V : Set (ι → F)) ∧
      (D'.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      D' ⊆ Finset.filter (fun c => v₀ c = u₀ c) Finset.univ ∧
      ∀ j : Fin k, ∃ w_j ∈ (V : Set (ι → F)),
        D' ⊆ Finset.filter (fun c => w_j c = dirs j c) Finset.univ := by
  classical
  -- Step A: Per-direction JA witnesses.
  choose S_j hS_j v_pair hv_pair using fun j => h_pair_ja j
  set U_fin := affineFinset u₀ dirs
  have h_elem_fin : ∀ x ∈ U_fin, jointAgreement (C := (V : Set (ι → F))) (δ := δ)
      (W := finMapTwoWords u₀ (x - u₀)) := by
    intro x hx; apply h_elem_ja; rwa [← affine_mem_iff_finset_mem] at hx
  -- For each x ∈ U, extract the u₀-codeword (v 0) and its agreement set.
  -- Use a non-dependent wrapper to avoid membership-in-filter issues.
  have h_ja_all : ∀ x ∈ U_fin, ∃ (Sx : Finset ι) (_ : Sx.card ≥ (1 - δ) * Fintype.card ι)
      (vx : Fin 2 → ι → F),
      (∀ i, vx i ∈ (V : Set (ι → F)) ∧
        Sx ⊆ Finset.filter (fun j => vx i j = (finMapTwoWords u₀ (x - u₀)) i j) Finset.univ) := by
    intro x hx; obtain ⟨S, hS, v, hv⟩ := h_elem_fin x hx; exact ⟨S, hS, v, hv⟩
  choose S_x hS_x v_x hv_x using h_ja_all
  -- pickCodeword: for each x ∈ U, the codeword close to u₀.
  let pickCW : (x : ι → F) → x ∈ U_fin → (ι → F) := fun x hx => v_x x hx 0
  -- closeWords: image of pickCW over U.
  let closeWords : Finset (ι → F) := U_fin.attach.image (fun ⟨x, hx⟩ => pickCW x hx)
  have h_cw_mem : ∀ x (hx : x ∈ U_fin), pickCW x hx ∈ (V : Set (ι → F)) :=
    fun x hx => (hv_x x hx 0).1
  -- pickCW x agrees with u₀ on S_x (which has size ≥ (1-δ)|ι|).
  have h_cw_agree : ∀ x (hx : x ∈ U_fin),
      S_x x hx ⊆ Finset.filter (fun c => pickCW x hx c = u₀ c) Finset.univ := by
    intro x hx
    exact (hv_x x hx 0).2
  -- Step B: Bucket U by pickCW, pigeonhole for dominant bucket.
  -- h_list_bound needs δᵣ(u₀, v) ≤ δ. This is relHammingDist (ℚ≥0) vs δ (ℝ≥0).
  -- Agreement on ≥ (1-δ)|ι| coords ⟹ disagreement on ≤ δ|ι| coords ⟹ relHammingDist ≤ δ.
  have h_cw_close : ∀ x (hx : x ∈ U_fin), δᵣ(u₀, pickCW x hx) ≤ δ := by
    intro x hx
    have h_agree := h_cw_agree x hx
    have h_agree_size := hS_x x hx
    -- hammingDist ≤ |ι| - |S_x|
    have h_filter_card : (S_x x hx).card ≤
        (Finset.filter (fun c => u₀ c = pickCW x hx c) Finset.univ).card := by
      apply Finset.card_le_card; intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_agree hc ⊢
      exact (Finset.mem_filter.mp (h_agree hc)).2.symm
    have h_compl : (Finset.filter (fun c => ¬u₀ c = pickCW x hx c) Finset.univ).card =
        Fintype.card ι - (Finset.filter (fun c => u₀ c = pickCW x hx c) Finset.univ).card := by
      have := Finset.card_filter_add_card_filter_not
          (s := Finset.univ) (p := fun c => u₀ c = pickCW x hx c)
      simp only [Finset.card_univ] at this
      omega
    have h_ham : hammingDist u₀ (pickCW x hx) ≤ Fintype.card ι - (S_x x hx).card := by
      simp only [hammingDist]; rw [h_compl]; omega
    have h_sx_le : (S_x x hx).card ≤ Fintype.card ι := Finset.card_le_univ _
    -- Work in ℝ to avoid NNReal subtraction issues.
    -- Goal: δᵣ(u₀, pickCW x hx) ≤ δ, i.e., relHammingDist ≤ δ
    -- relHammingDist = ham / |ι|. Suffices ham ≤ δ * |ι|.
    -- Lift to ℝ via NNReal.coe_le_coe and work there.
    suffices h : (hammingDist u₀ (pickCW x hx) : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) by
      unfold relHammingDist
      -- Goal: ↑(↑ham / ↑|ι| : ℚ≥0) ≤ δ in ℝ≥0
      -- Convert via NNReal.coe_le_coe and ℝ
      apply NNReal.coe_le_coe.mp
      push_cast
      have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
      exact (div_le_iff₀ hn).mpr h
    calc (hammingDist u₀ (pickCW x hx) : ℝ)
        ≤ (Fintype.card ι : ℝ) - ((S_x x hx).card : ℝ) := by exact_mod_cast h_ham
      _ ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := by
          have h1 := h_agree_size
          -- h1 : (|S_x| : ℝ≥0) ≥ (1 - δ) * |ι|
          -- Lift to ℝ
          have h2 : ((S_x x hx).card : ℝ) ≥ ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
            by_cases hδ_le : δ ≤ 1
            · have h1' : ((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) ≤ ((S_x x hx).card : ℝ≥0) := h1.le
              calc ((S_x x hx).card : ℝ)
                  ≥ ((((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) := by exact_mod_cast h1'
                _ = ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
                    rw [NNReal.coe_mul, NNReal.coe_sub hδ_le, NNReal.coe_one, NNReal.coe_natCast]
            · push Not at hδ_le
              have hδ_real : (1 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_le
              linarith [Nat.cast_nonneg' (α := ℝ) (S_x x hx).card,
                        mul_nonpos_of_nonpos_of_nonneg (by linarith : (1 : ℝ) - ↑δ ≤ 0)
                          (Nat.cast_nonneg' (α := ℝ) (Fintype.card ι))]
          linarith
  have h_cw_bound : closeWords.card < Fintype.card F := by
    apply h_list_bound u₀
    intro v hv
    obtain ⟨⟨x, hx⟩, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨h_cw_mem x hx, h_cw_close x hx⟩
  -- Step B (cont): Pigeonhole via exists_large_of_finset_cover.
  -- Need buckets indexed by Fin L. Enumerate closeWords.
  let L := closeWords.card
  let cwList := closeWords.val.toList
  have hcwLen : cwList.length = L := by simp [cwList, L]
  -- Build Fin L-indexed buckets.
  let bucketsFin : Fin L → Finset (ι → F) :=
    fun i => U_fin.filter (fun x => ∃ hx : x ∈ U_fin, pickCW x hx = cwList.get (i.cast hcwLen.symm))
  -- Cover: every x ∈ U is in some bucket.
  have h_cover_fin : ∀ x ∈ U_fin, ∃ i : Fin L, x ∈ bucketsFin i := by
    intro x hx
    have h_in_cw : pickCW x hx ∈ closeWords :=
      Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    have h_in_list : pickCW x hx ∈ cwList := by
      simp only [cwList, Multiset.mem_toList]; exact h_in_cw
    obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem h_in_list
    refine ⟨⟨idx, by omega⟩, ?_⟩
    simp only [bucketsFin, Finset.mem_filter]
    exact ⟨hx, ⟨hx, by simp only [Fin.cast_mk, List.get_eq_getElem]; exact heq.symm⟩⟩
  -- Handle r = 0 case separately: U = {u₀}, all dirs = 0, conclusion trivial.
  set r := Module.finrank F ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F)))
    with hr_def
  by_cases hr : r = 0
  · -- r = 0: span(dirs) = ⊥, so all dirs j = 0. Conclusion trivial.
    have h_span_bot : Submodule.span F (Finset.univ.image dirs : Set (ι → F)) = ⊥ := by
      rwa [Submodule.finrank_eq_zero] at hr
    have h_dirs_zero : ∀ j, dirs j = 0 := by
      intro j
      have : dirs j ∈ (Submodule.span F (Finset.univ.image dirs : Set (ι → F)) : Set (ι → F)) :=
        Submodule.subset_span (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      rw [h_span_bot] at this
      exact (Submodule.mem_bot F).mp this
    set j₀ : Fin k := ⟨0, NeZero.pos k⟩
    refine ⟨v_pair j₀ 0, S_j j₀, (hv_pair j₀ 0).1, hS_j j₀, ?_, ?_⟩
    · convert (hv_pair j₀ 0).2 using 2
    · intro j
      refine ⟨0, V.zero_mem, ?_⟩
      intro c _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply]
      exact (h_dirs_zero j ▸ rfl)
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr
  -- Size bound: L * |F|^{r-1} < |U| = |F|^r since L < |F|.
  have h_size : L * Fintype.card F ^ (r - 1) < U_fin.card := by
    rw [affine_finset_card_eq]
    have hF_pos : 0 < Fintype.card F := Fintype.card_pos
    have : Fintype.card F * Fintype.card F ^ (r - 1) = Fintype.card F ^ r := by
      calc Fintype.card F * Fintype.card F ^ (r - 1)
          = Fintype.card F ^ (r - 1) * Fintype.card F := Nat.mul_comm _ _
        _ = Fintype.card F ^ (r - 1 + 1) := (pow_succ _ _).symm
        _ = Fintype.card F ^ r := by
          congr 1; exact Nat.succ_pred_eq_of_pos hr_pos
    calc L * Fintype.card F ^ (r - 1)
        < Fintype.card F * Fintype.card F ^ (r - 1) := by
          exact Nat.mul_lt_mul_of_pos_right h_cw_bound (Nat.pos_of_ne_zero (by
            intro h; rw [Nat.pow_eq_zero] at h; omega))
      _ = Fintype.card F ^ r := this
  obtain ⟨i₀, h_big⟩ := exists_large_of_finset_cover' h_cover_fin h_size
  -- u₀ ∈ U and u₀ + dirs j ∈ U.
  have h_u0_mem : u₀ ∈ U_fin := by
    simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset]
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  -- Step C: Choose v₀ as dominant bucket's codeword. Build h_restrict.
  -- The dominant bucket bucketsFin i₀ has codeword cwList[i₀].
  set v₀ := cwList.get (i₀.cast hcwLen.symm) with hv₀_def
  -- v₀ ∈ closeWords, so v₀ = pickCW x hx for some x.
  have hv₀_in_cw : v₀ ∈ closeWords := by
    have h1 : v₀ ∈ cwList := List.get_mem cwList _
    simp only [cwList, Multiset.mem_toList] at h1
    exact Finset.mem_def.mpr h1
  obtain ⟨⟨x₀, hx₀⟩, _, hpick₀⟩ := Finset.mem_image.mp hv₀_in_cw
  have hv₀_mem : v₀ ∈ (V : Set (ι → F)) := by rw [← hpick₀]; exact h_cw_mem x₀ hx₀
  set D' := S_x x₀ hx₀
  have hD'_size : (D'.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := hS_x x₀ hx₀
  have hD'_sub_filter : D' ⊆ Finset.filter (fun c => v₀ c = u₀ c) Finset.univ := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := Finset.mem_filter.mp (h_cw_agree x₀ hx₀ hc)
    rw [← hpick₀]; exact this.2
  have h_restrict : ∀ x ∈ U_fin, ∃ w ∈ (V : Set (ι → F)),
      D' ⊆ Finset.filter (fun c => w c = x c) Finset.univ := by
    let B_v₀ := U_fin.filter (fun x => ∃ w ∈ (V : Set (ι → F)),
        D' ⊆ Finset.filter (fun c => w c = x c) Finset.univ)
    have h_bucket_sub : ∀ x (hx : x ∈ U_fin), pickCW x hx = v₀ → x ∈ B_v₀ := by
      intro x hx hpick
      simp only [B_v₀, Finset.mem_filter]
      refine ⟨hx, v₀ + v_x x hx 1, V.add_mem hv₀_mem (hv_x x hx 1).1, ?_⟩
      -- hδ_exact forces δᵣ(u₀, v₀) = δ, making {c | v₀ c = u₀ c} have exact size (1-δ)|ι|.
      -- Since S_x ⊆ {c | v₀ c = u₀ c} and |S_x| ≥ (1-δ)|ι| = |{c | v₀ c = u₀ c}|,
      -- S_x = {c | v₀ c = u₀ c} ⊇ D'. Then (v₀ + v_x 1) agrees with x on S_x ⊇ D'.
      have hSx_sub_filter : S_x x hx ⊆ Finset.filter (fun c => v₀ c = u₀ c) Finset.univ := by
        have h := h_cw_agree x hx; rw [hpick] at h; exact h
      have hv₀_close : δᵣ(u₀, v₀) ≤ δ := by rw [← hpick]; exact h_cw_close x hx
      have hv₀_far : (δᵣ(u₀, v₀) : ℝ≥0) ≥ δ := hδ_exact v₀ hv₀_mem hv₀_close
      have hv₀_eq : (δᵣ(u₀, v₀) : ℝ≥0) = δ := le_antisymm hv₀_close hv₀_far
      -- S_x = {c | v₀ c = u₀ c} because both have the same cardinality
      have hfilter_card : (Finset.filter (fun c => v₀ c = u₀ c) Finset.univ).card =
          Fintype.card ι - hammingDist u₀ v₀ := by
        have h_compl := Finset.card_filter_add_card_filter_not
          (s := Finset.univ) (p := fun c => v₀ c = u₀ c)
        simp only [Finset.card_univ] at h_compl
        have : (Finset.filter (fun c => ¬v₀ c = u₀ c) Finset.univ).card = hammingDist u₀ v₀ := by
          congr 1; ext c; simp [ne_eq, eq_comm]
        omega
      have hSx_eq_filter : S_x x hx = Finset.filter (fun c => v₀ c = u₀ c) Finset.univ :=
        Finset.eq_of_subset_of_card_le hSx_sub_filter (by
          rw [hfilter_card]
          -- Use the existing h_cw_close proof pattern (L896-928) for NNReal arithmetic.
          -- Filter card = |ι| - ham. |S_x| ≥ (1-δ)|ι|. ham = δ*|ι| from hv₀_eq.
          -- So filter card = (1-δ)|ι| ≤ |S_x|.
          have h_ham_le : hammingDist u₀ v₀ ≤ Fintype.card ι := hammingDist_le_card_fintype
          -- Extract |S_x| bound in ℕ via ℝ detour
          suffices h : (Fintype.card ι - hammingDist u₀ v₀ : ℤ) ≤ (S_x x hx).card by omega
          -- Work in ℝ: from hv₀_eq get ham = δ*|ι|, from hS_x get |S_x| ≥ (1-δ)*|ι|.
          suffices h_real :
              (Fintype.card ι : ℝ) - (hammingDist u₀ v₀ : ℝ) ≤ ((S_x x hx).card : ℝ) by
            exact_mod_cast h_real
          -- Step 1: Extract ham = δ * |ι| in ℝ from hv₀_eq
          have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
          have h_ham_real : (hammingDist u₀ v₀ : ℝ) = (δ : ℝ) * (Fintype.card ι : ℝ) := by
            -- hv₀_eq : (δᵣ(u₀, v₀) : ℝ≥0) = δ, i.e. (ham/|ι| : ℚ≥0) cast to ℝ≥0 = δ
            -- Cast both sides to ℝ: (ham/|ι|) = δ in ℝ, multiply by |ι|.
            have h_le : (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) ≤ (δ : ℝ) := by
              calc (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ)
                  = ((hammingDist u₀ v₀ / Fintype.card ι : ℚ≥0) : ℝ) := by
                    push_cast; norm_cast
                _ ≤ (δ : ℝ) := by exact_mod_cast hv₀_close
            have h_ge : (δ : ℝ) ≤ (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) := by
              calc (δ : ℝ)
                  ≤ ((δᵣ(u₀, v₀) : ℝ≥0) : ℝ) := by exact_mod_cast hv₀_far.le
                _ = ((hammingDist u₀ v₀ / Fintype.card ι : ℚ≥0) : ℝ) := by rfl
                _ = (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) := by
                    push_cast; norm_cast
            have h_eq : (hammingDist u₀ v₀ : ℝ) / (Fintype.card ι : ℝ) = (δ : ℝ) :=
              le_antisymm h_le h_ge
            rwa [div_eq_iff (ne_of_gt hn_pos)] at h_eq
          -- Step 2: Extract |S_x| ≥ (1-δ)*|ι| in ℝ
          have h_sx_real : ((S_x x hx).card : ℝ) ≥ ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
            have h1 := hS_x x hx  -- (|S_x| : ℝ≥0) ≥ (1 - δ) * |ι|
            by_cases hδ_le : δ ≤ 1
            · have h1' : ((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) ≤ ((S_x x hx).card : ℝ≥0) := h1.le
              calc ((S_x x hx).card : ℝ)
                  ≥ ((((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)) := by exact_mod_cast h1'
                _ = ((1 : ℝ) - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
                    rw [NNReal.coe_mul, NNReal.coe_sub hδ_le, NNReal.coe_one, NNReal.coe_natCast]
            · push Not at hδ_le
              have hδ_real : (1 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_le
              linarith [Nat.cast_nonneg' (α := ℝ) (S_x x hx).card,
                        mul_nonpos_of_nonpos_of_nonneg (by linarith : (1 : ℝ) - ↑δ ≤ 0)
                          (Nat.cast_nonneg' (α := ℝ) (Fintype.card ι))]
          -- Step 3: Combine
          linarith)
      -- D' ⊆ {c | v₀ c = u₀ c} = S_x, so D' ⊆ S_x
      have hD'_sub_Sx : D' ⊆ S_x x hx := hSx_eq_filter ▸ hD'_sub_filter
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
      have hc_Sx := hD'_sub_Sx hc
      have hcD' := (Finset.mem_filter.mp (hD'_sub_filter hc)).2
      have h1 : v_x x hx 1 c = (finMapTwoWords u₀ (x - u₀)) 1 c :=
        (Finset.mem_filter.mp ((hv_x x hx 1).2 hc_Sx)).2
      simp only [finMapTwoWords] at h1
      rw [hcD', h1, Pi.sub_apply]; ring
    have h_Bv0_sub_U : ↑B_v₀ ⊆ (Affine.affineSubspaceAtOrigin (F := F) u₀ dirs : Set (ι → F)) := by
      intro x hx
      exact (affine_mem_iff_finset_mem u₀ dirs x).mpr
        (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
    -- B_v₀ is affine: it's {x ∈ U | x|_{D'} ∈ V|_{D'}}, preimage of linear sub under affine map.
    have h_Bv0_affine : B_v₀ ≠ U_fin →
        ∃ (m : ℕ) (u₀' : ι → F) (dirs' : Fin m → ι → F),
          B_v₀ = affineFinset u₀' dirs' ∧
          (Submodule.span F (Finset.univ.image dirs' : Set (ι → F)) :
            Submodule F (ι → F)) <
          Submodule.span F (Finset.univ.image dirs : Set (ι → F)) := by
      intro h_ne
      let π : (ι → F) →ₗ[F] (↑D' → F) := {
        toFun := fun f i => f i.1
        map_add' := fun _ _ => funext fun _ => rfl
        map_smul' := fun _ _ => funext fun _ => rfl
      }
      let span_dirs := Submodule.span F (Finset.univ.image dirs : Set (ι → F))
      let W := span_dirs ⊓ Submodule.comap π (Submodule.map π V)
      -- Extract basis of W, produce dirs'
      let m := Module.finrank F ↥W
      let bW := Module.finBasis F ↥W
      let dirs' : Fin m → ι → F := fun i => ((bW i : ↥W) : ι → F)
      -- span(dirs') = W: basis of W spans W via subtype inclusion
      have h_span_eq : Submodule.span F (Finset.univ.image dirs' : Set (ι → F)) = W := by
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          exact (bW i).2
        · intro x hx
          have h := bW.sum_repr ⟨x, hx⟩
          apply_fun Subtype.val at h
          simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
          rw [← h]
          exact Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span
              (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
      -- v₀ agrees with u₀ on D'
      have hv₀_agree : ∀ c ∈ D', v₀ c = u₀ c := fun c hc =>
        (Finset.mem_filter.mp (hD'_sub_filter hc)).2
      -- B_v₀ = affineFinset u₀ dirs'  (both equal W.toFinset.image (· + u₀))
      have h_eq : B_v₀ = affineFinset u₀ dirs' := by
        simp only [affineFinset, h_span_eq]
        ext x
        simp only [B_v₀, Finset.mem_filter, Finset.mem_image, Set.mem_toFinset]
        constructor
        · rintro ⟨hxU, w, hw, hD⟩
          refine ⟨x - u₀, ?_, by abel⟩
          refine ⟨?_, ?_⟩
          · -- x - u₀ ∈ span_dirs
            have hxU' := hxU
            simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset] at hxU'
            obtain ⟨d, hd, hxd⟩ := hxU'
            have : x - u₀ = d := by rw [← hxd]; abel
            rw [this]; exact hd
          · -- x - u₀ ∈ comap π (map π V)
            change π (x - u₀) ∈ Submodule.map π V
            rw [Submodule.mem_map]
            refine ⟨w - v₀, V.sub_mem hw hv₀_mem, ?_⟩
            ext ⟨c, hc⟩
            have hcD := hD hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcD
            simp only [π, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
            rw [hcD, hv₀_agree c hc]
        · rintro ⟨d, ⟨hd_span, hd_comap⟩, rfl⟩
          constructor
          · simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset]
            exact ⟨d, hd_span, rfl⟩
          · have hd_comap' : π d ∈ Submodule.map π V := hd_comap
            rw [Submodule.mem_map] at hd_comap'
            obtain ⟨w', hw', hπeq⟩ := hd_comap'
            refine ⟨w' + v₀, V.add_mem hw' hv₀_mem, ?_⟩
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
            have h1 : w' c = d c := congr_fun hπeq ⟨c, hc⟩
            rw [h1, hv₀_agree c hc, add_comm]
      -- W < span_dirs (from B_v₀ ≠ U_fin)
      have hW_lt : W < span_dirs := by
        rw [lt_iff_le_and_ne]
        refine ⟨inf_le_left, fun h_eq_W => h_ne ?_⟩
        suffices h : affineFinset u₀ dirs' = affineFinset u₀ dirs by
          rwa [h_eq]
        ext x
        simp only [affineFinset, Finset.mem_image, Set.mem_toFinset]
        have h_sub_eq : Submodule.span F (↑(image dirs' univ) : Set (ι → F)) =
            Submodule.span F (↑(image dirs univ) : Set (ι → F)) :=
          h_span_eq.trans h_eq_W
        constructor
        · rintro ⟨d, hd, rfl⟩
          exact ⟨d, h_sub_eq ▸ hd, rfl⟩
        · rintro ⟨d, hd, rfl⟩
          exact ⟨d, h_sub_eq ▸ hd, rfl⟩
      exact ⟨m, u₀, dirs', h_eq, h_span_eq ▸ hW_lt⟩
    -- |B_v₀| > |F|^{r-1}: dominant bucket ⊆ B_v₀ via h_bucket_sub.
    have h_Bv0_big : Fintype.card F ^ (Module.finrank F
        ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F))) - 1) < B_v₀.card := by
      calc Fintype.card F ^ (Module.finrank F
              ↥(Submodule.span F (Finset.univ.image dirs : Set (ι → F))) - 1)
          < (bucketsFin i₀).card := h_big
        _ ≤ B_v₀.card := by
            apply Finset.card_le_card
            intro x hx
            simp only [bucketsFin, Finset.mem_filter] at hx
            obtain ⟨hx_U, hx_mem, hpick⟩ := hx
            exact h_bucket_sub x hx_U hpick
    have h_Bv0_eq_U : B_v₀ = U_fin := by
      by_contra h_ne
      obtain ⟨m, u₀', dirs', h_eq, h_proper⟩ := h_Bv0_affine h_ne
      have := proper_affine_sub_card_le u₀ dirs B_v₀ h_Bv0_sub_U ⟨m, u₀', dirs', h_eq, h_proper⟩
      omega
    intro x hx
    have : x ∈ B_v₀ := h_Bv0_eq_U ▸ hx
    exact (Finset.mem_filter.mp this).2
  -- Step D: take v₀ and D'. For directions, use h_restrict at u₀ + dirs j.
  refine ⟨v₀, D', hv₀_mem, hD'_size, hD'_sub_filter, ?_⟩
  · intro j
    have h_uj_mem : u₀ + dirs j ∈ U_fin := by
      simp only [U_fin, affineFinset, Finset.mem_image, Set.mem_toFinset]
      exact ⟨dirs j, Submodule.subset_span (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩), rfl⟩
    obtain ⟨w, hw_mem, hw_agree⟩ := h_restrict (u₀ + dirs j) h_uj_mem
    refine ⟨w - v₀, V.sub_mem hw_mem hv₀_mem, ?_⟩
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply]
    have hw_c := Finset.mem_filter.mp (hw_agree hc) |>.2
    have hv₀_c : v₀ c = u₀ c := (Finset.mem_filter.mp (hD'_sub_filter hc)).2
    rw [hw_c, hv₀_c, Pi.add_apply, add_sub_cancel_left]

end Bucketing

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Pigeonhole for finite covers: if `U` is covered by `L` indexed subsets and
`L * B < |U|`, then some subset has more than `B` elements. -/
theorem exists_large_of_finset_cover {α : Type}
    {U : Finset α} {L : ℕ} {buckets : Fin L → Finset α}
    (hcover : ∀ x ∈ U, ∃ i, x ∈ buckets i)
    {B : ℕ} (hLB : L * B < U.card) :
    ∃ i, B < (buckets i).card := by
  classical
  by_contra hall
  push Not at hall
  have hle : U.card ≤ L * B := by
    calc U.card
        ≤ (Finset.univ.biUnion buckets).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, hi⟩ := hcover x hx
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      _ ≤ ∑ i : Fin L, (buckets i).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin L, B := Finset.sum_le_sum (fun i _ => hall i)
      _ = L * B := by simp [Finset.sum_const]
  exact absurd hle (not_le.mpr hLB)

/-- If `S` is a finite set of elements that are all roots of a nonzero polynomial `Q`,
then `|S| ≤ deg(Q)`. Wrapper around Mathlib's `card_le_degree_of_subset_roots`. -/
theorem card_roots_finset_le_natDegree {R : Type} [CommRing R] [IsDomain R]
    {Q : Polynomial R} (hQ : Q ≠ 0)
    {S : Finset R} (hroots : ∀ a ∈ S, Polynomial.IsRoot Q a) :
    S.card ≤ Q.natDegree := by
  classical
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  exact (Polynomial.mem_roots hQ).mpr (hroots a ha)

omit [DecidableEq F] in
/-- The Guruswami-Sudan list-decoding bound: given a nonzero polynomial `Q` over `F[X]`
whose `Y`-degree is less than `|F|`, the number of distinct polynomials `P` such that
`(Y - P(X)) | Q(X, Y)` is strictly less than `|F|`. This is the structural core of the
list-decoding argument (BCIKS20 §5). -/
theorem card_divisors_lt_field
    {Q : Polynomial (Polynomial F)} (hQ : Q ≠ 0)
    (hd : Q.natDegree < Fintype.card F)
    {polys : Finset (Polynomial F)}
    (hdiv : ∀ P ∈ polys, (Polynomial.X - Polynomial.C P) ∣ Q) :
    polys.card < Fintype.card F := by
  calc polys.card
      ≤ Q.natDegree := by
        apply card_roots_finset_le_natDegree hQ
        intro P hP
        exact (Polynomial.dvd_iff_isRoot).mp (hdiv P hP)
    _ < Fintype.card F := hd

/-- Degree-bound numerator step: `(m + 1/2) * s * n / (deg - 1) ≤ 5 / (4 * μ)`.
Extracted from `exists_gs_multiplicity` to reduce heartbeat pressure. -/
private lemma gs_degree_bound_le_inv_mu
    {s η : ℝ} {m deg : ℕ} {n : ℕ}
    (hs_pos : 0 < s) (hη_pos : 0 < η)
    (hs_sq : s ^ 2 = (deg : ℝ) / n) (hn_pos : (0 : ℝ) < n)
    (hdeg : 1 < deg)
    (hm_bound : (m : ℝ) + 1 / 2 ≤ s / (2 * η) + 5 / 2)
    (μ : ℝ) (hμ_pos : 0 < μ) (hμ_le_η : μ ≤ η) (hμ_le_s20 : μ ≤ s / 20) :
    (↑m + 1/2) * s * (n : ℝ) / (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / (4 * μ) := by
  have hdeg1 : 0 < deg - 1 := by omega
  have hdeg_pos : (0 : ℝ) < deg := by exact_mod_cast (show 0 < deg by omega)
  have hdeg1_cast_eq : (↑(deg - 1 : ℕ) : ℝ) = (deg : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ deg), Nat.cast_one]
  have hdeg1_ge : (↑(deg - 1 : ℕ) : ℝ) ≥ (deg : ℝ) / 2 := by
    rw [hdeg1_cast_eq]; linarith [show (2 : ℝ) ≤ deg from by exact_mod_cast hdeg]
  have h_num : (↑m + 1/2) * s * (n : ℝ) ≤
      (deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s) := by
    have h1 : (↑m + 1/2) * s * (n : ℝ) ≤
        (s / (2 * η) + 5/2) * s * (n : ℝ) := by
        have : (0 : ℝ) ≤ s * n := mul_nonneg hs_pos.le hn_pos.le
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm_bound hs_pos.le) hn_pos.le]
    have hsqn : s ^ 2 * (n : ℝ) = (deg : ℝ) := by
      have := hs_sq; field_simp at this; linarith
    have h2 : (s / (2 * η) + 5/2) * s * (n : ℝ) =
        (deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s) := by
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hη_ne : η ≠ 0 := ne_of_gt hη_pos
      field_simp
      nlinarith [hsqn, mul_comm s (n : ℝ)]
    linarith
  have hdeg_le_2d1 : (deg : ℝ) ≤ 2 * ↑(deg - 1 : ℕ) := by linarith [hdeg1_ge]
  have h3 : (deg : ℝ) / (2 * η) / (↑(deg - 1 : ℕ) : ℝ) ≤ 1 / η := by
    have hd1_pos : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
    rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) hd1_pos) hη_pos, one_mul]
    nlinarith
  have h4 : 5 * (deg : ℝ) / (2 * s) / (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / s := by
    have hd1_pos : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
    rw [div_div, div_le_div_iff₀ (mul_pos (by positivity) hd1_pos) hs_pos]
    nlinarith
  have h5 : 1 / η ≤ 1 / μ := by
    rw [div_le_div_iff₀ hη_pos hμ_pos]; linarith [hμ_le_η]
  have h6 : 5 / s ≤ 1 / (4 * μ) := by
    rw [div_le_div_iff₀ hs_pos (by positivity : (0:ℝ) < 4 * μ)]
    linarith [hμ_le_s20]
  calc (↑m + 1/2) * s * (n : ℝ) / (↑(deg - 1 : ℕ) : ℝ)
      ≤ ((deg : ℝ) / (2 * η) + 5 * (deg : ℝ) / (2 * s)) / (↑(deg - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right h_num (by positivity)
    _ = (deg : ℝ) / (2 * η) / (↑(deg - 1 : ℕ) : ℝ) +
        5 * (deg : ℝ) / (2 * s) / (↑(deg - 1 : ℕ) : ℝ) := add_div _ _ _
    _ ≤ 1 / η + 5 / s := add_le_add h3 h4
    _ ≤ 1 / μ + 1 / (4 * μ) := add_le_add h5 h6
    _ = 5 / (4 * μ) := by ring

omit [DecidableEq ι] [DecidableEq F] in
/-- Construct a GS multiplicity `m` satisfying both the Johnson radius bound and the degree
bound. Witness: `m = ⌈√ρ/(2η)⌉ + 1` where `η = 1 - √ρ - δ`. -/
lemma exists_gs_multiplicity {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1)
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ) :
    ∃ m : ℕ, 1 ≤ m
      ∧ (δ : ℝ) < gs_johnson deg (Fintype.card ι) m
      ∧ gs_degree_bound deg (Fintype.card ι) m / (deg - 1) < Fintype.card F := by
  have hn_le : Fintype.card ι ≤ Fintype.card F :=
    Fintype.card_le_of_injective domain domain.injective
  have hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1 :=
    NNReal.sqrt_le_one.mpr (by exact_mod_cast
      @DivergenceOfSets.reedSolomon_rate_le_one ι _ _ F _ _ domain)
  have hδ_real : (δ : ℝ) < 1 - (ReedSolomon.sqrtRate deg domain : ℝ) := by
    calc (δ : ℝ) < ((1 - ReedSolomon.sqrtRate deg domain : ℝ≥0) : ℝ) := by exact_mod_cast hδ
      _ = 1 - (ReedSolomon.sqrtRate deg domain : ℝ) := by
          rw [NNReal.coe_sub hsqrt_le, NNReal.coe_one]
  have hη_pos : 0 < 1 - (ReedSolomon.sqrtRate deg domain : ℝ) - (δ : ℝ) := by linarith
  set s : ℝ := (ReedSolomon.sqrtRate deg domain : ℝ) with hs_def
  set η : ℝ := 1 - s - (δ : ℝ) with hη_def
  -- For deg ≤ 1: degree bound is trivial (Nat division by 0 = 0)
  by_cases hdeg : 1 < deg
  · -- deg ≥ 2: full GS multiplicity construction
    set m := Nat.ceil (s / (2 * η)) + 1
    refine ⟨m, by omega, ?_, ?_⟩
    · -- Johnson bound: δ < gs_johnson deg n m
      have hn_pos : (0 : ℝ) < Fintype.card ι := by positivity
      have hm_pos : (0 : ℝ) < m := by positivity
      have hs_eq : s = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
        simp only [s, hs_def, ReedSolomon.sqrtRate]
        rw [Real.coe_sqrt]
        congr 1
        haveI : NeZero deg := ⟨by omega⟩
        have hdim := ReedSolomon.dim_eq_deg_of_le' (α := domain) (n := deg)
          (by omega : deg ≤ Fintype.card ι)
        rw [LinearCode.rate, hdim]
        simp [LinearCode.length]
      have hgs_eq : gs_johnson deg (Fintype.card ι) m = 1 - s - s / (2 * m) := by
        unfold gs_johnson; simp only
        rw [hs_eq]
        have : (↑(↑deg / ↑(Fintype.card ι) : ℚ) : ℝ) = (deg : ℝ) / Fintype.card ι := by
          push_cast; ring
        rw [this]
      rw [hgs_eq]
      have hm_gt : s / (2 * η) < m := by
        have h1 : s / (2 * η) ≤ ↑(Nat.ceil (s / (2 * η))) := Nat.le_ceil _
        have h2 : (↑(Nat.ceil (s / (2 * η))) : ℝ) + 1 = (m : ℝ) := by
          simp only [m, Nat.cast_add, Nat.cast_one]
        linarith
      have hs_nn : (0 : ℝ) ≤ s := by positivity
      have hs_div_lt : s / (2 * ↑m) < η := by
        rcases eq_or_lt_of_le hs_nn with hs0 | hs_pos
        · rw [← hs0]; simp only [zero_div]; exact hη_pos
        · have h2m_pos : (0 : ℝ) < 2 * ↑m := by positivity
          rw [div_lt_iff₀ h2m_pos]
          have h2η_pos : (0 : ℝ) < 2 * η := by positivity
          have := (div_lt_iff₀ h2η_pos).mp hm_gt
          linarith
      linarith
    · -- Degree bound: gs_degree_bound deg n m / (deg - 1) < |F|
      have hn_pos : (0 : ℝ) < Fintype.card ι := by
        exact_mod_cast (show 0 < Fintype.card ι from Fintype.card_pos)
      have hdeg_pos : (0 : ℝ) < deg := by exact_mod_cast (show 0 < deg by omega)
      have hs_lt_one : s < 1 := by linarith [NNReal.coe_pos.mpr hδ_pos, hδ_real]
      have hs_eq : s = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
        simp only [s, hs_def, ReedSolomon.sqrtRate]
        rw [Real.coe_sqrt]; congr 1
        haveI : NeZero deg := ⟨by omega⟩
        have hdim := ReedSolomon.dim_eq_deg_of_le' (α := domain) (n := deg)
          (by omega : deg ≤ Fintype.card ι)
        rw [LinearCode.rate, hdim]; simp [LinearCode.length]
      have hs_pos : 0 < s := by
        rw [hs_eq]; exact Real.sqrt_pos_of_pos (div_pos hdeg_pos hn_pos)
      have hs_sq : s ^ 2 = (deg : ℝ) / Fintype.card ι :=
        hs_eq ▸ Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have hdeg1 : 0 < deg - 1 := by omega
      suffices h_real : (gs_degree_bound deg (Fintype.card ι) m : ℝ) /
          (↑(deg - 1 : ℕ) : ℝ) < (Fintype.card F : ℝ) by
        have hdeg1_cast : (0 : ℝ) < ↑(deg - 1 : ℕ) := by exact_mod_cast hdeg1
        have hmul := (div_lt_iff₀ hdeg1_cast).mp h_real
        exact Nat.div_lt_of_lt_mul (by
          have : (gs_degree_bound deg (Fintype.card ι) m : ℝ) <
            ↑(deg - 1 : ℕ) * ↑(Fintype.card F) := by linarith
          exact_mod_cast this)
      -- floor ≤ real expression
      have hfloor_le : (gs_degree_bound deg (Fintype.card ι) m : ℝ) ≤
          (↑m + 1/2) * s * (Fintype.card ι : ℝ) := by
        unfold gs_degree_bound; dsimp only
        have hnn : (0 : ℝ) ≤ (↑m + 1 / 2) * √↑(↑deg / ↑(Fintype.card ι) : ℚ) *
          ↑(Fintype.card ι) := by positivity
        have hcast : (↑(↑deg / ↑(Fintype.card ι) : ℚ) : ℝ) =
            (deg : ℝ) / Fintype.card ι := by push_cast; ring
        calc (↑⌊(↑m + 1 / 2) * √↑(↑deg / ↑(Fintype.card ι) : ℚ) *
              ↑(Fintype.card ι)⌋₊ : ℝ)
            ≤ (↑m + 1/2) * √↑(↑deg / ↑(Fintype.card ι) : ℚ) * ↑(Fintype.card ι) :=
              Nat.floor_le hnn
          _ = (↑m + 1/2) * s * (Fintype.card ι : ℝ) := by rw [hcast, ← hs_eq]
      -- Bound using μ = min(η, s/20)
      have hdeg1_cast_eq : (↑(deg - 1 : ℕ) : ℝ) = (deg : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ deg), Nat.cast_one]
      have hdeg1_ge : (↑(deg - 1 : ℕ) : ℝ) ≥ (deg : ℝ) / 2 := by
        rw [hdeg1_cast_eq]; linarith [show (2 : ℝ) ≤ deg from by exact_mod_cast hdeg]
      set μ : ℝ := min η (s / 20) with hμ_def
      have hμ_pos : 0 < μ := lt_min hη_pos (by positivity)
      have hμ_le_η : μ ≤ η := min_le_left _ _
      have hμ_le_s20 : μ ≤ s / 20 := min_le_right _ _
      have hμ_lt_one20 : μ < 1 / 20 := lt_of_le_of_lt hμ_le_s20 (by linarith)
      have hm_bound : (m : ℝ) + 1/2 ≤ s / (2 * η) + 5/2 := by
        have hm_eq : (m : ℝ) = ↑(Nat.ceil (s / (2 * η))) + 1 := by
          simp only [m, Nat.cast_add, Nat.cast_one]
        have hceil_le : (↑(Nat.ceil (s / (2 * η))) : ℝ) ≤ s / (2 * η) + 1 :=
          le_of_lt (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ s / (2 * η)))
        linarith
      have h_le_54μ : (↑m + 1/2) * s * (Fintype.card ι : ℝ) /
          (↑(deg - 1 : ℕ) : ℝ) ≤ 5 / (4 * μ) :=
        gs_degree_bound_le_inv_mu hs_pos hη_pos hs_sq hn_pos hdeg
          hm_bound μ hμ_pos hμ_le_η hμ_le_s20
      -- 5/(4μ) < |F| via errorBound < 1
      have h_160 : 160 * μ ^ 6 < (deg : ℝ) ^ 2 := by
        have hμ6 : μ ^ 6 < (1/20 : ℝ) ^ 6 :=
          pow_lt_pow_left₀ hμ_lt_one20 hμ_pos.le (by omega)
        have h4 : (4 : ℝ) ≤ (deg : ℝ) ^ 2 := by
          nlinarith [show (2 : ℝ) ≤ deg from by exact_mod_cast hdeg]
        nlinarith
      have h_54_lt_deg2 : 5 / (4 * μ) < (deg : ℝ) ^ 2 / (128 * μ ^ 7) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h_160]
      -- Extract |F| bound from hε
      have h_field : (deg : ℝ) ^ 2 / (128 * μ ^ 7) < Fintype.card F := by
        -- δ > 0 and δ < 1 - sqrtRate, so δ is in UD or Johnson regime of errorBound
        simp only [ProximityGap.errorBound, Set.mem_Icc, Set.mem_Ioo] at hε
        split_ifs at hε with h_ud h_j
        · -- UD regime: contradicts Johnson hypothesis hJ
          exact absurd hJ (not_lt.mpr h_ud.2)
        · -- Johnson regime: deg²/((2·min(1-√ρ-δ, √ρ/20))⁷·|F|) < 1
          set rate_nn : ℝ≥0 := ↑(LinearCode.rate (ReedSolomon.code domain deg))
          set sqr_nn := NNReal.sqrt rate_nn
          have hsqr_s : (↑sqr_nn : ℝ) = s := by
            simp [sqr_nn, rate_nn, ReedSolomon.sqrtRate, hs_def]
          have hδ_le : δ ≤ 1 - sqr_nn := le_of_lt (by
            simpa [sqr_nn, rate_nn, ReedSolomon.sqrtRate] using hδ)
          have hsqr_le1 : sqr_nn ≤ 1 := by
            simpa [sqr_nn, rate_nn, ReedSolomon.sqrtRate] using hsqrt_le
          have hmin_eq : (↑(min (1 - sqr_nn - δ) (sqr_nn / 20)) : ℝ) = μ := by
            rw [NNReal.coe_min, NNReal.coe_sub hδ_le, NNReal.coe_sub hsqr_le1,
              NNReal.coe_one, NNReal.coe_div, hsqr_s]
            norm_num [hμ_def, hη_def]
          have hε_real : (↑(↑deg ^ 2 : ℝ≥0) : ℝ) /
              ((2 * (↑(min (1 - sqr_nn - δ) (sqr_nn / 20)) : ℝ)) ^ 7 *
                ↑(Fintype.card F)) < 1 := by exact_mod_cast hε
          rw [hmin_eq] at hε_real
          have hd : (0 : ℝ) < (2 * μ) ^ 7 * ↑(Fintype.card F) := by positivity
          have := (div_lt_one hd).mp hε_real
          rw [show (2 * μ) ^ 7 = 128 * μ ^ 7 from by ring] at this
          have hcast : (↑(↑deg ^ 2 : ℝ≥0) : ℝ) = (↑deg : ℝ) ^ 2 := by push_cast; ring
          rw [hcast] at this
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < 128 * μ ^ 7)]
          linarith
        · -- Otherwise: impossible since δ > 0 and δ < 1 - sqrtRate
          exfalso
          have h1 : ¬(δ ≤ (1 - (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ≥0)) / 2) :=
            fun hle => h_ud (Set.mem_Icc.mpr ⟨zero_le _, hle⟩)
          have h2 : (1 - (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ≥0)) / 2 < δ :=
            not_le.mp h1
          have h3 : δ < 1 - NNReal.sqrt ↑(LinearCode.rate (ReedSolomon.code domain deg)) := by
            simpa [ReedSolomon.sqrtRate] using hδ
          exact h_j (Set.mem_Ioo.mpr ⟨h2, h3⟩)
      calc (gs_degree_bound deg (Fintype.card ι) m : ℝ) / ↑(deg - 1 : ℕ)
          ≤ (↑m + 1/2) * s * ↑(Fintype.card ι) / ↑(deg - 1 : ℕ) :=
            div_le_div_of_nonneg_right hfloor_le (by positivity)
        _ ≤ 5 / (4 * μ) := h_le_54μ
        _ < (deg : ℝ) ^ 2 / (128 * μ ^ 7) := h_54_lt_deg2
        _ < Fintype.card F := h_field
  · -- deg ≤ 1: degree bound trivial (div by 0 = 0), Johnson bound via m selection
    have h_deg_le : deg ≤ 1 := by omega
    -- Degree bound is always trivial: deg - 1 = 0 in ℕ, so Nat.div _ 0 = 0 < |F|
    have h_deg_bound : ∀ m,
        gs_degree_bound deg (Fintype.card ι) m / (deg - 1) < Fintype.card F := by
      intro m
      have h0 : deg - 1 = 0 := by omega
      simp [h0]
    -- For deg = 0: gs_johnson 0 n m = 1 (√(0/n) = 0), and δ < 1 trivially.
    -- For deg = 1: use m = ⌈s/(2η)⌉ + 1 with dim_eq_deg_of_le'.
    rcases h_deg_le.eq_or_lt with rfl | h1
    · -- deg = 1
      set m := Nat.ceil (s / (2 * η)) + 1
      refine ⟨m, by omega, ?_, h_deg_bound m⟩
      have hn_pos : (0 : ℝ) < Fintype.card ι := by positivity
      have hs_eq : s = Real.sqrt ((1 : ℝ) / Fintype.card ι) := by
        simp only [s, hs_def, ReedSolomon.sqrtRate]; rw [Real.coe_sqrt]; congr 1
        haveI : NeZero (1 : ℕ) := ⟨by omega⟩
        have hdim := ReedSolomon.dim_eq_deg_of_le' (α := domain) (n := 1)
          (by omega : 1 ≤ Fintype.card ι)
        rw [LinearCode.rate, hdim]; simp [LinearCode.length]
      have hgs_eq : gs_johnson 1 (Fintype.card ι) m = 1 - s - s / (2 * m) := by
        simp only [gs_johnson, Nat.cast_one, one_div, Rat.cast_inv, Rat.cast_natCast,
          Real.sqrt_inv]
        congr 1 <;> [congr 1; congr 2] <;>
          rw [hs_eq, Real.sqrt_div (by positivity : (0:ℝ) ≤ 1), Real.sqrt_one, one_div]
      rw [hgs_eq]
      have hm_gt : s / (2 * η) < m := by
        have h1 : s / (2 * η) ≤ ↑(Nat.ceil (s / (2 * η))) := Nat.le_ceil _
        linarith [show (↑(Nat.ceil (s / (2 * η))) : ℝ) + 1 = (m : ℝ) from by
          simp only [m, Nat.cast_add, Nat.cast_one]]
      have hs_nn : (0 : ℝ) ≤ s := by positivity
      have hs_div_lt : s / (2 * ↑m) < η := by
        rcases eq_or_lt_of_le hs_nn with hs0 | hs_pos
        · rw [← hs0]; simp only [zero_div]; exact hη_pos
        · have h2m_pos : (0 : ℝ) < 2 * ↑m := by positivity
          rw [div_lt_iff₀ h2m_pos]
          have h2η_pos : (0 : ℝ) < 2 * η := by positivity
          have := (div_lt_iff₀ h2η_pos).mp hm_gt
          linarith
      linarith
    · -- deg = 0: gs_johnson 0 n m = 1 trivially > δ
      have hdeg0 : deg = 0 := by omega
      subst hdeg0
      refine ⟨1, le_refl 1, ?_, h_deg_bound 1⟩
      -- gs_johnson 0 n 1 = 1 - √(0/n) - √(0/n)/2 = 1
      show (δ : ℝ) < gs_johnson 0 (Fintype.card ι) 1
      have hgs0 : gs_johnson 0 (Fintype.card ι) 1 = 1 := by
        simp only [gs_johnson, CharP.cast_eq_zero, zero_div, Rat.cast_zero, Real.sqrt_zero,
          sub_zero, Nat.cast_one, mul_one]
      rw [hgs0]
      linarith [hδ_real, show (0 : ℝ) ≤ s from by positivity]

omit [DecidableEq ι] in
theorem rs_listDecoding_card_lt_field {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ) (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (hε : errorBound δ deg domain < 1)
    (w : ι → F)
    (closeWords : Finset (ι → F))
    (hclose : ∀ v ∈ closeWords, v ∈ ReedSolomon.code domain deg ∧ δᵣ(w, v) ≤ δ) :
    closeWords.card < Fintype.card F := by
  classical
  -- Each codeword v is in (degreeLT F deg).map (evalOnPoints domain),
  -- so ∃ P ∈ degreeLT, evalOnPoints domain P = v.
  -- Choose a polynomial witness for each codeword.
  let choosePoly : (v : ι → F) → v ∈ closeWords → Polynomial F :=
    fun v hv => ((Submodule.mem_map).mp ((hclose v hv).1)).choose
  have heval : ∀ (v : ι → F) (hv : v ∈ closeWords),
      ReedSolomon.evalOnPoints domain (choosePoly v hv) = v :=
    fun v hv => ((Submodule.mem_map).mp ((hclose v hv).1)).choose_spec.2
  -- Build the image Finset of polynomials.
  let polys : Finset (Polynomial F) :=
    closeWords.attach.image (fun ⟨v, hv⟩ => choosePoly v hv)
  -- Injectivity: if choosePoly v₁ = choosePoly v₂, then
  -- v₁ = evalOnPoints(choosePoly v₁) = evalOnPoints(choosePoly v₂) = v₂.
  have hinj : ∀ (a₁ a₂ : closeWords),
      choosePoly a₁.1 a₁.2 = choosePoly a₂.1 a₂.2 → a₁ = a₂ := by
    intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
    apply Subtype.ext; change v₁ = v₂
    calc v₁ = ReedSolomon.evalOnPoints domain (choosePoly v₁ hv₁) := (heval v₁ hv₁).symm
      _ = ReedSolomon.evalOnPoints domain (choosePoly v₂ hv₂) := by rw [h]
      _ = v₂ := heval v₂ hv₂
  have hcard_eq : polys.card = closeWords.card := by
    simp only [polys]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  -- Case split: deg ≤ 1 is trivial (code too small), deg ≥ 2 uses GS.
  by_cases hdeg : 1 < deg
  case neg =>
    -- deg ≤ 1: code ⊆ (degreeLT F deg).map evalOnPoints, dim ≤ deg ≤ 1.
    -- closeWords.card ≤ polys.card, and polys injects into degreeLT F deg.
    -- degreeLT F 0 = ⊥, degreeLT F 1 has dim 1, so |code| ≤ |F|^1 = |F|.
    -- But we need strict <. For deg = 0, code = {0}, card ≤ 1 < |F|.
    -- For deg = 1, polys ⊆ degreeLT F 1 = constants, |polys| ≤ |F|.
    -- We use: polys.card = closeWords.card, and polys ⊆ F (as constant polys).
    -- Actually: closeWords.card = polys.card ≤ (degreeLT F deg).card.
    -- For deg = 0: degreeLT F 0 = ⊥, so code = {0}, closeWords ⊆ {0}.
    push Not at hdeg
    interval_cases deg
    · -- deg = 0: code α 0 = ⊥, so closeWords ⊆ {0}, card ≤ 1 < |F|.
      have hcode_triv : ∀ v ∈ closeWords, v = 0 := fun v hv => by
        simpa [ReedSolomon.code_zero] using (hclose v hv).1
      have : closeWords.card ≤ 1 :=
        Finset.card_le_one_iff.mpr (fun hx hy => (hcode_triv _ hx).trans (hcode_triv _ hy).symm)
      linarith [Fintype.one_lt_card_iff_nontrivial.mpr (Field.toNontrivial : Nontrivial F)]
    · -- deg = 1: each poly has degree < 1, so is constant: p = C(p.coeff 0).
      -- Inject closeWords into F via coeff 0. Strict < follows from injectivity.
      have hinj_F : ∀ (v₁ : ι → F) (hv₁ : v₁ ∈ closeWords)
          (v₂ : ι → F) (hv₂ : v₂ ∈ closeWords),
          (choosePoly v₁ hv₁).coeff 0 = (choosePoly v₂ hv₂).coeff 0 → v₁ = v₂ := by
        intro v₁ hv₁ v₂ hv₂ hcoeff
        have h1 := ((Submodule.mem_map).mp ((hclose v₁ hv₁).1)).choose_spec.1
        have h2 := ((Submodule.mem_map).mp ((hclose v₂ hv₂).1)).choose_spec.1
        have hp1 : choosePoly v₁ hv₁ = Polynomial.C ((choosePoly v₁ hv₁).coeff 0) := by
          apply Polynomial.eq_C_of_degree_le_zero
          rw [Polynomial.mem_degreeLT] at h1
          exact Order.lt_succ_iff.mp (by exact_mod_cast h1)
        have hp2 : choosePoly v₂ hv₂ = Polynomial.C ((choosePoly v₂ hv₂).coeff 0) := by
          apply Polynomial.eq_C_of_degree_le_zero
          rw [Polynomial.mem_degreeLT] at h2
          exact Order.lt_succ_iff.mp (by exact_mod_cast h2)
        have : choosePoly v₁ hv₁ = choosePoly v₂ hv₂ := by rw [hp1, hp2, hcoeff]
        calc v₁ = evalOnPoints domain (choosePoly v₁ hv₁) := (heval v₁ hv₁).symm
          _ = evalOnPoints domain (choosePoly v₂ hv₂) := by rw [this]
          _ = v₂ := heval v₂ hv₂
      -- Each close codeword v is constant: v = fun i => (choosePoly v hv).coeff 0.
      -- Show each close constant c must appear in range(w) (otherwise dist = 1 > δ).
      have hv_const : ∀ (v : ι → F) (hv : v ∈ closeWords) (i : ι),
          v i = (choosePoly v hv).coeff 0 := by
        intro v hv i
        have hmem := ((Submodule.mem_map).mp ((hclose v hv).1)).choose_spec.1
        have hp : choosePoly v hv = Polynomial.C ((choosePoly v hv).coeff 0) := by
          apply Polynomial.eq_C_of_degree_le_zero
          rw [Polynomial.mem_degreeLT] at hmem
          exact Order.lt_succ_iff.mp (by exact_mod_cast hmem)
        have h := congr_fun (heval v hv) i
        simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at h
        rw [hp, Polynomial.eval_C] at h
        exact h.symm
      -- closeWords.card ≤ |range(w)|: inject closeWords → range(w) via coeff 0
      -- Every close constant c must be in range(w)
      have hsqrt_pos : (0 : ℝ≥0) < ReedSolomon.sqrtRate 1 domain := by
        simp only [ReedSolomon.sqrtRate]
        exact NNReal.sqrt_pos.mpr
          (by exact_mod_cast DivergenceOfSets.reedSolomon_rate_pos Nat.one_pos)
      have hc_in_range : ∀ (v : ι → F) (hv : v ∈ closeWords),
          (choosePoly v hv).coeff 0 ∈ Finset.image w Finset.univ := by
        intro v hv
        by_contra hc
        simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hc
        have hdist_all : ∀ i, w i ≠ v i := fun i => by rw [hv_const v hv i]; exact hc i
        have hdist_eq : hammingDist w v = Fintype.card ι := by
          simp [hammingDist, Finset.filter_true_of_mem (fun i _ => hdist_all i)]
        have hrel : relHammingDist w v = 1 := by
          simp only [relHammingDist, hdist_eq]
          exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        have hle : (1 : ℝ≥0) ≤ δ := by
          have := (hclose v hv).2; rw [hrel] at this; exact_mod_cast this
        exact absurd (lt_of_lt_of_le hδ tsub_le_self) (not_lt.mpr hle)
      -- closeWords.card ≤ |image w univ| ≤ card ι
      have hcard_le_range : closeWords.card ≤ (Finset.image w Finset.univ).card := by
        let img := closeWords.attach.image (fun ⟨v, hv⟩ => (choosePoly v hv).coeff 0)
        have himg_card : img.card = closeWords.card := by
          rw [Finset.card_image_of_injective]
          · exact Finset.card_attach
          · intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ h
            exact Subtype.ext (hinj_F v₁ hv₁ v₂ hv₂ h)
        have himg_sub : img ⊆ Finset.image w Finset.univ := by
          intro c hc
          rw [Finset.mem_image] at hc
          obtain ⟨⟨v, hv⟩, _, rfl⟩ := hc
          exact hc_in_range v hv
        rw [← himg_card]
        exact Finset.card_le_card himg_sub
      have hrange_le : (Finset.image w Finset.univ).card ≤ Fintype.card ι :=
        (Finset.card_image_le).trans (by simp)
      -- card ι ≤ card F (from domain injective)
      have hn_le : Fintype.card ι ≤ Fintype.card F :=
        Fintype.card_le_of_injective domain domain.injective
      -- If card ι < card F, done
      by_cases hn_eq : Fintype.card ι = Fintype.card F
      · -- card ι = card F. If closeWords nonempty, derive contradiction.
        -- w maps ι to F. range(w) ⊆ F with |range| ≤ |ι| = |F|.
        -- Each close codeword is const_c with c ∈ range(w).
        -- Since each const_c is constant, agreement with w at position i iff w(i) = c.
        -- Sum over all c in range of |agree_c| = |ι| = n.
        -- If closeWords is nonempty, pick v ∈ closeWords. v = const_c.
        -- δᵣ(w, v) ≤ δ ≤ 1 - sqrtRate.
        -- For deg = 1: sqrtRate = √(1/n). So δ ≤ 1 - 1/√n.
        -- hammingDist(w, v) = n - |{i : w i = c}|
        -- |{i : w i = c}| ≤ n, and we need to show δᵣ gives contradiction.
        -- Since |range(w)| ≤ n = |F|, and each c in range has |agree_c| ≥ 1,
        -- if |range(w)| = |F| = n, each agree = 1, so hammingDist = n-1.
        -- δᵣ = (n-1)/n. Need (n-1)/n > 1 - 1/√n. Equiv to 1/√n > 1/n. True for n ≥ 2.
        -- If |range(w)| < |F| = n, some c ∉ range so closeWords doesn't map to it,
        -- but range(w).card < n = |F| and closeWords.card ≤ range.card < |F|. Done.
        by_cases hrange_full : (Finset.image w Finset.univ).card = Fintype.card F
        · -- range(w) = F, so |range| = n = |F|.
          -- Every position gives a distinct value, so w is injective.
          -- Then each agreement set has size ≤ n / |F| = 1.
          -- Pick any v ∈ closeWords (if empty, 0 < |F| is trivial).
          by_cases hempty : closeWords = ∅
          · simp [hempty]
          · -- closeWords nonempty, range(w) = F, n = |F|. Derive contradiction.
            -- w is injective: card(image w univ) = card(univ) implies InjOn
            have hw_inj : Function.Injective w := by
              rw [← Set.injOn_univ]
              have h : (Finset.image w (Finset.univ : Finset ι)).card =
                  (Finset.univ : Finset ι).card := by
                simp [hrange_full, hn_eq]
              rwa [← Finset.coe_univ, ← Finset.card_image_iff]
            exfalso
            obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
            -- v is constant, c ∈ range(w). w injective gives exactly 1 agreement.
            have hc_range := hc_in_range v hv
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc_range
            obtain ⟨i₀, hi₀⟩ := hc_range
            -- All j ≠ i₀ disagree: w j ≠ v j (v is constant (choosePoly v hv).coeff 0)
            have hdisagree : ∀ j, j ≠ i₀ → w j ≠ v j := by
              intro j hne
              rw [hv_const v hv j]
              intro heq; exact hne (hw_inj (heq.trans hi₀.symm))
            -- hammingDist ≥ n - 1
            have hdist_ge : hammingDist w v ≥ Fintype.card ι - 1 := by
              unfold hammingDist
              calc (Finset.univ.filter (fun i => w i ≠ v i)).card
                  ≥ ((Finset.univ).erase i₀).card := by
                    apply Finset.card_le_card; intro j hj
                    simp only [Finset.mem_erase, Finset.mem_univ] at hj
                    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdisagree j hj.1⟩
                _ = Fintype.card ι - 1 := by
                    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
            -- hammingDist = n means all disagree → δᵣ = 1 → same contradiction as hc_in_range
            -- hammingDist = n - 1 means δᵣ = (n-1)/n
            -- But actually: just need hammingDist ≥ n - 1 and n ≥ 2.
            -- δᵣ = hammingDist/n ≥ (n-1)/n
            -- Need (n-1)/n > 1 - sqrtRate (in ℝ≥0).
            -- sqrtRate = √(rate), rate = dim/n. For deg = 1: dim ≥ 1, rate ≥ 1/n.
            -- sqrtRate ≥ 1/√n. And (n-1)/n = 1 - 1/n.
            -- 1 - 1/n > 1 - 1/√n ⟺ 1/√n > 1/n ⟺ n > √n ⟺ n ≥ 2. ✓
            -- Cast to ℝ and derive contradiction.
            -- hammingDist = n - 1 (w injective, exactly one agreement at i₀)
            have hi₀_agree : w i₀ = v i₀ := by rw [hv_const v hv i₀]; exact hi₀
            have hdist_lt_n : hammingDist w v < Fintype.card ι := by
              unfold hammingDist
              calc (Finset.univ.filter (fun i => w i ≠ v i)).card
                  < Finset.univ.card := Finset.card_lt_card
                    (Finset.filter_ssubset.mpr ⟨i₀, Finset.mem_univ _, by simp [hi₀_agree]⟩)
                _ = Fintype.card ι := Finset.card_univ
            have hdist_eq : hammingDist w v = Fintype.card ι - 1 :=
              le_antisymm (by omega) hdist_ge
            -- Chain in ℝ: (n-1)/n ≤ δᵣ ≤ δ, δ + sqrtRate ≤ 1 ⟹ sqrtRate ≤ 1/n.
            -- But √(rate) > rate ≥ 1/n ⟹ sqrtRate > 1/n. Contradiction.
            have hv_dist' : (δᵣ(w, v) : ℝ≥0) ≤ δ := (hclose v hv).2
            have hsqrt_le_one : ReedSolomon.sqrtRate 1 domain ≤ 1 := by
              simp only [ReedSolomon.sqrtRate]
              exact NNReal.sqrt_le_one.mpr (by exact_mod_cast
                @DivergenceOfSets.reedSolomon_rate_le_one ι _ _ F _ _ domain)
            have h_add_le : δ + ReedSolomon.sqrtRate 1 domain ≤ 1 :=
              (le_tsub_iff_right hsqrt_le_one).mp (le_of_lt hδ)
            have h_add_real : (δ : ℝ) + (ReedSolomon.sqrtRate 1 domain : ℝ) ≤ 1 := by
              exact_mod_cast h_add_le
            have hrel_le_delta : (δᵣ(w, v) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hv_dist'
            have hn_pos : (0 : ℝ) < Fintype.card ι := by positivity
            have hrel_val : (δᵣ(w, v) : ℝ) = (Fintype.card ι - 1 : ℝ) / Fintype.card ι := by
              unfold relHammingDist; rw [hdist_eq]
              have hn_ne : (Fintype.card ι : ℚ≥0) ≠ 0 :=
                Nat.cast_ne_zero.mpr Fintype.card_ne_zero
              rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
              congr 1
              rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
            have hsqrt_le_inv : (ReedSolomon.sqrtRate 1 domain : ℝ) ≤
                1 / Fintype.card ι := by
              have h : (Fintype.card ι - 1 : ℝ) / Fintype.card ι =
                  1 - 1 / Fintype.card ι := by field_simp
              linarith [hrel_val, hrel_le_delta, h_add_real]
            -- sqrtRate > 1/n: √rate > rate ≥ 1/n
            have hrate_pos : (0 : ℝ≥0) <
                (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) := by
              exact_mod_cast @DivergenceOfSets.reedSolomon_rate_pos ι _ _ F _ _ _ Nat.one_pos
            have hrate_lt_one :
                (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) < 1 := by
              have hdim_le := @DivergenceOfSets.reedSolomon_dim_le_deg ι _ F _ 1 domain
              have hdlt : LinearCode.dim (ReedSolomon.code domain 1) <
                  LinearCode.length (ReedSolomon.code domain 1) := by
                simp only [LinearCode.length]; omega
              exact_mod_cast show (LinearCode.rate (ReedSolomon.code domain 1) : ℚ≥0) < 1 from by
                rw [LinearCode.rate]
                exact (div_lt_one (by positivity : (0 : ℚ≥0) < _)).mpr (by exact_mod_cast hdlt)
            have hrate_ge_inv : (1 : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤
                (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) := by
              have hdim_ge : 1 ≤ LinearCode.dim (ReedSolomon.code domain 1) := by
                have hmul := @DivergenceOfSets.reedSolomon_rate_mul_card_eq_dim ι _ _ F _ 1 domain
                have h0 : (0 : ℝ≥0) < (LinearCode.dim (ReedSolomon.code domain 1) : ℝ≥0) :=
                  hmul ▸ mul_pos (by positivity) hrate_pos
                have : 0 < LinearCode.dim (ReedSolomon.code domain 1) := by exact_mod_cast h0
                omega
              have hge : (1 : ℚ≥0) / (Fintype.card ι : ℚ≥0) ≤
                  (LinearCode.rate (ReedSolomon.code domain 1) : ℚ≥0) := by
                rw [LinearCode.rate]; simp only [LinearCode.length]
                exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℚ≥0) < _)).mpr
                  (by exact_mod_cast hdim_ge)
              calc (1 : ℝ≥0) / (Fintype.card ι : ℝ≥0)
                  = ((1 : ℚ≥0) / (Fintype.card ι : ℚ≥0) : ℝ≥0) := by push_cast; ring
                _ ≤ _ := by exact_mod_cast hge
            have h_sqrt_gt : (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) <
                NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) := by
              have h1 : (_ : ℝ≥0) * _ < _ * 1 :=
                mul_lt_mul_of_pos_left hrate_lt_one hrate_pos
              rw [mul_one] at h1
              calc _ = NNReal.sqrt (_ * _) := (NNReal.sqrt_mul_self _).symm
                _ < NNReal.sqrt _ := NNReal.sqrt_lt_sqrt.2 h1
            have hsqrt_gt_inv : 1 / (Fintype.card ι : ℝ) <
                (ReedSolomon.sqrtRate 1 domain : ℝ) := by
              have h1 : ((1 : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ) =
                  1 / (Fintype.card ι : ℝ) := by push_cast; ring
              rw [← h1]
              exact_mod_cast show ((1 : ℝ≥0) / (Fintype.card ι : ℝ≥0)) <
                  ReedSolomon.sqrtRate 1 domain from
                calc (1 : ℝ≥0) / _ ≤ _ := hrate_ge_inv
                  _ < NNReal.sqrt _ := h_sqrt_gt
                  _ = ReedSolomon.sqrtRate 1 domain := by simp [ReedSolomon.sqrtRate]
            linarith
        · -- range(w).card < |F|
          calc closeWords.card ≤ (Finset.image w Finset.univ).card := hcard_le_range
            _ < Fintype.card F := by omega
      · -- card ι < card F
        calc closeWords.card
            ≤ (Finset.image w Finset.univ).card := hcard_le_range
          _ ≤ Fintype.card ι := hrange_le
          _ < Fintype.card F := by omega
  case pos =>
  -- Split on UD vs Johnson regime
  by_cases hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ
  swap
  · -- UD regime: δ ≤ (1-ρ)/2. Unique decoding gives at most 1 close codeword.
    push Not at hJ
    have hcard_le_one : closeWords.card ≤ 1 :=
      Finset.card_le_one_iff.mpr fun {v₁ v₂} hv₁ hv₂ => by
      have hv₁_code := (hclose v₁ hv₁).1
      have hv₂_code := (hclose v₂ hv₂).1
      have hv₁_dist := (hclose v₁ hv₁).2
      have hv₂_dist := (hclose v₂ hv₂).2
      haveI : NeZero deg := ⟨by omega⟩
      have hrelUDR : Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
          (C := (ReedSolomon.code domain deg : Set (ι → F))) =
          ((1 : ℝ≥0) - ↑deg / ↑(Fintype.card ι)) / 2 :=
        ReedSolomon.relativeUniqueDecodingRadius_RS_eq' (by omega)
      have hrate_eq : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) =
          (↑deg : ℝ≥0) / ↑(Fintype.card ι) := by
        have hdim := ReedSolomon.dim_eq_deg_of_le' (α := domain) (n := deg) (by omega)
        simp [LinearCode.rate, hdim, LinearCode.length]
      rw [hrate_eq] at hJ
      rw [← hrelUDR] at hJ
      have h_v₁_le : (hammingDist w v₁ : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤
          Code.relativeUniqueDecodingRadius
            (C := (ReedSolomon.code domain deg : Set (ι → F))) := by
        calc (hammingDist w v₁ : ℝ≥0) / (Fintype.card ι : ℝ≥0)
            = ((δᵣ(w, v₁) : ℚ≥0) : ℝ≥0) := by
              simp [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
          _ ≤ (δ : ℝ≥0) := by exact_mod_cast hv₁_dist
          _ ≤ _ := hJ
      have h_v₂_le : (hammingDist w v₂ : ℝ≥0) / (Fintype.card ι : ℝ≥0) ≤
          Code.relativeUniqueDecodingRadius
            (C := (ReedSolomon.code domain deg : Set (ι → F))) := by
        calc (hammingDist w v₂ : ℝ≥0) / (Fintype.card ι : ℝ≥0)
            = ((δᵣ(w, v₂) : ℚ≥0) : ℝ≥0) := by
              simp [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
          _ ≤ (δ : ℝ≥0) := by exact_mod_cast hv₂_dist
          _ ≤ _ := hJ
      have hudr₁ : hammingDist w v₁ ≤ Code.uniqueDecodingRadius
          (C := (ReedSolomon.code domain deg : Set (ι → F))) :=
        (Code.dist_le_UDR_iff_relDist_le_relUDR _ _).2 h_v₁_le
      have hudr₂ : hammingDist w v₂ ≤ Code.uniqueDecodingRadius
          (C := (ReedSolomon.code domain deg : Set (ι → F))) :=
        (Code.dist_le_UDR_iff_relDist_le_relUDR _ _).2 h_v₂_le
      exact eq_of_le_uniqueDecodingRadius _ w hv₁_code hv₂_code hudr₁ hudr₂
    linarith [Fintype.one_lt_card_iff_nontrivial.mpr (Field.toNontrivial : Nontrivial F)]
  -- Johnson regime: use Guruswami-Sudan with parameterized multiplicity m.
  suffices ∃ (Q : Polynomial (Polynomial F)), Q ≠ 0 ∧ Q.natDegree < Fintype.card F ∧
      ∀ P ∈ polys, (Polynomial.X - Polynomial.C P) ∣ Q by
    obtain ⟨Q, hQ_ne, hQ_deg, hQ_div⟩ := this
    rw [← hcard_eq]
    exact card_divisors_lt_field hQ_ne hQ_deg hQ_div
  have hn_le : Fintype.card ι ≤ Fintype.card F :=
    Fintype.card_le_of_injective domain domain.injective
  let ωs : Fin (Fintype.card ι) ↪ F := (Fintype.equivFin ι).symm.toEmbedding.trans domain
  let f : Fin (Fintype.card ι) → F := w ∘ (Fintype.equivFin ι).symm
  have hn_ne : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  -- Choose multiplicity m satisfying both GS conditions:
  -- (A) gs_johnson(deg,n,m) > δ (hence > δᵣ for all close codewords)
  -- (B) gs_degree_bound(deg,n,m) / (deg-1) < |F| (degree bound for Q)
  -- Requires strict gap δ < 1-sqrtRate (from rationality of δᵣ).
  -- gs_johnson(k,n,m) = 1-√(k/n)·(1+1/(2m)) → 1-√(k/n) as m→∞.
  obtain ⟨m, hm, hm_johnson, hm_degree⟩ :=
    exists_gs_multiplicity hδ_pos hδ hRS hε hJ
  obtain ⟨Q, hQ⟩ := GuruswamiSudan.gs_existence
    deg (Fintype.card ι) ωs f hdeg hn_ne hm
  refine ⟨Q, hQ.Q_ne_0, ?_, ?_⟩
  · -- Q.natDegree < |F|
    have hb : 0 < deg - 1 := by omega
    have hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (deg - 1) ≤
        gs_degree_bound deg (Fintype.card ι) m := by
      have h := hQ.Q_deg
      rw [Polynomial.Bivariate.weightedDegree_eq_natWeightedDegree] at h
      exact Option.some_le_some.mp h
    exact lt_of_le_of_lt (GuruswamiSudan.natDegree_le_of_natWeightedDegree hb hwd) hm_degree
  · -- ∀ P ∈ polys, (Y - C P) ∣ Q
    intro P hP
    simp only [polys, Finset.mem_image] at hP
    obtain ⟨⟨v, hv⟩, _, rfl⟩ := hP
    have hv_code := (hclose v hv).1
    have hP_deg : (choosePoly v hv) ∈ Polynomial.degreeLT F deg :=
      ((Submodule.mem_map).mp hv_code).choose_spec.1
    have hP_in_code : (fun i => (choosePoly v hv).eval (ωs i)) ∈
        ReedSolomon.code ωs deg :=
      Submodule.mem_map.mpr ⟨choosePoly v hv, hP_deg, rfl⟩
    let p : ReedSolomon.code ωs deg :=
      ⟨fun i => (choosePoly v hv).eval (ωs i), hP_in_code⟩
    have h_poly_eq : ReedSolomon.codewordToPoly p = choosePoly v hv := by
      symm; rw [ReedSolomon.codewordToPoly]
      exact Lagrange.eq_interpolate (ωs.injective.injOn) (by
        rw [Polynomial.mem_degreeLT] at hP_deg
        calc (choosePoly v hv).degree < deg := hP_deg
          _ ≤ Fintype.card (Fin (Fintype.card ι)) := by simp; omega)
    rw [← h_poly_eq]
    apply GuruswamiSudan.gs_divisibility hRS hm p hQ
    -- Bridge: hammingDist f (codewordToPoly p ∘ ωs) / n ≤ δᵣ(w,v) ≤ δ < gs_johnson
    have hv_dist : (δᵣ(w, v) : ℝ≥0) ≤ δ := (hclose v hv).2
    have h_dist_eq : hammingDist f (fun i =>
        (ReedSolomon.codewordToPoly p).eval (ωs i)) = hammingDist w v := by
      have hvi : ∀ i : Fin (Fintype.card ι),
          (choosePoly v hv).eval (ωs i) = v ((Fintype.equivFin ι).symm i) := by
        intro i
        have h := congr_fun (heval v hv) ((Fintype.equivFin ι).symm i)
        simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at h
        rw [← h]; congr 1
      simp only [hammingDist, h_poly_eq, f]; simp_rw [hvi]
      exact Finset.card_bij (fun i _ => (Fintype.equivFin ι).symm i)
        (fun i hi => by simpa [Finset.mem_filter] using hi)
        (fun _ _ _ _ h => (Fintype.equivFin ι).symm.injective h)
        (fun j hj => ⟨(Fintype.equivFin ι) j,
          by simp only [comp_apply, ne_eq, mem_filter, mem_univ, Equiv.symm_apply_apply,
            true_and] at hj ⊢; exact hj,
          (Fintype.equivFin ι).symm_apply_apply j⟩)
    rw [show (Fintype.card ι : ℝ) = ((Fintype.card ι : ℚ≥0) : ℝ) from by push_cast; ring]
    calc (hammingDist f (fun i => (ReedSolomon.codewordToPoly p).eval (ωs i)) : ℝ) /
          ((Fintype.card ι : ℚ≥0) : ℝ)
        = (hammingDist w v : ℝ) / ((Fintype.card ι : ℚ≥0) : ℝ) := by rw [h_dist_eq]
      _ = ((δᵣ(w, v) : ℚ≥0) : ℝ) := by
          simp [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
      _ ≤ (δ : ℝ) := by exact_mod_cast hv_dist
      _ < gs_johnson deg (Fintype.card ι) m := hm_johnson

/-- Theorem 1.7 (Correlated agreement over affine spaces) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space with origin `u₀` and affine generating set `u₁, ..., uκ`
such that the probability a random point in the affine space is `δ`-close to the Reed-Solomon
code is greater than `ε`. Then the words `u₀, ..., uκ` have correlated agreement.

Note that we have `k + 2` vectors to form the affine space. This an intricacy needed us to be
able to isolate the affine origin from the affine span and to form a generating set of the
correct size. The reason for taking an extra vector is that after isolating the affine origin,
the affine span is formed as the span of the difference of the rest of the vector set. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (_hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (_hε : errorBound δ deg domain < 1) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  intro u hPr
  classical
  -- BCIKS20 §6.3 (p31). Proof structure follows the paper exactly.
  -- Overview:
  -- 1. All elements of U are δ-close to V (Lemma 6.3 + extension to span(U)).
  -- 2. Pick u* ∈ U achieving min distance δ* to V. δ* ≤ δ.
  -- 3. For each x ∈ U, Thm 1.4 on line (u*, x-u*) assigns a codeword for u*.
  --    List-decoding: < |F| possible codewords.
  -- 4. Pigeonhole: |U| = |F|^k elements → < |F| buckets → some bucket = U.
  -- 5. D' = {col : u* = v₀} has size (1-δ*)|ι| ≥ (1-δ)|ι|.
  --    ALL words agree with codewords on D' (bucket = U property).
  --    One D' for all words — no intersection, hence (1-δ) not (1-kδ).
  set V := ReedSolomon.code domain deg with hV_def
  set U := (Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u) : Set (ι → F))
  have hPr_sub : Pr_{let y ← $ᵖ (Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(↑y, (V : Set (ι → F))) ≤ δ] > errorBound δ deg domain := by
    convert hPr using 1
  have h_all_close : ∀ x ∈ U, δᵣ(x, (V : Set (ι → F))) ≤ δ :=
    all_affine_elements_close u (le_of_lt hδ) hPr_sub
  have hu0_mem : u 0 ∈ U := by
    change u 0 ∈ Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u)
    rw [Affine.mem_affineSubspaceFrom_iff]; exact ⟨0, by simp⟩
  -- ═══════════════════════════════════════════════════════════
  -- Step 2: Pick u* ∈ U achieving divergence (max distance to V).
  -- ═══════════════════════════════════════════════════════════
  haveI : Nonempty (V : Set (ι → F)) := ⟨0, V.zero_mem⟩
  haveI : Nonempty U := ⟨⟨u 0, hu0_mem⟩⟩
  obtain ⟨u_star, hu_star_mem, hu_star_div⟩ :=
    DivergenceOfSets.divergence_attains (U := U) (V := (V : Set (ι → F)))
  -- Extract u*'s affine coefficients without destroying u_star via rfl.
  have hu_star_aff : ∃ α_star : Fin k → F,
      u_star = u 0 + ∑ i : Fin k, α_star i • Fin.tail u i :=
    (Affine.mem_affineSubspaceFrom_iff (F := F) (u 0) (Fin.tail u) u_star).mp hu_star_mem
  obtain ⟨α_star, hα_star⟩ := hu_star_aff
  set δ_star : ℝ≥0 :=
    (DivergenceOfSets.divergence U (V : Set (ι → F)) : ℝ≥0) with hδ_star_def
  have hu_star_eq : (δᵣ'(u_star, (V : Set (ι → F))) : ℝ≥0) = δ_star := by
    simp only [δ_star]; exact_mod_cast hu_star_div
  have hδ_star_le : δ_star ≤ δ := by
    rw [← hu_star_eq]
    have h_close := h_all_close u_star hu_star_mem
    rw [relDistFromCode'_eq_relDistFromCode] at h_close
    exact_mod_cast h_close
  have hδ_star_le_sqrt : δ_star ≤ 1 - ReedSolomon.sqrtRate deg domain :=
    le_trans hδ_star_le (le_of_lt hδ)
  -- The affine space with u* as origin equals U (same direction span).
  have hU_star_eq : (Affine.affineSubspaceAtOrigin (F := F) u_star (Fin.tail u) :
      Set (ι → F)) = U := by
    ext x; constructor
    · intro hx
      have hx' := (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) x).mp hx
      obtain ⟨β, rfl⟩ := hx'
      exact (Affine.mem_affineSubspaceFrom_iff (F := F) (u 0) (Fin.tail u) _).mpr
        ⟨fun i => α_star i + β i, by rw [hα_star]; simp [Finset.sum_add_distrib, add_smul]; abel⟩
    · intro hx
      have hx' := (Affine.mem_affineSubspaceFrom_iff (F := F) (u 0) (Fin.tail u) x).mp hx
      obtain ⟨β, rfl⟩ := hx'
      exact (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) _).mpr
        ⟨fun i => β i - α_star i, by rw [hα_star]; simp [Finset.sum_sub_distrib, sub_smul]⟩
  -- Lines through u* in U stay in U.
  have h_line_in_U_star : ∀ x ∈ U, ∀ z : F, u_star + z • (x - u_star) ∈ U := by
    intro x hx z
    rw [← hU_star_eq] at hx ⊢
    obtain ⟨β, rfl⟩ := (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) x).mp hx
    exact (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) _).mpr
      ⟨fun i => z * β i, by
        congr 1; simp only [add_sub_cancel_left, Finset.smul_sum, smul_smul]⟩
  -- For any direction, line through u* has Pr[δ_star-close] = 1.
  have h_line_pr1_star : ∀ (dir : ι → F),
      (∀ z : F, u_star + z • dir ∈ U) →
      Pr_{let z ← $ᵖ F}[δᵣ((finMapTwoWords u_star dir) 0
        + z • (finMapTwoWords u_star dir) 1,
        (V : Set (ι → F))) ≤ δ_star] = 1 := by
    intro dir h_line_in_U
    rw [prob_uniform_eq_card_filter_div_card]
    have : Finset.filter (fun z : F =>
        δᵣ((finMapTwoWords u_star dir) 0
          + z • (finMapTwoWords u_star dir) 1,
          (V : Set (ι → F))) ≤ ↑δ_star) Finset.univ = Finset.univ := by
      ext z; constructor
      · exact fun _ => Finset.mem_univ _
      · intro _
        simp only [finMapTwoWords, Finset.mem_filter, Finset.mem_univ, true_and]
        have hx_mem := h_line_in_U z
        have hx_le_div := DivergenceOfSets.relDistFromCode'_le_divergence
          (U := U) (V := (V : Set (ι → F))) _ hx_mem
        have h_eq := relDistFromCode'_eq_relDistFromCode
          (u_star + z • dir) (V : Set (ι → F))
        rw [h_eq]
        apply ENNReal.coe_le_coe.mpr
        show (δᵣ'(u_star + z • dir, (V : Set (ι → F))) : ℝ≥0) ≤ δ_star
        simp only [hδ_star_def]
        exact_mod_cast hx_le_div
    rw [this, Finset.card_univ]
    exact_mod_cast div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- ═══════════════════════════════════════════════════════════
  -- Step 3: Direction generators through u* stay in U.
  -- ═══════════════════════════════════════════════════════════
  have h_dir_in_U_star : ∀ j : Fin k, ∀ z : F,
      u_star + z • Fin.tail u j ∈ U := by
    intro j z
    rw [← hU_star_eq]
    exact (Affine.mem_affineSubspaceFrom_iff (F := F) u_star (Fin.tail u) _).mpr
      ⟨Pi.single j z, by simp⟩
  -- ═══════════════════════════════════════════════════════════
  -- Step 4: Apply Thm 1.4 with u* and δ_star.
  -- ═══════════════════════════════════════════════════════════
  have hε_star : errorBound δ_star deg domain < 1 :=
    lt_of_le_of_lt (DivergenceOfSets.errorBound_mono hdeg hδ_star_le hδ) _hε
  have hεδ_star_lt_one : (errorBound δ_star deg domain : ENNReal) < 1 := by
    exact_mod_cast hε_star
  have h_pair_ja : ∀ j : Fin k,
      jointAgreement (C := (V : Set (ι → F))) (δ := δ_star)
        (W := finMapTwoWords u_star (Fin.tail u j)) := by
    intro j
    apply RS_correlatedAgreement_affineLines hδ_star_le_sqrt
    rw [h_line_pr1_star _ (h_dir_in_U_star j)]
    exact hεδ_star_lt_one
  choose S_j hS_j v_pair hv_pair using fun j => h_pair_ja j
  -- Step 5: BCIKS20 §6.3 bucketing with u* and δ_star.
  have h_elem_ja : ∀ x ∈ (Affine.affineSubspaceAtOrigin (F := F) u_star (Fin.tail u) :
      Set (ι → F)),
      jointAgreement (C := (V : Set (ι → F))) (δ := δ_star)
        (W := finMapTwoWords u_star (x - u_star)) := by
    intro x hx
    have hx_U := (hU_star_eq ▸ hx : x ∈ U)
    apply RS_correlatedAgreement_affineLines hδ_star_le_sqrt
    rw [h_line_pr1_star _ (fun z => h_line_in_U_star x hx_U z)]
    exact hεδ_star_lt_one
  have hδ_star_strict : δ_star < 1 - ReedSolomon.sqrtRate deg domain :=
    lt_of_le_of_lt hδ_star_le hδ
  have h_bucket := bucket_exists_common_codeword V u_star (Fin.tail u) h_elem_ja h_pair_ja
    (fun w close hclose => by
      by_cases hδs_pos : (0 : ℝ≥0) < δ_star
      · exact rs_listDecoding_card_lt_field hδs_pos hδ_star_strict hRS hε_star w close
          (fun v hv => ⟨(hclose v hv).1, (hclose v hv).2⟩)
      · -- δ_star = 0: only w itself can be at distance 0, so |closeWords| ≤ 1 < |F|
        push Not at hδs_pos
        have hδs_eq : δ_star = 0 := le_antisymm hδs_pos (zero_le _)
        have hclose_eq : ∀ v ∈ close, v = w := by
          intro v hv
          have hd := (hclose v hv).2
          have hd0 : hammingDist w v = 0 := by
            rw [hammingDist_eq_zero]
            by_contra hne
            have hpos : 0 < hammingDist w v := Nat.pos_of_ne_zero (hammingDist_ne_zero.mpr hne)
            have hrel_pos : (0 : ℚ≥0) < δᵣ(w, v) := by
              simp only [relHammingDist]
              exact div_pos (Nat.cast_pos.mpr hpos) (by positivity)
            have hrel_le : (δᵣ(w, v) : ℝ≥0) ≤ 0 := by
              calc (δᵣ(w, v) : ℝ≥0) ≤ δ_star := hd
                _ = 0 := hδs_eq
            exact absurd (show (0 : ℝ≥0) < δᵣ(w, v) from by exact_mod_cast hrel_pos)
              (not_lt.mpr hrel_le)
          exact (hammingDist_eq_zero.mp hd0).symm
        have hcard1 : close.card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          exact (hclose_eq a ha).trans (hclose_eq b hb).symm
        have hF_card : 1 < Fintype.card F :=
          Fintype.one_lt_card_iff_nontrivial.mpr (Field.toNontrivial)
        omega)
    (fun v hv hv_close => by
      -- hδ_exact: δᵣ(u*, v) ≥ δ_star. Since δ_star = δᵣ'(u*, V) = min_{v∈V} δᵣ(u*, v).
      rw [← hu_star_eq]
      change (relDistFromCode' u_star (V : Set (ι → F)) : ℝ≥0) ≤ (relHammingDist u_star v : ℝ≥0)
      exact_mod_cast Finset.min'_le _ _
        (Finset.mem_image.mpr ⟨(⟨v, hv⟩ : (V : Set (ι → F))), Finset.mem_univ _, rfl⟩))
  obtain ⟨v₀, D', hv₀_mem, hD'_card, hD'_ustar, h_dirs⟩ := h_bucket
  choose w_j hw_j_mem hw_j_agree using h_dirs
  -- D' has size ≥ (1-δ_star)|ι| ≥ (1-δ)|ι|.
  have hD'_card_δ : (D'.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := by
    calc (D'.card : ℝ≥0) ≥ (1 - (δ_star : ℝ≥0)) * Fintype.card ι := hD'_card
      _ ≥ (1 - δ) * Fintype.card ι := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact tsub_le_tsub_left hδ_star_le 1
  -- Build codeword for u 0: u 0 ∈ U = u* + span(dirs), so u 0 = u* + ∑ α_j • dirs j.
  -- On D': v₀ c = u* c and w_j c = dirs j c, so (v₀ + ∑ α_j • w_j) c = u 0 c.
  have hu0_in_star : u 0 ∈ (Affine.affineSubspaceAtOrigin (F := F) u_star (Fin.tail u) :
      Set (ι → F)) := hU_star_eq ▸ hu0_mem
  obtain ⟨α_u0, hα_u0⟩ := (Affine.mem_affineSubspaceFrom_iff (F := F) u_star
    (Fin.tail u) (u 0)).mp hu0_in_star
  set v_u0 := v₀ + ∑ j : Fin k, α_u0 j • w_j j with hv_u0_def
  have hv_u0_mem : v_u0 ∈ (V : Set (ι → F)) := by
    apply V.add_mem hv₀_mem
    exact V.sum_mem fun j _ => V.smul_mem _ (hw_j_mem j)
  have hv_u0_agree : D' ⊆ Finset.filter (fun c => v_u0 c = u 0 c) Finset.univ := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_star : v₀ c = u_star c := by
      have := hD'_ustar hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have h_dirs_c : ∀ j, w_j j c = Fin.tail u j c := by
      intro j
      have := hw_j_agree j hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [hv_u0_def, Pi.add_apply, Finset.sum_apply, h_star]
    conv_rhs => rw [hα_u0, Pi.add_apply, Finset.sum_apply]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, h_dirs_c j]
  refine ⟨D', hD'_card_δ, ?_⟩
  refine ⟨fun i => if h : i = 0 then v_u0
    else w_j (i.pred (Fin.pos_iff_ne_zero.mp (Fin.pos_of_ne_zero h))), ?_⟩
  intro i
  by_cases hi : i = 0
  · subst hi; simp only [dite_true]
    exact ⟨hv_u0_mem, hv_u0_agree⟩
  · simp only [hi, dite_false]
    set j := i.pred (Fin.pos_iff_ne_zero.mp (Fin.pos_of_ne_zero hi))
    refine ⟨hw_j_mem j, fun c hc => ?_⟩
    have := hw_j_agree j hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
    rw [show i = Fin.succ j from (Fin.succ_pred i hi).symm]
    exact this

end CoreResults

end ProximityGap

set_option linter.style.longFile 2400
