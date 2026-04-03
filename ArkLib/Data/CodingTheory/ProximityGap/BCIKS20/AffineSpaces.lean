/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
/-! # BCIKS20 Affine Spaces -/


namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
/-- Theorem 1.6 (Correlated agreement over affine spaces) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space with origin `u₀` and affine generting set `u₁, ..., uκ`
such that the probability a random point in the affine space is `δ`-close to the Reed-Solomon
code is at most `ε`. Then the words `u₀, ..., uκ` have correlated agreement.

Note that we have `k+2` vectors to form the affine space. This an intricacy needed us to be
able to isolate the affine origin from the affine span and to form a generating set of the
correct size. The reason for taking an extra vector is that after isolating the affine origin,
the affine span is formed as the span of the difference of the rest of the vector set. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain) :
    δ_ε_correlatedAgreementAffineSpaces (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  sorry

end CoreResults

section BCIKS20ProximityGapSection6

open scoped ReedSolomonCode

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
    (hδ : δ ∈ Set.Ioo 0 (1 - ReedSolomonCode.sqrtRate (k + 1) domain)) :
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
  have hδ_le : δ ≤ 1 - ReedSolomonCode.sqrtRate (k + 1) domain :=
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

end ProximityGap
