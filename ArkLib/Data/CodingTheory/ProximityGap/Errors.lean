/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.TensorGenerator
import ArkLib.Data.Probability.Instances

/-!
# Numeric proximity-gap and correlated-agreement errors

This file defines numeric proximity-gap and correlated-agreement errors and compares them with
`CoreDefinitions.mcaError` specialized to affine lines.

## Main definitions

* `epsPg` — the proximity-gap error.
* `epsCa` — the correlated-agreement error with separate fold and interleaved radii.
* `epsCa'` — the equal-radius specialization of `epsCa`.
* `epsMca` — affine-line notation for the canonical `mcaError`.

The file also relates these values to the correlated-agreement predicates in `Basic.lean`, proves
their elementary order and endpoint properties, and states the unique-decoding and interleaving
comparison theorems used by the grand-challenge API.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E., *WHIR: Reed--Solomon Proximity Testing
  with Super-Fast Verification*][ACFY25]
* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26]
-/

namespace ProximityGap

open NNReal Code CoreDefinitions unitInterval
open scoped ProbabilityTheory BigOperators
open Probability

section McaNotation

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F] [Fintype F]
variable {A : Type} [AddCommMonoid A] [Module F A]

/-- The affine-line mutual-correlated-agreement error at a nonnegative radius. -/
noncomputable abbrev epsMca (C : ModuleCode ι F A) (δ : ℝ≥0) : ENNReal :=
  mcaError (AffineLineGenerator F) C (δ : ℝ)

end McaNotation

section McaStructuralInterleaving

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F] [Fintype F]
variable {A : Type} [AddCommMonoid A] [Module F A]

/-- Affine-line MCA of a code is at most that of any nonempty row-wise interleaving. -/
theorem mcaError_le_moduleInterleavedCode
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (ht : 0 < t) (hδ_le : δ ≤ 1) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ) := by
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  let ε : I → ℝ≥0 := fun γ =>
    ENNReal.toNNReal (mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (γ : ℝ))
  have hInterleaved : IsMCAGenerator (AffineLineGenerator F) ε (C ^⋈ (Fin t)) := by
    intro γ
    dsimp [ε]
    rw [ENNReal.coe_toNNReal
      (mcaError_ne_top (AffineLineGenerator F) (C ^⋈ (Fin t)) (γ : ℝ))]
  have hBase := TensorMCA.isMCAGenerator_of_moduleInterleavedCode
    (ℓ := Fin t) (AffineLineGenerator F) ε C hInterleaved
  let δI : I :=
    ⟨(δ : ℝ), ⟨NNReal.coe_nonneg δ, by exact_mod_cast hδ_le⟩⟩
  simpa [δI, ε, ENNReal.coe_toNNReal
    (mcaError_ne_top (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ))] using hBase δI

end McaStructuralInterleaving

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The largest fraction of an affine line that is close to `C` without the whole line being
close. -/
noncomputable def epsPg (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]

open Classical in
/-- The largest probability that an affine combination is `δ_fld`-close to `C` when its two
components are not jointly `δ_int`-close to `C`. -/
noncomputable def epsCa (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]

/-- The equal-radius specialization `epsCa C δ δ`. -/
noncomputable def epsCa' (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  epsCa (F := F) C δ δ

open Classical in
/-- Correlated-agreement error for degree-`k` polynomial combinations. -/
noncomputable def epsCaCurves
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let r ← $ᵖ F}[δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fld]

open Classical in
/-- Correlated-agreement error for uniform samples from the affine span of a word stack. -/
noncomputable def epsCaAffineSpaces
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(y.1, C) ≤ δ_fld]

/-! ## Monotonicity -/

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsCa` is monotone in its fold radius. -/
theorem epsCa_mono_left
    (C : Set (ι → A)) {δ_fld δ_fld' : ℝ≥0} (δ_int : ℝ≥0) (h : δ_fld ≤ δ_fld') :
    epsCa (F := F) C δ_fld δ_int ≤ epsCa (F := F) C δ_fld' δ_int := by
  classical
  unfold epsCa
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    apply Pr_le_Pr_of_implies
    intro _ hclose
    exact le_trans hclose (by exact_mod_cast h)

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsCa` is antitone in its interleaved radius. -/
theorem epsCa_antitone_right
    (C : Set (ι → A)) (δ_fld : ℝ≥0) {δ_int δ_int' : ℝ≥0} (h : δ_int ≤ δ_int') :
    epsCa (F := F) C δ_fld δ_int' ≤ epsCa (F := F) C δ_fld δ_int := by
  classical
  unfold epsCa
  apply iSup_mono
  intro u
  have hjp_mono : jointProximity (C := C) (u := u) δ_int →
      jointProximity (C := C) (u := u) δ_int' :=
    fun hjp => le_trans hjp (by exact_mod_cast h)
  by_cases hjp' : jointProximity (C := C) (u := u) δ_int'
  · rw [if_pos hjp']
    exact zero_le
  · have hjp : ¬ jointProximity (C := C) (u := u) δ_int := fun h0 => hjp' (hjp_mono h0)
    rw [if_neg hjp', if_neg hjp]

/-! ## Endpoint behavior -/

omit [DecidableEq ι] in
/-- Every word is within relative distance `δ` of a nonempty code once `1 ≤ δ`. -/
lemma relDistFromCode_le_of_one_le {α : Type} [DecidableEq α] {C : Set (ι → α)}
    (hC : C.Nonempty) (w : ι → α) {δ : ℝ≥0} (hδ : 1 ≤ δ) : δᵣ(w, C) ≤ (δ : ENNReal) := by
  have hne : Nonempty C := hC.to_subtype
  rw [relDistFromCode_le_iff_distFromCode_le]
  refine le_trans (distFromCode_le_card_index_of_Nonempty w) ?_
  have hfloor : Fintype.card ι ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := by
    refine Nat.le_floor ?_
    calc ((Fintype.card ι : ℕ) : ℝ≥0) = 1 * (Fintype.card ι : ℝ≥0) := by ring
      _ ≤ δ * (Fintype.card ι : ℝ≥0) := by gcongr
  exact_mod_cast hfloor

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsPg C δ = 0` for `δ ≥ 1`. -/
theorem epsPg_eq_zero_of_one_le {C : Set (ι → A)} (hC : C.Nonempty) {δ : ℝ≥0} (hδ : 1 ≤ δ) :
    epsPg (F := F) C δ = 0 := by
  classical
  refine le_antisymm ?_ zero_le
  unfold epsPg
  refine iSup_le fun u => ?_
  have hguard : ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ (δ : ENNReal) :=
    fun γ => relDistFromCode_le_of_one_le hC _ hδ
  rw [if_pos hguard]

omit [DecidableEq ι] [Fintype A] [AddCommGroup A] in
/-- Every two-word stack is jointly close once the radius is at least one. -/
lemma jointProximity_of_one_le {C : Set (ι → A)} (hC : C.Nonempty)
    (u : WordStack A (Fin 2) ι) {δ : ℝ≥0} (hδ : 1 ≤ δ) :
    jointProximity C (u := u) δ := by
  classical
  obtain ⟨v, hv⟩ := hC
  have hne : (interleavedCodeSet (κ := Fin 2) (C := C)).Nonempty := by
    refine ⟨fun i (_ : Fin 2) => v i, fun k => ?_⟩
    have heq : Matrix.transpose (fun i (_ : Fin 2) => v i) k = v := by
      funext i
      rfl
    rw [heq]
    exact hv
  exact relDistFromCode_le_of_one_le hne _ hδ

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsCa` is zero when its interleaved radius is at least one. -/
theorem epsCa_eq_zero_of_one_le_right {C : Set (ι → A)} (hC : C.Nonempty)
    (δ_fld : ℝ≥0) {δ_int : ℝ≥0} (hδ : 1 ≤ δ_int) :
    epsCa (F := F) C δ_fld δ_int = 0 := by
  classical
  refine le_antisymm ?_ zero_le
  unfold epsCa
  exact iSup_le fun u => by rw [if_pos (jointProximity_of_one_le hC u hδ)]

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsCa'` is zero at every radius at least one. -/
theorem epsCa'_eq_zero_of_one_le {C : Set (ι → A)} (hC : C.Nonempty)
    {δ : ℝ≥0} (hδ : 1 ≤ δ) : epsCa' (F := F) C δ = 0 :=
  epsCa_eq_zero_of_one_le_right hC δ hδ

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- A globally monotone `epsPg` is zero throughout the closed unit interval. -/
theorem epsPg_eq_zero_of_mono {C : Set (ι → A)} (hC : C.Nonempty)
    (hmono : ∀ δ δ' : ℝ≥0, δ ≤ δ' → epsPg (F := F) C δ ≤ epsPg (F := F) C δ')
    {δ : ℝ≥0} (hδ : δ ≤ 1) : epsPg (F := F) C δ = 0 :=
  le_antisymm (le_of_le_of_eq (hmono δ 1 hδ) (epsPg_eq_zero_of_one_le hC le_rfl)) zero_le

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- A globally monotone `epsCa'` is zero throughout the closed unit interval. -/
theorem epsCa'_eq_zero_of_mono {C : Set (ι → A)} (hC : C.Nonempty)
    (hmono : ∀ δ δ' : ℝ≥0, δ ≤ δ' → epsCa' (F := F) C δ ≤ epsCa' (F := F) C δ')
    {δ : ℝ≥0} (hδ : δ ≤ 1) : epsCa' (F := F) C δ = 0 :=
  le_antisymm (le_of_le_of_eq (hmono δ 1 hδ) (epsCa'_eq_zero_of_one_le hC le_rfl)) zero_le

omit [DecidableEq ι] [Field F] [Fintype F] in
private lemma dist_le_zero_iff_mem {C : Set (ι → F)} (u : ι → F) :
    δᵣ(u, C) ≤ (0 : ℝ≥0) ↔ u ∈ C := by
  rw [relDistFromCode_le_iff_distFromCode_le]
  simp [distFromCode_eq_zero_iff_mem]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private lemma const_mem_zero_iff (γ : F) :
    ((fun _ : ι => γ) ∈ ({0} : Set (ι → F))) ↔ γ = 0 := by
  simp [Set.mem_singleton_iff, funext_iff]

omit [DecidableEq ι] in
/-- The proximity-gap error of the zero singleton code is positive at radius zero. -/
theorem epsPg_singleton_zero_pos :
    (0 : ENNReal) < epsPg (F := F) (A := F) (ι := ι) ({0} : Set (ι → F)) 0 := by
  classical
  set u : WordStack F (Fin 2) ι := ![(0 : ι → F), (1 : ι → F)] with hu
  have hfold : ∀ γ : F, u 0 + γ • u 1 = (fun _ : ι => γ) := by
    intro γ
    funext i
    simp [hu]
  have hevent : ∀ γ : F,
      (δᵣ(u 0 + γ • u 1, ({0} : Set (ι → F))) ≤ (0 : ℝ≥0)) ↔ γ = 0 := by
    intro γ
    rw [hfold γ, dist_le_zero_iff_mem, const_mem_zero_iff]
  have hguard : ¬ (∀ γ : F,
      δᵣ(u 0 + γ • u 1, ({0} : Set (ι → F))) ≤ (0 : ℝ≥0)) :=
    fun h => one_ne_zero ((hevent 1).mp (h 1))
  have hterm : Pr_{let γ ← $ᵖ F}[
      δᵣ(u 0 + γ • u 1, ({0} : Set (ι → F))) ≤ (0 : ℝ≥0)] =
      Pr_{let γ ← $ᵖ F}[γ = 0] := Pr_congr (fun γ => hevent γ)
  have hpos : (0 : ENNReal) < Pr_{let γ ← $ᵖ F}[(γ : F) = 0] := by
    rw [prob_uniform_eq_card_filter_div_card]
    simp [Finset.filter_eq']
  calc
    (0 : ENNReal) < Pr_{let γ ← $ᵖ F}[(γ : F) = 0] := hpos
    _ = Pr_{let γ ← $ᵖ F}[
        δᵣ(u 0 + γ • u 1, ({0} : Set (ι → F))) ≤ (0 : ℝ≥0)] := hterm.symm
    _ ≤ epsPg (F := F) ({0} : Set (ι → F)) 0 := by
      unfold epsPg
      refine le_trans (le_of_eq ?_) (le_iSup _ u)
      rw [if_neg hguard]

/-! ## Comparison and predicate bridges -/

omit [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] in
/-- If a pair is jointly close to a module code, every affine combination is close to the code. -/
theorem line_close_of_jointProximity
    (MC : ModuleCode ι F A) (u : WordStack A (Fin 2) ι) (δ : ℝ≥0)
    (h : jointProximity (C := (MC : Set (ι → A))) (u := u) δ) :
    ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ := by
  rw [← jointAgreement_iff_jointProximity] at h
  obtain ⟨S, hS_card, v, hv⟩ := h
  have hagree : ∀ j ∈ S, v 0 j = u 0 j ∧ v 1 j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp ((hv 0).2 hj)).2
    · exact (Finset.mem_filter.mp ((hv 1).2 hj)).2
  intro γ
  have hvγ : v 0 + γ • v 1 ∈ MC := MC.add_mem (hv 0).1 (MC.smul_mem γ (hv 1).1)
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨v 0 + γ • v 1, hvγ, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj => ?_, fun hne hj => ?_⟩
  · obtain ⟨h0, h1⟩ := hagree j hj
    simp [Pi.add_apply, Pi.smul_apply, h0, h1]
  · obtain ⟨h0, h1⟩ := hagree j hj
    exact hne (by simp [Pi.add_apply, Pi.smul_apply, h0, h1])

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- The proximity-gap error is at most the equal-radius correlated-agreement error. -/
theorem epsPg_le_epsCa (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsPg (F := F) (MC : Set (ι → A)) δ ≤ epsCa (F := F) (MC : Set (ι → A)) δ δ := by
  unfold epsPg epsCa
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · have hall : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ :=
      line_close_of_jointProximity MC u δ hjp
    rw [if_pos hall, if_pos hjp]
  · by_cases hall : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ
    · rw [if_pos hall, if_neg hjp]
      exact zero_le
    · rw [if_neg hall, if_neg hjp]

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- A line-close event outside joint proximity satisfies affine-line `IsMCA`. -/
lemma isMCA_affineLine_of_line_close_of_not_jointProximity
    (MC : ModuleCode ι F A) (u : WordStack A (Fin 2) ι) (δ : ℝ≥0) (γ : F)
    (hjp : ¬ jointProximity (C := (MC : Set (ι → A))) (u := u) δ)
    (hline : δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ) :
    IsMCA (AffineLineGenerator F) MC γ u (δ : ℝ) := by
  classical
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hline
  obtain ⟨w, hw, hwclose⟩ := hline
  rw [relCloseToWord_iff_exists_agreementCols] at hwclose
  obtain ⟨T, hTcard, hagree⟩ := hwclose
  have hTcardNN : (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι :=
    (relDist_floor_bound_iff_complement_bound _ _ _).mp hTcard
  have hTcardR : (T.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) := by
    by_cases hδ : δ ≤ 1
    · have hco := NNReal.coe_le_coe.mpr hTcardNN
      rw [NNReal.coe_mul, NNReal.coe_sub hδ] at hco
      push_cast at hco
      nlinarith
    · have hδ' : (1 : ℝ) < δ := by exact_mod_cast lt_of_not_ge hδ
      have hrhs : (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
      exact hrhs.trans (Nat.cast_nonneg _)
  refine ⟨T, hTcardR, ?_, ?_⟩
  · rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨w, hw, ?_⟩
    funext i
    simp only [LinearCode.projectedWord, Set.restrict_apply]
    simpa [AffineLineGenerator] using (hagree i).1 i.property
  · by_contra hall
    push Not at hall
    apply hjp
    rw [← jointAgreement_iff_jointProximity]
    refine ⟨T, hTcardNN, ?_⟩
    choose v hv hvproj using fun j =>
      (LinearCode.mem_projectedCodeSubmod_iff MC T (LinearCode.projectedWord (u j) T)).mp (hall j)
    refine ⟨v, fun j => ⟨hv j, ?_⟩⟩
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    exact congr_fun (hvproj j).symm ⟨i, hi⟩

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- The equal-radius correlated-agreement error is at most affine-line MCA. -/
theorem epsCa_le_mcaError_affineLine (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsCa (F := F) (MC : Set (ι → A)) δ δ ≤
      mcaError (AffineLineGenerator F) MC (δ : ℝ) := by
  unfold epsCa mcaError
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · rw [if_pos hjp]
    exact zero_le
  · rw [if_neg hjp]
    apply Pr_le_Pr_of_implies
    intro γ hline
    exact isMCA_affineLine_of_line_close_of_not_jointProximity MC u δ γ hjp hline

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- The proximity-gap, correlated-agreement, and affine-line MCA errors are ordered. -/
theorem epsPg_le_epsCa_le_epsMca (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsPg (F := F) (MC : Set (ι → A)) δ ≤ epsCa (F := F) (MC : Set (ι → A)) δ δ ∧
    epsCa (F := F) (MC : Set (ι → A)) δ δ ≤ epsMca MC δ :=
  ⟨epsPg_le_epsCa MC δ, epsCa_le_mcaError_affineLine MC δ⟩

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsCa` is constant when its interleaved radii have the same integer agreement bound. -/
theorem epsCa_eq_of_floor_eq (C : Set (ι → A)) (δ_fld δ_int δ_int' : ℝ≥0)
    (h : Nat.floor (δ_int * Fintype.card ι) = Nat.floor (δ_int' * Fintype.card ι)) :
    epsCa (F := F) C δ_fld δ_int = epsCa (F := F) C δ_fld δ_int' := by
  unfold epsCa
  apply iSup_congr
  intro u
  have hiff : jointProximity (C := C) (u := u) δ_int ↔
      jointProximity (C := C) (u := u) δ_int' := by
    unfold jointProximity
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, h]
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos (hiff.mp hjp)]
  · rw [if_neg hjp, if_neg (mt hiff.mpr hjp)]

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- Bridge between affine-line correlated agreement and the numeric CA error. -/
theorem δ_ε_correlatedAgreementAffineLines_iff_epsCa_le
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineLines (F := F) C δ ε ↔
      epsCa (F := F) C δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro hpred
    refine iSup_le fun u => ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]
      exact zero_le
    · rw [if_neg hjp]
      have hnja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]
        exact hjp
      by_contra hgt
      push Not at hgt
      exact hnja (hpred u hgt)
  · intro heps u hpr
    unfold epsCa at heps
    have hterm := iSup_le_iff.mp heps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]
      exact hjp
    · rw [if_neg hjp] at hterm
      exact absurd hpr (not_lt.mpr hterm)

omit [DecidableEq ι] [DecidableEq F] in
/-- Bridge for the polynomial-curve correlated-agreement predicate. -/
theorem δ_ε_correlatedAgreementCurves_iff_epsCaCurves_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementCurves (F := F) (k := k) C δ ε ↔
      epsCaCurves (F := F) C k δ δ ≤ ((k * ε : ℝ≥0) : ENNReal) := by
  classical
  constructor
  · intro hpred
    refine iSup_le fun u => ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]
      exact zero_le
    · rw [if_neg hjp]
      have hnja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]
        exact hjp
      by_contra hgt
      push Not at hgt
      exact hnja (hpred u hgt)
  · intro heps u hpr
    unfold epsCaCurves at heps
    have hterm := iSup_le_iff.mp heps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]
      exact hjp
    · rw [if_neg hjp] at hterm
      exact absurd hpr (not_lt.mpr hterm)

omit [Fintype F] [DecidableEq F] in
/-- Bridge for the affine-space correlated-agreement predicate. -/
theorem δ_ε_correlatedAgreementAffineSpaces_iff_epsCaAffineSpaces_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineSpaces (F := F) (k := k) C δ ε ↔
      epsCaAffineSpaces (F := F) C k δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro hpred
    refine iSup_le fun u => ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]
      exact zero_le
    · rw [if_neg hjp]
      have hnja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]
        exact hjp
      by_contra hgt
      push Not at hgt
      exact hnja (hpred u hgt)
  · intro heps u hpr
    unfold epsCaAffineSpaces at heps
    have hterm := iSup_le_iff.mp heps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]
      exact hjp
    · rw [if_neg hjp] at hterm
      exact absurd hpr (not_lt.mpr hterm)

/-! ## Unique decoding and interleaving -/

end

section UniqueDecoding

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- Below half the relative minimum distance, affine-line MCA is at most correlated agreement. -/
theorem mcaError_le_epsCa_of_pos_of_two_mul_lt_dist
    (C : LinearCode ι F) (δ : ℝ≥0) (_hδ_pos : 0 < δ)
    (_h_udr : 2 * (δ : ℝ) * Fintype.card ι < Code.dist (C : Set (ι → F))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      epsCa (F := F) (A := F) (C : Set (ι → F)) δ δ := by
  sorry -- external admit [ACFY25 Lemma 4.10].

open Classical in
/-- Below half the relative minimum distance, affine-line MCA equals correlated agreement. -/
theorem mcaError_eq_epsCa_of_pos_of_two_mul_lt_dist
    (C : LinearCode ι F) (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (h_udr : 2 * (δ : ℝ) * Fintype.card ι < Code.dist (C : Set (ι → F))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) =
      epsCa (F := F) (A := F) (C : Set (ι → F)) δ δ :=
  le_antisymm (mcaError_le_epsCa_of_pos_of_two_mul_lt_dist C δ hδ_pos h_udr)
    (epsCa_le_mcaError_affineLine C δ)

end UniqueDecoding

section Interleaving

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F] [Fintype F]
variable {A : Type} [AddCommMonoid A] [Module F A]

/-- A nonempty row-wise interleaving does not increase affine-line MCA at radii in `(0, 1)`. -/
theorem mcaError_interleaved_le
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (_ht : 0 < t) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ) ≤
      mcaError (AffineLineGenerator F) C (δ : ℝ) := by
  sorry -- external admit [Jo26 Corollary 4.5].

/-- Affine-line MCA is invariant under nonempty row-wise interleaving at radii in `(0, 1)`. -/
theorem mcaError_interleaved_eq
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (ht : 0 < t) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ) =
      mcaError (AffineLineGenerator F) C (δ : ℝ) :=
  le_antisymm (mcaError_interleaved_le C t δ ht hδ_pos hδ_lt)
    (mcaError_le_moduleInterleavedCode C t δ ht hδ_lt.le)

end Interleaving

end ProximityGap
