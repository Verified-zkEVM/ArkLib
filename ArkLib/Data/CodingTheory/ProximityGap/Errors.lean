/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.TensorGenerator
import ArkLib.Data.Probability.Instances
import Mathlib.FieldTheory.Finiteness

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

-- Keep the public `WordStack`/`InterleavedWord` Matrix aliases transparent while elaborating the
-- legacy proximity API under Lean 4.33's stricter backwards-definitional-equality behavior.
set_option backward.isDefEq.respectTransparency false

namespace ProximityGap

open NNReal Code CoreDefinitions unitInterval LinearCode
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
  let : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
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
    have hrow : Matrix.transpose (fun i (_ : Fin 2) => v i) k = v := by
      funext i
      rw [Matrix.transpose_apply]
    rwa [hrow]
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
    simp only [LinearCode.projectedWord, Set.domRestrict_apply]
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
/-- `epsCa` is constant when both radii have the same integer error bounds. -/
theorem epsCa_eq_of_floors_eq (C : Set (ι → A))
    (δ_fld δ_fld' δ_int δ_int' : ℝ≥0)
    (hfld : Nat.floor (δ_fld * Fintype.card ι) =
      Nat.floor (δ_fld' * Fintype.card ι))
    (hint : Nat.floor (δ_int * Fintype.card ι) =
      Nat.floor (δ_int' * Fintype.card ι)) :
    epsCa (F := F) C δ_fld δ_int = epsCa (F := F) C δ_fld' δ_int' := by
  unfold epsCa
  apply iSup_congr
  intro u
  have hiff : jointProximity (C := C) (u := u) δ_int ↔
      jointProximity (C := C) (u := u) δ_int' := by
    unfold jointProximity
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, hint]
  have hclose : ∀ γ : F,
      δᵣ(u 0 + γ • u 1, C) ≤ (δ_fld : ENNReal) ↔
        δᵣ(u 0 + γ • u 1, C) ≤ (δ_fld' : ENNReal) := by
    intro γ
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, hfld]
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos (hiff.mp hjp)]
  · rw [if_neg hjp, if_neg (mt hiff.mpr hjp)]
    exact Pr_congr hclose

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- `epsCa` is constant when its interleaved radii have the same integer agreement bound. -/
theorem epsCa_eq_of_floor_eq (C : Set (ι → A)) (δ_fld δ_int δ_int' : ℝ≥0)
    (h : Nat.floor (δ_int * Fintype.card ι) = Nat.floor (δ_int' * Fintype.card ι)) :
    epsCa (F := F) C δ_fld δ_int = epsCa (F := F) C δ_fld δ_int' :=
  epsCa_eq_of_floors_eq C δ_fld δ_fld δ_int δ_int' rfl h

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

private noncomputable def pairErrors (u c : Fin 2 → ι → F) : Finset ι := by
  classical
  exact disagreementCols (u 0) (c 0) ∪ disagreementCols (u 1) (c 1)

omit [Fintype F] in
private lemma jointProximity_iff_exists_pairErrors_le
    (C : LinearCode ι F) (u : Fin 2 → ι → F) (δ : ℝ≥0) :
    jointProximity (C := (C : Set (ι → F))) (u := u) δ ↔
      ∃ c : Fin 2 → ι → F, (∀ j, c j ∈ C) ∧
        (pairErrors u c).card ≤ Nat.floor (δ * Fintype.card ι) := by
  classical
  rw [← jointAgreement_iff_jointProximity]
  constructor
  · rintro ⟨T, hT, c, hc⟩
    refine ⟨c, fun j => (hc j).1, ?_⟩
    have hsub : pairErrors u c ⊆ Tᶜ := by
      intro i hi
      simp only [pairErrors, Finset.mem_union, mem_disagreementCols] at hi
      simp only [Finset.mem_compl]
      intro hiT
      rcases hi with hi | hi
      · exact hi ((Finset.mem_filter.mp ((hc 0).2 hiT)).2.symm)
      · exact hi ((Finset.mem_filter.mp ((hc 1).2 hiT)).2.symm)
    have hTnat : Fintype.card ι - Nat.floor (δ * Fintype.card ι) ≤ T.card :=
      (relDist_floor_bound_iff_complement_bound _ _ _).mpr hT
    calc
      (pairErrors u c).card ≤ Tᶜ.card := Finset.card_le_card hsub
      _ = Fintype.card ι - T.card := Finset.card_compl T
      _ ≤ Nat.floor (δ * Fintype.card ι) := by omega
  · rintro ⟨c, hc, hE⟩
    let E := pairErrors u c
    refine ⟨Eᶜ, (relDist_floor_bound_iff_complement_bound _ _ _).mp ?_, c, ?_⟩
    · rw [Finset.card_compl]
      exact Nat.sub_le_sub_left hE _
    · intro j
      refine ⟨hc j, ?_⟩
      intro i hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      have hiE : i ∉ E := by simpa [E] using hi
      simp only [E, pairErrors, Finset.mem_union, mem_disagreementCols, not_or] at hiE
      fin_cases j
      · exact of_not_not hiE.1 |>.symm
      · exact of_not_not hiE.2 |>.symm

private lemma line_close_of_isMCA_affineLine
    (C : LinearCode ι F) (u : Fin 2 → ι → F) (δ : ℝ≥0) (γ : F)
    (h : IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)) :
    δᵣ(u 0 + γ • u 1, (C : Set (ι → F))) ≤ (δ : ENNReal) := by
  classical
  obtain ⟨T, hT, hcomb, _⟩ := h
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨w, hw, hproj⟩ := hcomb
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨T, ?_, ?_⟩
  · apply (relDist_floor_bound_iff_complement_bound _ _ _).mpr
    by_cases hδ_le : δ ≤ 1
    · rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδ_le]
      push_cast
      nlinarith
    · rw [tsub_eq_zero_of_le (le_of_not_ge hδ_le)]
      simp
  · intro i
    constructor
    · intro hi
      have := congr_fun hproj ⟨i, hi⟩
      simpa [projectedWord, AffineLineGenerator] using this
    · intro hne hi
      have := congr_fun hproj ⟨i, hi⟩
      exact hne (by simpa [projectedWord, AffineLineGenerator] using this)

open Classical in
/-- Below half the relative minimum distance, affine-line MCA is at most correlated agreement. -/
theorem mcaError_le_epsCa_of_pos_of_two_mul_lt_dist
    (C : LinearCode ι F) (δ : ℝ≥0) (_hδ_pos : 0 < δ)
    (h_udr : 2 * (δ : ℝ) * Fintype.card ι < Code.dist (C : Set (ι → F))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      epsCa (F := F) (A := F) (C : Set (ι → F)) δ δ := by
  let e := Nat.floor (δ * Fintype.card ι)
  have hdist_eq : Code.dist (C : Set (ι → F)) = Code.minDist (C : Set (ι → F)) :=
    Code.dist_eq_minDist (C : Set (ι → F))
  have hud : 2 * e < Code.minDist (C : Set (ι → F)) := by
    have heR : (e : ℝ) ≤ (δ : ℝ) * Fintype.card ι := by
      exact_mod_cast Nat.floor_le (mul_nonneg δ.coe_nonneg (Nat.cast_nonneg _))
    have htwoR : ((2 * e : ℕ) : ℝ) < (Code.dist (C : Set (ι → F)) : ℝ) := by
      calc
        ((2 * e : ℕ) : ℝ) = 2 * (e : ℝ) := by norm_num
        _ ≤ 2 * ((δ : ℝ) * Fintype.card ι) := by gcongr
        _ = 2 * (δ : ℝ) * Fintype.card ι := by ring
        _ < (Code.dist (C : Set (ι → F)) : ℝ) := h_udr
    have htwoNat : 2 * e < Code.dist (C : Set (ι → F)) := by
      exact_mod_cast htwoR
    rwa [hdist_eq] at htwoNat
  have hdle : Code.minDist (C : Set (ι → F)) ≤ Fintype.card ι := by
    rw [← hdist_eq]
    exact Code.dist_le_card (C : Set (ι → F))
  have he_lt_n : e < Fintype.card ι := by omega
  have hδ_lt_one : δ < 1 := by
    have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hdistleR : (Code.minDist (C : Set (ι → F)) : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast hdle
    rw [hdist_eq] at h_udr
    exact_mod_cast (by nlinarith : (δ : ℝ) < 1)
  unfold mcaError
  refine iSup_le fun u => ?_
  have fold_probability_le_epsCa_of_not_jointProximity
      (v : WordStack F (Fin 2) ι)
      (hv : ¬ jointProximity (C := (C : Set (ι → F))) (u := v) δ) :
      Pr_{let x ← $ᵖ F}[δᵣ(v 0 + x • v 1, (C : Set (ι → F))) ≤ δ] ≤
        epsCa (F := F) (C : Set (ι → F)) δ δ := by
    unfold epsCa
    calc
      Pr_{let x ← $ᵖ F}[δᵣ(v 0 + x • v 1, (C : Set (ι → F))) ≤ δ] =
          (if jointProximity (C := (C : Set (ι → F))) (u := v) δ then 0
          else Pr_{let x ← $ᵖ F}[δᵣ(v 0 + x • v 1, (C : Set (ι → F))) ≤ δ]) :=
        (if_neg hv).symm
      _ ≤ ⨆ w : WordStack F (Fin 2) ι,
          if jointProximity (C := (C : Set (ι → F))) (u := w) δ then 0
          else Pr_{let x ← $ᵖ F}[δᵣ(w 0 + x • w 1, (C : Set (ι → F))) ≤ δ] :=
        @le_iSup ENNReal (WordStack F (Fin 2) ι)
          ENNReal.instCompleteLinearOrder.toCompleteLattice _ v
  by_cases hjp : jointProximity (C := (C : Set (ι → F))) (u := u) δ
  · obtain ⟨c, hc, hE⟩ :=
      (jointProximity_iff_exists_pairErrors_le C u δ).mp hjp
    change (pairErrors u c).card ≤ e at hE
    let B := Finset.univ.filter fun γ : F =>
      IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)
    have hcancel : ∀ γ ∈ B, ∃ i ∈ pairErrors u c,
        (u 0 i - c 0 i) + γ * (u 1 i - c 1 i) = 0 := by
      intro γ hγ
      have hmca : IsMCA (AffineLineGenerator F) C γ u (δ : ℝ) :=
        (Finset.mem_filter.mp hγ).2
      obtain ⟨T, hT, hcomb, hfail⟩ := hmca
      rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
      obtain ⟨w, hw, hproj⟩ := hcomb
      have hcγ : c 0 + γ • c 1 ∈ C := C.add_mem (hc 0) (C.smul_mem γ (hc 1))
      have hTnat : Fintype.card ι - e ≤ T.card := by
        apply (relDist_floor_bound_iff_complement_bound _ _ _).mpr
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδ_lt_one.le]
        push_cast
        nlinarith
      have huw : Δ₀(u 0 + γ • u 1, w) ≤ e := by
        rw [hammingDist_eq_disagreementCols_card]
        calc
          (disagreementCols (u 0 + γ • u 1) w).card ≤ Tᶜ.card := by
            apply Finset.card_le_card
            intro i hi
            rw [Finset.mem_compl]
            intro hiT
            have heq := congr_fun hproj ⟨i, hiT⟩
            exact (mem_disagreementCols.mp hi) (by
              simpa [projectedWord, AffineLineGenerator] using heq)
          _ = Fintype.card ι - T.card := Finset.card_compl T
          _ ≤ e := by omega
      have huc : Δ₀(u 0 + γ • u 1, c 0 + γ • c 1) ≤ e := by
        rw [hammingDist_eq_disagreementCols_card]
        apply le_trans (Finset.card_le_card (t := pairErrors u c) ?_) hE
        intro i hi
        simp only [mem_disagreementCols, Pi.add_apply, Pi.smul_apply] at hi
        by_contra hiE
        simp only [pairErrors, Finset.mem_union, mem_disagreementCols, not_or] at hiE
        exact hi (by simp [of_not_not hiE.1, of_not_not hiE.2])
      have hw_eq : w = c 0 + γ • c 1 := by
        apply Code.eq_of_lt_dist hw hcγ
        calc
          Δ₀(w, c 0 + γ • c 1) ≤
              Δ₀(w, u 0 + γ • u 1) + Δ₀(u 0 + γ • u 1, c 0 + γ • c 1) :=
            hammingDist_triangle _ _ _
          _ ≤ e + e := by simpa [hammingDist_comm] using Nat.add_le_add huw huc
          _ < Code.dist (C : Set (ι → F)) := by rw [hdist_eq]; omega
      have hnsub : ¬ T ⊆ (pairErrors u c)ᶜ := by
        intro hsub
        obtain ⟨j, hj⟩ := hfail
        apply hj
        rw [LinearCode.mem_projectedCodeSubmod_iff]
        refine ⟨c j, hc j, ?_⟩
        funext i
        have hiE : (i : ι) ∉ pairErrors u c := Finset.mem_compl.mp (hsub i.property)
        simp only [pairErrors, Finset.mem_union, mem_disagreementCols, not_or] at hiE
        fin_cases j
        · simp [projectedWord, of_not_not hiE.1]
        · simp [projectedWord, of_not_not hiE.2]
      rw [Finset.not_subset] at hnsub
      obtain ⟨i, hiT, hiE⟩ := hnsub
      refine ⟨i, Finset.notMem_compl.mp hiE, ?_⟩
      have heq := congr_fun hproj ⟨i, hiT⟩
      have hline : u 0 i + γ * u 1 i = w i := by
        simpa [projectedWord, AffineLineGenerator] using heq
      rw [hw_eq] at hline
      have hline' : u 0 i + γ * u 1 i = c 0 i + γ * c 1 i := by
        simpa [Pi.add_apply, Pi.smul_apply] using hline
      linear_combination hline'
    choose f hfE hfcancel using fun γ : B => hcancel γ γ.property
    have hfinj : Function.Injective f := by
      intro γ γ' hff
      have hγ := hfcancel γ
      have hγ' := hfcancel γ'
      rw [hff] at hγ
      have hpair := hfE γ'
      simp only [pairErrors, Finset.mem_union, mem_disagreementCols] at hpair
      have hnonzero : u 1 (f γ') - c 1 (f γ') ≠ 0 := by
        intro hz
        rw [hz, mul_zero, add_zero] at hγ'
        have h0 : u 0 (f γ') = c 0 (f γ') := sub_eq_zero.mp hγ'
        rcases hpair with h0' | h1'
        · exact h0' h0
        · exact h1' (sub_eq_zero.mp hz)
      apply Subtype.ext
      apply (mul_left_cancel₀ hnonzero)
      linear_combination hγ - hγ'
    have hBcard : B.card ≤ e := by
      let fE : B → pairErrors u c := fun γ => ⟨f γ, hfE γ⟩
      have hfEinj : Function.Injective fE := fun γ γ' h => hfinj (congrArg Subtype.val h)
      calc
        B.card = Fintype.card B := (Fintype.card_coe B).symm
        _ ≤ Fintype.card (pairErrors u c) := Fintype.card_le_of_injective fE hfEinj
        _ = (pairErrors u c).card := Fintype.card_coe _
        _ ≤ e := hE
    by_cases hBne : B.Nonempty
    · obtain ⟨β, hβ⟩ := hBne
      let βB : B := ⟨β, hβ⟩
      have hKle : e + 1 ≤ Fintype.card ι := by omega
      obtain ⟨K, _hKuniv, hKcard⟩ :=
        Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) hKle
      have hEmbCard : Fintype.card B ≤ Fintype.card K := by
        rw [Fintype.card_coe, Fintype.card_coe, hKcard]
        exact hBcard.trans (Nat.le_succ e)
      let emb : B ↪ K := (Function.Embedding.nonempty_of_card_le hEmbCard).some
      let assigned (i : ι) : Prop := ∃ γ : B, (emb γ).1 = i
      let slope (i : ι) : F := if h : assigned i then (Classical.choose h).1 - β else 0
      have hembK (γ : B) : (emb γ).1 ∈ K := (emb γ).2
      have hslope (γ : B) : slope (emb γ).1 = γ.1 - β := by
        simp only [slope]
        split
        next h =>
          have heq : Classical.choose h = γ := by
            apply emb.injective
            apply Subtype.ext
            exact Classical.choose_spec h
          rw [heq]
        next h => exact (h ⟨γ, rfl⟩).elim
      let v : Fin 2 → ι → F := fun j i =>
        if hi : i ∈ K then
          if j = 0 then c 0 i + if assigned i then -slope i else 1
          else c 1 i + if assigned i then 1 else 0
        else c j i
      have hpairV : pairErrors v c = K := by
        ext i
        by_cases hiK : i ∈ K
        · by_cases hiA : assigned i <;> simp [pairErrors, v, hiK, hiA, one_ne_zero]
        · simp [pairErrors, v, hiK]
      have hrow1 : Δ₀(v 1, c 1) ≤ e := by
        rw [hammingDist_eq_disagreementCols_card]
        let R := Finset.univ.image fun γ : B => (emb γ).1
        apply le_trans (Finset.card_le_card (t := R) ?_) ?_
        · intro i hi
          simp only [mem_disagreementCols] at hi
          have hiK : i ∈ K := by
            by_contra hiK
            simp [v, hiK] at hi
          have hiA : assigned i := by
            by_contra hiA
            simp [v, hiK, hiA] at hi
          obtain ⟨γ, hγ⟩ := hiA
          exact Finset.mem_image.mpr ⟨γ, Finset.mem_univ _, hγ⟩
        · calc
            R.card ≤ B.card := by
              dsimp only [R]
              simpa using (Finset.card_image_le :
                ((Finset.univ : Finset B).image fun γ : B => (emb γ).1).card ≤
                  (Finset.univ : Finset B).card)
            _ ≤ e := hBcard
      have hrow0 : Δ₀(v 0, c 0) ≤ e := by
        rw [hammingDist_eq_disagreementCols_card]
        apply le_trans (Finset.card_le_card (t := K.erase (emb βB).1) ?_) ?_
        · intro i hi
          simp only [mem_disagreementCols] at hi
          have hiK : i ∈ K := by
            by_contra hiK
            simp [v, hiK] at hi
          rw [Finset.mem_erase]
          refine ⟨?_, hiK⟩
          intro hiβ
          subst i
          have hiA : assigned (emb βB).1 := ⟨βB, rfl⟩
          have hs : slope (emb βB).1 = 0 := by simpa [βB] using hslope βB
          simp [v, hembK βB, hiA, hs] at hi
        · rw [Finset.card_erase_of_mem (hembK βB), hKcard]
          omega
      have hvNotJoint : ¬ jointProximity (C := (C : Set (ι → F))) (u := v) δ := by
        intro hvJoint
        obtain ⟨d, hd, hdE⟩ :=
          (jointProximity_iff_exists_pairErrors_le C v δ).mp hvJoint
        change (pairErrors v d).card ≤ e at hdE
        have hvd (j : Fin 2) : Δ₀(v j, d j) ≤ e := by
          rw [hammingDist_eq_disagreementCols_card]
          apply le_trans (Finset.card_le_card (t := pairErrors v d) ?_) hdE
          intro i hi
          simp only [mem_disagreementCols] at hi
          fin_cases j
          · exact Finset.mem_union_left _ (mem_disagreementCols.mpr hi)
          · exact Finset.mem_union_right _ (mem_disagreementCols.mpr hi)
        have hdc : d = c := by
          funext j
          apply Code.eq_of_lt_dist (hd j) (hc j)
          calc
            Δ₀(d j, c j) ≤ Δ₀(d j, v j) + Δ₀(v j, c j) :=
              hammingDist_triangle _ _ _
            _ ≤ e + e := by
              have hcj : Δ₀(v j, c j) ≤ e := by
                fin_cases j
                · exact hrow0
                · exact hrow1
              simpa [hammingDist_comm] using Nat.add_le_add (hvd j) hcj
            _ < Code.dist (C : Set (ι → F)) := by rw [hdist_eq]; omega
        subst d
        rw [hpairV] at hdE
        omega
      have hcloseV (γ : B) :
          δᵣ(v 0 + (γ.1 - β) • v 1, (C : Set (ι → F))) ≤ (δ : ENNReal) := by
        let x := γ.1 - β
        let iγ := (emb γ).1
        have hiγK : iγ ∈ K := hembK γ
        have hiγA : assigned iγ := ⟨γ, rfl⟩
        have hdist : Δ₀(v 0 + x • v 1, c 0 + x • c 1) ≤ e := by
          rw [hammingDist_eq_disagreementCols_card]
          apply le_trans (Finset.card_le_card (t := K.erase iγ) ?_) ?_
          · intro i hi
            simp only [mem_disagreementCols] at hi
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hii
              subst i
              apply hi
              have hv0 : v 0 iγ = c 0 iγ - x := by
                simp [v, hiγK, hiγA, iγ, x, hslope γ]
                ring
              have hv1 : v 1 iγ = c 1 iγ + 1 := by
                simp [v, hiγK, hiγA]
              simp only [Pi.add_apply, Pi.smul_apply, hv0, hv1]
              ring
            · by_contra hiK
              simp [v, hiK] at hi
          · rw [Finset.card_erase_of_mem hiγK, hKcard]
            omega
        rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
        refine ⟨c 0 + x • c 1, C.add_mem (hc 0) (C.smul_mem x (hc 1)), ?_⟩
        rw [pairRelDist_le_iff_pairDist_le]
        exact hdist
      calc
        Pr_{let γ ← $ᵖ F}[IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)] ≤
            Pr_{let x ← $ᵖ F}[δᵣ(v 0 + x • v 1, (C : Set (ι → F))) ≤ δ] := by
          rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card]
          apply ENNReal.div_le_div_right
          exact_mod_cast (calc
            (Finset.univ.filter fun γ : F =>
                IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)).card = B.card := by rfl
            _ = (B.image fun γ => γ - β).card := by
              symm
              apply Finset.card_image_of_injective
              intro x y hxy
              exact sub_left_injective hxy
            _ ≤ (Finset.univ.filter fun x : F =>
                δᵣ(v 0 + x • v 1, (C : Set (ι → F))) ≤ δ).card := by
              apply Finset.card_le_card
              intro x hx
              obtain ⟨γ, hγB, rfl⟩ := Finset.mem_image.mp hx
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hcloseV ⟨γ, hγB⟩⟩)
        _ ≤ epsCa (F := F) (C : Set (ι → F)) δ δ :=
          fold_probability_le_epsCa_of_not_jointProximity v hvNotJoint
    · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBne
      rw [prob_uniform_eq_card_filter_div_card]
      have hfilter : (Finset.univ.filter fun γ : F =>
          IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)) = B := rfl
      rw [hfilter, hBempty]
      simp
  · calc
      Pr_{let γ ← $ᵖ F}[IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)] ≤
          Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, (C : Set (ι → F))) ≤ δ] := by
        apply Pr_le_Pr_of_implies
        intro γ h
        exact line_close_of_isMCA_affineLine C u δ γ h
      _ ≤ epsCa (F := F) (C : Set (ι → F)) δ δ :=
        fold_probability_le_epsCa_of_not_jointProximity u hjp

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

/-- At most `|K|` proper subspaces cannot cover a nontrivial finite `K`-vector space. -/
private lemma exists_forall_notMem_of_card_le
    {α K M : Type} [Field K] [Fintype K] [AddCommGroup M] [Module K M]
    [Finite M] [Nontrivial M]
    (s : Finset α) (p : α → Submodule K M)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  let := Fintype.ofFinite M
  let q := Fintype.card K
  let d := Module.finrank K M
  let nz (i : α) := Finset.univ.filter fun x : M => x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : M) (s.biUnion nz)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hnz (i : α) (hi : i ∈ s) : (nz i).card ≤ q ^ (d - 1) - 1 := by
    let allp := Finset.univ.filter fun x : M => x ∈ p i
    have hzero : (0 : M) ∈ allp := by simp [allp]
    have hnz_eq : nz i = allp.erase 0 := by
      ext x
      simp [nz, allp, and_comm]
    rw [hnz_eq, Finset.card_erase_of_mem hzero]
    have hcard : allp.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset allp (by simp [allp])
    have hcardpow : Fintype.card (p i) = q ^ Module.finrank K (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := K) (V := p i))
    rw [hcard, hcardpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card M := by
    have hbi : (s.biUnion nz).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        (s.biUnion nz).card ≤ ∑ i ∈ s, (nz i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi => hnz i hi
        _ = s.card * (q ^ (d - 1) - 1) := by simp
    have hmul : s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcardM : Fintype.card M = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := K) (V := M))
    rw [hcardM, hpow]
    calc
      covered.card ≤ (s.biUnion nz).card + 1 := Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hbi 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) := pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi => hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · simp only [covered, Finset.mem_insert]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nz, hxi, hx0]⟩)

/-- A nonempty row-wise interleaving does not increase affine-line MCA at radii in `(0, 1)`. -/
theorem mcaError_interleaved_le
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (ht : 0 < t) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ) ≤
      mcaError (AffineLineGenerator F) C (δ : ℝ) := by
  classical
  let : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  unfold mcaError
  refine iSup_le fun U => ?_
  let isBad (x : F) := IsMCA (AffineLineGenerator F) (C ^⋈ (Fin t)) x U (δ : ℝ)
  let B := Finset.univ.filter isBad
  obtain ⟨T, hT⟩ : ∃ T : F → Finset ι, ∀ x, isBad x →
      (T x).card ≥ (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) ∧
      projectedWord (fun k => ∑ j, AffineLineGenerator F x j • U j k) (T x) ∈
        projectedCodeSubmod (C ^⋈ (Fin t)) (T x) ∧
      ∃ j, projectedWord (U j) (T x) ∉ projectedCodeSubmod (C ^⋈ (Fin t)) (T x) := by
    choose! T hT using fun x (hx : isBad x) => hx
    exact ⟨T, hT⟩
  let rowComb (l : Fin t → F) (j : Fin 2) : ι → A :=
    fun k => ∑ i, l i • U j k i
  let K (x : F) : Submodule F (Fin t → F) :=
    { carrier := {l | ∀ j, projectedWord (rowComb l j) (T x) ∈ projectedCodeSubmod C (T x)}
      zero_mem' := by
        intro j
        have hz : projectedWord (rowComb 0 j) (T x) = 0 := by
          ext k
          simp [projectedWord, rowComb]
        rw [hz]
        exact (projectedCodeSubmod C (T x)).zero_mem
      add_mem' := by
        intro l l' hl hl' j
        have hadd : projectedWord (rowComb (l + l') j) (T x) =
            projectedWord (rowComb l j) (T x) + projectedWord (rowComb l' j) (T x) := by
          ext k
          simp [projectedWord, rowComb, add_smul, Finset.sum_add_distrib]
        rw [hadd]
        exact (projectedCodeSubmod C (T x)).add_mem (hl j) (hl' j)
      smul_mem' := by
        intro a l hl j
        have hsmul : projectedWord (rowComb (a • l) j) (T x) =
            a • projectedWord (rowComb l j) (T x) := by
          ext k
          simp [projectedWord, rowComb, Finset.smul_sum, mul_smul]
        rw [hsmul]
        exact (projectedCodeSubmod C (T x)).smul_mem a (hl j) }
  have hK (x : F) (hx : x ∈ B) : K x ≠ ⊤ := by
    obtain ⟨j, hj⟩ := (hT x (Finset.mem_filter.mp hx).2).2.2
    have hj' : ¬ ∀ i : Fin t,
        projectedWord (fun k => U j k i) (T x) ∈ projectedCodeSubmod C (T x) := by
      intro hall
      apply hj
      exact (projectedCodeSubmod_moduleInterleavedCode_iff
        F A (Fin t) ι C (U j) (T x)).mpr hall
    push Not at hj'
    obtain ⟨i, hi⟩ := hj'
    intro htop
    have he : Pi.single i (1 : F) ∈ K x := by rw [htop]; exact Submodule.mem_top
    apply hi
    simpa [K, rowComb] using he j
  have hBcard : B.card ≤ Fintype.card F := by
    simpa [B] using Finset.card_filter_le Finset.univ isBad
  obtain ⟨l, hl⟩ := exists_forall_notMem_of_card_le B K hK hBcard
  let V : Fin 2 → (ι → A) := rowComb l
  have himp : ∀ x : F, isBad x → IsMCA (AffineLineGenerator F) C x V (δ : ℝ) := by
    intro x hx
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hdata := hT x hx
    refine ⟨T x, hdata.1, ?_, ?_⟩
    · have hrows : ∀ i : Fin t,
          projectedWord (fun k => ∑ j, AffineLineGenerator F x j • U j k i) (T x) ∈
            projectedCodeSubmod C (T x) :=
        (projectedCodeSubmod_moduleInterleavedCode_iff F A (Fin t) ι C
          (fun k => ∑ j, AffineLineGenerator F x j • U j k) (T x)).mp hdata.2.1
      rw [mem_projectedCodeSubmod_iff]
      convert projectedCode_linearCombination C (T x)
        (fun i k => ∑ j, AffineLineGenerator F x j • U j k i) l
        (fun i => (mem_projectedCodeSubmod_iff C (T x) _).mp (hrows i)) using 1
      ext k
      simp only [projectedWord, Set.domRestrict_apply, V, rowComb, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    · have hnot := hl x hxB
      change ¬ ∀ j, projectedWord (rowComb l j) (T x) ∈ projectedCodeSubmod C (T x) at hnot
      push Not at hnot
      simpa [V] using hnot
  calc
    Pr_{let x ← $ᵖ F}[IsMCA (AffineLineGenerator F) (C ^⋈ (Fin t)) x U (δ : ℝ)]
        ≤ Pr_{let x ← $ᵖ F}[IsMCA (AffineLineGenerator F) C x V (δ : ℝ)] :=
      Pr_le_Pr_of_implies _ _ _ himp
    _ ≤ ⨆ V : Fin 2 → (ι → A),
        Pr_{let x ← $ᵖ F}[IsMCA (AffineLineGenerator F) C x V (δ : ℝ)] :=
      le_iSup (fun V : Fin 2 → (ι → A) =>
        Pr_{let x ← $ᵖ F}[IsMCA (AffineLineGenerator F) C x V (δ : ℝ)]) V

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
