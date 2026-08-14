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

This file supplies the numeric errors from Section 4 of [ABF26]. The MCA value is not defined
again here: `CoreDefinitions.mcaError`, specialized to `AffineLineGenerator F`, is the canonical
value. `epsMCA` is only a reducible compatibility spelling for callers using the paper's notation.

## Main definitions

* `epsPG` — the proximity-gap error from ABF26 Section 4.1.
* `epsCA` — the correlated-agreement error from ABF26 Definition 4.1.
* `epsCA'` — the no-proximity-loss specialization.
* `epsMCA` — a compatibility abbreviation for
  `mcaError (AffineLineGenerator F) C (δ : ℝ)`.

The radius conversion in the MCA adapter is intentionally visible. The value API accepts `ℝ`,
whereas the paper-facing radius is `ℝ≥0`; `epsMCA_eq_mcaError`, `epsMCA_zero`, and `epsMCA_one`
pin the conversion and its endpoints.

Only the guard-free MCA error is monotone in its radius. The endpoint and positive-witness results
below record why analogous global monotonicity claims for `epsPG` and `epsCA'` are false.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E., *WHIR: Reed--Solomon Proximity Testing
  with Super-Fast Verification*][ACFY25]
* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26]
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code CoreDefinitions unitInterval
open scoped ProbabilityTheory BigOperators
open Probability

section MCAAdapter

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F] [Fintype F]
variable {A : Type} [AddCommMonoid A] [Module F A]

/-- Paper-notation compatibility for affine-line MCA. This is a reducible adapter, not a second
MCA supremum: unfolding it exposes the merged `CoreDefinitions.mcaError` value. Its assumptions
are exactly those of the canonical value specialized to `AffineLineGenerator`. -/
noncomputable abbrev epsMCA (C : ModuleCode ι F A) (δ : ℝ≥0) : ENNReal :=
  mcaError (AffineLineGenerator F) C (δ : ℝ)

/-- Exact bridge from the paper spelling to the canonical MCA value. -/
theorem epsMCA_eq_mcaError (C : ModuleCode ι F A) (δ : ℝ≥0) :
    epsMCA C δ = mcaError (AffineLineGenerator F) C (δ : ℝ) := rfl

/-- The `ℝ≥0 → ℝ` radius conversion preserves the zero endpoint. -/
@[simp] theorem epsMCA_zero (C : ModuleCode ι F A) :
    epsMCA C 0 = mcaError (AffineLineGenerator F) C 0 := rfl

/-- The `ℝ≥0 → ℝ` radius conversion preserves the one endpoint. -/
@[simp] theorem epsMCA_one (C : ModuleCode ι F A) :
    epsMCA C 1 = mcaError (AffineLineGenerator F) C 1 := rfl

/-- Monotonicity of the affine-line specialization, inherited from the canonical value. -/
theorem epsMCA_mono (C : ModuleCode ι F A) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    epsMCA C δ ≤ epsMCA C δ' :=
  mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast h)

/-- `epsMCA` is constant on the same integer-agreement cells as `mcaError`. The floor is
deliberately stated after coercion to `ℝ`, matching the canonical lemma's value type. -/
theorem epsMCA_eq_of_floor_eq (C : ModuleCode ι F A) {δ δ' : ℝ≥0}
    (h : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ =
      ⌊(δ' : ℝ) * (Fintype.card ι : ℝ)⌋₊) :
    epsMCA C δ = epsMCA C δ' :=
  mcaError_eq_of_floor_eq (AffineLineGenerator F) C (by positivity) (by positivity) h

end MCAAdapter

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Section 4.1.** Worst-case fraction of points on an affine line that are close to
`C`, when the whole line is not close. -/
noncomputable def epsPG (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]

open Classical in
/-- **ABF26 Definition 4.1.** Correlated-agreement error with fold radius `δ_fld` and
interleaved radius `δ_int`. -/
noncomputable def epsCA (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]

/-- No-proximity-loss specialization `ε_ca(C, δ) := ε_ca(C, δ, δ)`. -/
noncomputable def epsCA' (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  epsCA (F := F) C δ δ

open Classical in
/-- Curve variant of ABF26 Definition 4.1. -/
noncomputable def epsCA_curves
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let r ← $ᵖ F}[δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fld]

open Classical in
/-- Affine-space variant of ABF26 Definition 4.1. -/
noncomputable def epsCA_affineSpaces
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(y.1, C) ≤ δ_fld]

/-! ## Monotonicity -/

/-- `epsCA` is monotone in the fold radius. -/
theorem epsCA_mono_δ_fld
    (C : Set (ι → A)) {δ_fld δ_fld' : ℝ≥0} (δ_int : ℝ≥0) (h : δ_fld ≤ δ_fld') :
    epsCA (F := F) C δ_fld δ_int ≤ epsCA (F := F) C δ_fld' δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    apply Pr_le_Pr_of_implies
    intro _ hclose
    exact le_trans hclose (by exact_mod_cast h)

/-- `epsCA` is antitone in the interleaved radius. -/
theorem epsCA_antitone_δ_int
    (C : Set (ι → A)) (δ_fld : ℝ≥0) {δ_int δ_int' : ℝ≥0} (h : δ_int ≤ δ_int') :
    epsCA (F := F) C δ_fld δ_int' ≤ epsCA (F := F) C δ_fld δ_int := by
  classical
  unfold epsCA
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

/-! ## Why `epsPG` and `epsCA'` are not globally monotone -/

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

/-- `epsPG C δ = 0` for `δ ≥ 1`. -/
theorem epsPG_eq_zero_of_one_le {C : Set (ι → A)} (hC : C.Nonempty) {δ : ℝ≥0} (hδ : 1 ≤ δ) :
    epsPG (F := F) C δ = 0 := by
  classical
  refine le_antisymm ?_ zero_le
  unfold epsPG
  refine iSup_le fun u => ?_
  have hguard : ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ (δ : ENNReal) :=
    fun γ => relDistFromCode_le_of_one_le hC _ hδ
  rw [if_pos hguard]

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

/-- `epsCA` vanishes once the interleaved radius is at least one. -/
theorem epsCA_eq_zero_of_one_le_δ_int {C : Set (ι → A)} (hC : C.Nonempty)
    (δ_fld : ℝ≥0) {δ_int : ℝ≥0} (hδ : 1 ≤ δ_int) :
    epsCA (F := F) C δ_fld δ_int = 0 := by
  classical
  refine le_antisymm ?_ zero_le
  unfold epsCA
  exact iSup_le fun u => by rw [if_pos (jointProximity_of_one_le hC u hδ)]

/-- The no-loss CA error vanishes at and beyond the radius-one endpoint. -/
theorem epsCA'_eq_zero_of_one_le {C : Set (ι → A)} (hC : C.Nonempty)
    {δ : ℝ≥0} (hδ : 1 ≤ δ) : epsCA' (F := F) C δ = 0 :=
  epsCA_eq_zero_of_one_le_δ_int hC δ hδ

/-- A global monotonicity hypothesis for `epsPG` forces vacuity on `[0,1]`. -/
theorem epsPG_mono_forces_vacuity {C : Set (ι → A)} (hC : C.Nonempty)
    (hmono : ∀ δ δ' : ℝ≥0, δ ≤ δ' → epsPG (F := F) C δ ≤ epsPG (F := F) C δ')
    {δ : ℝ≥0} (hδ : δ ≤ 1) : epsPG (F := F) C δ = 0 :=
  le_antisymm (le_of_le_of_eq (hmono δ 1 hδ) (epsPG_eq_zero_of_one_le hC le_rfl)) zero_le

/-- A global monotonicity hypothesis for `epsCA'` likewise forces vacuity on `[0,1]`. -/
theorem epsCA'_mono_forces_vacuity {C : Set (ι → A)} (hC : C.Nonempty)
    (hmono : ∀ δ δ' : ℝ≥0, δ ≤ δ' → epsCA' (F := F) C δ ≤ epsCA' (F := F) C δ')
    {δ : ℝ≥0} (hδ : δ ≤ 1) : epsCA' (F := F) C δ = 0 :=
  le_antisymm (le_of_le_of_eq (hmono δ 1 hδ) (epsCA'_eq_zero_of_one_le hC le_rfl)) zero_le

private lemma dist_le_zero_iff_mem {C : Set (ι → F)} (u : ι → F) :
    δᵣ(u, C) ≤ (0 : ℝ≥0) ↔ u ∈ C := by
  rw [relDistFromCode_le_iff_distFromCode_le]
  simp [distFromCode_eq_zero_iff_mem]

private lemma const_mem_zero_iff (γ : F) :
    ((fun _ : ι => γ) ∈ ({0} : Set (ι → F))) ↔ γ = 0 := by
  simp [Set.mem_singleton_iff, funext_iff]

/-- A positive witness showing that `epsPG` is not the zero function. -/
theorem epsPG_pos_witness :
    (0 : ENNReal) < epsPG (F := F) (A := F) (ι := ι) ({0} : Set (ι → F)) 0 := by
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
    _ ≤ epsPG (F := F) ({0} : Set (ι → F)) 0 := by
      unfold epsPG
      refine le_trans (le_of_eq ?_) (le_iSup _ u)
      rw [if_neg hguard]

/-! ## ABF26 Fact 4.5 and predicate bridges -/

/-- If a pair is jointly close to a module code, every affine combination is close to the code. -/
theorem jointProximity_imp_line_close
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

/-- **ABF26 Fact 4.5, first inequality.** `ε_pg ≤ ε_ca`. -/
theorem epsPG_le_epsCA (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ := by
  unfold epsPG epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · have hall : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ :=
      jointProximity_imp_line_close MC u δ hjp
    rw [if_pos hall, if_pos hjp]
  · by_cases hall : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ
    · rw [if_pos hall, if_neg hjp]
      exact zero_le
    · rw [if_neg hall, if_neg hjp]

/-- A line-close event outside joint proximity is an affine-line `IsMCA` event for the canonical
projected-code formulation. -/
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

/-- **ABF26 Fact 4.5, second inequality**, stated against the canonical affine-line MCA value. -/
theorem epsCA_le_mcaError_affineLine (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤
      mcaError (AffineLineGenerator F) MC (δ : ℝ) := by
  unfold epsCA mcaError
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · rw [if_pos hjp]
    exact zero_le
  · rw [if_neg hjp]
    apply Pr_le_Pr_of_implies
    intro γ hline
    exact isMCA_affineLine_of_line_close_of_not_jointProximity MC u δ γ hjp hline

/-- Compatibility spelling of `epsCA_le_mcaError_affineLine`. -/
theorem epsCA_le_epsMCA (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA MC δ :=
  epsCA_le_mcaError_affineLine MC δ

/-- **ABF26 Fact 4.5.** `ε_pg ≤ ε_ca ≤ ε_mca`, with the final term definitionally the
canonical affine-line `mcaError`. -/
theorem epsPG_le_epsCA_le_epsMCA (MC : ModuleCode ι F A) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ ∧
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA MC δ :=
  ⟨epsPG_le_epsCA MC δ, epsCA_le_epsMCA MC δ⟩

/-- **ABF26 Remark 4.2.** `epsCA` is constant on interleaved-radius floor cells. -/
theorem epsCA_eq_of_floor_eq (C : Set (ι → A)) (δ_fld δ_int δ_int' : ℝ≥0)
    (h : Nat.floor (δ_int * Fintype.card ι) = Nat.floor (δ_int' * Fintype.card ι)) :
    epsCA (F := F) C δ_fld δ_int = epsCA (F := F) C δ_fld δ_int' := by
  unfold epsCA
  apply iSup_congr
  intro u
  have hiff : jointProximity (C := C) (u := u) δ_int ↔
      jointProximity (C := C) (u := u) δ_int' := by
    unfold jointProximity
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, h]
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos (hiff.mp hjp)]
  · rw [if_neg hjp, if_neg (mt hiff.mpr hjp)]

/-- Bridge between affine-line correlated agreement and the numeric CA error. -/
theorem δ_ε_correlatedAgreementAffineLines_iff_epsCA_le
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineLines (F := F) C δ ε ↔
      epsCA (F := F) C δ δ ≤ (ε : ENNReal) := by
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
    unfold epsCA at heps
    have hterm := iSup_le_iff.mp heps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]
      exact hjp
    · rw [if_neg hjp] at hterm
      exact absurd hpr (not_lt.mpr hterm)

/-- Bridge for the polynomial-curve correlated-agreement predicate. -/
theorem δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementCurves (F := F) (k := k) C δ ε ↔
      epsCA_curves (F := F) C k δ δ ≤ ((k * ε : ℝ≥0) : ENNReal) := by
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
    unfold epsCA_curves at heps
    have hterm := iSup_le_iff.mp heps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]
      exact hjp
    · rw [if_neg hjp] at hterm
      exact absurd hpr (not_lt.mpr hterm)

/-- Bridge for the affine-space correlated-agreement predicate. -/
theorem δ_ε_correlatedAgreementAffineSpaces_iff_epsCA_affineSpaces_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineSpaces (F := F) (k := k) C δ ε ↔
      epsCA_affineSpaces (F := F) C k δ δ ≤ (ε : ENNReal) := by
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
    unfold epsCA_affineSpaces at heps
    have hterm := iSup_le_iff.mp heps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]
      exact hjp
    · rw [if_neg hjp] at hterm
      exact absurd hpr (not_lt.mpr hterm)

/-! ## Externally sourced leaves and their derived equalities -/

/-- The externally sourced direction of **ABF26 Lemma 4.6 / ACFY25 Lemma 4.10**: below half the
relative minimum distance, affine-line MCA is at most CA.

The explicit `0 < δ` hypothesis preserves the source's open radius domain; this admitted leaf does
not claim endpoint behavior absent from the cited theorem. -/
theorem mcaError_le_epsCA_below_udr
    (C : LinearCode ι F) (δ : ℝ≥0) (_hδ_pos : 0 < δ)
    (_h_udr : 2 * (δ : ℝ) * Fintype.card ι < Code.dist (C : Set (ι → F))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      epsCA (F := F) (A := F) (C : Set (ι → F)) δ δ := by
  sorry -- external admit [ACFY25 Lemma 4.10].

/-- **ABF26 Lemma 4.6 / ACFY25 Lemma 4.10.** Below half the relative minimum distance,
affine-line MCA and CA coincide. The reverse inequality is the proved ABF26 Fact 4.5 bridge, so
only `mcaError_le_epsCA_below_udr` is externally admitted. -/
theorem mcaError_eq_epsCA_below_udr
    (C : LinearCode ι F) (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (h_udr : 2 * (δ : ℝ) * Fintype.card ι < Code.dist (C : Set (ι → F))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) =
      epsCA (F := F) (A := F) (C : Set (ι → F)) δ δ :=
  le_antisymm (mcaError_le_epsCA_below_udr C δ hδ_pos h_udr)
    (epsCA_le_mcaError_affineLine C δ)

/-- Compatibility spelling of `mcaError_eq_epsCA_below_udr`. -/
theorem epsMCA_eq_epsCA_below_udr
    (C : LinearCode ι F) (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (h_udr : 2 * (δ : ℝ) * Fintype.card ι < Code.dist (C : Set (ι → F))) :
    epsMCA C δ = epsCA (F := F) (A := F) (C : Set (ι → F)) δ δ :=
  mcaError_eq_epsCA_below_udr C δ hδ_pos h_udr

/-- The PR 692 structural direction: affine-line MCA for a nonempty row-wise interleaving bounds
affine-line MCA for the base code at every radius in `[0,1]`. -/
theorem mcaError_le_affineLine_interleaved
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

/-- The externally sourced direction of **ABF26 Lemma 4.7 / Jo26 Corollary 4.5**: nonempty
row-wise interleaving does not increase affine-line MCA at radii in `(0,1)`. -/
theorem mcaError_affineLine_interleaved_le
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (_ht : 0 < t) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ) ≤
      mcaError (AffineLineGenerator F) C (δ : ℝ) := by
  sorry -- external admit [Jo26 Corollary 4.5].

/-- **ABF26 Lemma 4.7 / Jo26 Corollary 4.5.** Affine-line MCA is invariant under nonempty
row-wise interleaving at radii in `(0,1)`. The base-to-interleaved inequality is derived from PR
692's `TensorMCA.isMCAGenerator_of_moduleInterleavedCode`; only the reverse is admitted.

The theorem is stated directly on the canonical `mcaError` value. -/
theorem mcaError_affineLine_interleaved_eq
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (ht : 0 < t) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    mcaError (AffineLineGenerator F) (C ^⋈ (Fin t)) (δ : ℝ) =
      mcaError (AffineLineGenerator F) C (δ : ℝ) :=
  le_antisymm (mcaError_affineLine_interleaved_le C t δ ht hδ_pos hδ_lt)
    (mcaError_le_affineLine_interleaved C t δ ht hδ_lt.le)

/-- Paper-notation compatibility for the canonical interleaving theorem. -/
theorem epsMCA_interleaved_eq
    (C : ModuleCode ι F A) (t : ℕ) (δ : ℝ≥0)
    (ht : 0 < t) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    epsMCA (C ^⋈ (Fin t)) δ = epsMCA C δ :=
  mcaError_affineLine_interleaved_eq C t δ ht hδ_pos hδ_lt

end

end ProximityGap
