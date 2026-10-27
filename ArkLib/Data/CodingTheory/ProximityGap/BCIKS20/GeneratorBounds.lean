/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineCoefficients
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
public import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Generator-indexed BCIKS20 bounds

Independent affine coefficients cost `errorBound`; powers of one seed cost
`m * errorBound`. Both bounds hold in the open Johnson regime.
-/

@[expose] public section

namespace ProximityGap

open CoreDefinitions Code OracleComp
open scoped NNReal ENNReal ProbabilityTheory

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable [Fintype ι] [Nonempty ι]

/-- The BCIKS20 curve bound for powers, with precisely its open Johnson hypotheses. -/
theorem caError_powers_le (m : ℕ) {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    caError (univariatePowersGenerator F m) (ReedSolomon.code domain deg).carrier δ δ ≤
      ((m * errorBound δ deg domain : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementCurves_iff_caError_le _ _ _).mp
    (correlatedAgreement_affine_curves hdeg hδ_pos hδ)

/-- Independent affine coefficients have the BCIKS20 affine-space error, including
zero directions. No linear independence assumption is needed. -/
theorem caError_affineSpace_le (m : ℕ) {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    caError (AffineSpaceGenerator F m) (ReedSolomon.code domain deg).carrier δ δ ≤
      (errorBound δ deg domain : ENNReal) := by
  classical
  by_cases hm : m = 0
  · subst m
    unfold caError
    apply iSup_le
    intro u
    split
    · exact zero_le
    next hnot =>
      have hz : Pr{let cs ← $ᵗ (Fin 0 → F)}[
          relDistFromCode (∑ i, AffineSpaceGenerator F 0 cs i • u i)
            (ReedSolomon.code domain deg).carrier ≤ δ] = 0 := by
        apply prEvent_eq_zero_of_forall_mem_support
        intro cs _ hclose
        simp only [Fin.sum_univ_succ, AffineSpaceGenerator, Fin.cons_zero,
          Fin.sum_univ_zero, add_zero, one_smul] at hclose
        obtain ⟨v, hv, hd⟩ :=
          (relCloseToCode_iff_relCloseToCodeword_of_minDist _ δ).mp hclose
        obtain ⟨T, hT, ha⟩ := (relCloseToWord_iff_exists_agreementCols _ _ δ).mp hd
        apply hnot
        rw [← jointAgreement_iff_jointProximity]
        refine ⟨T, (relDist_floor_bound_iff_complement_bound _ _ δ).mp hT,
          (fun _ => v), ?_⟩
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        refine ⟨hv, ?_⟩
        intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((ha z).1 hz).symm⟩
      exact hz.le.trans zero_le
  let : NeZero m := ⟨hm⟩
  by_cases hε : errorBound δ deg domain < 1
  · apply (δ_ε_correlatedAgreementAffineSpaces_iff_caError_le _ _ _).mp
    apply correlatedAgreement_affine_spaces hdeg hδ_pos hδ _ hε
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    by_contra h
    have hfull : Fintype.card ι ≤ deg := by omega
    have hrate : LinearCode.rate (ReedSolomon.code domain deg) = 1 := by
      rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    have hsone : ReedSolomon.sqrtRate deg domain = 1 := by
      simp [ReedSolomon.sqrtRate, hrate]
    rw [hsone, tsub_self] at hδ
    exact (lt_irrefl 0) (hδ_pos.trans hδ)
  · apply le_trans _ (show (1 : ENNReal) ≤ errorBound δ deg domain by
      exact_mod_cast le_of_not_gt hε)
    unfold caError
    apply iSup_le
    intro u
    split
    · exact zero_le
    · exact prEvent_le_one _

end ProximityGap
