/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Exceptional sets for mutual correlated agreement

Convert a uniform bound on the number of bad challenges into an MCA error bound. The exceptional
set may depend on the input words, but it must work simultaneously for every agreement set. This
is the quantifier order needed to consume [BCHKS25, Theorem 4.6]. These bridges do not assert the
Reed–Solomon exceptional-set bound itself.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
    *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Theorem 4.6.
-/

namespace CoreDefinitions

open LinearCode
open scoped ProbabilityTheory

variable {ι F ℓ S A : Type} [Fintype ι] [Field F] [Fintype ℓ]
  [Nonempty S] [Fintype S] [AddCommMonoid A] [Module F A]

/-- An exceptional set of at most `B` seeds for each input family bounds the worst-case MCA
error by `B / |S|`. A single exceptional set must cover all bad agreement sets for that family. -/
theorem mcaError_le_of_exists_exceptional_set
    (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ B : ℝ)
    (h : ∀ U : ℓ → ι → A, ∃ E : Finset S, (E.card : ℝ) ≤ B ∧
      ∀ x, x ∉ E → ¬ IsMCA G MC x U δ) :
    mcaError G MC δ ≤ ENNReal.ofReal (B / Fintype.card S) := by
  classical
  refine iSup_le fun U => ?_
  obtain ⟨E, hE, hgood⟩ := h U
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hE
  intro x hx
  by_contra hxE
  exact hgood x hxE (Finset.mem_filter.mp hx).2

/-- Same-set simultaneous extension outside an exceptional set implies the MCA error bound.
The codeword extensions are chosen after the agreement set, not uniformly across all sets. -/
theorem mcaError_le_of_exists_exceptional_set_codewords
    (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ B : ℝ)
    (h : ∀ U : ℓ → ι → A, ∃ E : Finset S, (E.card : ℝ) ≤ B ∧
      ∀ x, x ∉ E → ∀ T : Finset ι,
        (T.card : ℝ) ≥ Fintype.card ι * (1 - δ) →
        projectedWord (fun i => ∑ j, G x j • U j i) T ∈ projectedCodeSubmod MC T →
        ∃ p : ℓ → MC, ∀ j i, i ∈ T → (p j).val i = U j i) :
    mcaError G MC δ ≤ ENNReal.ofReal (B / Fintype.card S) := by
  apply mcaError_le_of_exists_exceptional_set
  intro U
  obtain ⟨E, hE, hgood⟩ := h U
  exact ⟨E, hE, fun x hx =>
    (not_isMCA_iff_forall_exists_codewords G MC x U δ).mpr (hgood x hx)⟩

end CoreDefinitions
