/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-! # Degree-two polynomial collision bound for packing sumcheck

This local proof avoids importing the full Binary Basefold soundness protocol hierarchy.
-/

@[expose] public section

namespace RingSwitching.SumcheckPhase
open scoped NNReal ProbabilityTheory Polynomial
variable {L : Type} [Field L] [Fintype L] [SampleableType L]

lemma probability_bound_badSumcheckEventProp (h_i h_star : L⦃≤ 2⦄[X]) :
    Pr{ let r_i' ← $ᵗ L }[ Binius.BinaryBasefold.badSumcheckEventProp r_i' h_i h_star ] ≤
      (2 : ℝ≥0) / Fintype.card L := by
  classical
  unfold Binius.BinaryBasefold.badSumcheckEventProp
  by_cases h_ne : h_i ≠ h_star
  · simp only [ne_eq, h_ne, not_false_eq_true, true_and, ENNReal.coe_ofNat]
    let : DecidableEq L := Classical.decEq L
    let p : L[X] := h_i.val - h_star.val
    have h_p_ne : p ≠ 0 := by
      intro h_p_zero
      apply h_ne
      apply Subtype.ext
      dsimp [p] at h_p_zero
      exact sub_eq_zero.mp h_p_zero
    have h_p_degree : p.natDegree ≤ 2 := by
      apply Polynomial.natDegree_le_of_degree_le
      dsimp [p]
      exact (Polynomial.degree_sub_le _ _).trans <|
        max_le (Polynomial.mem_degreeLE.mp h_i.property)
          (Polynomial.mem_degreeLE.mp h_star.property)
    have h_event (r : L) : h_i.val.eval r = h_star.val.eval r ↔ p.eval r = 0 := by
      dsimp [p]
      rw [Polynomial.eval_sub, sub_eq_zero]
    simp_rw [h_event]
    let : DecidablePred (fun r : L => p.eval r = 0) := Classical.decPred _
    rw [SampleableType.prEvent_uniformSample]
    have h_root_card : (Finset.univ.filter fun r : L => p.eval r = 0).card ≤ p.natDegree := by
      refine le_trans ?_ (Polynomial.card_roots' p)
      calc
        (Finset.univ.filter fun r : L => p.eval r = 0).card ≤ p.roots.toFinset.card := by
          refine Finset.card_le_card ?_
          intro r hr
          rw [Multiset.mem_toFinset]
          exact (Polynomial.mem_roots h_p_ne).mpr (Finset.mem_filter.mp hr).2
        _ ≤ p.roots.card := Multiset.toFinset_card_le _
    calc
      ((Finset.univ.filter fun r : L => p.eval r = 0).card : ENNReal) / Fintype.card L
          ≤ (p.natDegree : ENNReal) / Fintype.card L := by
            gcongr
      _ ≤ (2 : ENNReal) / Fintype.card L := by
        gcongr
        exact_mod_cast h_p_degree
  · simp only [h_ne, false_and, ENNReal.coe_ofNat]
    exact (prEvent_eq_zero_of_forall_not _ _ (fun _ h => h)).le.trans _root_.zero_le

end RingSwitching.SumcheckPhase
