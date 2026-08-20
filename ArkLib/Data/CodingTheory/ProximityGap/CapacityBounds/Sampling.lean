/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Ambient density lower-bounds correlated agreement

This file proves the DG25 double-counting reduction from ambient close-word density to
correlated agreement.

## Main result

- `linear_close_probability_le_epsCa` is [DG25dist, Theorem 2.5].

## References

- [DG25dist] Theorem 2.5.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section Sampling

open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Lower-bounds linear-code CA error by the probability that a uniformly sampled ambient
word is within radius `δ`, provided `δ` is below the relative covering radius. -/
theorem linear_close_probability_le_epsCa
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (_h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < δ') :
    ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
        * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ] ≤
      epsCa (F := F) (A := F) ((C : Set (ι → F))) δ δ := by
  classical
  let Good : (ι → F) → Prop := fun w => δᵣ(w, (C : Set (ι → F))) ≤ (δ : ENNReal)
  obtain ⟨z, hz⟩ : ∃ z : ι → F, ¬ Good z := by
    by_contra h
    push Not at h
    have hle : (δ' : ENNReal) ≤ (δ : ENNReal) := by
      rw [_h_δ']
      exact iSup_le h
    have hlt : (δ : ENNReal) < (δ' : ENNReal) := by
      exact_mod_cast _hδ_lt
    exact (not_lt_of_ge hle) hlt
  let G : Finset (ι → F) := Finset.univ.filter Good
  let L : (ι → F) → Finset F := fun d =>
    Finset.univ.filter (fun r : F => Good (z + r • d))
  have hfiber (r : F) (hr : r ≠ 0) :
      (Finset.univ.filter (fun d : ι → F => Good (z + r • d))).card = G.card := by
    apply Finset.card_bijective (fun d : ι → F => z + r • d)
    · constructor
      · intro d e hde
        have h := congrArg (fun w : ι → F => r⁻¹ • (w - z)) hde
        simpa [hr] using h
      · intro w
        refine ⟨r⁻¹ • (w - z), ?_⟩
        ext i
        simp [hr]
    · intro d
      simp [G]
  have hsum : ∑ d : ι → F, (L d).card = (Fintype.card F - 1) * G.card := by
    calc
      ∑ d : ι → F, (L d).card =
          ∑ d : ι → F, ∑ r : F, if Good (z + r • d) then 1 else 0 := by
            simp [L, Finset.card_filter]
      _ = ∑ r : F, ∑ d : ι → F, if Good (z + r • d) then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ r : F, if r = 0 then 0 else G.card := by
            apply Finset.sum_congr rfl
            intro r hrmem
            by_cases hr : r = 0
            · subst r
              simp [hz]
            · rw [if_neg hr]
              rw [← Finset.card_filter]
              exact hfiber r hr
      _ = (Fintype.card F - 1) * G.card := by
            rw [Finset.sum_ite]
            simp
  obtain ⟨d, hd⟩ : ∃ d : ι → F,
      (Fintype.card F - 1) * G.card ≤ Fintype.card (ι → F) * (L d).card := by
    by_contra h
    push Not at h
    have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun d _ => h d)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at hs
    rw [hsum] at hs
    omega
  have havg :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal) *
          Pr_{let w ← $ᵖ (ι → F)}[Good w] ≤
        Pr_{let r ← $ᵖ F}[Good (z + r • d)] := by
    rw [Probability.prob_uniform_eq_card_filter_div_card,
      Probability.prob_uniform_eq_card_filter_div_card]
    change ((Fintype.card F - 1 : ENNReal) / Fintype.card F) *
        ((G.card : ENNReal) / Fintype.card (ι → F)) ≤
      ((L d).card : ENNReal) / Fintype.card F
    norm_cast
    have hV0 : (Fintype.card (ι → F) : ENNReal) ≠ 0 := by positivity
    have hVtop : (Fintype.card (ι → F) : ENNReal) ≠ ⊤ := by simp
    have hcore :
        ((↑(Fintype.card F - 1) : ENNReal) * G.card) /
            Fintype.card (ι → F) ≤ (L d).card := by
      apply (ENNReal.div_le_iff' hV0 hVtop).2
      exact_mod_cast (by simpa [mul_comm] using hd)
    calc
      ((↑(Fintype.card F - 1) : ENNReal) / Fintype.card F) *
          ((G.card : ENNReal) / Fintype.card (ι → F)) =
          (((↑(Fintype.card F - 1) : ENNReal) * G.card) /
            Fintype.card (ι → F)) / Fintype.card F := by
              simp only [div_eq_mul_inv]
              ac_rfl
      _ ≤ ((L d).card : ENNReal) / Fintype.card F :=
        ENNReal.div_le_div_right hcore _
  let u : Code.WordStack F (Fin 2) ι := ![z, d]
  have hnotjoint : ¬ Code.jointProximity (C := (C : Set (ι → F))) (u := u) δ := by
    intro hjp
    have hzero := line_close_of_jointProximity C u δ hjp 0
    apply hz
    simpa [Good, u] using hzero
  have hline :
      Pr_{let r ← $ᵖ F}[Good (z + r • d)] ≤
        epsCa (F := F) (A := F) (C : Set (ι → F)) δ δ := by
    unfold epsCa
    refine le_trans (le_of_eq ?_) (le_iSup (fun v : Code.WordStack F (Fin 2) ι =>
      if Code.jointProximity (C := (C : Set (ι → F))) (u := v) δ then 0
      else Pr_{let r ← $ᵖ F}[δᵣ(v 0 + r • v 1, (C : Set (ι → F))) ≤ δ]) u)
    rw [if_neg hnotjoint]
    simp [u, Good]
  simpa [Good] using havg.trans hline

end Sampling

end CodingTheory
