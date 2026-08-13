/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.InterleavedCode
import Mathlib.FieldTheory.Finite.Basic

/-!
# Mutual correlated agreement is strictly stronger than correlated agreement

The correlated-agreement notions in `ProximityGap/Basic.lean` are threshold implications about
`Code.jointAgreement`: *if the random combination is `δ`-close to the code with probability
exceeding some threshold, then the words jointly agree*. Mutual correlated agreement
(`CoreDefinitions.IsMCA`) is not of that shape, and this file pins the difference.

The two bad events differ in where the agreement set is quantified. The CA bad event is
`combination is δ-close ∧ ¬jointAgreement` — the words share *no* large agreement set. The MCA bad
event ties one `T` to both clauses: the combination agrees with a codeword on `T` while some `U j`
does not agree on *that same* `T`. Joint agreement may hold via some other set `S` while the MCA
event still fires, so the MCA event is strictly the larger of the two. This is [ABF26] Fact 4.5's
`ε_ca ≤ ε_mca` seen as a difference in shape rather than in size.

## Why this file exists

A bound on `mcaError` therefore *implies* the corresponding threshold statement but is not implied
by it, so the `eps?_le_iff_threshold` bridge recorded in
`docs/wiki/proximity-error-conventions.md` is an equivalence for correlated agreement and only an
implication for mutual correlated agreement. `no_threshold_characterisation` below is the witness,
so that claim is checked by the build rather than asserted in a document.

The separation is between the two *definitions*, and is deliberately small: at `n = 2` and
`δ = 1/2` joint agreement needs agreement on one coordinate out of two, which `rep` gives for free.
It says nothing about the quantitative question [ABF26] leaves open after Fact 4.5, namely whether
a proximity gap implies CA or CA implies MCA at comparable errors.

## Main statements

* `jointAgreement_repetitionCode` — over `rep`, at radius `1/2`, *every* family jointly agrees, so
  every threshold implication about `jointAgreement` holds trivially — by its consequent, not by a
  false antecedent — at any threshold.
* `isMCA_repetitionCode` — the MCA event nevertheless fires, at the seed `0` and the family
  `witness`.
* `mcaError_rep_pos` — hence the MCA error is strictly positive: one seed out of `|F|` carries the
  event, which is what turns the pointwise witness into a statement about the value.
* `no_threshold_characterisation` — for **any** threshold-side predicate whatsoever, the
  equivalence fails at threshold `0`. This is the statement the conventions page cites.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace MCASeparation

open CoreDefinitions LinearCode Probability
open scoped NNReal ENNReal ProbabilityTheory

/-- The repetition code `{(a, a)} ⊆ (ZMod 2)²`, as a module code over itself. Chosen because its
projection onto either single coordinate is everything, which is what makes joint agreement at
radius `1/2` unconditional. -/
noncomputable def rep : ModuleCode (Fin 2) (ZMod 2) (ZMod 2) :=
  Submodule.span (ZMod 2) {(fun _ => 1 : Fin 2 → ZMod 2)}

/-- The separating family: `U 0 = (0, 0)` is a codeword, `U 1 = (1, 0)` is not. -/
def witness : Fin 2 → (Fin 2 → ZMod 2) := ![(fun _ => 0), ![1, 0]]

/-- **Every** family jointly agrees with `rep` at radius `1/2`: take the agreement set `{0}` and,
for each row, the constant codeword matching that row's first coordinate. Since `rep` projects onto
the coordinate `0` surjectively, no family can fail.

Consequently every threshold implication of the correlated-agreement shape — *probability exceeds
`t` implies joint agreement* — holds here at every threshold, including `t = 0`. -/
theorem jointAgreement_repetitionCode (W : Fin 2 → Fin 2 → ZMod 2) :
    Code.jointAgreement (rep : Set (Fin 2 → ZMod 2)) (1/2 : ℝ≥0) W := by
  refine ⟨{0}, ?_, fun i _ => W i 0, ?_⟩
  · rw [ge_iff_le, ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub (show (1 : ℝ≥0)/2 ≤ 1 by norm_num)]
    norm_num
  · intro i
    refine ⟨Submodule.mem_span_singleton.mpr ⟨W i 0, by funext k; simp⟩, ?_⟩
    intro j hj
    simp only [Finset.mem_singleton] at hj
    subst hj
    simp

/-- The MCA bad event nevertheless fires, at the seed `0`: the affine-line combination is then
`witness 0 = 0`, a codeword on all of `Fin 2`, while `witness 1 = (1, 0)` is not a codeword there.
The agreement set forced by the second clause is `Finset.univ`, not the `{0}` that
`jointAgreement_repetitionCode` uses — which is exactly how the two notions come apart. -/
theorem isMCA_repetitionCode :
    IsMCA (AffineLineGenerator (ZMod 2)) rep (0 : ZMod 2) witness (1/2 : ℝ) := by
  refine ⟨Finset.univ, by norm_num, ?_, 1, ?_⟩
  · have h : (fun k => ∑ j, AffineLineGenerator (ZMod 2) 0 j • witness j k) = (fun _ => 0) := by
      funext k
      simp [AffineLineGenerator, witness, Fin.sum_univ_two]
    rw [h]
    exact Submodule.zero_mem _
  · intro h
    obtain ⟨c, hc, hcw⟩ := (mem_projectedCodeSubmod_iff rep Finset.univ _).mp h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
    have h0 := congrFun hcw ⟨0, Finset.mem_univ 0⟩
    have h1 := congrFun hcw ⟨1, Finset.mem_univ 1⟩
    simp [projectedWord, witness, ← ha] at h0 h1
    simp [← h0] at h1

/-- **The separation, pointwise.** The MCA bad event and joint agreement hold simultaneously, so
`IsMCA` does not imply `¬ jointAgreement`. This is the pointwise core;
`no_threshold_characterisation` is the consequence for the error *value*. -/
theorem separation :
    IsMCA (AffineLineGenerator (ZMod 2)) rep (0 : ZMod 2) witness (1/2 : ℝ) ∧
      Code.jointAgreement (rep : Set (Fin 2 → ZMod 2)) (1/2 : ℝ≥0) witness :=
  ⟨isMCA_repetitionCode, jointAgreement_repetitionCode witness⟩

/-- The MCA error is strictly positive here: the event fires on one seed out of `|F| = 2`, and
`mcaError` is a supremum over families, so `witness` alone bounds it below. This is the step that
lifts the pointwise witness to a statement about the value. -/
theorem mcaError_rep_pos : 0 < mcaError (AffineLineGenerator (ZMod 2)) rep (1/2 : ℝ) := by
  classical
  have hle := le_iSup
    (fun U => Pr_{let x ←$ᵖ (ZMod 2)}[IsMCA (AffineLineGenerator (ZMod 2)) rep x U (1/2 : ℝ)])
    witness
  refine lt_of_lt_of_le ?_ hle
  rw [prob_uniform_eq_ofReal, ENNReal.ofReal_pos]
  have hcard : 0 < (Finset.univ.filter
      (fun x => IsMCA (AffineLineGenerator (ZMod 2)) rep x witness (1/2 : ℝ))).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, isMCA_repetitionCode⟩⟩
  have hF : 0 < (Fintype.card (ZMod 2) : ℝ) := by norm_num
  positivity

/-- **No threshold statement characterises `mcaError`.** For *any* threshold-side predicate `P`
whatsoever, the equivalence `mcaError ≤ t ↔ ∀ U, P U → jointAgreement` fails at `t = 0` over this
code: the right-hand side holds because joint agreement is unconditional here, while the left-hand
side fails because the MCA error is positive.

The forward implication — an `mcaError` bound gives the threshold statement — does hold, and in
that direction alone the bridge is available. Contrast correlated agreement, whose bad event is
`close ∧ ¬jointAgreement` and for which the equivalence is genuine; see
`docs/wiki/proximity-error-conventions.md`. -/
theorem no_threshold_characterisation (P : (Fin 2 → Fin 2 → ZMod 2) → Prop) :
    ¬ (mcaError (AffineLineGenerator (ZMod 2)) rep (1/2 : ℝ) ≤ (0 : ENNReal) ↔
        ∀ U, P U → Code.jointAgreement (rep : Set (Fin 2 → ZMod 2)) (1/2 : ℝ≥0) U) := fun h =>
  absurd (h.mpr fun U _ => jointAgreement_repetitionCode U) (not_le.mpr mcaError_rep_pos)

end MCASeparation
