/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.CodingTheory.InterleavedCode
import Mathlib.FieldTheory.Finite.Basic

/-!
# Mutual correlated agreement is strictly stronger than correlated agreement

Correlated agreement is a threshold implication about `Code.jointAgreement`: if the random
combination is `δ`-close to the code with probability exceeding some threshold, then the words
jointly agree. Mutual correlated agreement (`CoreDefinitions.IsMCA`) is not of that shape, and this
file separates the two.

The bad events differ in where the agreement set is quantified. Correlated agreement's is
`combination is δ-close ∧ ¬ jointAgreement` — the words share *no* large agreement set. The mutual
one ties a single `T` to both clauses: the combination agrees with a codeword on `T` while some
`U j` does not agree on that same `T`. Joint agreement may therefore hold via some other set while
the mutual event still fires, making the mutual event the larger of the two.

The consequence is that a bound on `CoreDefinitions.mcaError` *implies* the corresponding threshold
statement — that direction is [BCGM25] Lemma 3.22, which is not formalized here — but is not
implied by it. `not_mcaError_le_iff_forall_jointAgreement` is the failing direction.

What is separated is the two *definitions*: the witness is a two-coordinate code at radius `1/2`,
and no correlated-agreement definition appears in any statement below. The quantitative question
[ABF26] leaves open after its Fact 4.5 is untouched.

## Main definitions

* `MCASeparation.repetitionCode` — `{(a, a)} ⊆ (ZMod 2)²`. Its projection onto either single
  coordinate is everything, which is what makes joint agreement unconditional at radius `1/2`.
* `MCASeparation.separatingFamily` — the pair `((0, 0), (1, 0))`: a codeword and a non-codeword.

## Main statements

* `MCASeparation.jointAgreement_repetitionCode` — *every* family jointly agrees, so every threshold
  implication about `Code.jointAgreement` holds by its consequent at any threshold.
* `MCASeparation.isMCA_repetitionCode` — the mutual event nevertheless fires, at seed `0`.
* `MCASeparation.mcaError_repetitionCode_pos` — hence the error value is positive.
* `MCASeparation.not_mcaError_le_iff_forall_jointAgreement` — below the error value, no threshold
  implication is equivalent to a `mcaError` bound.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace MCASeparation

open CoreDefinitions LinearCode Probability
open scoped NNReal ENNReal ProbabilityTheory

/-- The repetition code `{(a, a)} ⊆ (ZMod 2)²`, as a module code over its own alphabet. -/
noncomputable def repetitionCode : ModuleCode (Fin 2) (ZMod 2) (ZMod 2) :=
  Submodule.span (ZMod 2) {(fun _ => 1 : Fin 2 → ZMod 2)}

/-- The family separating the two notions: `(0, 0)` is a codeword of `repetitionCode` and
`(1, 0)` is not. -/
def separatingFamily : Fin 2 → (Fin 2 → ZMod 2) := ![(fun _ => 0), ![1, 0]]

/-- Every family jointly agrees with `repetitionCode` at radius `1/2`, witnessed by the agreement
set `{0}` and, for each row, the constant codeword matching that row's first coordinate.

So a threshold implication about `Code.jointAgreement` holds here by its consequent — not by a
false antecedent — at every threshold, including `0`. -/
theorem jointAgreement_repetitionCode (W : Fin 2 → Fin 2 → ZMod 2) :
    Code.jointAgreement (repetitionCode : Set (Fin 2 → ZMod 2)) (1/2 : ℝ≥0) W := by
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

/-- The mutual bad event fires at seed `0`, where the affine-line combination is
`separatingFamily 0 = 0`, a codeword on all of `Fin 2`, while `separatingFamily 1 = (1, 0)` is not.

The agreement set forced by the second clause is `Finset.univ`, not the `{0}` that
`jointAgreement_repetitionCode` uses — which is how the two notions come apart. -/
theorem isMCA_repetitionCode :
    IsMCA (AffineLineGenerator (ZMod 2)) repetitionCode (0 : ZMod 2) separatingFamily
      (1/2 : ℝ) := by
  refine ⟨Finset.univ, by norm_num, ?_, 1, ?_⟩
  · have h : (fun k => ∑ j, AffineLineGenerator (ZMod 2) 0 j • separatingFamily j k)
        = (fun _ => 0) := by
      funext k
      simp [AffineLineGenerator, separatingFamily, Fin.sum_univ_two]
    rw [h]
    exact Submodule.zero_mem _
  · intro h
    obtain ⟨c, hc, hcw⟩ := (mem_projectedCodeSubmod_iff repetitionCode Finset.univ _).mp h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
    have h0 := congrFun hcw ⟨0, Finset.mem_univ 0⟩
    have h1 := congrFun hcw ⟨1, Finset.mem_univ 1⟩
    simp [projectedWord, separatingFamily, ← ha] at h0 h1
    simp [← h0] at h1

/-- The error value is positive: the event fires on one seed out of two, and `mcaError` is a
supremum over families, so `separatingFamily` alone bounds it below. -/
theorem mcaError_repetitionCode_pos :
    0 < mcaError (AffineLineGenerator (ZMod 2)) repetitionCode (1/2 : ℝ) := by
  classical
  have hle := le_iSup
    (fun U => Pr_{let x ←$ᵖ (ZMod 2)}[IsMCA (AffineLineGenerator (ZMod 2)) repetitionCode x U
      (1/2 : ℝ)]) separatingFamily
  refine lt_of_lt_of_le ?_ hle
  rw [prob_uniform_eq_ofReal, ENNReal.ofReal_pos]
  have hcard : 0 < (Finset.univ.filter (fun x =>
      IsMCA (AffineLineGenerator (ZMod 2)) repetitionCode x separatingFamily (1/2 : ℝ))).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, isMCA_repetitionCode⟩⟩
  have hF : 0 < (Fintype.card (ZMod 2) : ℝ) := by norm_num
  positivity

/-- No threshold implication characterizes `mcaError`. At any threshold `t` strictly below the
error value — in particular at `t = 0`, by `mcaError_repetitionCode_pos` — the equivalence fails
for every threshold-side predicate `P`: the right-hand side holds because joint agreement is
unconditional over this code, while the left-hand side fails by hypothesis.

The `∀ P` is carried by the right-hand side being true here, not by an argument about `P`. What
makes the statement land on the intended target is that the correlated-agreement error, whose bad
event is `close ∧ ¬ jointAgreement`, *does* satisfy the equivalence at every threshold.

The forward implication for `mcaError` — a bound gives the threshold statement — is [BCGM25]
Lemma 3.22 and is not formalized here. -/
theorem not_mcaError_le_iff_forall_jointAgreement {t : ENNReal}
    (ht : t < mcaError (AffineLineGenerator (ZMod 2)) repetitionCode (1 / 2 : ℝ))
    (P : (Fin 2 → Fin 2 → ZMod 2) → Prop) :
    ¬ (mcaError (AffineLineGenerator (ZMod 2)) repetitionCode (1/2 : ℝ) ≤ t ↔
        ∀ U, P U → Code.jointAgreement (repetitionCode : Set (Fin 2 → ZMod 2)) (1/2 : ℝ≥0) U) :=
  fun h => absurd (h.mpr fun U _ => jointAgreement_repetitionCode U) (not_le.mpr ht)

end MCASeparation
