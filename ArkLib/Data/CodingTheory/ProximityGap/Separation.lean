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
implication for mutual correlated agreement. `separation` below is the witness, so that claim is
checked by the build rather than asserted in a document.

## Main statements

* `jointAgreement_repetitionCode` — over `rep`, at radius `1/2`, *every* family jointly agrees, so
  every threshold implication about `jointAgreement` holds vacuously at any threshold.
* `isMCA_repetitionCode` — the MCA event nevertheless fires, at the seed `0` and the family
  `witness`.
* `separation` — the two hold together. Hence `IsMCA` does not imply failure of joint agreement,
  and no threshold statement about `jointAgreement` can characterise `mcaError`.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace MCASeparation

open CoreDefinitions LinearCode
open scoped NNReal ENNReal

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The repetition code `{(a, a)} ⊆ (ZMod 2)²`, as a module code over itself. Chosen because its
projection onto either single coordinate is everything, which is what makes joint agreement at
radius `1/2` unconditional. -/
noncomputable def rep : ModuleCode (Fin 2) (ZMod 2) (ZMod 2) :=
  Submodule.span (ZMod 2) {(fun _ => 1 : Fin 2 → ZMod 2)}

/-- The separating family: `U 0 = (0, 0)` is a codeword, `U 1 = (1, 0)` is not. -/
noncomputable def witness : Fin 2 → (Fin 2 → ZMod 2) := ![(fun _ => 0), ![1, 0]]

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

/-- **The separation.** The MCA bad event and joint agreement hold simultaneously, so `IsMCA` does
not imply `¬ jointAgreement`.

Hence no threshold implication about `jointAgreement` can be *equivalent* to a bound on
`mcaError`: over this code every such implication holds at every threshold, while the MCA event has
positive probability. The implication from an `mcaError` bound to the threshold statement does
hold, and in that direction alone the bridge is available. -/
theorem separation :
    IsMCA (AffineLineGenerator (ZMod 2)) rep (0 : ZMod 2) witness (1/2 : ℝ) ∧
      Code.jointAgreement (rep : Set (Fin 2 → ZMod 2)) (1/2 : ℝ≥0) witness :=
  ⟨isMCA_repetitionCode, jointAgreement_repetitionCode witness⟩

end MCASeparation
