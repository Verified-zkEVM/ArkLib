/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import VCVio.EvalDist.ProbabilityBounds

/-!
# Union bounds for candidates fixed before sampling

`prEvent_exists_finset_le_card_mul` bounds the probability that some index of a finite set `s`
has its event by `s.card * ε`, when each event has probability at most `ε`. The set is a parameter
outside the probability, so it cannot depend on the drawn value; these bounds say nothing about
sets chosen after sampling. `prEvent_exists_and_le_of_subsingleton` is the case of at most one
index satisfying a predicate, with bound `ε`.

Staged for VCVio: both lemmas are proposed in VCVio PR #828, next to
`prEvent_exists_le_card_mul` in `VCVio/EvalDist/ProbabilityBounds.lean`, under the same names. This
file mirrors that path and is deleted at the VCVio repin that brings them; the duplicate names then
clash, so the repin cannot keep both.
-/

@[expose] public section

open scoped ENNReal

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}

/-- Union bound over a finite index set with a uniform bound on each event. -/
theorem prEvent_exists_finset_le_card_mul {ι : Type} (s : Finset ι) (mx : m α)
    (p : ι → α → Prop) {ε : ℝ≥0∞} (h : ∀ i ∈ s, Pr{let x ← mx}[p i x] ≤ ε) :
    Pr{let x ← mx}[∃ i ∈ s, p i x] ≤ s.card * ε :=
  (prEvent_exists_finset_le s mx p).trans (by simpa using Finset.sum_le_card_nsmul s _ ε h)

/-- If at most one index satisfies `p`, and each index satisfying `p` has its event with
probability at most `ε`, then some index satisfying `p` has its event with probability at most
`ε`. The predicate `p` does not depend on the drawn value. -/
theorem prEvent_exists_and_le_of_subsingleton {ι : Type} (mx : m α) (p : ι → Prop)
    (event : ι → α → Prop) {ε : ℝ≥0∞} (hε : ∀ i, p i → Pr{let x ← mx}[event i x] ≤ ε)
    (hp : {i | p i}.Subsingleton) :
    Pr{let x ← mx}[∃ i, p i ∧ event i x] ≤ ε := by
  have hcard : hp.finite.toFinset.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦
    hp (hp.finite.mem_toFinset.mp ha) (hp.finite.mem_toFinset.mp hb)
  refine (prEvent_mono _ _ (fun x ↦ ∃ i ∈ hp.finite.toFinset, event i x)
    fun _ ⟨i, hi, h⟩ ↦ ⟨i, hp.finite.mem_toFinset.mpr hi, h⟩).trans
    ((prEvent_exists_finset_le_card_mul _ mx event
      fun i hi ↦ hε i (hp.finite.mem_toFinset.mp hi)).trans ?_)
  calc (hp.finite.toFinset.card : ℝ≥0∞) * ε ≤ (1 : ℕ) * ε := by gcongr
    _ = ε := by simp
