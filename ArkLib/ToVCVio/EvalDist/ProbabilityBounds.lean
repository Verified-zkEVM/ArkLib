/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import VCVio.EvalDist.ProbabilityBounds

/-!
# Union bounds for candidates fixed before sampling

A finite set of candidates is fixed before a value is drawn from a computation `mx`. Each
candidate is either correct or incorrect, and each has an event over the drawn value. If every
incorrect candidate's event has probability at most `ε`, then some incorrect candidate of a set of
at most `L` candidates has its event with probability at most `L * ε`
(`prEvent_exists_mem_and_le_mul`). Correct candidates need no bound and do not enter the event.
When at most one candidate is valid, the bound is `ε` (`prEvent_exists_and_and_le_of_subsingleton`).

The set of candidates is a parameter outside the probability, so it cannot depend on the drawn
value. These bounds say nothing about candidate sets chosen after sampling.

Staged for VCVio: both lemmas are proposed in VCVio PR #828, next to
`prEvent_exists_le_card_mul` in `VCVio/EvalDist/ProbabilityBounds.lean`, under the same names. This
file mirrors that path and is deleted at the VCVio repin that brings them; the duplicate names then
clash, so the repin cannot keep both.
-/

@[expose] public section

open scoped ENNReal

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α ι : Type}

/-- **Bounded candidate-list union bound.** Let `S` be a finite set of at most `L` candidates
that does not depend on the value drawn from `mx`. If each incorrect candidate of `S` has its
event of probability at most `ε`, then some incorrect candidate of `S` has its event with
probability at most `L * ε`. Correct candidates need no bound and do not enter the event. -/
theorem prEvent_exists_mem_and_le_mul (mx : m α)
    (incorrect : ι → Prop) (event : ι → α → Prop) {ε : ℝ≥0∞} (S : Finset ι)
    (hε : ∀ i ∈ S, incorrect i → Pr{let x ← mx}[event i x] ≤ ε)
    {L : ℕ} (hS : S.card ≤ L) :
    Pr{let x ← mx}[∃ i ∈ S, incorrect i ∧ event i x] ≤ L * ε :=
  calc
    _ ≤ ∑ i ∈ S, Pr{let x ← mx}[incorrect i ∧ event i x] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _i ∈ S, ε := Finset.sum_le_sum fun i hiS => by
      by_cases hi : incorrect i
      · exact (prEvent_mono _ _ _ fun _ h => h.2).trans (hε i hiS hi)
      · rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => hi h.1]
        exact bot_le
    _ ≤ L * ε := by
      rw [Finset.sum_const, nsmul_eq_mul]
      gcongr

/-- **Exact-functional union bound**, the `L = 1` case of `prEvent_exists_mem_and_le_mul`. If at
most one candidate satisfies `valid` (a predicate independent of the drawn value) and each valid
incorrect candidate has its event of probability at most `ε`, then some valid incorrect candidate
has its event with probability at most `ε`. -/
theorem prEvent_exists_and_and_le_of_subsingleton (mx : m α)
    (valid incorrect : ι → Prop) (event : ι → α → Prop) {ε : ℝ≥0∞}
    (hε : ∀ i, valid i → incorrect i → Pr{let x ← mx}[event i x] ≤ ε)
    (hvalid : {i | valid i}.Subsingleton) :
    Pr{let x ← mx}[∃ i, valid i ∧ incorrect i ∧ event i x] ≤ ε := by
  have hS : hvalid.finite.toFinset.card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb =>
      hvalid (hvalid.finite.mem_toFinset.mp ha) (hvalid.finite.mem_toFinset.mp hb)
  refine (prEvent_mono _ _ (fun x => ∃ i ∈ hvalid.finite.toFinset, incorrect i ∧ event i x)
    fun _ ⟨i, hi, h⟩ => ⟨i, hvalid.finite.mem_toFinset.mpr hi, h⟩).trans ?_
  simpa using prEvent_exists_mem_and_le_mul mx incorrect event _
    (fun i hi => hε i (hvalid.finite.mem_toFinset.mp hi)) hS
