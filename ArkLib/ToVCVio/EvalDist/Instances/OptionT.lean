/-
Copyright (c) 2025-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/

import VCVio.EvalDist.Instances.OptionT
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbComp
/-! # Additions to VCV-io's `EvalDist.Instances.OptionT`

(Also a compatibility import for earlier additions that now live in VCVio.) -/

open OracleComp

/-- **Event-probability-one propagates through a bind under `OptionT.mk`**: if the (option-free)
prefix never fails and every branch is an event-probability-one `OptionT` computation, so is the
bound computation. This is the sequencing step for games of the form
"sample keys/setup, then play a sub-game that is perfect for every outcome of the setup"
(e.g. `Commitment.perfectCorrectness_of_opening_perfectCompleteness`). Stated over `ProbComp`;
the proof is monad-generic modulo the failure/support characterizations used. -/
lemma OptionT.probEvent_eq_one_bind {α β : Type} {oa : ProbComp α}
    {f : α → ProbComp (Option β)} {P : β → Prop}
    (h1 : NeverFail oa)
    (h2 : ∀ a ∈ support oa, Pr[ P | OptionT.mk (f a)] = 1) :
    Pr[ P | OptionT.mk (oa >>= f)] = 1 := by
  have h2' : ∀ a ∈ support oa, Pr[⊥ | OptionT.mk (f a)] = 0 ∧
      ∀ x ∈ support (OptionT.mk (f a)), P x :=
    fun a ha => probEvent_eq_one_iff.mp (h2 a ha)
  have hfail : ∀ a ∈ support oa, Pr[⊥ | f a] = 0 ∧ Pr[= none | f a] = 0 := by
    intro a ha
    have h := (h2' a ha).1
    rw [OptionT.probFailure_eq, OptionT.run_mk] at h
    exact add_eq_zero.mp h
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk, add_eq_zero]
    refine ⟨?_, ?_⟩
    · rw [probFailure_eq_zero_iff, neverFail_bind_iff]
      exact ⟨h1, fun a ha => (probFailure_eq_zero_iff _).mp (hfail a ha).1⟩
    · rw [probOutput_eq_zero_iff]
      intro hnone
      rw [mem_support_bind_iff] at hnone
      obtain ⟨a, ha, hnone⟩ := hnone
      exact (probOutput_eq_zero_iff _ _).mp (hfail a ha).2 hnone
  · intro x hx
    obtain ⟨a, ha, hx⟩ := OptionT.mem_support_bind_mk oa f hx
    exact (h2' a ha).2 x hx
