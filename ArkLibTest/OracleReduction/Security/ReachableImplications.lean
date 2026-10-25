/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Security.ReachableImplications

/-! # Arbitrary-state empty-oracle implication clients

These clients retain the caller's initialization and handler, including non-singleton state.
The shared-state counterexample is separately rejected in `RbrSharedState`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace ReachableImplicationTests

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

def verifier : Verifier []ₒ Bool Bool !p[] := ⟨fun stmt _ => pure stmt⟩

def relation : Set (Bool × Unit) := { ⟨stmt, _⟩ | stmt = true }

def extractor : Extractor.RoundByRound []ₒ Bool Unit Unit !p[] (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun m => nomatch m
  extractOut := fun _ _ witOut => witOut

def knowledgeState : verifier.KnowledgeStateFunction init impl relation relation extractor where
  toFun := fun _ stmt _ _ => stmt = true
  toFun_empty := by intros; rfl
  toFun_next := fun m => nomatch m
  toFun_full := by
    intro stmt tr wit h
    simp only [Fin.val_last, gt_iff_lt, OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨out, hout, hrel⟩ := h
    change some out ∈ support (do
      (simulateQ impl (pure (some stmt))).run' (← init)) at hout
    simp only [simulateQ_pure, StateT.run'_pure'] at hout
    obtain ⟨_, _, hout⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq : out = stmt := by simpa using hout
    exact heq.symm.trans hrel

theorem rbr : verifier.rbrKnowledgeSoundness init impl relation relation (fun _ => 0) := by
  refine ⟨fun _ => Unit, extractor, knowledgeState init impl, ?_⟩
  intro stmt wit prover i
  exact Fin.elim0 i.1

theorem arbitrary_state_knowledgeSoundness :
    verifier.knowledgeSoundness init impl relation relation 0 := by
  simpa using Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_empty
    init impl relation relation verifier (fun _ => 0) (rbr init impl)

example (handler : QueryImpl []ₒ (StateT Bool ProbComp)) :
    verifier.knowledgeSoundness ($ᵗ Bool) handler relation relation 0 :=
  arbitrary_state_knowledgeSoundness _ handler

end ReachableImplicationTests

/-- info: 'Verifier.rbrSoundness_implies_soundness_of_reachable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrSoundness_implies_soundness_of_reachable

/-- info: 'Verifier.rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith_of_reachable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundnessWith_implies_knowledgeSoundnessWith_of_reachable
