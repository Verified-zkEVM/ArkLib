/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.StatefulKnowledge

/-! Dependency checks for composition and extraction at actual shared states. -/

open OracleComp OracleSpec ProtocolSpec

namespace StatefulRefinementExample

abbrev spec : OracleSpec Unit := Unit →ₒ Unit

def impl : QueryImpl spec (StateT Bool ProbComp) := fun _ => do
  modify Bool.not
  pure ()

abbrev wire : ProtocolSpec 0 := !p[]

def reference : Verifier spec Bool Bool wire := Verifier.id

def guarded : reference.GuardedForm :=
  ⟨fun _ _ => true, fun stmt _ => stmt, fun _ _ => rfl⟩

/-- Identity on statements, but flips the shared oracle bit. -/
def actual : Verifier spec Bool Bool wire := ⟨fun stmt _ => OptionT.mk do
  let _ ← (query (spec := spec) () : OracleComp spec Unit)
  pure (some stmt)⟩

theorem changes_state (stmt : Bool) (tr : wire.FullTranscript) (s : Bool) :
    (simulateQ impl (actual.run stmt tr).run).run s = pure (some stmt, !s) := rfl

theorem refines : guarded.AcceptingRefinement impl actual := by
  intro stmt tr s out hout
  have heq : out = stmt := by
    change some out ∈ support (pure (some stmt) : ProbComp (Option Bool)) at hout
    simpa using hout
  exact ⟨rfl, heq⟩

/-- Nontrivial input relation: the statement must equal its witness. -/
theorem secure : actual.knowledgeSoundness (pure false) impl
    {x : Bool × Bool | x.1 = x.2} {x : Bool × Bool | x.1 = x.2} 0 := by
  have h := Verifier.knowledgeSoundness_of_acceptingRefinement
    (pure false) impl guarded refines
    (Verifier.id_rbrKnowledgeSoundness (pure false) impl {x : Bool × Bool | x.1 = x.2})
  simpa only [Pi.zero_apply, Finset.sum_const_zero] using h

end StatefulRefinementExample

/-- info: 'OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement

/-- info: 'OracleVerifier.knowledgeSoundness_of_acceptingRefinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.knowledgeSoundness_of_acceptingRefinement

/-- info: 'StatefulRefinementExample.secure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StatefulRefinementExample.secure


/-- info: 'Verifier.GuardedForm.AcceptingRefinement.append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.AcceptingRefinement.append

/-- info: 'Verifier.GuardedForm.AcceptingRefinement.seqCompose'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.AcceptingRefinement.seqCompose

/-- info: 'Verifier.append_rbrKnowledgeSoundness_of_acceptingRefinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundness_of_acceptingRefinement

/-- info: 'Verifier.seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement

/-- info: 'Verifier.knowledgeSoundness_of_acceptingRefinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.knowledgeSoundness_of_acceptingRefinement

/-- info: 'Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_of_full_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness_of_full_support

/-- info:
'Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_support_closed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_support_closed
