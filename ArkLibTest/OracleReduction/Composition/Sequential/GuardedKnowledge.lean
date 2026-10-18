/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.KnowledgeState
import ArkLib.OracleReduction.Composition.Sequential.GuardedKnowledge

/-!
# Guarded composition boundary checks

No admitted composition contract is needed to identify the shared-state boundary or transport
an accepting guarded output into the first component's knowledge state.
-/

/-- info: 'Verifier.seqCompose_append_rbrKnowledgeSoundness_of_guarded_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.seqCompose_append_rbrKnowledgeSoundness_of_guarded_prefix

/-- info: 'Verifier.append_run_stateful' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_run_stateful

/-- info: 'Verifier.append_accepting_support_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_accepting_support_iff

/-- info: 'Verifier.GuardedForm.related_output_pos_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.related_output_pos_iff

/-- info: 'Verifier.GuardedForm.knowledgeState_of_related_output' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.knowledgeState_of_related_output

/-- info: 'Verifier.GuardedForm.append_related_output_pos_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.append_related_output_pos_iff

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_zero

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_full' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_full

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_next_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_next_left

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_next_seam' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_next_seam

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_next_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_next_right

/-- info: 'Verifier.KnowledgeStateFunction.appendGuarded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendGuarded

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_badEvent_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_badEvent_left

/-- info: 'Verifier.KnowledgeStateFunction.appendGuarded_bound_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendGuarded_bound_left

/-- info: 'Verifier.KnowledgeStateFunction.appendPredicate_badEvent_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendPredicate_badEvent_right

/-- info: 'Verifier.KnowledgeStateFunction.appendGuarded_bound_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.appendGuarded_bound_right

/-- info: 'Verifier.append_rbrKnowledgeSoundness_of_guarded_first' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundness_of_guarded_first

/-- info: 'Verifier.append_rbrKnowledgeSoundnessAveraged_of_guarded_first' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundnessAveraged_of_guarded_first

/-- info: 'Verifier.seqCompose_rbrKnowledgeSoundness_of_guarded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness_of_guarded

/-- info: 'Verifier.seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded

/-- info: 'OracleVerifier.seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded

/-- info: 'OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first

/-- info: 'OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_guarded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_guarded
