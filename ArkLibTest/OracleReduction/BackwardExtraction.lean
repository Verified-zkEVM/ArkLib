/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.BackwardExtraction
import ArkLib.OracleReduction.Security.GuardedTerminal
import ArkLib.OracleReduction.Security.ExecutionPrefix
import ArkLib.OracleReduction.Security.ExecutionBadTransitions
import ArkLib.OracleReduction.Security.ActualExtraction
import ArkLib.OracleReduction.Security.Implications

/-! Axiom checks for backward extraction and the bad-transition union bound. -/

/-- info:
'Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_invariant

/-- info:
'Verifier.KnowledgeStateFunction.terminal_of_mem_init_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.terminal_of_mem_init_support

/-- info:
'Verifier.KnowledgeStateFunction.terminalFromEveryState_of_full_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.terminalFromEveryState_of_full_support
/-- info: 'Extractor.RoundByRound.toStraightline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Extractor.RoundByRound.toStraightline

/-- info:
'Verifier.KnowledgeStateFunction.exists_bad_challenge_of_extract_failure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.exists_bad_challenge_of_extract_failure

/-- info: 'Verifier.KnowledgeStateFunction.exists_badChallengeOnTranscript_of_extract_failure'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Verifier.KnowledgeStateFunction.exists_badChallengeOnTranscript_of_extract_failure

/-- info:
'Verifier.KnowledgeStateFunction.extraction_failure_le_sum_badChallenges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.extraction_failure_le_sum_badChallenges

/-- info: 'Verifier.GuardedForm.terminalFromEveryState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.terminalFromEveryState

/-- info: 'Prover.simulate_processRound_preserves_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulate_processRound_preserves_prefix

/-- info: 'Prover.simulate_processRound_prefix_event' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulate_processRound_prefix_event

/-- info: 'Prover.simulate_processRound_prefix_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulate_processRound_prefix_probability

/-- info: 'Prover.simulate_runToRound_prefix_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulate_runToRound_prefix_probability

/-- info: 'Prover.simulate_fullRun_challenge_prefix_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulate_fullRun_challenge_prefix_probability

/-- info: 'Verifier.KnowledgeStateFunction.badChallenge_probability_le_of_rbr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.badChallenge_probability_le_of_rbr

/-- info:
'Verifier.KnowledgeStateFunction.exists_badChallenge_probability_le_sum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.exists_badChallenge_probability_le_sum

/-- info: 'Prover.simulate_run_transcript_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulate_run_transcript_probability

/-- info:
'Verifier.KnowledgeStateFunction.verifier_failure_probability_eq_zero_of_no_badChallenge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Verifier.KnowledgeStateFunction.verifier_failure_probability_eq_zero_of_no_badChallenge

/-- info: 'Verifier.KnowledgeStateFunction.reduction_failure_le_sum_of_rbr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.KnowledgeStateFunction.reduction_failure_le_sum_of_rbr

/-- info:
'Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_terminal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_terminal

/-- info:
'Verifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded

/-- info: 'OracleVerifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  OracleVerifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded

/-- info: 'Verifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness

/-- info:
'Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Verifier.rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable
