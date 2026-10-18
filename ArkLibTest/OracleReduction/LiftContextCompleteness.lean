/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# Completeness transport does not require admitted context-lifting results

These guards also check the execution-transport dependencies of the proof.
-/

/-- info: 'Reduction.liftContext_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.liftContext_completeness

/-- info: 'Reduction.liftContext_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.liftContext_perfectCompleteness

/-- info: 'Extractor.RoundByRound.liftContext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Extractor.RoundByRound.liftContext

/-- info: 'Verifier.liftContext_rbr_knowledgeSoundnessAveraged' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.liftContext_rbr_knowledgeSoundnessAveraged

/-- info: 'OracleReduction.liftContext_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.liftContext_completeness

/-- info: 'OracleVerifier.liftContext_rbr_knowledgeSoundnessAveraged' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.liftContext_rbr_knowledgeSoundnessAveraged

/-- info: 'Verifier.liftContext_rbr_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.liftContext_rbr_knowledgeSoundness

/-- info: 'OracleVerifier.liftContext_rbr_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.liftContext_rbr_knowledgeSoundness
