/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.Knowledge
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-! The corrected round's security proof must not use the legacy admitted theorems. -/

/-- info:
'Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundnessAveraged' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundnessAveraged

/-- info: 'Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundnessAveraged'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundnessAveraged

/-- info: 'Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundnessAveraged' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundnessAveraged

/-- info:
'Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundnessAveraged' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundnessAveraged

/-- info: 'Sumcheck.Spec.SingleRound.Simple.verifier_fixedPrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.Simple.verifier_fixedPrefix

/-- info: 'Sumcheck.Spec.SingleRound.Simple.oracleVerifier_fixedPrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_fixedPrefix

/-- info: 'Sumcheck.Spec.SingleRound.projected_input_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.projected_input_iff

/-- info: 'Sumcheck.Spec.SingleRound.projected_output_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.SingleRound.projected_output_iff

/-- info: 'Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundnessAveraged'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundnessAveraged
