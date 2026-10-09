/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps

/-!
# Binary Basefold steps: axioms of the leaf theorems

The worst-case round-by-round knowledge soundness and the perfect completeness of the four
Binary Basefold steps (fold, commit, relay, final sum-check) at their own extractors,
knowledge-state functions and errors depend only on the standard axioms. The core interaction
composes these leaves, so a `sorry` reaching any of them would taint every composite.
-/

open Binius.BinaryBasefold.CoreInteraction

/-! The two longest leaf names are checked through short aliases, whose axioms are those of the
aliased theorems. -/

/-- `commitOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.commitWorstCaseWith :=
  commitOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith

/-- `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.finalSumcheckWorstCaseWith :=
  finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith

/--
info: 'Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  foldOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith

/--
info: 'ArkLibTest.Binius.BinaryBasefold.commitWorstCaseWith'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.commitWorstCaseWith

/--
info: 'Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  relayOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith

/--
info: 'ArkLibTest.Binius.BinaryBasefold.finalSumcheckWorstCaseWith'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.finalSumcheckWorstCaseWith

/--
info: 'Binius.BinaryBasefold.CoreInteraction.foldOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  foldOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.commitOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  commitOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.relayOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  relayOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  finalSumcheckOracleReduction_perfectCompleteness
