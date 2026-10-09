/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase

/-!
# Binary Basefold core interaction: axioms of the composite theorems

The worst-case round-by-round knowledge soundness, its averaged form and the perfect completeness
of every composite of the Binary Basefold core interaction (the fold-relay and fold-commit
rounds, the non-last and last blocks, the non-last blocks in sequence, the sum-check-and-fold
rounds and the core interaction) depend only on the standard axioms, as does the bound
`sumcheckFoldKnowledgeError_le` on their total error. The composites are built from the steps,
whose theorems `Steps.lean` pins, by the guarded composition theorems and the index casts of
`OracleReduction/CastIdx.lean`; a `sorry` reaching any composite would show here.
-/

open Binius.BinaryBasefold.CoreInteraction

/-! Names too long for one line are checked through short aliases, whose axioms are those of the
aliased theorems. -/

/-- `foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.foldRelayWorstCase :=
  foldRelayOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `foldCommitOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.foldCommitWorstCase :=
  foldCommitOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockWorstCase :=
  nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.nonLastBlocksWorstCase :=
  nonLastBlocksOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.lastBlockWorstCase :=
  lastBlockOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.sumcheckFoldWorstCase :=
  sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `coreInteractionOracleVerifier_rbrKnowledgeSoundnessWorstCase`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.coreInteractionWorstCase :=
  coreInteractionOracleVerifier_rbrKnowledgeSoundnessWorstCase

/-- `nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockAveraged :=
  nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness

/-- `coreInteractionOracleVerifier_rbrKnowledgeSoundness`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.coreInteractionAveraged :=
  coreInteractionOracleVerifier_rbrKnowledgeSoundness

/-- `nonLastSingleBlockOracleReduction_perfectCompleteness`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockCompleteness :=
  nonLastSingleBlockOracleReduction_perfectCompleteness

/-- `coreInteractionOracleReduction_perfectCompleteness`, under a short name. -/
alias ArkLibTest.Binius.BinaryBasefold.coreInteractionCompleteness :=
  coreInteractionOracleReduction_perfectCompleteness

/--
info: 'ArkLibTest.Binius.BinaryBasefold.foldRelayWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.foldRelayWorstCase

/--
info: 'ArkLibTest.Binius.BinaryBasefold.foldCommitWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.foldCommitWorstCase

/--
info: 'ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockWorstCase

/--
info: 'ArkLibTest.Binius.BinaryBasefold.nonLastBlocksWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.nonLastBlocksWorstCase

/--
info: 'ArkLibTest.Binius.BinaryBasefold.lastBlockWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.lastBlockWorstCase

/--
info: 'ArkLibTest.Binius.BinaryBasefold.sumcheckFoldWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.sumcheckFoldWorstCase

/--
info: 'ArkLibTest.Binius.BinaryBasefold.coreInteractionWorstCase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.coreInteractionWorstCase

/--
info: 'Binius.BinaryBasefold.CoreInteraction.foldRelayOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  foldRelayOracleVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.foldCommitOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  foldCommitOracleVerifier_rbrKnowledgeSoundness

/--
info: 'ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockAveraged'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockAveraged

/--
info: 'Binius.BinaryBasefold.CoreInteraction.nonLastBlocksOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  nonLastBlocksOracleVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.lastBlockOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  lastBlockOracleVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  sumcheckFoldOracleVerifier_rbrKnowledgeSoundness

/--
info: 'ArkLibTest.Binius.BinaryBasefold.coreInteractionAveraged'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.coreInteractionAveraged

/--
info: 'Binius.BinaryBasefold.CoreInteraction.foldRelayOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  foldRelayOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.foldCommitOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  foldCommitOracleReduction_perfectCompleteness

/--
info: 'ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.nonLastSingleBlockCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.nonLastBlocksOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  nonLastBlocksOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.lastBlockOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  lastBlockOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction_perfectCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  sumcheckFoldOracleReduction_perfectCompleteness

/--
info: 'ArkLibTest.Binius.BinaryBasefold.coreInteractionCompleteness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ArkLibTest.Binius.BinaryBasefold.coreInteractionCompleteness

/--
info: 'Binius.BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  sumcheckFoldKnowledgeError_le
