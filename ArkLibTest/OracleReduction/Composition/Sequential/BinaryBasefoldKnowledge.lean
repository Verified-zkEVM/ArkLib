/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Protocol
import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase.Security
import ArkLib.ProofSystem.Binius.BinaryBasefold.General

/-! # Binary Basefold guarded-composition dependency checks -/

/-- info:
'Binius.BinaryBasefold.CoreInteraction.foldRelayOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.BinaryBasefold.CoreInteraction.foldRelayOracleVerifier_rbrKnowledgeSoundness

/-- info:
'Binius.BinaryBasefold.CoreInteraction.foldCommitOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.BinaryBasefold.CoreInteraction.foldCommitOracleVerifier_rbrKnowledgeSoundness

/-- info:
'Binius.BinaryBasefold.CoreInteraction.lastBlockOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.BinaryBasefold.CoreInteraction.lastBlockOracleVerifier_rbrKnowledgeSoundness

/-- info:
'Binius.BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness

/-- info:
'Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness

/-- info: 'Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness
