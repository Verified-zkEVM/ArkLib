/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase
import ArkLib.ProofSystem.RingSwitching.Packing.General
import ArkLib.ProofSystem.RingSwitching.Packing.BBFSmallFieldIOPCS

/-!
# Ring-switching composition dependency regression

The sumcheck core uses proved guarded composition, not the admitted unrestricted contracts.
-/

/-- info: 'RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness

/-- info: 'RingSwitching.FullRingSwitching.batchingCore_rbrKnowledgeSoundness_fixedPrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.FullRingSwitching.batchingCore_rbrKnowledgeSoundness_fixedPrefix

/-- info: 'RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness_fixedPrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness_fixedPrefix

/-- info: 'RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness

/-- info:
'Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleVerifier_rbrKnowledgeSoundness

/-- info: 'Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleVerifier_knowledgeSoundness
