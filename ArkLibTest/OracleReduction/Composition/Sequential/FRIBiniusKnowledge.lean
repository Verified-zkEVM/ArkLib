/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.FRIBinius.General

/-!
# FRI-Binius composition dependency regression

The headline guarantees must not depend on admitted framework composition results.
-/

/-- info: 'Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness_fixedPrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness_fixedPrefix

/-- info: 'Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness

/-- info: 'Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_knowledgeSoundness
