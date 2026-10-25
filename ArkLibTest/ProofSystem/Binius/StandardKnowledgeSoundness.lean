/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch

/-! # Kernel trust for the standard knowledge-soundness specializations -/

open Binius.BinaryBasefold.FullBinaryBasefold

/-- info: 'Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullOracleVerifier_knowledgeSoundness

/-- info: 'RingSwitching.Packing.TensorPrefix.knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.TensorPrefix.knowledgeSoundness

/-- info: 'Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness
