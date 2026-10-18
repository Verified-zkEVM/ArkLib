/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Cast

/-! # Fixed-prefix security transport: dependency regression checks -/

/-- info: 'Verifier.cast_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.cast_rbrKnowledgeSoundness

/-- info: 'OracleVerifier.cast_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.cast_rbrKnowledgeSoundness
