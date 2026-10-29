/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Lean
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps

/-!
# Binary Basefold steps: axioms of the leaf theorems

The round-by-round knowledge soundness and the perfect completeness of the four
Binary Basefold steps (fold, commit, relay, final sum-check) at their own extractors,
knowledge-state functions and errors depend only on the standard axioms. The core interaction
composes these leaves, so a `sorry` reaching any of them would taint every composite.
-/

open Binius.BinaryBasefold.CoreInteraction

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[
      ``foldOracleVerifier_rbrKnowledgeSoundnessWith,
      ``commitOracleVerifier_rbrKnowledgeSoundnessWith,
      ``relayOracleVerifier_rbrKnowledgeSoundnessWith,
      ``finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith,
      ``foldOracleReduction_perfectCompleteness,
      ``commitOracleReduction_perfectCompleteness,
      ``relayOracleReduction_perfectCompleteness,
      ``finalSumcheckOracleReduction_perfectCompleteness] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "{n} depends on unexpected axioms: {axioms}"
