/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Lean
import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase

/-!
# Binary Basefold core interaction: axioms of the composite theorems

The round-by-round knowledge soundness and the perfect completeness
of every composite of the Binary Basefold core interaction (the fold-relay and fold-commit
rounds, the non-last and last blocks, the non-last blocks in sequence, the sum-check-and-fold
rounds and the core interaction) depend only on the standard axioms, as does the bound
`sumcheckFoldKnowledgeError_le` on their total error. The composites are built from the steps,
whose theorems `Steps.lean` pins, by the guarded composition theorems and the index casts of
`OracleReduction/CastIdx.lean`; a `sorry` reaching any composite would show here.
-/

open Binius.BinaryBasefold.CoreInteraction

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[
      ``foldRelayOracleVerifier_rbrKnowledgeSoundness,
      ``foldCommitOracleVerifier_rbrKnowledgeSoundness,
      ``nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness,
      ``nonLastBlocksOracleVerifier_rbrKnowledgeSoundness,
      ``lastBlockOracleVerifier_rbrKnowledgeSoundness,
      ``sumcheckFoldOracleVerifier_rbrKnowledgeSoundness,
      ``coreInteractionOracleVerifier_rbrKnowledgeSoundness,
      ``foldRelayOracleReduction_perfectCompleteness,
      ``foldCommitOracleReduction_perfectCompleteness,
      ``nonLastSingleBlockOracleReduction_perfectCompleteness,
      ``nonLastBlocksOracleReduction_perfectCompleteness,
      ``lastBlockOracleReduction_perfectCompleteness,
      ``sumcheckFoldOracleReduction_perfectCompleteness,
      ``coreInteractionOracleReduction_perfectCompleteness,
      ``sumcheckFoldKnowledgeError_le] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "{n} depends on unexpected axioms: {axioms}"
