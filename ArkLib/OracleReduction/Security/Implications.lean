/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Implications.SpecialSoundnessRewinding
import ArkLib.OracleReduction.Security.Implications.CoordinateWiseSpecialSoundnessRewinding

/-!
  # Security implications

  Re-exports the implications between security notions — one file per implication:

  * `CoordinateWiseSpecialSoundnessRewinding` — `coordinateWiseSpecialSound →
    knowledgeSoundnessRewinding`: the route-independent run-forest/tree-assembly infrastructure
    (`RunForest`, `toTree`, `WellFormed`, `WellFormed.toTree_isStructured`,
    `WellFormed.mem_toTree_fullTranscripts`). The single-shot forking implementation
    (`collectForest`, `forkBound`, the implication theorem) is **DEPRECATED and commented out**,
    superseded by the seeded-replay value-indexed exhaustive extractor (work in progress)
    targeting the additive bound `knowledgeSoundnessRewindingWithError … D.knowledgeError`.
  * `SpecialSoundnessRewinding` — the bridge `specialSound_implies_coordinateWiseSpecialSound`
    (`ℓᵢ = 1` case) is LIVE; its `knowledgeSoundnessRewinding` corollary is DEPRECATED/commented
    out alongside the single-shot CWSS implication.
-/
