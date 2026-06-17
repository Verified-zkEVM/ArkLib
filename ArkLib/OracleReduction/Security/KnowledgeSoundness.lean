/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Rewinding

/-!
  # Knowledge Soundness

  Re-exports ArkLib's knowledge-soundness notions:

  * **Straightline** — `Verifier.knowledgeSoundness` (from `Security.Basic`): the extractor sees a
    single prover run (transcript + query logs) and cannot rewind.
  * **Rewinding** — `Verifier.knowledgeSoundnessRewinding` (from `Rewinding`):
    the extractor has black-box, type-enforced access to a fork oracle `F`, parameterized so both
    plain special soundness and coordinate-wise special soundness can target it.

  The soundness ⇒ knowledge-soundness implications live in `Security.Implications`.
-/
