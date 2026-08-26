/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Recursion.TraceHandoff

/-!
# Hachi Recursion Adapters

Umbrella module for `Hachi/Recursion/`: the adapters that *would* close one Hachi opening
iteration and hand its evaluation claim to the next ring (future recursion work).

## Folder structure

* `Recursion/PartialEval.lean` — transforms the final multilinear-evaluation claim into the
  collection of partial evaluations used by the recursion step.
* `Recursion/ZBatchBridge.lean` — packs those partial evaluations into `relHatEval`.
* `Recursion/TraceHandoff.lean` — performs the guarded trace handoff into the next iteration's
  plain `QuadEval.relIn` relation. All three adapters reshape or re-read claims rather than
  introducing a new commitment, so all three are escape-free.

This umbrella re-exports the folder (`TraceHandoff` transitively imports `ZBatchBridge` and
`PartialEval`). These adapters are **not** currently composed into `Composition.lean`, whose
`iteration` ends at the multilinear-evaluation claim `relWEvalClaim` and is closed by `endPiece`;
they are staged for the future recursion step at that same seam, and `ZBatchBridge` carries a
documented soundness gap that needs a repair decision first.
-/
