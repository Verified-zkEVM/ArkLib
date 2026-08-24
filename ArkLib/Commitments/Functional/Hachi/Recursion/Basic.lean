/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Recursion.TraceHandoff

/-!
# Hachi Recursion Adapters

Umbrella module for `Hachi/Recursion/`: the adapters that close one Hachi opening iteration and
hand its evaluation claim to the next ring.

## Folder structure

* `Recursion/PartialEval.lean` — transforms the final multilinear-evaluation claim into the
  collection of partial evaluations used by the recursion step.
* `Recursion/ZBatchBridge.lean` — packs those partial evaluations into `relHatEval`.
* `Recursion/TraceHandoff.lean` — performs the guarded trace handoff into the next iteration's
  plain `QuadEval.relIn` relation. All three adapters reshape or re-read claims rather than
  introducing a new commitment, so all three are escape-free.

This umbrella re-exports the folder (`TraceHandoff` transitively imports `ZBatchBridge` and
`PartialEval`). The full guarded chain is composed in the sibling `Composition.lean`.
-/
