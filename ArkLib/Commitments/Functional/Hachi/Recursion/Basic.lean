/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Recursion.TraceHandoff

/-!
# Hachi Recursion Adapters

Umbrella module for `Hachi/Recursion/`: the [NOZ26] §4.5 adapters that carry one opening
iteration's evaluation claim to the next ring, so that several iterations can precede a single
end-piece.

**These adapters are outside the completed development.** They are not composed into
`Composition.lean`, whose `iteration` ends at `relWEvalClaim` and is closed by `endPiece`, and
they carry `sorry`s. `Recursion/ZBatchBridge.lean` additionally records a soundness gap in the
paper's own argument for Eq. (26); its module docstring gives the counterexample. Since any
repair of that step changes the protocol content of all three adapters, they are left as stated.

## Folder structure

* `Recursion/PartialEval.lean` — transforms the final multilinear-evaluation claim into the
  collection of partial evaluations used by the recursion step.
* `Recursion/ZBatchBridge.lean` — packs those partial evaluations into `relHatEval`.
* `Recursion/TraceHandoff.lean` — performs the guarded trace handoff into the next iteration's
  plain `QuadEval.relIn` relation.

All three reshape or re-read claims rather than introducing a new commitment, so all three are
escape-free. This umbrella re-exports the folder (`TraceHandoff` transitively imports
`ZBatchBridge` and `PartialEval`).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
