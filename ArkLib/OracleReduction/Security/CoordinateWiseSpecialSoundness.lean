/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.CoordinateOracle
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ForkOracle

/-!
  # Coordinate-Wise Special Soundness (CWSS)

  Re-exports the coordinate-wise special-soundness development of [FMN24] / [NOZ26]:

  * `Basic` — the notion: the `SS(S, ℓ, k)` combinatorics (`CoordEq`, `IsSpecialSoundFamily`), the
    `CWSSStructure` (per-round challenge decomposition + soundness parameters), the structured-tree
    predicate `ChallengeTree.IsStructured`, the predicate `Verifier.coordinateWiseSpecialSound`, and
    the reference knowledge error `CWSSStructure.knowledgeError`.
  * `CoordinateOracle` — the coordinate-indexed challenge oracle
    `CWSSStructure.coordChallengeOracle` (the per-coordinate execution substrate), with Bridge 1
    (`challenge_uniform_eq_bundle_coords`).
  * `ForkOracle` — the fork oracle `CWSSStructure.forkOracle` (the rewinding extractor's
    interface: fork a parent run at one challenge coordinate, receive a sibling run), its concrete
    implementation `CWSSStructure.cwssForkImpl` by indexed replay, and the structural fork
    guarantees (`cwssForkImpl_coordEq`, `cwssForkImpl_prefix_eq`).

  The CWSS ⇒ rewinding-knowledge-soundness implication (tree builder, extraction bound) lives in
  `Security.Implications.CoordinateWiseSpecialSoundnessRewinding`; plain `(k)`-special soundness is
  `Security.SpecialSoundness`.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/
