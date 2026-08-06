/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge

/-!
  # Coordinate-Wise Special Soundness (CWSS)

  Re-exports the coordinate-wise special-soundness development of [FMN24] / [NOZ26]. CWSS is built
  as one instance of the protocol-generic, shape-based tree-soundness machinery in
  `Security.TranscriptTree`:

  * `Basic` — the notion: the `SS(S, ℓ, k)` combinatorics (`CoordEq`, `IsSpecialSoundFamily`), the
    intrinsic `CWSSStructure` (per-round challenge decomposition with built-in valid soundness
    parameters) and its induced `ChallengeTreeShape` (`CWSSStructure.toShape`), the CWSS
    predicate `Verifier.coordinateWiseSpecialSound` obtained by instantiating the shape-generic core
    `Verifier.treeSpecialSound` (`Security.TranscriptTree`) at `D.toShape`, and its escape-threaded
    twin `Verifier.coordinateWiseSpecialSoundWithEscape`.
  * `Composition` — transport of CWSS structures across protocol append (`CWSSStructure.append`),
    its agreement with the generic appended shape (`toShape_append`), the pure-verifier acceptance
    bridge (`Verifier.pure_accepting_of_mem` / `mem_of_pure_accepting`), and preservation of CWSS
    under binary verifier append (`Verifier.append_coordinateWiseSpecialSoundWith` and
    `…WithEscape`) as thin wrappers over the generic `Verifier.append_treeSpecialSoundWith` /
    `append_treeSpecialSoundWithEscape`.
  * `NoChallenge` — the degenerate bridge for protocols with no challenge rounds
    (`IsEmpty pSpec.ChallengeIdx`): tree special soundness collapses to a transcript-level extractor
    (`Verifier.treeSpecialSoundWith_of_isEmpty_challengeIdx`).

  **Composition is deliberately binary**: multi-step chains are built by recursion over the binary
  append (the `CoordinateWise` packages' `▷`, in `CoordinateWiseSpecialSoundness/Escape.lean`),
  which keeps the composed extractor a nameable function instead of a transport across an `n`-ary
  shape identity. The protocol-level `ProtocolSpec.seqCompose` is unaffected.

  Plain `(k)`-special soundness is the `ℓᵢ = 1` instance (`CWSSStructure.ofSpecialSound`); see also
  `Security.SpecialSoundness`.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/
