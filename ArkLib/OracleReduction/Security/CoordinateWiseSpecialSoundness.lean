/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition

/-!
  # Coordinate-Wise Special Soundness (CWSS)

  Re-exports the coordinate-wise special-soundness development of [FMN24] / [NOZ26]. CWSS is built
  as one instance of the protocol-generic, shape-based tree-soundness machinery in
  `Security.TranscriptTree`:

  * `Basic` — the notion: the `SS(S, ℓ, k)` combinatorics (`CoordEq`, `IsSpecialSoundFamily`), the
    intrinsic `CWSSStructure` (per-round challenge decomposition with built-in valid soundness
    parameters) and its induced `ChallengeTreeShape` (`CWSSStructure.toShape`), and the CWSS
    predicate `Verifier.coordinateWiseSpecialSound` obtained by instantiating the shape-generic core
    `Verifier.treeSpecialSound` (`Security.TranscriptTree`) at `D.toShape`.
  * `Composition` — transport of CWSS structures across sequential composition
    (`CWSSStructure.append` / `seqCompose`), their agreement with the generic appended shape
    (`toShape_append` / `toShape_seqCompose`), and preservation of CWSS under binary verifier append
    (`Verifier.append_coordinateWiseSpecialSound`) as a thin wrapper over the generic
    `Verifier.append_treeSpecialSound`.

  Plain `(k)`-special soundness is the `ℓᵢ = 1` instance (`CWSSStructure.ofSpecialSound`); see also
  `Security.SpecialSoundness`.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/
