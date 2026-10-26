/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.FoldDistance
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.BadBlocks
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryRejection
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness

/-!
# Binary Basefold: the soundness bounds

The probability bounds behind the round-by-round knowledge soundness of Binary Basefold:

* `Soundness.Lift` and `Soundness.Incremental`: the per-challenge bound on the incremental
  folding bad event, which the fold step consumes;
* `Soundness.FoldDistance`: the distance of the fold of a noncompliant oracle from the next
  decoded codeword;
* `Soundness.QueryPhasePrelims`, `Soundness.BadBlocks`, `Soundness.QueryRejection` and
  `Soundness.QueryPhaseSoundness`: the query-phase check and the bound on the acceptance
  probability of one query repetition, which the query phase consumes.
-/

@[expose] public section
