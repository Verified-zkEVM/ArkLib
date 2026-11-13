/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Completeness
public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Soundness

/-!
# Binary Basefold query phase

The oracle-query verifier and honest prover, strict-input perfect completeness, and
round-by-round knowledge soundness. Pure query mathematics is owned by `Soundness/`.
-/

@[expose] public section
