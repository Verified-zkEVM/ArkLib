/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Knowledge

/-!
# Product sumcheck on one committed multilinear polynomial

For a public multilinear multiplier `A` and a committed multilinear polynomial `p`, scalar
rounds reduce the Boolean sum of `A · p` to `A(r) · v`. The terminal check preserves the public
context and leaves `v = p(r)` as the opening relation on the original commitment.
-/

@[expose] public section
