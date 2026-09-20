/-
Copyright (c) 2025-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import VCVio.EvalDist.Monad.Option

/-! Compatibility import for native `OptionT` event laws.

The sequencing result formerly defined here is superseded by
`OptionT.prEvent_mk_bind_eq_one_of_support`, which states prefix losslessness as the native
true-event equation and preserves the exact operational-support premise.
-/
