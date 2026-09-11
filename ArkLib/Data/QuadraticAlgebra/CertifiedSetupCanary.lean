/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.CertifiedSetup

/-!
# Observed setup values survive proof-erased certification

The wrapper retains the actual nonsquare, base alphabet, crossing sample prefix and full ledger.
The large correctness proof does not alter any runtime value or select a replacement witness.
-/

@[expose] public section

namespace QuadraticAlgebra.SetupMachine

private def prepared := certifiedRun (q := 3) 4 (by decide) (by decide) (by decide)

example : (prepared.parameter, prepared.data.base, prepared.data.baseCount,
    prepared.data.extensionCount, prepared.data.sampleCount, prepared.cost) =
      (2, [0, 1, 2], 3, 9, 4, ⟨26, 9, 21, 84, 46, 293, 846, 5⟩) := by decide +kernel

theorem certified_setup_preserves_sample_prefix :
    let prepared := certifiedRun (q := 3) 4 (by decide) (by decide) (by decide)
    (prepared.data.samples.map fun x ↦ (x.re, x.im)) =
    [(0, 0), (0, 1), (0, 2), (1, 0)] := by decide +kernel

end QuadraticAlgebra.SetupMachine
