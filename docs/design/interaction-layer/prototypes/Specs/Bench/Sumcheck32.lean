/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench

/-!
# Bench case: sum-check with 32 rounds, tree and accessors

The tree agreement by `rfl` and one accessor by label at the first and at the last round, for
`sumcheckSpec ℚ 2 32 D`. The skeleton export is a separate case (`Specs.Bench.Export*`). See
`Specs.Bench`.
-/

namespace Specs.Bench.Sumcheck32
open Interaction

/-- The tree agreement, by `rfl`. -/
theorem tree_eq : Spec.tree (sumcheckSpec ℚ 2 32 D) = Sumcheck.protocol ℚ 2 32 := rfl

/-- The round polynomial of round 1, by its label. -/
theorem access_first (tr : (sumcheckSpec ℚ 2 32 D).Tr) : tr⟦sumcheck, 1, g⟧ = tr.2.2.1 := rfl

/-- The challenge of the last round, by its label. -/
noncomputable def accessLast (tr : (sumcheckSpec ℚ 2 32 D).Tr) : ℚ := tr⟦sumcheck, 31, r⟧

end Specs.Bench.Sumcheck32

#print axioms Specs.Bench.Sumcheck32.tree_eq
#print axioms Specs.Bench.Sumcheck32.access_first
