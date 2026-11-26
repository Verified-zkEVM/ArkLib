/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench

/-!
# Bench case: sum-check with 128 rounds, tree and accessors

The tree agreement by `rfl` and one accessor by label at the first and at the last round, for
`sumcheckSpec ℚ 2 128 D`. The skeleton export is a separate case (`Specs.Bench.Export*`). See
`Specs.Bench`.

The accessor at round 127 needs `maxRecDepth` above Lean's default of 512: with the default, the
label lookup `tr⟦sumcheck, 127, r⟧` stops with "maximum recursion depth has been reached". The
default suffices up to round 120. The file raises the limit to 1024 for that one definition.
-/

namespace Specs.Bench.Sumcheck128
open Interaction

/-- The tree agreement, by `rfl`. -/
theorem tree_eq : Spec.tree (sumcheckSpec ℚ 2 128 D) = Sumcheck.protocol ℚ 2 128 := rfl

/-- The round polynomial of round 1, by its label. -/
theorem access_first (tr : (sumcheckSpec ℚ 2 128 D).Tr) : tr⟦sumcheck, 1, g⟧ = tr.2.2.1 := rfl

set_option maxRecDepth 1024 in
/-- The challenge of the last round, by its label. -/
noncomputable def accessLast (tr : (sumcheckSpec ℚ 2 128 D).Tr) : ℚ := tr⟦sumcheck, 127, r⟧

end Specs.Bench.Sumcheck128

#print axioms Specs.Bench.Sumcheck128.tree_eq
#print axioms Specs.Bench.Sumcheck128.access_first
