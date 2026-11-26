/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench
import Specs.Examples.Spartan

/-!
# Bench case: Spartan with `m = n = 8`

The tree agreement by `rfl`, one accessor by label in each sum-check, and the skeleton export, for
`spartanSpec ℚ 8 8`. See `Specs.Bench`.
-/

set_option linter.hashCommand false

namespace Specs.Bench.Spartan8
open Interaction Specs.Spartan

/-- The tree agreement, by `rfl`. -/
theorem tree_eq : (spartanSpec ℚ 8 8).tree = spartanTree ℚ 8 8 := rfl

/-- The first round polynomial of the outer sum-check, by its label. -/
theorem access_outer (tr : (spartanSpec ℚ 8 8).Tr) : tr⟦outer, sumcheck, 0, g⟧ = tr.2.2.1 := rfl

/-- The last challenge of the inner sum-check, by its label. -/
noncomputable def accessInner (tr : (spartanSpec ℚ 8 8).Tr) : ℚ := tr⟦inner, sumcheck, 7, r⟧

/-! The skeleton export to JSON and to LaTeX. -/
#guard jsonSize (spartanSpec ℚ 8 8).skeleton > 0
#guard texSize (spartanSpec ℚ 8 8).skeleton > 0

end Specs.Bench.Spartan8

#print axioms Specs.Bench.Spartan8.tree_eq
#print axioms Specs.Bench.Spartan8.access_outer
