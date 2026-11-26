/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench
import Specs.Examples.Fri

/-!
# Bench case: FRI with `k = 4` folds and `l = 8` queries

The tree agreement by `rfl`, accessors by label, and the skeleton export, for
`friSpec (ZMod 17) 4 8 3`. The generator `ω = 3` is not a root of unity of order `2^5`
in `ZMod 17`. The tree and the skeleton do not depend on `ω`, so the bench uses it as it is.
See `Specs.Bench`.
-/

set_option linter.hashCommand false

namespace Specs.Bench.Fri4
open Interaction Specs.Fri

/-- The tree agreement, by `rfl`. -/
theorem tree_eq : (friSpec (ZMod 17) 4 8 3).tree = friTree (ZMod 17) 4 8 := rfl

/-- The oracle word of fold round 1, by its label. -/
theorem access_fold (tr : (friSpec (ZMod 17) 4 8 3).Tr) : tr⟦fold, 1, f⟧ = tr.2.2.2.1 := rfl

/-- The last query position, by its label. -/
noncomputable def accessQuery (tr : (friSpec (ZMod 17) 4 8 3).Tr) := tr⟦query, 7, t⟧

/-! The skeleton export to JSON and to LaTeX. -/
#guard jsonSize (friSpec (ZMod 17) 4 8 3).skeleton > 0
#guard texSize (friSpec (ZMod 17) 4 8 3).skeleton > 0

end Specs.Bench.Fri4

#print axioms Specs.Bench.Fri4.tree_eq
#print axioms Specs.Bench.Fri4.access_fold
