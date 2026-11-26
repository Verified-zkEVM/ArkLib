/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Export
import Specs.Examples.Spartan
import Specs.Examples.Fri
import Specs.Examples.Branching

/-!
# Export of the example specifications

`main` writes, for each example, the JSON skeleton `name.json`, the folded figure `name.tex` and the
expanded figure `name-expanded.tex` into `docs/design/interaction-layer/prototypes/out/`. Run it
from the worktree root:

```
lake env lean --run docs/design/interaction-layer/prototypes/Specs/Main.lean
```

The skeleton of a specification is part of its type, so the export never runs a description. The
examples are instantiated at small sizes, since the skeleton fixes the number of rounds:

* `sumcheck`: three variables over `ℚ`, degree 2, domain `{0, 1}`.
* `spartan`: `2^2` rows and `2^3` columns over `ℚ`.
* `fri`: two fold rounds (`k = 2`) and the final constant on a domain of 8 points, and three
  queries, over `ZMod 17` with `ω = 2` of order 8.
* `branching`: degree 2 over `ℚ`, domain `{0, 1}`.
-/

open Specs

/-- Write the exported files of the four examples. -/
def main : IO Unit := do
  let dir : System.FilePath := "docs/design/interaction-layer/prototypes/out"
  writeExample dir "sumcheck" "Sum-check" (sumcheckSpec ℚ 2 3 ![0, 1]).skeleton
  writeExample dir "spartan" "Spartan" (Spartan.spartanSpec ℚ 2 3).skeleton
  writeExample dir "fri" "FRI" (Fri.friSpec (ZMod 17) 2 3 2).skeleton
  writeExample dir "branching" "Sum-check with a prover-chosen number of variables"
    (branchingSpec ℚ 2 ![0, 1]).skeleton
  IO.println s!"wrote the examples to {dir}"
