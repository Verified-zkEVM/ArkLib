/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Examples.Sumcheck
import Specs.Export

/-!
# Elaboration benchmarks

This module holds the shared setup of the elaboration benchmarks. Each case is a small file under
`Specs/Bench/` that imports this module and elaborates, for one size, what a user of a
specification writes most often:

* `Specs.Bench.Sumcheck{8,32,128}`: the tree agreement
  `Spec.tree (sumcheckSpec ℚ 2 n D) = Sumcheck.protocol ℚ 2 n` by `rfl`, and one accessor by label
  at the first round (checked by `rfl`) and one at the last round;
* `Specs.Bench.Export{8,16,20}`: the export of the skeleton to JSON and to TeX;
* `Specs.Bench.Spartan{4,8}` (`spartanSpec ℚ m m`) and `Specs.Bench.Fri{4,8,32}`
  (`friSpec (ZMod 17) k l 3`): the tree agreement by `rfl`, accessors by label and the skeleton
  export, in one file per size.

The script `bench.sh` (next to `Specs/`) runs each case file through the build lock with
`lake env lean -Dprofiler=true`, adds an export probe at 32 rounds under a time limit, and writes
the table `out/bench.md`.

## The export cost is exponential in the number of rounds

Computing the skeleton of `sumcheckSpec ℚ 2 n D` takes time `Θ(2^n)`: 0.1 s of interpretation at
`n = 16`, 2 s at `n = 20`, more than 60 s at `n = 24`. Even `skeleton.checks.length` costs 2 s at
`n = 20`. The cause is in `Specs.Formula`: the stage's input claim sums over
`(Dom.ofFn "D" D).pow n`, `Dom.pow` stores its elements as the list `Dom.tuples D.elems n`, and
compiled code evaluates that list when it builds the claim's syntax, although the syntax keeps only
the domain's TeX name. Storing the elements lazily (for example as `Thunk (List α)`) would remove
the cost. This module does not change `Specs.Formula`, which belongs to the core.

## The accessor at round 127 needs a higher recursion limit

At 128 rounds, the label lookup `tr⟦sumcheck, 127, r⟧` stops with "maximum recursion depth has
been reached" under Lean's default `maxRecDepth` of 512. The default suffices up to round 120.
`Specs.Bench.Sumcheck128` raises the limit to 1024 for that one definition.

## Design choices

* **One file per case, with the size written out.** *Why:* the profiler reports per file, and a
  file with a literal size measures exactly what a user's file at that size costs, including
  the reduction of the tree at that size.
* **The export cases are separate and stop at 20 rounds.** *Why:* the export cost is exponential
  (above), and the case files belong to the `ArkLibPrototypes` library, so a case at 32 rounds
  would stop `lake build ArkLibPrototypes`. `bench.sh` measures the export at 32 rounds as a
  separate probe under a time limit.
* **The cases import this module, not each other.** *Why:* every case of one example then pays
  the same import cost, so the differences between its rows come from the size. The Spartan and
  FRI cases also import their example module.
* **The domain is `{0, 1}` over `ℚ` with degree 2.** *Why:* the bench measures the front end, so
  the field and the domain are the smallest that make the formulas non-trivial.
-/

namespace Specs.Bench

/-- The bench domain `{0, 1}`. -/
def D : Fin 2 → ℚ := ![0, 1]

/-- The size of the skeleton's JSON export, as a cheap witness that the export ran. -/
def jsonSize (ks : Skel) : ℕ := (Skel.toJson "sumcheck" "Sum-check" ks).compress.length

/-- The size of the skeleton's folded TeX export. -/
def texSize (ks : Skel) : ℕ := (Skel.toTex "Sum-check" true ks).length

end Specs.Bench
