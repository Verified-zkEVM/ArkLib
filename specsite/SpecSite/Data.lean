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
# The data that the site computes from the examples

The protocol widget shows what Lean exports for each example: the JSON skeleton, the folded figure
and the expanded figure. This module computes all three when the site builds, from the same
specifications that `Specs/Main.lean` writes to `prototypes/out/`. The site therefore never reads a
file that could be stale.

Each example also carries its skeleton at a few more sizes. The widget unrolls loops itself, for
any counts the reader picks, and prints the result with a port of `Skel.toTex`. On load it checks
that port against Lean's expanded figure at every size below, so that a reader can see that the page
unrolls a loop the way Lean does.
-/

namespace SpecSite

open Lean Specs

/-- An example specification as the site shows it. -/
structure Example where
  /-- The key of the example: its JSON name and its tab in the widget. -/
  key : String
  /-- The title of its figure. -/
  title : String
  /-- The label of its tab in the widget. -/
  short : String := title
  /-- The skeleton at the sizes that `Specs/Main.lean` exports. -/
  skel : Skel
  /-- The skeleton at more sizes, for the widget's check of its unrolling. -/
  samples : List Skel := []
  /-- The specification as a Lean term, written out in full. The protocol block elaborates each
  accessor that the widget's transcript view shows on a transcript of this term. -/
  spec : String := ""

/-- The counts of the loops of a skeleton outside any branch, each symbol at its first loop: the
sizes at which the skeleton was built. Since a loop inside a branch case takes its count from the
case, it is not listed. -/
partial def loopCounts (ks : Skel) (acc : Array (String × Nat) := #[]) : Array (String × Nat) :=
  match ks with
  | .done | .opaque .. | .branch .. => acc
  | .cons _ rest => loopCounts rest acc
  | .loop l n body rest =>
    let acc := if acc.any (·.1 == l.count) then acc else acc.push (l.count, n)
    loopCounts rest (loopCounts body acc)

/-- Counts as a JSON object from symbol to number. -/
def countsJson (cs : Array (String × Nat)) : Json :=
  Json.mkObj (cs.toList.map fun (c, n) => (c, toJson n))

/-- What the widget reads for one example: the JSON skeleton, the counts it was built at, Lean's
folded and expanded figures, and the expanded figure at each sample size. -/
def Example.toJson (e : Example) : Json :=
  Json.mkObj [
    ("key", e.key),
    ("title", e.title),
    ("short", e.short),
    ("skeleton", e.skel.toJson e.key e.title),
    ("counts", countsJson (loopCounts e.skel)),
    ("tex", e.skel.toTex e.title true),
    ("texExpanded", e.skel.toTex e.title false),
    ("samples", Json.arr (e.samples.map fun ks =>
      Json.mkObj [("counts", countsJson (loopCounts ks)),
        ("tex", ks.toTex e.title false)]).toArray)]

/-- Sum-check over `ℚ` with degree 2 and domain `{0, 1}`, at three variables. -/
def sumcheck : Example where
  key := "sumcheck"
  title := "Sum-check"
  spec := "Specs.sumcheckSpec ℚ 2 3 ![(0 : ℚ), 1]"
  skel := (sumcheckSpec ℚ 2 3 ![0, 1]).skeleton
  samples := [0, 1, 2, 4, 5].map fun n => (sumcheckSpec ℚ 2 n ![0, 1]).skeleton

/-- Spartan over `ℚ` with `2^2` rows and `2^3` columns. -/
def spartan : Example where
  key := "spartan"
  title := "Spartan"
  spec := "Specs.Spartan.spartanSpec ℚ 2 3"
  skel := (Spartan.spartanSpec ℚ 2 3).skeleton
  samples := [(1, 1), (1, 2), (3, 1), (2, 4)].map fun (m, n) => (Spartan.spartanSpec ℚ m n).skeleton

/-- FRI over `ZMod 17` with `ω = 2`, two fold rounds and three queries. -/
def fri : Example where
  key := "fri"
  title := "FRI"
  spec := "Specs.Fri.friSpec (ZMod 17) 2 3 2"
  skel := (Fri.friSpec (ZMod 17) 2 3 2).skeleton
  samples := [(0, 1), (1, 1), (1, 2), (3, 2)].map fun (k, l) =>
    (Fri.friSpec (ZMod 17) k l 2).skeleton

/-- Sum-check where the prover picks the number of variables, degree 2 over `ℚ`, domain
`{0, 1}`. -/
def branching : Example where
  key := "branching"
  title := "Sum-check with a prover-chosen number of variables"
  short := "Branching"
  spec := "Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]"
  skel := (branchingSpec ℚ 2 ![0, 1]).skeleton

/-- The four examples, in the order of the widget's tabs. -/
def examples : List Example := [sumcheck, spartan, fri, branching]

end SpecSite
