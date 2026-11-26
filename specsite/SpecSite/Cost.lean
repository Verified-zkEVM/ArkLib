/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Blocks
import SpecSite.Tables
import Specs.Bench.Sumcheck128
import Specs.Bench.Export128

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "Size and speed" =>
%%%
tag := "cost"
htmlSplit := .never
%%%

Specifications cost little to elaborate, and the cost does not grow with the number of rounds.
Every number in this chapter is computed when the site builds: the line counts from the files, the
times from `prototypes/out/bench.md`, which `bench.sh` writes.

# Lines

The prototype by part. Hover over a file name for its own count, or follow it to the source.

{sizes SpecSite.prototypeSizes}

The {ref "before-after"}[before-and-after chapter] counts today's sum-check against its
specification.

# Elaboration time

Each benchmark case is a small file that elaborates what a user of a specification writes most
often, at one size: the tree agreement by `rfl`, accessors by label, and the export of the
skeleton. `bench.sh` runs each file once with Lean's profiler and writes this table:

{bench}

The times stay flat across sizes. A sum-check file costs about the same at 8 rounds as at 128, and
FRI costs about the same at 4 fold rounds as at 32. About 1 s of every case is the import of the
prototype.

# Why the cost does not grow

The skeleton holds a loop once, as one node that records its count. The JSON and the folded
figure read the skeleton with every count erased, and {name}`Specs.sumcheck_erase` proves by `rfl`
that the erased skeleton is the same for every number of rounds:

{decl +statement Specs.sumcheck_erase}

The input claim of sum-check sums over a domain with `2^n` points. Since `Dom` stores its elements
as a function from `Unit`, compiled code builds the list only when a formula is evaluated, never
when it builds the skeleton. The export at 128 rounds therefore takes as long as the export at 8
rounds. When `Dom.pow` stored the list itself, the export took 2 s at 20 rounds and more than 60 s
at 24.

{decl -docs Specs.Dom Specs.Dom.pow}

The case at 128 rounds checks the tree agreement by `rfl` and reaches the first and the last round
by label:

{decl Specs.Bench.Sumcheck128.tree_eq Specs.Bench.Sumcheck128.access_first Specs.Bench.Sumcheck128.accessLast}

The accessor at round 127 needs `maxRecDepth` 1024. Lean's default of 512 suffices up to round 120.
This is the one place where the size shows: the label lookup recurses once per round before it.

# What these numbers do not cover

* Each time is a single run on one machine (the table's caption names it), and other builds may run
  at the same time. The numbers show the trend across sizes, not a precise cost.
* The cases measure the front end: the specification, its tree, accessors and exports. They do not
  time the security proofs, which are proved once for a variable number of rounds and do not
  depend on a size.
