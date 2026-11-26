/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Blocks
import Specs.Claims
import Specs.Kit.Sumcheck

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "Adopting the specifications" =>
%%%
tag := "adopting"
htmlSplit := .never
%%%

The prototype and this site are meant to move into ArkLib's development. This chapter covers the
steps that move a protocol onto a specification, with sum-check as the worked case, how the site
is built and what it checks, and what this site adds to the open items of the
{ref "design"}[design record]. D10's {ref "design-plan"}[order of work] gives the plan for the
library itself.

# Moving a protocol onto a specification

Sum-check went through every step below. Each step names the theorem that did it for sum-check, and
the table at the end of the section checks that each one exists and uses no `sorry`.

: 1. Write the round

  Write one round with moves, in protocol order, with its checks as formulas
  ({name}`Specs.sumcheckRound`). Names that change from round to round use the round variable. That
  way the round's skeleton is the same for every round. The {ref "language"}[language chapter] lists
  the moves.

: 2. Write the specification

  Put the rounds in a loop and the loop in stages with input and output claims
  ({name}`Specs.sumcheckSpec`). The specification names ArkLib's tree family when the agreement
  theorems should typecheck at a variable size.

: 3. Prove the tree

  Prove that the specification's tree is the tree that ArkLib's proofs use, by `rfl`
  ({name}`Specs.sumcheck_tree`). Then every existing theorem about that tree applies to the
  specification's transcripts.

: 4. Prove the figure is size-independent

  Prove by `rfl` that the erased skeleton does not depend on the sizes
  ({name}`Specs.sumcheck_erase`). The JSON and the folded figure read the erased skeleton.

: 5. Prove completeness

  Prove that every check holds on the honest messages when the input claim holds
  ({name}`Specs.sumcheck_complete`). The generic {name}`Specs.rounds_complete` does the induction
  over the loop.

: 6. Prove soundness through the kit

  Supply the per-round obligation {name}`Specs.Kit.RoundSound`
  ({name}`Specs.Kit.sumcheck_roundSound` for sum-check). The kit proves round-by-round soundness for
  the whole protocol, and the bridge carries it to the specification's verifier
  ({name}`Specs.Bridge.sumcheckSpec_sound`). See the
  {ref "proofs"}[proofs chapter].

: 7. Prove the claims

  Prove that the stage claims are the languages of the soundness statement
  ({name}`Specs.Claims.sumcheckSpec_contract`).

: 8. Add it to the site

  Add an `Example` to `specsite/SpecSite/Data.lean`, and write a page with `{protocols}` for the
  figure, `{decl}` for the source and `{theorems}` for what is proved. The README in `specsite/`
  lists the blocks.

{theorems Specs.sumcheck_tree Specs.sumcheck_erase Specs.sumcheck_complete Specs.rounds_complete Specs.Kit.sumcheck_roundSound Specs.Bridge.sumcheckSpec_sound Specs.Claims.sumcheckSpec_contract}

# Building the site

The site is a Lake package in `specsite/` that requires ArkLib by path and shares its package
directory, like `docbuild/`. Build ArkLib's prototype library, then the site, then render it:

```
lake build ArkLibPrototypes
cd specsite
lake build specsite
.lake/build/bin/specsite --output _out --without-html-single
```

The pages are in `specsite/_out/html-multi/`. `specsite/build.sh` runs the same steps and fails on
any warning. The first build of an excerpt runs `lake build +Module:highlighted` in
`specsite/highlight/` for the module the excerpt comes from: SubVerso elaborates the module again
and records the highlighting, hovers and proof states. Later builds reuse that result until the
module changes.

# What the build checks

: Excerpts

  `{decl}` resolves each name in the environment, finds its module, and loads the module's
  highlighted source. A renamed or deleted declaration fails the build. The caption links to the
  lines on GitHub at the commit the site was built from.

: Names in prose

  `{name}` resolves its name, and the build fails if the name does not exist.

: Theorems

  `{theorems}` collects the axioms of each theorem, the way `#print axioms` does. The build fails
  if a theorem depends on `sorryAx` or on an axiom other than `propext`, `Classical.choice` and
  `Quot.sound`.

: Figures

  `{protocols}` evaluates each example specification when the site builds and embeds the JSON
  skeleton, the folded figure, and the expanded figure at several sizes. The page draws the figure
  with its own port of Lean's printer. On load it prints every formula and figure that Lean
  computed and compares the strings, byte for byte. The line under the figure reports the result.

: Accessor paths

  `{protocols}` also computes the accessor path of every move in the transcript view, at the
  example's sizes and in every branch case, by the page's rule. It elaborates each path on a
  transcript of the example's specification and fails the build if Lean rejects one. It first
  checks that the specification term it elaborates against has the example's skeleton. The page
  shows the type Lean gave each path, and its check on load compares its own paths with Lean's.

: Tables

  `{sizes}` counts the lines of its files, and `{bench}` reads the benchmark table that `bench.sh`
  writes.

# Keeping the site in CI

No workflow builds the prototype library or this site yet. A job would build `ArkLibPrototypes`,
then the site, and publish `specsite/_out/html-multi/` as a GitHub Pages artifact. Because the
build fails on a stale excerpt, a missing theorem or a `sorry`, the job would also check that the
documentation agrees with the code on every pull request that touches `Specs/` or `specsite/`.

# What this site adds to the open items

The design record lists what stays open for the specifications themselves. The site adds three
items of its own:

* The page's port of Lean's printer must follow `Specs/Export.lean`, and its accessor rule must
  follow `findMove` in `Specs/Run.lean`. The check on load catches a difference at every size that
  Lean evaluated, but not at sizes that only the page draws.
* SubVerso elaborates each excerpted module a second time. A cold build of the site therefore costs
  about one more elaboration of every module it quotes.
* Verso is pinned to `v4.36.0`, the release that matches ArkLib's toolchain. A toolchain bump needs
  the matching Verso release.
