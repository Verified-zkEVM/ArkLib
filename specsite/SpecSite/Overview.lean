/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Data
import SpecSite.Meta.Blocks
import Specs.Claims

open Verso.Genre Manual
open SpecSite

#doc (Manual) "Overview" =>
%%%
tag := "overview"
htmlSplit := .never
%%%

A protocol in ArkLib should read like the protocol in the paper. This site shows a prototype of
that: a small language in which a protocol is written once, in protocol order, with its checks and
claims as formulas. From that one text Lean derives the interaction tree that ArkLib's security
proofs use, the honest prover, the verifier's decision, the claims between stages, a JSON skeleton
and a `cryptocode` figure. The prototype lives in `docs/design/interaction-layer/prototypes/Specs/`
and the decision record behind it is {ref "design"}[D10].

Lean produces the code, the figures and the tables on this site. When the site builds, Lean
* loads every code excerpt from the module that defines it, which makes a renamed or deleted
  declaration fail the build;
* evaluates the four example specifications and embeds what it computes: the JSON skeleton, the
  folded figure, and the expanded figure at several sizes;
* elaborates every accessor path that the transcript view shows, such as
  `tr⟦m = 2, sumcheck, 1, r⟧`, on a transcript of its specification, and fails the build if Lean
  rejects one;
* checks every theorem that a table names, and fails the build if one of them depends on `sorryAx`
  or on an axiom other than `propext`, `Classical.choice` and `Quot.sound`;
* counts the lines of every file that a size table lists, and reads the benchmark table from the
  output of `bench.sh`.

The four numbers below are the headline measurements of D10. Unlike the tables, they are typed into
this page by hand and can fall behind the code. The site recomputes the size tables and the
benchmark table each time it builds.

::::stats
:::stat "6 + 12 lines"
One sum-check round, then the whole specification with its claims, both shown below. D10 counts
the same round today in 12 files and 2,351 lines.
:::
:::stat "317 → 118"
Lines of the sum-check soundness proof today and through the proof kit, for the identical
statement, as D10 counts them.
:::
:::stat "0 strings"
Hand-written display text on checks, local values and claims. The verifier evaluates a formula and
the figure prints the same formula.
:::
:::stat "≈ 2.3 s"
Elaboration time of each benchmark file at every size tried, up to 128 sum-check rounds, in the
{ref "cost"}[benchmark table]. About 1 s of it is imports.
:::
::::

# Four protocols, drawn by Lean

The figure below is what Lean computes from the four example specifications when the site builds.
Pick a protocol, then a view:

: Figure

  The `cryptocode`-style figure. A loop folds to one round with symbolic indices: the round
  `i` of `n`, the challenge `r_i`, the target `c_{i+1}`. Expand it to unroll the loop at any count
  you type. A branch shows each case, and a stage shows its input and output claims.

: Claim flow

  The claims between stages, with the values each claim reads.

: Transcript

  Every move in order, who sends it, and the accessor that reaches it in Lean, such as
  `tr⟦sumcheck, 1, g⟧` for the polynomial of round 1.

: LaTeX

  The `cryptocode` source. At the counts Lean computed, this is Lean's string. At other counts the
  page unrolls the loop itself.

: JSON

  The skeleton that Lean exports for other tools.

{protocols SpecSite.sumcheck SpecSite.spartan SpecSite.fri SpecSite.branching}

The line under the figure reports a check that runs when the page loads. The page carries its own
port of Lean's printer, which draws the figure at counts that Lean did not compute. It first prints
every formula and every figure that Lean computed and compares the strings, byte for byte. A
mismatch turns the line red.

# One round, as written

This is round `i` of sum-check, the whole of it. The prover sends the round polynomial `g` as an
oracle, the verifier checks that it sums to the current target over the domain, draws the
challenge `r`, and computes the next target `g(r)`:

{decl Specs.sumcheckRound}

The specification wraps the loop of `n` rounds in a stage. The stage's input claim is the sum of
`p` over `D^n` and its output claim is `p(r) = c_n`. Since both are formulas, the verifier evaluates
them and the figure prints them:

{decl Specs.sumcheckSpec}

Lean proves that this text describes ArkLib's sum-check. The tree is ArkLib's tree by `rfl`, the
honest prover and the verdict are ArkLib's, and the stage claims are the languages of the soundness
statement:

{theorems Specs.sumcheck_tree Specs.sumcheck_erase Specs.sumcheck_prover Specs.sumcheck_verdict Specs.sumcheck_decide Specs.Bridge.sumcheckSpec_sound Specs.Claims.sumcheckSpec_contract}

# How this site is organized

: {ref "language"}[The specification language]

  The moves, rounds, stages, formulas and names of the language, and what Lean derives from a
  specification.

: {ref "protocols"}[Four protocols]

  Sum-check, Spartan, FRI, and a protocol where the prover picks the size. Each page shows the
  specification, its figure and what Lean proves about it.

: {ref "proofs"}[Proofs]

  The proof kit, which proves round-by-round soundness once for any protocol made of rounds; the
  bridge from a specification to the kit; and the stage claims.

: {ref "before-after"}[Before and after]

  Today's sum-check next to its specification.

: {ref "design"}[The design record]

  D10: the decision, the nine limitations of the earlier prototypes and how each was resolved, what
  stays open, and the order of work.

: {ref "cost"}[Size and speed]

  Line counts and elaboration times, computed when the site builds.

: {ref "adopting"}[Adopting the specifications]

  How the site is built and checked, and what it takes to move a protocol of ArkLib onto
  specifications.
