/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Blocks
import SpecSite.Tables
import Specs.Examples.Sumcheck
import Specs.Kit.Sumcheck
import ArkLib.ProofSystem.Sumcheck.MessageTree
import ArkLib.ProofSystem.Sumcheck.IndexedDomain
import ArkLib.ProofSystem.Sumcheck.IntervalCompleteness
import ArkLib.ProofSystem.Sumcheck.Interval
import ArkLib.ProofSystem.Sumcheck.Interpreted
import ArkLib.ProofSystem.Sumcheck.SingleRound
import ArkLib.ProofSystem.Sumcheck.Indexed

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "Before and after" =>
%%%
tag := "before-after"
htmlSplit := .never
%%%

This chapter puts one sum-check round as ArkLib writes it today next to the same round as a
specification. Every excerpt is the current source, loaded when the site builds. The left column
collects what a reader needs to rebuild one round today: the tree, the honest message, the claim,
the check, the verifier's fold and the way proofs reach a move. The right column is the
specification and the theorems that tie it to today's definitions.

# One round

::::columns
:::column "Today: one round, assembled from seven files" (tone := "before")
The tree recurses on the number of rounds left. A round is an oracle node and a challenge node,
with no names:

{decl -docs Sumcheck.Interpreted.protocol Sumcheck.protocol}

The honest message is defined two files away from the tree, as a sum over the suffix of the domain:

{decl -docs Sumcheck.projectedRoundPolynomial}

The prover reads it through the interval state:

{decl -docs Sumcheck.intervalMessage}

The claim between rounds carries its round index as a field together with a proof about it:

{decl -docs Sumcheck.IntervalClaim}

The check itself, as an oracle computation:

{decl -docs Sumcheck.intervalCheck}

The verifier runs every check after the interaction, by a fold over the rounds left:

{decl -docs Sumcheck.Interpreted.decision}
:::
:::column "Specification: the round and the whole protocol" (tone := "after")
The round, in protocol order. Each move has a name, and the check is a formula that the verifier
evaluates and the figure prints:

{decl Specs.sumcheckRound}

The whole specification: the input polynomial, a stage with its input and output claims, and the
loop of `n` rounds:

{decl Specs.sumcheckSpec}

Lean proves that this is today's sum-check. The tree is today's tree by `rfl`:

{decl Specs.sumcheck_tree}

The honest prover is {name}`Sumcheck.intervalProver` and the verdict is
{name}`Sumcheck.indexedVerdict`:

{decl +statement Specs.sumcheck_prover Specs.sumcheck_verdict}
:::
::::

The specification also yields what today's code does not have: a figure, a claim-flow graph, a
transcript timeline and a JSON skeleton, all computed from the same text. The
{ref "sumcheck"}[sum-check page] shows them.

# Moves by name

Today a proof reaches a move of a round by its position in the tree. The challenge node of a round
is a path of constructors:

{decl -docs Sumcheck.roundChallengeNode}

A specification names its moves, and an accessor reaches a move by those names. The tests of
`Specs/Examples/Sumcheck.lean` check, by `rfl`, that the accessor is the same projection that a
proof writes by hand today:

```
example (tr : (sumcheckSpec ℚ 2 3 D).Tr) : tr⟦sumcheck, 1, g⟧ = tr.2.2.1 := rfl
example (tr : (sumcheckSpec ℚ 2 3 D).Tr) : tr⟦sumcheck, 2, r⟧ = tr.2.2.2.2.2.1 := by simp
```

`tr⟦sumcheck, 1, g⟧` is the polynomial `g` of round 1 of the loop `sumcheck`. The same accessor
works on the verifier's view of a transcript. The {ref "language"}[language chapter] gives the
label rules.

# The recursion that every proof repeats

Today each security proof of sum-check walks the rounds itself. {name}`Sumcheck.foldPrefix` is the
truth predicate after every completed round of a partial transcript, by recursion over
`Cursor.Spine`, and about eight lemmas in the same file follow it through sends, challenges and the
leaf:

{decl -docs Sumcheck.foldPrefix}

The proof kit does this recursion once, for every protocol made of rounds. A protocol supplies one
obligation per round: from a state whose claim is false, the round's check passes into a state whose
claim is true with probability at most `ε i`.

{decl Specs.Kit.RoundSound}

For sum-check, that obligation is the Schwartz–Zippel bound of one round. The kit turns it into
round-by-round soundness of the whole protocol, and the {ref "proofs"}[proofs chapter] shows how:

{decl +statement Specs.Kit.sumcheck_roundSound}

# In lines

The two tables count lines when the site builds. The first counts the whole files that the left
column quotes, and all of today's sum-check directory:

{sizes SpecSite.todaySumcheckSizes}

The second counts what sum-check needs on top of the shared layers of the prototype: the
specification, its soundness through the kit, the bridge between the two, and its claims.

{sizes SpecSite.sumcheckSpecSizes}

D10 reports the measurements behind these numbers: one round today spreads over 12 files and 2,351
lines, and sum-check's soundness proof through the kit is 118 lines instead of 317. The
{ref "cost"}[size chapter] counts the rest of the prototype.
