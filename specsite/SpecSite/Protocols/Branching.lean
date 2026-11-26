/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Data
import SpecSite.Meta.Blocks

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "A prover-chosen size" =>
%%%
tag := "branching"
%%%

In this protocol a plain prover message selects the shape of the rest. The specification is
{name}`Specs.branchingSpec`, in `Specs/Examples/Branching.lean`: sum-check in which the prover picks
the number of variables. Its parameters are the ring `R`, the degree `d` and the domain `D`, and
its statement is a target `c`.

The prover sends the number of variables `m : Fin 4` with `branch`, then a polynomial `p` in `m`
variables as an oracle message. The stage `sumcheck` reduces $`\sum_{x \in D^{m}} p(x) = c_{0}` to
$`p(r) = c_{m}` with the loop {name}`Specs.sumcheck` of the {ref "sumcheck"}[Sum-check page], and
the check `final` queries `p` at `r`.

The example demonstrates the shape mechanism only, and the module proves no soundness statement.
Because the prover chooses `p`, the claim it proves holds for every `c` that some polynomial sums
to.

# The specification

The witness is a number of variables below 4 and a polynomial in that many variables. The output is
the number of variables, the challenges and the final target.

{decl Specs.BranchWitness Specs.BranchOutput}

The honest functions read the whole witness. The honest oracle message of case `m` is
{name}`Specs.polyAt` `m w`: the witness's polynomial when `m` matches, and `0` in the cases that the
honest prover never takes ({name}`Specs.polyAt_self`).

{decl Specs.polyAt}

The specification branches on `m` with the four cases listed by their labels, then runs sum-check
on `m.val` variables with count symbol `m`:

{decl Specs.branchingSpec}

The prover sends `p` as an oracle message after `m`, not as an input oracle: the type of `p`
depends on `m`, and an input bundle is fixed before the prover sends `m`.

# The figure

The skeleton of a `branch` has one sub-skeleton per listed case ({ref "branches"}[Branches]). The
figure prints the message `m`, then each case after a division "case `m = v`", each with the rest
of the protocol: the oracle `p` with its type in that many variables, the stage, the generic round
of the loop, and the check `final`. In the folded figure every case prints the final target as
$`c_{m}`. The expanded figure binds `m` in each case, unrolls the loop of case `m = j` into `j`
rounds, and prints the target as $`c_{2}` in the case `m = 2`.

{protocols SpecSite.branching}

# Reaching moves

Since the branching message itself has a fixed position, `tr⟦m⟧` is a plain projection. A move
inside a case needs the case first: `m = 2` enters the case labelled `2`. Because the transcript
type after the message depends on the message, the accessor then returns an `Option` through
{name}`Specs.caseOf` ({ref "accessors"}[Transcript accessors]). The module's tests:

```lean
example
    (tr : (Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m⟧ = tr.1 := rfl
example
    (tr : (Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m = 2, p⟧ = (Specs.caseOf tr 2).map (·.1) :=
  rfl
example
    (tr : (Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m = 2, sumcheck, 0, g⟧ =
      (Specs.caseOf tr 2).map (·.2.1) := rfl
example
    (tr : (Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr) :
    tr⟦m = 2, sumcheck, 1, r⟧ =
      (Specs.caseOf tr 2).map (·.2.2.2.2.1) := rfl
```

On a concrete transcript the accessor reduces by `rfl`: on a transcript whose message is 2 it
returns `some` of the move, and on one whose message is 1 it returns `none`. The tests state both
with the transcript type {name}`Specs.CaseTr` of a case:

{decl Specs.CaseTr}

```lean
example (x : Specs.CaseTr 2)
    (tr : (Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr)
    (h : tr = ⟨(2 : Fin 4), x⟩) :
    tr⟦m = 2, sumcheck, 0, g⟧ = some x.2.1 := by
  subst h; rfl
example (x : Specs.CaseTr 1)
    (tr : (Specs.branchingSpec ℚ 2 ![(0 : ℚ), 1]).Tr)
    (h : tr = ⟨(1 : Fin 4), x⟩) :
    tr⟦m = 2, p⟧ = none := by
  subst h; rfl
```

# What Lean proves

The tree is the message `m`, the oracle `p` in `m` variables and ArkLib's `m`-round sum-check tree
`Sumcheck.protocol R d m`, by `rfl`:

{decl Specs.branchingTree Specs.branching_tree}

Honest acceptance: if the polynomial of the witness sums to `c` over $`D^m`, the verdict accepts
every honest transcript. The proof applies the generic {name}`Specs.Spec.verdict_isSome` and
{name}`Specs.sumcheck_complete` inside the case that the honest prover takes.

{decl Specs.branching_verdict_isSome +statement}

After the loop, the check `final` queries `p`, which the prover sent before the loop. The
completeness lemma of the loop therefore takes an invariant of the oracle table that the loop's
oracle messages preserve. {name}`Specs.Frozen` is that invariant: the table at level `ℓ` agrees with
an earlier table on every level below `ℓ₀`, and $`\ell_0 \le \ell`. Since later oracle messages
record at levels $`\ell \ge \ell_0`, they preserve the invariant. Spartan uses the same invariant.

{decl Specs.Frozen Specs.Frozen.refl Specs.Frozen.ext Specs.Frozen.find +statement}

{name}`Specs.roundSum_zero` states that the sum of the first round is the sum of the polynomial
over the whole domain.

{theorems Specs.branching_tree Specs.branching_verdict_isSome Specs.polyAt_self Specs.Frozen.refl Specs.Frozen.ext Specs.Frozen.find Specs.roundSum_zero Specs.caseOf_self Specs.caseOf_ne}

The module's tests also check that the skeleton has one case per value of `m`, each with the
generic round check $`\sum_{a \in D} g_{i}(a) = c_{i}` and the final check $`p(r) = c_{m}`, and
that the expanded figure prints the case `m = 2` with round checks for rounds 0 and 1 and the final
check on $`c_{2}`.

# Design choices

* The prover sends `p` as an oracle message after `m`, because the type of `p` depends on `m` and
  an input bundle is fixed before the prover sends `m`.
* The honest functions read the whole witness `⟨m, p⟩`. As a result, the honest oracle message of
  case `m` is `polyAt m w`, which is `p` when `m` matches and `0` in the cases the honest prover
  never takes.
* A label inside a branch names the case first (`tr⟦m = 2, p⟧`), and the accessor returns an
  `Option`. Since the transcript type after the message depends on the message, the case must be
  fixed before any move inside it has a type.
* Since `m : Fin 4` has finitely many values, the example uses `branch` with the four cases listed.
  A message of infinite type would use `branchOpaque`, and the skeleton would mark the rest opaque.
  No example uses `branchOpaque`.
