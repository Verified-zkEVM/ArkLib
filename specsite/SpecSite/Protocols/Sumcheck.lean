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
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "Sum-check" =>
%%%
tag := "sumcheck"
%%%

Sum-check reduces a claim about a sum to a claim about one evaluation. The input is a polynomial
`p` in `n` variables of individual degree at most `d` over a ring `R`, given as an input oracle,
and a target `c_0`. The input claim is $`\sum_{x \in D^{n}} p(x) = c_{0}` for a domain `D` of `k`
points. In round `i` the prover sends the univariate polynomial `g_i` as an oracle, the verifier
checks $`\sum_{a \in D} g_{i}(a) = c_{i}`, samples `r_i` and sets $`c_{i+1} = g_{i}(r_{i})`. After
`n` rounds the output claim is $`p(r) = c_{n}`.

The specification is {name}`Specs.sumcheckSpec`, in `Specs/Examples/Sumcheck.lean`. Its parameters
are the ring `R`, the degree `d`, the number of rounds `n` and the domain `D : Fin k → R`. Lean
proves that it describes ArkLib's sum-check: the tree, the honest prover, the verdict, the
verifier's decision and its output agree with ArkLib's. Other examples reuse its loop: Spartan runs
it twice, and the branching example runs it on a prover-chosen number of variables.

# The specification

The claim between rounds is a structure of handles: the target `c_i` as a named value and the
challenges so far. The check and the local value of a round then print as `c_{i}` and `c_{i+1}`.

{decl Specs.Claim}

One round sends the oracle `g_i`, checks its sum, samples `r_i` and computes the next target. Every
name in the round is symbolic in the round variable (`iv "g"`, `iv "c" 1`). Since `rounds` requires
the round's skeleton to be the same for every round, a name that mentions the round number would not
typecheck ({ref "loops"}[Loops]).

{decl Specs.sumcheckRound}

The tree of one round followed by the tree `t` is an oracle message and a challenge:

{decl Specs.roundTree}

The loop runs `n` rounds from a claim. Its error annotation is `d/|F|`, its count symbol `n` and its
round variable `i`. `block` and `countName` let a larger protocol rename the loop and its count, as
Spartan counts its two loops with `m` and `n`.

{decl Specs.sumcheck}

The specification reads the input polynomial `p`, declares the stage `sumcheck` with its input and
output claims, and runs the loop. The statement is ArkLib's `RoundStatement` at round 0, which holds
the target, and the witness is the polynomial.

{decl Specs.sumcheckSpec}

`sumcheckSpec` names ArkLib's tree family for its rounds (`tree := …`). The statements of the
agreement theorems then typecheck at a variable `n` with no cast. The loop `sumcheck` keeps the
default tree, and {name}`Specs.roundsTree_sumcheck` proves by induction that the two agree:

{decl Specs.roundsTree_sumcheck}

# The figure

The folded figure prints the generic round, and the expanded figure unrolls it at the count you
choose:

{protocols SpecSite.sumcheck}

# Reaching moves

An accessor reads a move by its label: the stage or loop, the round, and the base of the name
({ref "accessors"}[Transcript accessors]). The module's tests read the polynomial of round 1, the
challenge of round 2 and the first polynomial, at three rounds:

```lean
example (D : Fin 2 → ℚ)
    (tr : (Specs.sumcheckSpec ℚ 2 3 D).Tr) :
    tr⟦sumcheck, 1, g⟧ = tr.2.2.1 := rfl
example (D : Fin 2 → ℚ)
    (tr : (Specs.sumcheckSpec ℚ 2 3 D).Tr) :
    tr⟦sumcheck, 2, r⟧ = tr.2.2.2.2.2.1 := by
  simp
example (D : Fin 2 → ℚ)
    (tr : (Specs.sumcheckSpec ℚ 2 3 D).Tr) :
    tr⟦g⟧ = tr.1 := rfl
```

The accessor also works on a view of the verifier:

```lean
example (D : Fin 2 → ℚ)
    (p : PFunctor.FreeM.Path
      (Specs.sumcheckSpec ℚ 2 3 D).tree)
    (v : (Specs.sumcheckSpec ℚ 2 3 D).Vw p) :
    v⟦sumcheck, 1, g⟧ = v.1.2.2.1 := rfl
```

Lean elaborates these blocks when the site builds. A change to the accessor or to the specification
that breaks them therefore fails the build.

# What Lean proves

The specification agrees with ArkLib's sum-check. The tree is `Sumcheck.protocol R d n` by `rfl`.
Hence the transcripts of the specification are ArkLib's sum-check transcripts:

{decl Specs.sumcheck_tree}

The honest prover is ArkLib's interval prover, and the verdict is ArkLib's indexed verdict:

{decl Specs.sumcheck_prover Specs.sumcheck_verdict +statement}

On every transcript, the decision of the specification's verifier agrees with ArkLib's
`indexedVerifier` once the oracle queries are answered from the input data and the transcript, and
both verifiers keep the input polynomial as their output oracle:

{decl Specs.sumcheck_decide Specs.sumcheck_outputMap +statement}

{name}`Specs.sumcheck_decide` follows from the generic theorem {name}`Specs.Spec.decide_eq_verdict`
and {name}`Specs.sumcheck_verdict`. The only induction specific to sum-check is
{name}`Specs.verdict_roundsGo`, which compares two pure functions on transcripts.
{name}`Specs.prove_roundsGo` is the round induction behind {name}`Specs.sumcheck_prover`. Both state
their induction on `roundsFrom`, the rest of the loop from round `j`, and turn a claim after `j`
rounds into ArkLib's indexed claim with {name}`Specs.Claim.toIndexed`:

{decl Specs.Claim.toIndexed}

Completeness of the loop holds for any continuation. If the target `c_j` is the remaining sum of the
polynomial over the domain, every check of the rounds `j, …, n - 1` holds on the honest messages,
for every choice of challenges, provided the continuation is complete whenever its claim
$`p(r) = c_{n}` holds. `P` is any invariant of the oracle table that the rounds' oracle messages
preserve. As a result, the continuation can still read the oracles recorded before the loop. Spartan
and the branching example use this lemma.

{decl Specs.sumcheck_complete +statement}

The proofs evaluate the two round formulas with two small lemmas, stated at their exact hole lists:

{decl Specs.eval_round_value Specs.eval_round_check +statement}

These lemmas hold by `rfl` (with a `simp` step for the sum), because `simp` and `rw` time out on
`Curry.app`: the formula is a `Curry` function only after unfolding
({ref "limitations"}[limitation 4]).

The erased skeleton, which the JSON and the folded figure read, is the same for every number of
rounds:

{decl Specs.sumcheck_erase}

{theorems Specs.sumcheck_tree Specs.sumcheck_erase Specs.roundsTree_sumcheck Specs.sumcheck_prover Specs.sumcheck_verdict Specs.sumcheck_decide Specs.sumcheck_outputMap Specs.prove_roundsGo Specs.verdict_roundsGo Specs.sumcheck_complete Specs.eval_round_value Specs.eval_round_check}

Soundness is proved through the proof kit and the bridge, and the stage claims are the languages of
the soundness statement ({name}`Specs.Bridge.sumcheckSpec_sound`,
{name}`Specs.Claims.sumcheckSpec_contract`). The {ref "proofs"}[Proofs] chapter covers both.

The module's tests also fix the printed round check: $`\sum_{a \in D} g_{i}(a) = c_{i}` folded and
$`\sum_{a \in D} g_{1}(a) = c_{1}` with `i` bound to 1. They check that the round check, written
again as a closed formula, has the syntax that the skeleton exports, and that the first-order form
of that check evaluates like the formula.

# Design choices

* `sumcheckSpec` names ArkLib's tree family for its rounds so that the agreement theorems typecheck
  at a variable `n` with no cast. The loop `sumcheck` keeps the default tree, and
  {name}`Specs.roundsTree_sumcheck` proves that the two agree.
* The claim between rounds is a structure of handles. That way the check and the local value print
  as `c_{i}` and `c_{i+1}`.
* Every name in the round is symbolic in the round variable. The output claim renames the final
  target to `c_n`, and {name}`Specs.sumcheck_erase` proves that the erased skeleton does not depend
  on `n`.
* Because {name}`Specs.sumcheck_decide` follows from the generic
  {name}`Specs.Spec.decide_eq_verdict`, the only sum-check-specific induction compares two pure
  functions on transcripts.
* {name}`Specs.eval_round_value` and {name}`Specs.eval_round_check` evaluate the two round formulas
  at their exact hole lists, because `simp` and `rw` time out on `Curry.app`.
