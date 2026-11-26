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

#doc (Manual) "FRI" =>
%%%
tag := "fri"
%%%

FRI tests that a word is close to a low-degree polynomial by folding it in half, round by round,
and then checking the folds at random positions. The specification is
{name}`Specs.Fri.friSpec`, in `Specs/Examples/Fri.lean`, with a domain that halves each round. Its
parameters are the field `F`, the number of fold rounds `k`, the number of queries `l` and the
generator `ω` of the domain $`D_0` of size $`2^{k+1}`.

The domain $`D_j` of round `j` has $`2^{k+1-j}` points $`\omega^{2^j \cdot s}`, indexed by `s`. The
word $`f_0` on $`D_0` is an input oracle. The protocol has three loops, one nested in another:

* The loop `fold` has `k` rounds over the round variable `i`. In round `i` the verifier samples
  $`\alpha_i`, and the prover sends the folded word $`f_{i+1}` on $`D_{i+1}`, of size $`2^{k-i}`,
  as an oracle message.
* The verifier samples $`\alpha_k`, and the prover sends the final constant `c`, the fold of
  $`f_k`.
* The loop `query` has `l` rounds over the round variable `j`. Each samples a position $`t_j` of
  $`D_0`. The nested loop `consistency` then reads $`a_i = f_i(x_i)` and $`b_i = f_i(-x_i)` for the
  pair above $`t_j` in each round $`i < k` and checks the fold:
  $`2 x_i \cdot f_{i+1}(x_i^2) = x_i (a_i + b_i) + \alpha_i (a_i - b_i)`. Round 0 reads the input
  oracle $`f_0`. The check `final` tests the same relation for $`f_k` against `c`.

# Words and folding

A word of round `j` is its values on $`D_j`, indexed by position. One folding step with challenge
$`\alpha` is $`f'(x^2) = (f(x) + f(-x))/2 + \alpha (f(x) - f(-x))/(2x)`, the even part plus
$`\alpha` times the odd part:

{decl Specs.Fri.size Specs.Fri.Word Specs.Fri.foldStep}

The index maps take a query position `t` of $`D_0` to the pair of points in $`D_i` that folds to
one point of $`D_{i+1}`. They appear in the formulas as the named functions `lo`, `hi` and `pt`:

{decl Specs.Fri.loJ Specs.Fri.loI Specs.Fri.hiI Specs.Fri.ptI}

The honest word of round `i` is $`f_0` folded with the challenges $`\alpha_0, \dots, \alpha_{i-1}`:

{decl Specs.Fri.honestWord}

# The fold rounds

The verifier's state after `i` fold rounds is a {name}`Specs.Fri.FoldState`: the challenges so far
and the references of the words $`f_0, \dots, f_i`. A query round reads every word, under a name
relative to its own round variable. For that reason {name}`Specs.Fri.FoldState.f` gives a word's
handle the name that the reading round needs ($`f_i`, $`f_{i+1}` or $`f_k`).

{decl Specs.Fri.FoldState Specs.Fri.FoldState.f}

A fold round samples $`\alpha_i` and receives the folded word $`f_{i+1}` as an oracle. The word's
type prints symbolically as $`\mathbb{F}^{2^{k-i}}`, since its `TypeName` would print the number
and make the skeleton depend on `i` and `k`:

{decl Specs.Fri.foldRound}

# The query rounds

The query position is $`t_j`, named over the query loop's variable `j`:

{decl Specs.Fri.tName}

The formulas of a consistency round read $`a_i`, $`b_i` and the point $`x_i`, and check the fold.
The check has no division: $`2x \cdot f'(x^2) = x (a + b) + \alpha (a - b)` is the fold multiplied
by $`2x`, because the formula language has no division.

{decl Specs.Fri.fmlA Specs.Fri.fmlB Specs.Fri.fmlX Specs.Fri.fmlFold}

The hole types of these formulas mention the round: $`f_i` answers queries in
`Fin (2^(k+1-i))`. `rounds` therefore cannot infer the round's skeleton by unification, and the
consistency loop passes it explicitly as `G`. {name}`Specs.Fri.checkSkel` builds it from the
formulas of round 0. Because the syntax of a function application keeps only the function's name,
every round's skeleton evaluates to `checkSkel`, and Lean checks that by evaluation
({ref "loops"}[Loops]).

{decl Specs.Fri.checkSkel}

A consistency round computes the three local values and checks the fold. A query round samples the
position, runs the consistency loop over `i < k`, and checks the last fold against the final
constant `c`:

{decl Specs.Fri.checkRound Specs.Fri.queryRound}

# The specification

The specification reads $`f_0`, runs the fold loop with count symbol `k`, samples $`\alpha_k`,
receives `c`, and runs the query loop with count symbol `l` and round variable `j`:

{decl Specs.Fri.friSpec}

Every name in a loop body is symbolic: $`\alpha_i`, $`f_{i+1}`, $`a_i` over the round variable
`i`, and $`t_j` over the query loop's variable `j`. The values of the check `final` and the
challenge $`\alpha_k` use the count symbol `k` (`iv "a" (v := "k")`). The nested loops have
different round variables. The expanded figure therefore binds both.

# The figure

The folded figure prints each of the three loops once. The expanded figure unrolls them at the
counts you choose:

{protocols SpecSite.fri}

# Reaching moves

The module's tests, with `k = 2` and `l = 3` over $`\mathbb{F}_{17}` with `ω = 2`, read the word of
fold round 1, the final constant, the last folding challenge $`\alpha_2` and the position of the
second query:

```lean
example
    (tr : (Specs.Fri.friSpec (ZMod 17) 2 3 2).Tr) :
    tr⟦fold, 1, f⟧ = tr.2.2.2.1 := rfl
example
    (tr : (Specs.Fri.friSpec (ZMod 17) 2 3 2).Tr) :
    tr⟦c⟧ = tr.2.2.2.2.2.1 := rfl
example
    (tr : (Specs.Fri.friSpec (ZMod 17) 2 3 2).Tr) :
    tr⟦"\\alpha_2"⟧ = tr.2.2.2.2.1 := rfl
example
    (tr : (Specs.Fri.friSpec (ZMod 17) 2 3 2).Tr) :
    tr⟦"\\alpha"⟧ = tr⟦fold, 0, "\\alpha"⟧ := rfl
example
    (tr : (Specs.Fri.friSpec (ZMod 17) 2 3 2).Tr) :
    tr⟦query, 1, t⟧ = tr.2.2.2.2.2.2.2.1 := rfl
```

In fold round 1 the prover sends $`f_{i+1}` with `i = 1`, the word $`f_2`. The final challenge
$`\alpha_k` matches `"\\alpha_2"` because the accessor binds the finished fold loop's count `k` to
2. With the base alone, `tr⟦"\\alpha"⟧` reads the first challenge, $`\alpha_0` of fold round 0.

# What Lean proves

The tree is `k` pairs of a challenge and an oracle word, the challenge $`\alpha_k`, the message `c`
and `l` challenges, by `rfl`:

{decl Specs.Fri.friTree Specs.Fri.fri_tree}

The erased skeleton is the same for all numbers of folds `k` and queries `l`:

{decl Specs.Fri.fri_erase}

The fold identity behind the check holds when $`x \ne 0` and $`2 \ne 0`:

{decl Specs.Fri.fold_check +statement}

The last fold reads position 0, since the domain of round `k + 1` has one point
({name}`Specs.Fri.loJ_last`). Honest acceptance: if the input oracle holds the witness word,
$`\omega \ne 0` and $`2 \ne 0`, the verdict accepts every honest transcript.

{decl Specs.Fri.fri_verdict_isSome +statement}

The proof applies {name}`Specs.Spec.verdict_isSome`, the generic loop lemma
{name}`Specs.rounds_complete` for each of the three loops with the invariant
{name}`Specs.Fri.FoldInv`, and the identity {name}`Specs.Fri.fold_check`. The invariant says that
the next level is `i + 1`, that the handle of $`f_j` reads level `j`, and that level `j` answers
with the honest word of round `j`:

{decl Specs.Fri.FoldInv}

{theorems Specs.Fri.fri_tree Specs.Fri.fri_erase Specs.Fri.fold_check Specs.Fri.loJ_last Specs.Fri.fri_verdict_isSome}

The module's tests also fix the folded TeX of the two checks,
$`2 \cdot x_{i} \cdot f_{i+1}(\mathrm{lo}(t_{j})) = x_{i} \cdot (a_{i} + b_{i}) + \alpha_{i} \cdot (a_{i} - b_{i})`
and $`2 \cdot x_{k} \cdot c = x_{k} \cdot (a_{k} + b_{k}) + \alpha_{k} \cdot (a_{k} - b_{k})`, and
their expanded TeX in consistency round 0 of query round 1 with `k = 2`.

Lean does not prove soundness of the FRI specification, or that `ω` has order $`2^{k+1}`. Honest
acceptance does not need the order, since the honest prover and the checks use the same index maps.
The proof kit proves FRI's commit phase, but the specification groups a round as challenge then
word, while the kit groups it as words then challenge; relating them is a regrouping lemma that
D10 lists as open.

# Design choices

* The checks contain no division. The fold
  $`f'(x^2) = (a + b)/2 + \alpha (a - b)/(2x)` is multiplied by $`2x`, and the two forms agree when
  $`2x \ne 0`, which is why the theorem assumes $`\omega \ne 0` and $`2 \ne 0`.
* The index maps `lo`, `hi` and `pt` are named functions in the formulas. Their printed names do not
  carry the round, since the name of a function in a formula is a fixed string.
* The checks write the arity-2 fold directly instead of calling ArkLib's
  `RoundConsistency.roundConsistencyCheck`. That check interpolates an arbitrary list of points over
  ArkLib's FFT domains. As a named function it would therefore hide the fold relation in the figure,
  and completeness would need its Lagrange-interpolation lemmas.
* Every name in a loop body is symbolic, and the values after the fold loop use the count symbol
  `k`. The expanded figure prints each symbol as its value ($`a_{2}` when `k = 2`).
* The printed types that depend on the round or the counts are symbolic strings
  ($`\mathbb{F}^{2^{k-i}}`, $`[2^{k+1}]`). Because these strings are annotation text, the expanded
  figure prints them unchanged.
* The consistency loop passes its round skeleton {name}`Specs.Fri.checkSkel` explicitly, because
  the hole types of its formulas mention the round.
* The state of the fold loop keeps the challenges and the references of all words, and
  {name}`Specs.Fri.FoldState.f` names a word's handle as the reading round needs.
