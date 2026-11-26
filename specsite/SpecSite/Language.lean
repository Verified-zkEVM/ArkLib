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

#doc (Manual) "The specification language" =>
%%%
tag := "language"
%%%

This chapter explains how to read and write a specification. It covers the constructs one at a
time: what a specification is and what Lean derives from it, the moves, the handles that moves
return, the formulas of checks and claims, the names that formulas print, loops, stages, branches,
the transcript accessors and the exports. Every construct is shown in its Lean source, from
`docs/design/interaction-layer/prototypes/Specs/`.

The running example is round `i` of sum-check, {name}`Specs.sumcheckRound`:

{decl Specs.sumcheckRound}

Read it top to bottom as a protocol figure. The prover sends the round polynomial `g_i` as an
oracle, honestly the projection `Sumcheck.projectedRoundPolynomial`. The verifier checks that `g_i`
sums to the current target `c_i` over the domain `D`, samples the challenge `r_i`, and computes the
next target `c_{i+1} = g_i(r_i)`. The last line passes the new claim to the next round. The
{ref "sumcheck"}[Sum-check page] shows the rest of the protocol.

# A specification and what Lean derives from it
%%%
tag := "spec"
%%%

A specification is a description of the protocol for every input statement:

{decl Specs.Spec}

The description type {name}`Specs.Desc` is in continuation-passing style. Each constructor is one
step of the protocol, and its last argument is the rest of the protocol, as a function of the value
that the step produces:

{decl Specs.Desc}

`Desc In W T t ks` has five parameters:

: `In`

  The input oracle bundle: the oracles that the verifier may query before any message, such as
  the polynomial of sum-check or the matrices of Spartan.

: `W`

  The witness. Every honest function reads it.

: `T`

  The output of the protocol, returned by `done`.

: `t`

  The protocol tree, an ArkLib `OracleProtocol`. Since it is a type index, no challenge, oracle
  handle or local value can change it.

: `ks`

  The skeleton, a {name}`Specs.Skel`: the moves, checks, local values, stages, loops and branches
  in protocol order, with every formula as syntax. It is also a type index. Hence it is computable
  even when the description uses noncomputable polynomials.

The anonymous constructor `Spec.mk` infers `t` and `ks` from the description. The tree, the
skeleton and the transcript type are read from the type of a specification:

{decl Specs.Spec.tree Specs.Spec.skeleton Specs.Spec.Tr Specs.Spec.Vw}

The skeleton is a list of items that ends in `done`, in a branch with one sub-skeleton per case, in
an opaque branch, or in a loop:

{decl Specs.Item Specs.Skel}

From one specification Lean derives the objects that ArkLib's proofs use. Three interpreters walk
the same description: {name}`Specs.Desc.prove` is the honest prover, {name}`Specs.Desc.run` is the
verifier's decision in any monad, and {name}`Specs.Desc.verdict` is the pure verdict on a full
transcript. The specification wraps them as ArkLib objects:

{decl Specs.Spec.prover Specs.Spec.verdict Specs.Spec.verifier}

:::table +header
* * Object
  * Definition
  * ArkLib type
* * Protocol tree
  * {name}`Specs.Spec.tree`, the index `t`
  * `OracleProtocol`
* * Honest prover
  * {name}`Specs.Spec.prover`: send the honest values, answer oracle queries from them and from the
    input data
  * `Focal oracleSig m t (fun _ => T)`
* * Verifier
  * {name}`Specs.Spec.verifier`: evaluate every check in order, querying input oracles and oracle
    messages through `pathBundle`
  * `OracleVerifier`
* * Pure verdict
  * {name}`Specs.Spec.verdict`: the same walk on a full transcript, with the oracle data supplied
  * `Option T`
* * Transcript accessors
  * `tr⟦sumcheck, 1, g⟧` ({ref "accessors"}[below])
  * projections of `Transcript` and `View`
* * Stage claims
  * {name}`Specs.Spec.inClaim`, {name}`Specs.Spec.outClaim`, {name}`Specs.Spec.inputProblem`,
    {name}`Specs.Spec.outputProblem`
  * ArkLib problems
* * Skeleton
  * {name}`Specs.Spec.skeleton`, the index `ks`, exported to JSON and LaTeX
  * {name}`Specs.Skel` (new)
:::

`Desc` has no monad parameter, and a check or a local value is a closed formula with its
arguments. The honest prover, the decision and the verdict therefore interpret the same term, and
`Specs.Run` proves their agreement once, by induction on the description. The first prototype ran
one description in two monads and needed parametricity, which Lean cannot prove. The two generic
theorems are:

: Decision as evaluation

  A monad morphism that answers the input queries from the input data and the oracle-message
  queries from the transcript sends the decision to `pure` of the verdict
  ({name}`Specs.Desc.run_hom`). {name}`Specs.Spec.decide_eq_verdict` is its instance for the
  decision of ArkLib's verifier.

: Honest acceptance

  On an honest transcript the verdict accepts when every check holds on the honest values for
  every choice of challenges ({name}`Specs.Desc.verdict_isSome`, {name}`Specs.Spec.verdict_isSome`).
  The condition is {name}`Specs.Desc.Complete`, and an honest transcript is one that satisfies
  {name}`Specs.Desc.Honest`.

{theorems Specs.Desc.run_hom Specs.Spec.decide_eq_verdict Specs.Desc.verdict_isSome Specs.Spec.verdict_isSome}

The verdict is a separate pure function on transcripts, not the decision at `Id`. Proofs about a
fixed protocol, such as honest acceptance or the agreement with ArkLib's sum-check verdict, then
destructure the transcript directly.

# Moves
%%%
tag := "moves"
%%%

An author writes a description with the combinators below, not with the constructors of
{name}`Specs.Desc`. Each combinator takes the rest of the protocol as its last explicit argument,
usually written as `fun x =>` on the same line. That way the description reads top to bottom. The
excerpts show each combinator's statement.

## Prover messages

`message` sends a plain message. The continuation's tree may depend on the value, but its skeleton
may not; a message that selects the skeleton is a {ref "branches"}[branch]. The string `hn` names
the honest function in the figure, as annotation text that Lean does not check.

{decl Specs.message +statement}

`oracle` sends an oracle message. The verifier does not see the value: it gets an oracle handle that
answers queries in `A`. The proof `hA` fixes one answer type for every query, by `rfl` by default,
because a formula query has one result type.

{decl Specs.oracle +statement}

## Challenges

`challenge` samples a public challenge. Its continuation's tree and skeleton cannot depend on the
challenge, which is record D1's rule that challenges do not select shape, enforced by the type.

{decl Specs.challenge +statement}

## Input oracles

`input` gives the description a named handle on an input oracle. The handle's queries go to
`embed q` of the input bundle, and `resp` shows that the answer has type `A`, usually as
`fun _ => rfl`. The verifier routes input queries to the input part of ArkLib's `pathBundle` and
message queries to the message part. The honest prover answers input queries from the input data.

{decl Specs.input +statement}

## Checks and local values

`check` is a verifier check: a Boolean formula on the handles `args`. `compute` is a local value of
the verifier: a formula of any type, whose value the continuation receives as a named
{name}`Specs.Val`. The {ref "formulas"}[formulas] section explains `φ`, and the
{ref "handles"}[handles] section explains `args`.

{decl Specs.check Specs.compute +statement}

The decision, {name}`Specs.Desc.run`, returns `none` at the first check that evaluates to `false`.
It runs once the interaction is over, on the verifier's whole view, as ArkLib's passive verifier
does.

## The end

`done` ends the protocol with its output.

{decl Specs.done}

Three more combinators shape the protocol rather than add a move. `rounds` writes a loop
({ref "loops"}[Loops]), `stage` declares a stage and its claims ({ref "stages"}[Stages and claims]),
and `branch` and `branchOpaque` let a prover message select the rest ({ref "branches"}[Branches]).

# Handles and arguments
%%%
tag := "handles"
%%%

A move passes its continuation a handle, not a bare value. A handle carries the move's display name
in its type:

{decl Specs.Ref Specs.Val Specs.OHdl}

A {name}`Specs.Val` is a transcript value or a local value, and it coerces to its value. An
{name}`Specs.OHdl` is an oracle, which the verifier reads only through queries. It holds a
first-order reference {name}`Specs.Ref`: the oracle's level, which is the number of oracles (input
reads and oracle messages) before it, and a default answer. Every interpreter passes the same handle
value to the continuation and resolves the level in its own table of query functions. The decision
resolves an oracle message to a query of the path's oracle messages, the verdict to the transcript's
message, and the prover to its honest message. All three resolve an input read through the input
bundle. The default answer keeps the interpreters total on a level that a description invents
itself; a description built from the combinators never does this.

Because the name is in the type, a formula can print the handle without any value. In the running
example, `g : OHdl (iv "g") _ R` prints as `g_i` and `st.c : Val (iv "c") R` prints as `c_i`.

A check or a local value names the handles it reads with the argument notation `⟪a, b, …⟫`. The
type class {name}`Specs.ToArgs` turns a tuple of handles into the list of the formula's holes, a
list of {name}`Specs.Hole`. Since the elaborator resolves the holes at once, the formula written
after the notation sees its hole list:

{decl Specs.Hole Specs.ToArgs}

In `check "sum" ⟪g, st.c⟫ (fun g c => …)` the holes are an oracle hole named `g_i` and a value hole
named `c_i`, and the formula is a Lean function of one oracle and one value. The formula's type is
`Curry v o Γ Bool` for the hole list `Γ`. {name}`Specs.Closed` packs it for every choice of the two
carriers `v` and `o`, which the {ref "formulas"}[next section] explains:

{decl Specs.Curry Specs.Closed}

Handles and formula arguments do not mention the input bundle. Inside a description the bundle is
often still a metavariable when Lean elaborates a `check`, and {name}`Specs.ToArgs` must not depend
on it.

# Formulas
%%%
tag := "formulas"
%%%

Checks, local values and stage claims are formulas, not strings. A formula is a term of
{name}`Specs.Fml`, a small typed language in parametric higher-order abstract syntax (PHOAS):

{decl Specs.Fml}

The carrier `v` holds the bound values and the carrier `o` holds the oracle handles. There are two
carriers because the verifier reads an oracle only through queries: an oracle hole must not be
usable as a value, and with one carrier a formula could print an oracle as a value.

Formulas use Lean's arithmetic operators through instances on {name}`Specs.Fml`, a numeral is a
literal that prints as itself, `='` is decided equality and `∧'` is conjunction. An oracle query is
written with {name}`Specs.ask`:

{decl Specs.ask}

A sum or a product ranges over a finite domain. The notation `∑∈ x ∈ D, body` is
`Fml.sum` with the binder `x`, and `∏∈ x ∈ D, body` is `Fml.prod`. The binder prints as the Lean
identifier. A domain is a printed name and its elements:

{decl Specs.Dom Specs.Dom.ofFn Specs.Dom.pow Specs.Dom.fin}

The verifier evaluates a sum by enumerating the domain, and the figure prints
$`\sum_{a \in D}` without enumerating it. A domain holds its elements behind a function from `Unit`.
Since compiled code evaluates every argument of a constructor, a domain that stored its list would
build all $`k^n` points of `Dom.pow` whenever the export computes a formula's syntax, which made the
export exponential in the number of rounds. A function from `Unit`, rather than a `Thunk`, keeps the
elements reducible by `simp only`.

Two more constructors serve real protocols. `Fml.app` applies a named opaque function and prints
$`\mathrm{name}(x)`, as FRI's index maps `lo`, `hi` and `pt` do. `Fml.index` reads coordinate `j` of
a vector and prints it as a subscript, as in Spartan's
$`\prod_{j \in [m]} (\tau_{j} \cdot x_{j} + (1 - \tau_{j}) \cdot (1 - x_{j}))`. A literal carries
its printed form, since its value can be a polynomial or another object with no canonical printing.

## One formula, three readings

The round check of sum-check is `(∑∈ a ∈ Dom.ofFn "D" D, ask g a) =' .var c`. The same term is read
three ways:

: Evaluation

  {name}`Specs.Fml.evalM` runs a formula in a monad. The oracle answers come from a function `ask`
  on the carrier `o`, and the honest prover, the decision and the verdict instantiate the formula
  at the same carriers and differ only in `ask`. {name}`Specs.Fml.eval` is the evaluation without
  effects.

: Syntax

  {name}`Specs.Fml.syntax` instantiates both carriers at names and converts the formula into the
  untyped first-order tree {name}`Specs.Syn`. Because the skeleton stores this tree, the JSON can
  carry it. An untyped tree of strings and names keeps the skeleton computable even when a formula's
  values are noncomputable.

: TeX

  {name}`Specs.Fml.tex` prints the formula. With the names of the handles, the round check prints
  $`\sum_{a \in D} g_{i}(a) = c_{i}` in the folded figure and
  $`\sum_{a \in D} g_{1}(a) = c_{1}` in round 1 of the expanded figure (tests in
  `Examples/Sumcheck.lean`).

Two theorems tie the readings together. {name}`Specs.Fml.tex_eq` proves that printing a formula and
printing its syntax tree agree, and {name}`Specs.Fml.erase_toFO` proves that the exported tree is
the typed first-order form {name}`Specs.FO` with its types forgotten:

{decl Specs.Fml.tex_eq Specs.Fml.erase_toFO +statement}

{theorems Specs.Fml.tex_eq Specs.Fml.erase_toFO Specs.Fml.eval_sum Specs.Fml.eval_prod}

A reviewer who trusts the two small interpreters, the evaluator and the printer with one case per
constructor, trusts every figure, instead of comparing each string with its term. A formula is
parametric in its carriers. Therefore it cannot behave differently when printed and when evaluated.

That the exported tree evaluates like the formula, `FO.eval (toFO φ) = some (Fml.eval φ)`, is tested
on the examples' formulas but not proved in general ({ref "limitations"}[limitation 1]). A general
proof relates a PHOAS term at two carriers and needs parametricity, which Lean cannot prove
internally. Sum-check's tests check it for the round check by `simp`.

# Names and indices
%%%
tag := "names"
%%%

Every value, oracle and binder has a display name: a TeX base and a subscript.

{decl Specs.Ix Specs.Subscript Specs.Name}

An index is a fixed number or a symbol with an offset, never the number of a round. The symbol is a
loop's round variable (`i`) or a loop's count (`n`). The helpers below build the usual names:

{decl Specs.ix Specs.iv Specs.ivBelow}

A name prints in a {name}`Specs.Mode`. The folded figure prints every symbol as itself. The expanded
figure prints the value of each bound symbol: a round variable is bound to its round and a count to
the loop's count. An unbound symbol prints as itself.

{decl Specs.Mode Specs.Mode.bind Specs.Ix.tex}

The folded column and the expanded printings of `g`, `c_{i+1}` and `c_n` are tests in
`Specs/Formula.lean`; the other expanded printings follow from {name}`Specs.Ix.tex`:

:::table +header
* * Lean
  * Folded
  * Expanded
* * `ix "c" 0`
  * $`c_{0}`
  * $`c_{0}`
* * `iv "g"`
  * $`g_{i}`
  * $`g_{2}` with `i` bound to 2
* * `iv "c" 1`
  * $`c_{i+1}`
  * $`c_{3}` with `i` bound to 2
* * `iv "f" (-1)`
  * $`f_{i-1}`
  * $`f_{1}` with `i` bound to 2
* * `ivBelow "r"`
  * $`r_{<i}`
  * $`r_{<2}` with `i` bound to 2
* * `iv "c" (v := "n")`
  * $`c_{n}`
  * $`c_{3}` with `n` bound to 3, and $`c_{n}` with `n` unbound
:::

The index is symbolic because a loop's body is one skeleton for all of its rounds
({ref "loops"}[Loops]). A name in the body therefore cannot depend on the round, and `c_{i+1}`
is written `iv "c" 1`, never with the round's number. After a loop, a name can use the loop's
count: the sum-check stage ends with the target `iv "c" (v := "n")`, which prints $`c_{n}`. A
subscript can also be a fixed symbol (`Subscript.sym`), as in Spartan's $`r_{x}` and $`v_{A}`.

Names of the first prototype carried only an offset from the innermost round. They could not name a
value after the loop, such as $`c_{n}`, or the round variable of an outer loop, such as FRI's query
index $`j` inside the consistency loop over $`i` ({ref "limitations"}[limitation 9]).

# Loops
%%%
tag := "loops"
%%%

A loop is written once, for a generic round, as a paper writes it. `rounds block n init body next`
runs `body i` for `i = 0, …, n - 1`. Round `i` maps a state `State i` to `State (i + 1)`, and `next`
receives the final state. The count `n` is a Lean term and may be a variable.

{decl Specs.rounds}

{decl Specs.Loop}

The loop is one node of the skeleton, {name}`Specs.Skel.loop`. Its body is the skeleton of one
round, written over the round variable `i` and the count's symbol `n`. The display data
{name}`Specs.Loop` holds the block name, the round variable, the count's symbol and the soundness
error of one round, which prints as annotation text.

Sum-check's loop is `rounds` with the round {name}`Specs.sumcheckRound`, the error `d/|F|`, the
count symbol `n` and the round variable `i`:

{decl Specs.sumcheck}

## The round's skeleton must not depend on the round

`rounds` infers the skeleton of `body` as `G ks`, with `G` a function of the continuation's
skeleton only, not of the round number. The argument `hG` requires `G ks = (G .done).seq ks`, by
`rfl` by default. If any name, type or formula in a round mentioned the round number, `G` would have
to depend on it and elaboration would fail. So the one displayed round is, by typing, the skeleton
of every round. This is why names in a body use symbols (`iv "g"`, `iv "c" 1`), and why a type whose
printed name depends on the round passes a symbolic name, as FRI's word type does with
`ty := "\\mathbb{F}^{2^{k-i}}"`.

When the hole types of a round mention the round, `rounds` cannot infer `G` by unification. FRI's
consistency loop is the example: its oracle `f_i` answers queries in a domain whose size depends on
`i`. The author then passes the round skeleton explicitly (`G := checkSkel F ω k`), and Lean checks
by evaluation that every round has it ({ref "fri"}[FRI]).

## The tree of a loop

`rounds` passes the absolute round to the body, and the round's tree may vary with it:
`F : ℕ → OracleProtocol → OracleProtocol`. FRI needs this, since its oracle in round `i` lives on a
domain of size $`2^{k-i}`. By default the tree of the rounds is {name}`Specs.roundsTree`:

{decl Specs.roundsTree}

A `rounds` block may name another tree family (`tree`) when each step agrees with it by `rfl`. Since
the elaborator cannot unfold a structural recursion on a variable `n`, ArkLib's
`Sumcheck.protocol R d n` is not definitionally equal to a generic tree. Naming ArkLib's tree makes
the agreement theorems typecheck as they are: `sumcheckSpec` passes
`tree := fun _ r => Sumcheck.protocol R d r`.

## Folded and unrolled

The description keeps the unrolled rounds. `Desc.loop l n body inner` holds them as a description
of skeleton `Skel.unroll l body rest 0 n`, with begin and end markers per round. The interpreters
and the proofs about them run on the unrolled description unchanged, and the index ties the generic
body to the rounds that run. {name}`Specs.roundsGo` builds the unrolled rounds, and
{name}`Specs.roundsFrom` is the rest of a loop from round `j`, on which proofs state their round
induction.

{decl Specs.Skel.unroll}

The count stays in the skeleton, because the expanded figure and the accessors into later rounds
need its value. {name}`Specs.Skel.erase` sets every count to `0`:

{decl Specs.Skel.erase}

Each example proves by `rfl` that its erased skeleton is the same for every count. Because the JSON
and the folded figure read only the erased skeleton, they describe the protocol for every count:

{theorems Specs.sumcheck_erase Specs.Spartan.spartan_erase Specs.Fri.fri_erase}

The figure below is sum-check as Lean computes it. The folded view prints one generic round with
`g_i`, `r_i` and `c_{i+1}`. The expanded view unrolls the loop at the count you choose and prints
every symbol as its value.

{protocols SpecSite.sumcheck}

## Completeness of a loop

A loop is complete if each round is complete whenever its continuation is complete. The invariant
`I i st env ℓ` relates the state before round `i` to the table of oracle query functions and the
next level:

{decl Specs.rounds_complete +statement}

FRI uses {name}`Specs.rounds_complete` for all three of its loops. Sum-check proves its own loop
lemma, {name}`Specs.sumcheck_complete`, which Spartan and the branching example reuse.

{theorems Specs.roundsGo_complete Specs.rounds_complete}

# Stages and claims
%%%
tag := "stages"
%%%

A stage is a named part of the protocol that reduces one claim to another. It consumes the claim
`φ` on the handles `inArgs` and produces the claim `ψ` on `outArgs s`, where `s` is the value that
its body passes on:

{decl Specs.stage}

The body receives the continuation that closes the stage. In sum-check the stage `sumcheck` consumes
$`\sum_{x \in D^{n}} p(x) = c_{0}` and produces $`p(r) = c_{n}`, and its body is the loop:

{decl Specs.sumcheckSpec}

Because the claims are formulas, the verifier could evaluate them and the figure prints them. The
figure prints a stage's input claim where the stage opens and its output claim where it closes,
because the output claim names values after the loop, such as $`c_{n}`, which print with the count's
symbol.

No interpreter checks a stage claim. A claim states what a stage reduces, and a soundness proof
uses it as a relation, not as a verifier step. {name}`Specs.Desc.inClaim` evaluates the input claim
of the first stage, read before any move, and {name}`Specs.Desc.outClaim` evaluates the output claim
of the last stage along a full transcript. {name}`Specs.Spec.inputProblem` and
{name}`Specs.Spec.outputProblem` are the ArkLib problems whose languages these claims denote. The
{ref "proofs"}[Proofs] chapter states soundness and completeness on them.

A claim can be shared. Spartan's two stages receive one value, {name}`Specs.Spartan.rowClaims`. As a
result, the output claim of `outer` and the input claim of `inner` are the same formula by
construction ({ref "spartan"}[Spartan]). Stage contracts read the first stage's input claim and the
last stage's output claim; contracts for the inner stages of a multi-stage specification are not
stated yet ({ref "limitations"}[limitation 7]).

# Branches
%%%
tag := "branches"
%%%

A plain prover message may select the shape of the rest of the protocol. `branch` is a message
whose continuation's tree and skeleton both depend on the value. The skeleton has one case for each
element of `cases`, printed with its string:

{decl Specs.branch Specs.branchOpaque +statement}

`branchOpaque` is a branch on a message with no listed cases, such as a message of infinite type.
The skeleton marks it opaque, and the figure prints "the rest depends on" the message. Both build
their skeleton node with {name}`Specs.Skel.ofBranch`:

{decl Specs.Skel.ofBranch}

Challenges and oracle messages cannot select the shape, since their continuations have a fixed tree
and skeleton. The {ref "branching"}[branching example] has the prover send the number of variables
`m : Fin 4`, and an `m`-variable sum-check follows. Its figure shows one case for each value of `m`.

Since a transcript after a branching message has a type that depends on the message, no projection
reaches a move inside a case. {name}`Specs.caseOf` returns the rest of the transcript when the
message is a given value, and `none` otherwise:

{decl Specs.caseOf}

{theorems Specs.caseOf_self Specs.caseOf_ne}

# Transcript accessors
%%%
tag := "accessors"
%%%

An accessor reads a move of a transcript by its hierarchical label. `tr⟦a, …, x⟧` is the move with
name base `x` inside the stages, blocks and rounds `a, …`. In sum-check with three rounds:

```lean
example (D : Fin 2 → ℚ)
    (tr : (Specs.sumcheckSpec ℚ 2 3 D).Tr) :
    tr⟦sumcheck, 1, g⟧ = tr.2.2.1 := rfl
example (D : Fin 2 → ℚ)
    (tr : (Specs.sumcheckSpec ℚ 2 3 D).Tr) :
    tr⟦g⟧ = tr.1 := rfl
```

The elaborator walks the skeleton in the type of `tr` and emits a chain of `.1` and `.2`
projections. The result is a projection term. Hence it reduces by `rfl` and `simp` for every count
at which the skeleton up to the move is concrete. Because Lean computes the position while it
elaborates the label, a goal never contains a comparison of label strings. A label follows these
rules:

* The components before the last are stage names, block names and round numbers. They must appear,
  in order, among the stages, loops and rounds that enclose the move, but need not list all of
  them. `tr⟦g⟧` is the first `g` of sum-check, the polynomial of round 0.
* The last component is the base of the move's name. With the base alone, the accessor reads the
  first such move in the context.
* When moves in one context share a base, the last component adds the subscript, as an identifier
  such as `v_B` or as a string such as `"\\alpha_2"`. A subscript is matched as the expanded figure
  prints it, with each enclosing round variable and each finished loop's count bound to its
  numeral. In FRI with `k = 2`, the final challenge `α_k` matches `"\\alpha_2"`.
* A component `m = v` enters the case labelled `v` of the branch on the message `m`. The accessor
  then has type `Option α`: `some` of the move when the transcript's message is that case, and
  `none` otherwise. It goes through {name}`Specs.caseOf`.
* The accessor reaches moves: messages, oracle messages, challenges and branching messages. Input
  reads and local values are not part of the transcript.
* The accessor also works on a view of the verifier, of type `Spec.Vw s p`.

The examples' tests use every rule:

:::table +header
* * Accessor
  * Reads
* * `tr⟦sumcheck, 2, r⟧`
  * the challenge of round 2 of sum-check
* * `tr⟦outer, sumcheck, 0, g⟧`, `tr⟦inner, sumcheck, 0, g⟧`
  * the round-0 polynomials of Spartan's two stages, which are different moves
* * `tr⟦outer, v_B⟧`, `tr⟦inner, "\\rho_C"⟧`
  * Spartan's row value $`v_{B}` and batching challenge $`\rho_{C}`, by subscript
* * `tr⟦fold, 1, f⟧`, `tr⟦c⟧`, `tr⟦query, 1, t⟧`
  * FRI's word $`f_{2}` (sent in fold round 1), its final constant, and the position of its second
    query
* * `tr⟦m = 2, sumcheck, 1, r⟧`
  * the branching example's challenge of round 1 in the case $`m = 2`, as an `Option`
:::

The accessor has limits ({ref "limitations"}[limitation 9]). It needs a numeral count and a numeral
round: an accessor at a symbolic round `i` would need the loop's tree as a function of the round and
a transcript split at round `i`. It does not reach into a branch inside a loop body. At round 127 of
a 128-round sum-check it exceeds Lean's default `maxRecDepth` of 512, and the benchmark raises the
limit for that definition ({ref "limitations"}[limitation 8]).

# Exports
%%%
tag := "skeleton-exports"
%%%

Since the skeleton is part of a specification's type, the export never runs a description.
`Specs.Export` writes it as JSON and as a `cryptocode` figure.

{decl Specs.Skel.toJson}

The JSON has the schema `arklib-protocol-skeleton/2`. It nests stages, loops and branch cases, while
the skeleton keeps flat stage markers so that `simp` and `rfl` reduce it as a list. Its nodes are:

:::table +header
* * Kind
  * Fields
* * `move`
  * `move` (message, oracle or challenge), `owner` (prover or verifier), `name`, `type`, `honest`,
    `note`
* * `input`
  * `name`, `type`
* * `check`
  * `label`, `formula`, `note`
* * `let`
  * `name`, `type`, `formula`, `note`
* * `stage`
  * `name`, `input` and `output` claims, `body`
* * `loop`
  * `block`, `var`, `count`, `error`, `body` (one generic round)
* * `branch`
  * `on`, `type`, `honest`, and `cases`, each a `value` with a `body`
* * `opaque`
  * `on`, `type`, `honest`
:::

A name carries its base, its subscript and its folded TeX. An index in a subscript is a number
(`{"num": 0}`) or a symbol with an offset (`{"symbol": "i", "offset": 1}`). A formula carries its
syntax tree and its folded TeX. Every annotation (a move's note, the name of an honest function, a
loop's error) exports as `{"text": …, "checked": false}`, since nothing in Lean checks it. Version 1
of the schema unrolled every round with its number. A JSON file of version 1 therefore described
the protocol at one round count only.

{decl Specs.Skel.toTex}

The figure comes in two forms. The folded figure reads the erased skeleton and prints each loop as
one generic round over its round variable and count symbol. Like the JSON, it is the same at every
count, by the `erase` theorems of the {ref "loops"}[Loops] section. The expanded figure reads the
skeleton with its counts, unrolls each loop, and prints every symbol as its value. Since the count
stays bound after a loop, $`c_{n}` prints as $`c_{3}`. A dotted division opens each stage, round and
case. Annotation prints in gray with `\specannot`. {name}`Specs.writeExample` writes `name.json`,
the folded `name.tex` and the expanded `name-expanded.tex`, which `Specs/Main.lean` runs for the
four examples.

Some text in the exports is still annotation ({ref "limitations"}[limitation 9]). Parameters other
than counts print their values: sum-check's degree `d` appears as `2/|F|` in the example's error
annotation. The JSON therefore depends on `d`. Printed types are annotation too, and a type that
depends on a count or the round, such as FRI's word type $`\mathbb{F}^{2^{k-i}}`, is written
symbolically and prints symbolically in the expanded figure as well. `Skel.checks` lists a loop
body's checks once.
