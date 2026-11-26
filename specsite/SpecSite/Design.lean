/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Blocks
import Specs.Claims
import Specs.Export
import Specs.Examples.Spartan
import Specs.Examples.Fri
import Specs.Examples.Branching
import Specs.Kit.Fri
import Specs.Kit.TwoMessage
import ArkLib.Interaction.StageChain

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "The design record" =>
%%%
tag := "design"
htmlSplit := .never
%%%

This chapter is decision record D10, _Protocol specifications and the round-iteration proof kit_,
from `docs/design/interaction-rebuild/D10-protocol-specifications.md`. Its status is _proposed,
awaiting maintainer approval_. A post-milestone track implements it in the stages listed under
{ref "design-plan"}[Order of work]. Stage 0 is the prototype library `ArkLibPrototypes` under
`docs/design/interaction-layer/prototypes/Specs/`.

The prototype is a nondefault Lake library (`lake build ArkLibPrototypes`). It is outside the
production import graph, its files are classic so that `#print axioms` sees proof bodies, and it
builds against `main`. It has no `sorry`, `admit`, `native_decide` or `smartUnfolding` option, and
every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Every code excerpt in
this chapter is loaded from the prototype when the site builds, and every theorem table checks the
axioms of its theorems.

The first version of the prototype (two standalone files) left eight open points. Review judged
them to be limitations, not open questions, and the second version fixes each of them. Review of
the second version found a ninth: a loop was written out round by round for one fixed count. As a
result, each figure and each JSON file described one instance. The current version represents a loop
once, generic in its count. The section {ref "limitations"}[Limitations of the prototype] gives the
decision, the reason and the evidence for each of the nine.

# Decision
%%%
tag := "design-decision"
%%%

An author writes each protocol once, as a value of a description type, and the interaction layer's
objects are computed from that value. The eleven parts of the decision follow, lettered A to K.
The {ref "language"}[specification language] chapter treats the language in depth.

::::card "One description per protocol" (n := "A")
An author writes an interactive oracle reduction once, as a value of a description type whose
terms read like a paper's protocol figure: named prover messages (plain or oracle) with their
honest values, named challenges, reads of input oracles, verifier checks and local values written
as formulas next to the round whose moves they read, rounds, stages with their input and output
claims, and branches on a prover message. The interaction layer's objects are computed from that
value. Here is sum-check's round and its specification:

{decl Specs.sumcheckRound}

{decl Specs.sumcheckSpec}

Names inside a round are indexed by the loop's round variable: `iv "g"` is $`g_i`, `iv "c" 1` is
$`c_{i+1}`, and after the loop `iv "c" (v := "n")` is $`c_n`. `ix "c" 0` is the fixed index
$`c_0` (see {name}`Specs.iv` and {name}`Specs.ix`). `sumcheck n D poly input next` is
`rounds "sumcheck" n input (sumcheckRound n D poly) next` with error annotation `d/|F|`, count
symbol `n` and round variable `i`:

{decl Specs.sumcheck}

The description `Desc In W T t ks` ({name}`Specs.Desc`) is in continuation-passing style. `In` is
the input oracle bundle, `W` the witness and `T` the output. Its two indices are the protocol tree
`t` and the skeleton `ks`. A continuation receives a challenge value, an oracle handle or a local
value, but it cannot change either index. The type thus enforces record D1's rule that challenges
and oracle payloads do not select the shape. A plain message may select the shape
({name}`Specs.branch`), as D1 allows.
::::

::::card "Shallow elaboration, deep skeleton" (n := "B")
The description elaborates to the existing core objects, and proofs work on those objects exactly
as they do on hand-written ones.

:::table +header
* * Output
  * Definition
  * Core object
* * Protocol tree
  * `s.tree` (the index `t`)
  * {name}`Interaction.OracleProtocol`
* * Honest prover
  * {name}`Specs.Spec.prover`: send the honest values, answer oracle queries from them and from
    the input data
  * `Focal oracleSig m t Out`
* * Verifier
  * {name}`Specs.Spec.verifier`: evaluate every check in order, decide at the leaf, query input
    and message oracles through {name}`Interaction.pathBundle`
  * {name}`Interaction.OracleVerifier`
* * Pure verdict
  * {name}`Specs.Spec.verdict`: the same walk with the oracle data supplied
  * `Option T`
* * Accessors
  * `tr⟦outer, sumcheck, 0, g⟧`, `tr⟦m = 2, sumcheck, 1, r⟧`
  * projections of `Transcript`, `View`
* * Claims
  * {name}`Specs.Spec.inClaim`, {name}`Specs.Spec.outClaim`, {name}`Specs.Spec.inputProblem`,
    {name}`Specs.Spec.outputProblem`
  * ArkLib `Problem`s
* * Skeleton
  * `s.skeleton` (the index `ks`), exported to JSON and LaTeX
  * new: {name}`Specs.Skel`
:::
::::

::::card "Formulas, not strings" (n := "C")
Checks, local values and stage claims are terms of a small typed formula language `Fml v o β`
({name}`Specs.Fml`, in `Specs/Formula.lean`) in parametric higher-order abstract syntax (PHOAS).
It has variables, literals, ring operations, decided equality, conjunction, finite sums and
products with a binder, oracle queries, coordinate access, and named opaque functions. The
verifier evaluates the term ({name}`Specs.Fml.evalM`), the figure prints it ({name}`Specs.Fml.tex`),
and the skeleton and the JSON carry its erased syntax ({name}`Specs.Syn`). Every name that a
formula prints is the name in the type of the handle it reads. A printed variable is
therefore the move it denotes.
::::

::::card "Checks are written in place and decided at the leaf" (n := "D")
A check sits next to the round whose moves it reads, and the verifier decides all checks at the
leaf. This keeps record D4's passive verifier and the premise that nothing rejects early.
::::

::::card "Rounds count up, carry round-indexed state, and may change shape" (n := "E")
{name}`Specs.rounds` runs `body i` for `i = 0, …, n - 1` with state `State i → State (i + 1)` and
an optional tree family, which lets round `i`'s tree depend on `i` (FRI's domain halves). The
generated tree is the existing one: {name}`Specs.sumcheck_tree` holds by `rfl` against
`Sumcheck.protocol R d n`. This settles record D5's open point on dependent iteration state:
`rounds` and the kit certificate own the state, not `FreeM.replicate`.
::::

::::card "A loop is one node, generic in its count" (n := "F")
`rounds` records the skeleton node `Skel.loop l n body rest` ({name}`Specs.Skel.loop`). `l` names
the block, the round variable, the count symbol and the error annotation, and `body` is one round's
skeleton, whose names are indexed by the round variable:

{decl Specs.Loop}

`rounds` requires that a round's skeleton not depend on the round number (the argument `hG`, proved
by `rfl` by default). One body is therefore correct for every round. The JSON and the folded figure
read the skeleton with every count erased ({name}`Specs.Skel.erase`). They are therefore the same
for every count. {name}`Specs.sumcheck_erase`, {name}`Specs.Spartan.spartan_erase` and
{name}`Specs.Fri.fri_erase` prove that by `rfl`. The expanded figure unrolls each loop at the sizes
the author picks.
::::

::::card "Stages declare their claims as formulas, and security statements are about those claims" (n := "G")
`stage name inArgs inClaim outArgs outClaim body next` ({name}`Specs.stage`) records the claim the
stage consumes and the claim it produces. {name}`Specs.Spec.inputProblem` and
{name}`Specs.Spec.outputProblem` are the languages that those formulas denote, and the statement
front end states soundness and completeness on them.
::::

::::card "A statement front end" (n := "H")
{name}`Specs.Spec.Sound`, {name}`Specs.Spec.RBRSound`, {name}`Specs.Spec.RBRKnowledgeSound` and
{name}`Specs.Spec.Complete` (in `Specs/Security.lean`) are definitions over `Interaction.Security`
applied to the derived prover and verifier. Each has an `iff` lemma proved by `Iff.rfl`:
{name}`Specs.Spec.sound_iff`, {name}`Specs.Spec.rbrSound_iff`,
{name}`Specs.Spec.rbrKnowledgeSound_iff` and {name}`Specs.Spec.complete_iff`. The stage contracts
{name}`Specs.Spec.ClaimSound`, {name}`Specs.Spec.ClaimRBRSound`, {name}`Specs.Spec.ClaimComplete`
and {name}`Specs.Spec.StageContract` state them on the spec's own claims.
::::

::::card "A proof kit consumes the same round structure" (n := "I")
A kit round is a block of zero or more prover messages, plain or oracle, with types that may
depend on the round, followed by one challenge. An iteration has a prefix block and a suffix block.
The iteration theorem ({name}`Specs.Kit.Rounds.rbrSoundness`) builds round-by-round soundness from
a one-round obligation that mentions no spine, cursor or partial transcript, and soundness with
error `∑ i, ε i` follows ({name}`Specs.Kit.Rounds.soundness_of_rbrSoundness`). The obligation:

{decl Specs.Kit.RoundSound}

The {ref "proofs"}[Proofs] chapter treats the kit in depth.
::::

::::card "A bridge connects the two" (n := "J")
`Specs/Bridge/Rounds.lean` proves, for any `rounds` block whose round bodies have the kit's shape,
that the spec's verdict factors through the kit's iteration verdict. It concludes `Spec.Sound` from
per-round `RoundSound` ({name}`Specs.Bridge.sound_of_kit`, {name}`Specs.Bridge.rbrSound_of_kit`).
A protocol written in the spec layer thus gets its soundness from the kit without a hand-written
verifier.
::::

::::card "One skeleton schema" (n := "K")
The exporter writes `arklib-protocol-skeleton/2` JSON and a `cryptocode` figure. The JSON has
nested stages, loops and branch cases. A loop node carries its block name, round variable, count
symbol, error annotation and one round's body. Each step carries its label, kind, owner, display
name, printed type, formula syntax tree and stage claims, and any annotation text carries
`"checked": false`. An index in a name is a numeral (`{"num": 0}`) or a symbol with an offset
(`{"symbol": "i", "offset": 1}`). The figure comes in two forms: folded (one generic round per
loop, the same for every count) and expanded (every round at given sizes). The Binary Jolt Book's
book-graph reads the same schema. The {ref "protocols"}[Four protocols] chapter shows the JSON and
both figures of each example.
::::

# What the prototype proves
%%%
tag := "design-proves"
%%%

The prototype proves that the derived objects are ArkLib's, that the generic agreement theorems
hold for every spec, and that sum-check's soundness goes through the kit and the bridge.

:::table +header
* * Claim
  * Declaration
  * File
* * Sum-check's tree is ArkLib's, for every `n`, by `rfl`
  * {name}`Specs.sumcheck_tree`
  * `Examples/Sumcheck.lean`
* * Its honest prover is {name}`Sumcheck.intervalProver`
  * {name}`Specs.sumcheck_prover`
  * same
* * Its verdict is {name}`Sumcheck.indexedVerdict`, and its verifier agrees with
    {name}`Sumcheck.indexedVerifier` on every transcript
  * {name}`Specs.sumcheck_verdict`, {name}`Specs.sumcheck_decide`, {name}`Specs.sumcheck_outputMap`
  * same
* * The decision of any spec equals its pure verdict
  * {name}`Specs.Spec.decide_eq_verdict`
  * `Run.lean`
* * Any spec accepts the honest transcript when its checks hold on the honest run
  * {name}`Specs.Spec.verdict_isSome`
  * `Run.lean`
* * Sum-check soundness through the generalized kit, with exactly the statement of
    {name}`Sumcheck.indexedVerifier_soundness`
  * {name}`Specs.Kit.indexedVerifier_soundness_viaKit`, checked with `type_of%`
  * `Kit/Sumcheck.lean`
* * Round-by-round soundness of FRI's commit phase, whose domain halves each round, from ArkLib's
    folding lemmas, with no undischarged hypothesis
  * {name}`Specs.Kit.Fri.commitPhase_rbrSoundness`,
    {name}`Specs.Kit.Fri.commitPhase_rbrSoundness_johnson`
  * `Kit/Fri.lean`
* * Soundness of a round with two messages (an oracle and a plain message)
  * {name}`Specs.Kit.twoVerifier_soundness`
  * `Kit/TwoMessage.lean`
* * Soundness of the verifier that {name}`Specs.sumcheckSpec` derives, error $`n \cdot d / |R|`,
    through the bridge and not through `indexedVerifier`
  * {name}`Specs.Bridge.sumcheckSpec_sound`
  * `Bridge/Sumcheck.lean`
* * The same verifier agrees with the kit's iteration verifier
  * {name}`Specs.Bridge.sumcheckSpec_agrees`
  * `Bridge/Sumcheck.lean`
* * Soundness and round-by-round soundness on the claims the figure shows:
    $`\sum_{x \in D^n} p(x) = c` in, $`p(r) = c_n` out
  * {name}`Specs.Claims.sumcheckSpec_claimSound`, {name}`Specs.Claims.sumcheckSpec_claimRBRSound`
  * `Claims.lean`
* * Completeness on those claims: a true input claim makes every check pass and the output claim
    true
  * {name}`Specs.Claims.sumcheckSpec_claimComplete`, {name}`Specs.Claims.sumcheckSpec_contract`
  * `Claims.lean`
* * Spartan (input oracles $`\tilde A`, $`\tilde B`, $`\tilde C`, two stages reusing sum-check),
    FRI (halving domain, input oracle $`f_0`) and a branching protocol: trees by `rfl`, accessors
    by label path, honest acceptance
  * {name}`Specs.Spartan.spartan_tree`, {name}`Specs.Fri.fri_tree`, {name}`Specs.branching_tree`,
    and the three `*_verdict_isSome` theorems {name}`Specs.Spartan.spartan_verdict_isSome`,
    {name}`Specs.Fri.fri_verdict_isSome`, {name}`Specs.branching_verdict_isSome`
  * `Examples/*.lean`
* * The JSON and the folded figure of sum-check, Spartan and FRI do not depend on the round counts
  * {name}`Specs.sumcheck_erase`, {name}`Specs.Spartan.spartan_erase`, {name}`Specs.Fri.fri_erase`
  * `Examples/*.lean`
:::

When the site builds, it checks that every theorem in the table exists and depends only on Lean's
three standard axioms:

{theorems Specs.sumcheck_tree Specs.sumcheck_prover Specs.sumcheck_verdict Specs.sumcheck_decide Specs.sumcheck_outputMap Specs.Spec.decide_eq_verdict Specs.Spec.verdict_isSome Specs.Kit.indexedVerifier_soundness_viaKit Specs.Kit.Fri.commitPhase_rbrSoundness Specs.Kit.Fri.commitPhase_rbrSoundness_johnson Specs.Kit.twoVerifier_soundness Specs.Bridge.sumcheckSpec_sound Specs.Bridge.sumcheckSpec_agrees Specs.Claims.sumcheckSpec_claimSound Specs.Claims.sumcheckSpec_claimRBRSound Specs.Claims.sumcheckSpec_claimComplete Specs.Claims.sumcheckSpec_contract Specs.Spartan.spartan_tree Specs.Fri.fri_tree Specs.branching_tree Specs.Spartan.spartan_verdict_isSome Specs.Fri.fri_verdict_isSome Specs.branching_verdict_isSome Specs.sumcheck_erase Specs.Spartan.spartan_erase Specs.Fri.fri_erase}

# Limitations of the prototype and how this record resolves them
%%%
tag := "limitations"
%%%

The record resolves all nine limitations. Four of them leave gaps that it names, and their cards
(1, 4, 7 and 9) are marked partial. Items 1 to 8 are the first prototype's limitations, and item 9
is the second prototype's. Each item names the limitation, the decision, why, the alternatives
rejected, and the evidence in the current prototype.

::::card "Display text was not checked" (n := "1") (status := "partial")
: Decision

  Checks, local values and stage claims are formulas with three readings: evaluation, TeX and
  erased syntax. No check, local value or claim carries hand-written display text. The remaining
  free text is _annotation_: the printed type of a message, the name of an opaque honest function
  such as `\mathsf{proj}`, a round's error, and a literal's printed form. The figure prints
  annotation in gray, and the JSON marks it `"checked": false`.

: Why

  A reviewer who trusts two small interpreters (one case per constructor) trusts every figure,
  instead of comparing each string with its term. PHOAS keeps the syntax printable and
  inspectable, lets authors write binders as Lean lambdas, and needs no universe of types. Because a
  formula is parametric in its variable carrier, it cannot behave differently when printed and
  when evaluated.

: Rejected

  A value paired with a string at each node cannot print a binder's body without a value. A deep
  embedding with named variables and a dynamic environment needs a type universe that covers
  `R⦃≤ d⦄[X]`, `Fin N → R` and the rest. Proving the TeX correct has no meaning, since TeX has no
  semantics in Lean.

: Evidence

  {name}`Specs.Fml.tex_eq` proves that printing a formula and printing its erased syntax agree.
  {name}`Specs.Fml.erase_toFO` proves that the erased syntax is the erasure of the typed
  first-order form. `#guard` tests fix the printed text of every example's checks. The generated
  sum-check check is `\sum_{a \in D} g_{i}(a) = c_{i}` in the folded figure, which renders as
  $`\sum_{a \in D} g_{i}(a) = c_{i}`, and `\sum_{a \in D} g_{1}(a) = c_{1}` in round 1 of the
  expanded one.

  {theorems Specs.Fml.tex_eq Specs.Fml.erase_toFO}

: Gap

  That the exported tree evaluates like the formula (`FO.eval (toFO φ) = some (Fml.eval φ)`, with
  {name}`Specs.FO.eval` and {name}`Specs.Fml.toFO`) is tested on the examples' formulas, not proved
  in general. A general proof relates a PHOAS term at two carriers and needs parametricity, which
  Lean cannot prove internally.
::::

::::card "Input oracles could not be queried" (n := "2") (status := "fixed")
: Decision

  A spec declares its input bundle `In`, and {name}`Specs.input` gives the description a named
  handle on an input oracle. The verifier routes input queries to the input part of
  {name}`Interaction.pathBundle` and message queries to the message part, as `pathLift` does. The
  honest prover answers input queries from the input data.

: Why

  `OracleVerifier.decide` already has query access to the inputs. Ignoring them forced FRI to
  resend $`f_0` and kept Spartan from reading its index oracles.

: Evidence

  Sum-check reads `p`, FRI reads $`f_0`, and Spartan reads $`\tilde A`, $`\tilde B`, $`\tilde C`
  as input oracles. {name}`Specs.Spec.decide_eq_verdict` covers the routing for every spec.
::::

::::card "Round shape had to be uniform, and the kit's round was one oracle plus one challenge" (n := "3") (status := "fixed")
: Decision

  {name}`Specs.rounds` takes a tree family, which lets round `i`'s tree depend on `i`. The kit's
  round is a block of messages followed by a challenge, with prefix and suffix blocks.

: Why

  Real protocols change message types per round. Every interactive proof that the kit targets
  alternates prover blocks and single challenges, and two consecutive challenges are one challenge
  of the product type. One challenge per round therefore costs no generality for round-by-round
  soundness.

: Evidence

  The FRI spec sends round `i`'s word on a domain of size $`2^{k-i}`. The kit's FRI commit phase
  (`Kit/Fri.lean`) has per-round message types and an empty block in round 0.
  `Kit/TwoMessage.lean` has two messages per round and a plain suffix message.
::::

::::card "Proof ergonomics" (n := "4") (status := "partial")
: Decision

  Because {name}`Specs.Spec` is a structure, `(branchingSpec R d D).Tr` works. The smart constructor
  {name}`Specs.Spec.mk` infers the tree and the skeleton. Accessors compute positions at
  elaboration time. A goal therefore never contains a stuck label comparison. Tree agreement uses
  the tree family of `rounds`, whose obligations hold by `rfl`. The final-state cast stays inside
  {name}`Specs.roundsGo`.

: Why

  Computing positions while elaborating removes the stuck `if "g" = "g"` terms. Passing the target
  tree family lines up the definitional unfolding with ArkLib's recursion. Neither
  `smartUnfolding false` nor a cast is then needed.

: Evidence

  No file sets `smartUnfolding`. {name}`Specs.sumcheck_tree`, {name}`Specs.Spartan.spartan_tree`,
  {name}`Specs.Fri.fri_tree` and {name}`Specs.branching_tree` hold by `rfl`.

: Gaps

  `simp` and `rw` do not see through the `Curry` encoding of formula arguments. Proofs about a
  formula's value therefore use small `rfl` lemmas at the exact hole list
  ({name}`Specs.eval_round_value`,
  {name}`Specs.eval_round_check`) or `change`. Proofs step through the interpreters with
  `erw [Desc.verdict.eq_N]`. Simp lemmas generated per constructor would fix both. This is stage 2
  work.
::::

::::card "Labels were global" (n := "5") (status := "fixed")
: Decision

  Labels are paths of stage names, block names, round numbers and the label. A branch component
  `m = v` enters case `v`. Inside a branch the accessor returns an `Option`, because the transcript
  type after the branch message depends on the message. When moves in one context share a base,
  the label adds the subscript: `tr⟦outer, v_B⟧`, `tr⟦"\\alpha_2"⟧`. With the base alone the
  accessor reads the first such move. A subscript is matched as the expanded figure prints it,
  with each enclosing round variable and each finished loop's count bound to its numeral: in FRI
  with `k = 2`, the final challenge $`\alpha_k` matches `"\\alpha_2"`.

: Why

  Spartan's row values $`v_A`, $`v_B`, $`v_C` and FRI's last folding challenge share a base with
  other moves in their context. A base alone therefore cannot reach all of them. Matching the
  subscript reuses the name that the figure prints instead of adding a second label to each move.

: Evidence

  In Spartan, `tr⟦outer, sumcheck, 0, g⟧` and `tr⟦inner, sumcheck, 0, g⟧` are different moves,
  and `tr⟦outer, v_B⟧` and `tr⟦inner, "\\rho_C"⟧` read the second and third moves of their kind,
  by `rfl`. In the branching example `tr⟦m = 2, sumcheck, 1, r⟧` is `some` on a transcript whose
  message is 2 and `none` on one whose message is 1, both by `rfl`.
::::

::::card "Figures could not show dependent shapes" (n := "6") (status := "fixed")
: Decision

  The skeleton is a tree with stage, loop and branch nodes. {name}`Specs.branch` records one
  sub-skeleton per case of a finite message type, and {name}`Specs.branchOpaque` marks a
  shape-selecting message of infinite type.

: Evidence

  In `Examples/Branching.lean` ({name}`Specs.branchingSpec`) the prover sends `m : Fin 4` and an
  `m`-variable sum-check follows. The JSON and the figures show the four cases. The
  {ref "branching"}[branching example] page draws them.
::::

::::card "Where the symbolic sum-check layer lives" (n := "7") (status := "partial")
: Decision

  In the spec layer. Claims are formulas with a denotation. Sum-check's stage claims are
  $`\sum_{x \in D^n} p(x) = c` and $`p(r) = c_n`, and the soundness and completeness statements
  are about the languages those formulas denote. Spartan's two stages share one named claim value.
  The outer stage's output claim and the inner stage's input claim are therefore one term.

: Why

  With string claims, the claim-flow figure had no meaning that Lean knew. With formula claims,
  the figure's edges and the security statements come from one object, which is what "claims as
  data" asks for.

: Evidence

  {theorems Specs.Claims.sumcheckSpec_claimSound Specs.Claims.sumcheckSpec_claimRBRSound Specs.Claims.sumcheckSpec_claimComplete Specs.Claims.sumcheckSpec_contract}

: Gap

  Stage contracts read the first stage's input claim and the last stage's output claim. Contracts
  for the inner stages of a multi-stage spec, and their composition along a
  {name}`Interaction.StageChain`, are stage 3 work.
::::

::::card "Elaboration cost was unmeasured" (n := "8") (status := "fixed")
: Decision

  `bench.sh` measures it and writes `out/bench.md`. D10 records these single runs on an Apple M4
  with 24 GB and Lean 4.36.0:

  :::table +header
  * * Case
    * Size
    * Wall time
  * * sum-check: tree by `rfl`, accessors
    * n = 8 / 32 / 128
    * 2.24 s / 2.26 s / 2.34 s
  * * sum-check: skeleton export
    * n = 8 / 128
    * 2.26 s / 2.26 s
  * * Spartan: tree, accessors, export
    * m = n = 4 / 8
    * 2.36 s / 2.33 s
  * * FRI: tree, accessors, export
    * k = 4 / 32
    * 2.31 s / 2.41 s
  :::

  About 1 s of each row is importing the library. Cost does not grow with the protocol's size: the
  tree agreement is `rfl` for every size, the exported skeleton holds each loop once, and the
  skeleton is computed without enumerating any domain, because a domain stores its elements behind
  a function. One limit remains: the accessor at round 127 of a 128-round sum-check exceeds Lean's
  default `maxRecDepth` of 512, and the bench file (`Specs/Bench/Sumcheck128.lean`) raises the
  limit to 1024 for that definition. The {ref "cost"}[Size and speed] chapter shows the full table,
  which the site reads from `out/bench.md` when it builds.
::::

::::card "Loops were written out for one round count" (n := "9") (status := "partial")
: Decision

  A loop is one skeleton node, `Skel.loop l n body rest` ({name}`Specs.Skel.loop`), generic in its
  count `n`. `l : Loop` ({name}`Specs.Loop`) names the block, the round variable (`i`), the count
  symbol (`n`) and the error annotation, and `body` is one round's skeleton. Names inside a round
  carry symbolic indices (`iv "g"` is $`g_i`), and a name after the loop can use the count ($`c_n`).
  `rounds` requires that a round's skeleton not depend on the round number (`hG`, by `rfl` by
  default). {name}`Specs.Skel.erase` sets every count to 0. The JSON (schema `/2`) and the folded
  figure read the erased skeleton. The expanded figure unrolls each loop, binding the round variable
  to each round and the count after the loop. The description's skeleton index still unrolls the
  rounds ({name}`Specs.Skel.unroll`). Accessors and tree agreement at concrete sizes therefore work
  as before. Proofs state their round induction on {name}`Specs.roundsFrom`, the rest of a loop from
  round `j`.

: Why

  A paper draws one generic round with a variable index, and the reader instantiates it. With one
  skeleton per count, the JSON and the figure grew with `n`, and no single exported object
  described the protocol. Keeping the unrolled index in the description's type leaves accessors and
  the `rfl` tree agreements unchanged.

: Rejected

  * _An unrolled skeleton per count_ (the second prototype). Each exported file describes one
    instance, and a reader cannot tell which parts are generic.
  * _Names that carry only an offset from the innermost round._ They cannot name a value after the
    loop, such as $`c_n`, or the round variable of an outer loop, such as FRI's query index `j`
    inside the consistency loop over `i`.
  * _Dropping the unrolled index._ Accessors would then need symbolic rounds, which this version
    does not have (see the gaps).

: Evidence

  {name}`Specs.sumcheck_erase`, {name}`Specs.Spartan.spartan_erase` and {name}`Specs.Fri.fri_erase`
  prove by `rfl` that the erased skeleton is the same for all counts, and `Specs.Bench.Export128`
  checks that the sum-check JSON has the same size at 8 and 128 rounds. `#guard` tests fix the
  folded checks (`\sum_{a \in D} g_{i}(a) = c_{i}`), the expanded ones (`g_{1}` in round 1),
  Spartan's $`c_m` and $`c_n`, and the branching example's final check $`p(r) = c_{m}` in each
  case. The FRI spec has three loops, one nested: folding over `i < k`, queries over `j < l`, and a
  consistency loop over `i < k` inside each query. On the generated page, a port of the printer
  reproduces every TeX string that Lean exported (21 for sum-check, 160 for Spartan, 47 for FRI and
  101 for the branching example).

: Gaps

  * An accessor needs a numeral count and a numeral round. An accessor at a symbolic round
    (`tr⟦sumcheck, i, g⟧` for a variable `i`) needs the loop's tree as a function of the round and
    a transcript split at round `i`. `Transcript.split` and `Transcript.append` in
    `ArkLib/Interaction/Transcript.lean` could provide the split.
  * Accessors into a branch inside a loop body are not supported.
  * Parameters other than counts print their values: sum-check's degree `d` appears as its value in
    the error annotation (`2/|F|` in the example). The JSON therefore depends on `d`.
  * Printed types are annotation. A type that depends on a count or the round, such as the word
    type $`F^{2^{k-i}}` in FRI's folding loop, is written symbolically with `ty := …`, and the
    expanded figure prints it symbolically too.
  * When hole types depend on the round, as in FRI's consistency loop, the author passes the round
    skeleton explicitly (`G := checkSkel F ω k`, with {name}`Specs.Fri.checkSkel`), and Lean checks
    by evaluation that every round has it.
  * {name}`Specs.Skel.checks` lists a loop body's checks once.
  * The expanded figure binds a branch variable in each case. The term $`c_m` therefore prints as
    $`c_{2}` in the case `m = 2`. The folded figure keeps $`c_m`.
::::

# Further gaps found while fixing the limitations
%%%
tag := "design-gaps"
%%%

Fixing the limitations turned up two more gaps, and both are closed.

: The two prototypes were disconnected

  The bridge ({name}`Specs.Bridge.sound_of_kit`) and its sum-check instance
  ({name}`Specs.Bridge.sumcheckSpec_sound`) connect them.

: Each protocol needed its own induction for agreement

  {name}`Specs.Spec.decide_eq_verdict` and {name}`Specs.Spec.verdict_isSome` hold for every spec. A
  protocol still compares the pure verdict with a hand-written verifier when one exists, by a round
  induction ({name Specs.verdict_roundsGo}`verdict_roundsGo` for sum-check).

# What stays open
%%%
tag := "design-open"
%%%

Five pieces of work stay open.

* *Soundness of the Spartan and FRI specs.* The kit proves FRI's commit phase, but the FRI spec
  groups a round as challenge then word, while the kit groups it as words then challenge. A
  regrouping lemma relates them. Spartan needs per-stage contracts and their composition.
* *FRI's commit-phase output language.* It is "the input is close or some fold fails", the bad
  event that the query phase needs. Linking it to ArkLib's {name}`Fri.FoldTrace.Safe` and
  {name}`Fri.FoldTrace.query_soundness` needs cast lemmas between the two ways of indexing
  subdomains.
* *Probabilistic completeness.* Completeness is proved in its deterministic form, and ArkLib's
  `completeness` in the classical model is not instantiated.
* *The general evaluation theorem for exported syntax* ([item 1](#card-1)) and *simp support for
  formula arguments* ([item 4](#card-4)).
* *Accessors at a symbolic round*, accessors into a branch inside a loop, and the other gaps of
  [item 9](#card-9).

# Why
%%%
tag := "design-why"
%%%

A specification makes a protocol readable, and the proof kit makes its security proofs modular.
Both rest on the same round structure.

: Readability

  Today's sum-check spreads one round over 12 files and 2,351 lines under
  `ArkLib/ProofSystem/Sumcheck/`: the tree, the claim with a proof field, the honest message, the
  prover fold and the verifier fold. Proofs reach moves by position (`tr.2.1`). The spec's round is
  six lines in protocol order, and the whole specification with its claims is 12 more. Its figure,
  claim-flow graph and timeline are generated from those lines. The {ref "before-after"}[Before
  and after] chapter sets the two side by side.

: Modularity

  Protocol-specific mathematics is 8–45% of each security proof today. The rest is recursion over
  `Cursor.Spine` ({name}`Sumcheck.foldPrefix` and about eight companion lemmas in `Indexed.lean`).
  The kit does that recursion once, and sum-check's soundness through it is 118 lines instead of
  317. The sum-check round argument, proved four times today (`Indexed.lean:117`,
  `Spec/SingleRound.lean:560`, RingSwitching `RoundSecurity.lean:54`, Binius
  `Steps/Fold.lean:850-890`), becomes one lemma in `Kit/ClaimReduction.lean`
  ({name}`Specs.Kit.claimReduction_le`, with the form {name}`Specs.Kit.reduction_le` that
  {name}`Specs.Kit.RoundSound` uses). These sizes are D10's; the {ref "cost"}[Size and speed]
  chapter counts the lines when the site builds.

: The two belong together

  Rounds, stages, round-local checks and claims make a spec readable, and the generic theorems
  induct over the same structure. The bridge shows this: the spec's rounds are the kit's rounds,
  the round's check is the kit's step, and the stage claims are the soundness statement's
  languages.

# Alternatives considered
%%%
tag := "design-alternatives"
%%%

D10 rejects five alternatives.

: A deep embedding of whole protocols with a denotation

  It would put a denotation between every proof and the protocol, and proofs would stop working on
  the core objects. The formula language is deep only where display and evaluation must agree.

: Custom syntax first

  A `protocol … where` block, as in the old `Choreo.lean`, gives worse error messages and must be
  maintained against the core. Notation comes after the combinators stabilize and stays optional.

: Early rejection at a check

  It would change record D4. Placing a check next to its round is presentation, and the decision
  stays at the leaf.

: Labels only in the exported skeleton

  Accessors and figures could then disagree. Labels in the type index are one source.

: Constant-state `FreeM.replicate` (record D5's plan)

  Sum-check's state has a challenge vector whose length is the round index. The state type
  therefore depends on the round.

# Consequences
%%%
tag := "design-consequences"
%%%

* A ported protocol has a specification of a screen or two, and its figures, claim-flow graph and
  timeline are generated.
* A protocol whose rounds fit the kit's shape gets soundness on the claims its figure shows from a
  one-round obligation plus the round's algebra, through the bridge.
* Each hand-written form that a spec replaces needs one agreement proof until the hand-written form
  is deleted.
* Record D5's iteration section changes: `rounds` and the kit certificate own dependent round
  state.
* Authors write formula arguments with `⟪…⟫` and formulas with `='`, `∑∈` and `ask`. This is the
  cost of generated display text.

The {ref "adopting"}[Adopting the specifications] chapter describes what moving a protocol of
ArkLib onto specifications takes.

## Acceptance tests
%%%
tag := "design-acceptance"
%%%

Each stage that moves the prototype into `ArkLib/` must pass these tests:

* Tree agreement by `rfl` with every hand-written tree that a spec replaces.
* The erased skeleton does not depend on the round counts, by `rfl`.
* Honest-prover and verdict agreement for every size.
* Accessor tests by label path, including inside branches.
* No hand-written display text on checks, local values or claims; `#guard` tests on the printed
  text; the JSON parses and the TeX compiles with `cryptocode`.
* A soundness theorem through the kit whose statement equals the hand-written one (checked with
  `type_of%`), and a soundness theorem on the spec's own claims.
* No `cast`, `Fin.cast` or `Fin.vsum` in any spec, and no `smartUnfolding` option anywhere.
* The bench table at the protocol's realistic sizes.

# Order of work
%%%
tag := "design-plan"
%%%

The work proceeds in six stages: the kit first, then the spec layer for sum-check, then the
protocols.

:::table +header
* * Stage
  * Content
  * Exit
* * 0
  * This record and the prototype library
  * The maintainer approves this record
* * 1
  * The kit (blocks, iteration theorem, passive iteration verifier, claim reduction) in
    `ArkLib/Interaction/`; sum-check soundness re-proved through it
  * The new proof replaces the spine recursion in `Indexed.lean`, and the legacy-equivalence
    theorems still hold
* * 2
  * The formula language and the spec layer (descriptions, interpreters, generic lemmas,
    accessors, statement front end, exporter) for sum-check, with simp support for formula
    arguments
  * Sum-check's spec fits on one screen, its figure matches a paper figure line for line, and its
    soundness on its own claims goes through the bridge
* * 3
  * Stage contracts for inner stages and their composition along
    {name}`Interaction.StageChain`; oracle-verifier composition theorems; Spartan ported as a spec
    of stages
  * Spartan's total error comes from the chain theorem with no manual sum
* * 4
  * FRI (with the regrouping lemma and the link to {name}`Fri.FoldTrace.query_soundness`), then
    BinaryBasefold and RingSwitching, then WHIR
  * No `cast` or `Fin.vsum` in each spec, and each proof reuses the kit
* * 5
  * Batching with placement; the Binary Jolt Book's first slice rendered from the skeleton
  * `spartan.outer` renders from the exported skeleton
:::

Fiat–Shamir and BCS on the new layer run in parallel from stage 1. They need stage 3's composition
theorems only for the end-to-end statement.
