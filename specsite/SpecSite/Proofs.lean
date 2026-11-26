/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Meta.Blocks
import SpecSite.Tables
import Specs.Claims
import Specs.Kit.Fri
import Specs.Kit.TwoMessage

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "Proofs" =>
%%%
tag := "proofs"
%%%

A protocol written as a specification is proved secure with ArkLib's own security notions, applied
to the verifier and the honest prover that Lean derives from the specification. The proofs come in
four layers, and this chapter shows each with its Lean source:

: {ref "security"}[The security notions]

  Soundness, round-by-round soundness and completeness of a specification are ArkLib's notions for
  its derived verifier, each tied to ArkLib's definition by an `iff` lemma.

: {ref "kit"}[The proof kit]

  The kit proves round-by-round soundness once, for every protocol made of rounds. A protocol
  supplies one obligation about a single round.

: {ref "kit-instances"}[Three protocols through the kit]

  Sum-check, the FRI commit phase, and a sum-check whose rounds send two messages.

: {ref "bridge"}[The bridge]

  A specification whose `rounds` block has the kit's round shape gets its soundness from the kit,
  with no hand-written verifier.

: {ref "claims"}[Stage claims]

  The claims that a stage states as formulas are the languages of the soundness statement.

The chapter ends with {ref "proofs-open"}[what is not yet proved]. Every theorem table below is
checked when the site builds: each theorem must exist and depend only on `propext`,
`Classical.choice` and `Quot.sound`. The constructs that the specifications use are described in
{ref "language"}[the specification language], and the protocols themselves in
{ref "sumcheck"}[Sum-check] and {ref "fri"}[FRI].

# The security notions
%%%
tag := "security"
%%%

`Specs/Security.lean` adds no trusted definition. Each security notion of a specification is
ArkLib's notion applied to the specification's derived verifier, and each comes with an `iff` lemma
to ArkLib's statement, proved by `Iff.rfl`:

{decl Specs.Spec.Sound Specs.Spec.sound_iff}

:::table +header
* * Specification
  * ArkLib
  * Lemma
* * {name}`Specs.Spec.Sound`
  * {name}`Interaction.OracleVerifier.soundness`
  * {name}`Specs.Spec.sound_iff`
* * {name}`Specs.Spec.RBRSound`
  * {name}`Interaction.OracleVerifier.rbrSoundness`, with an error at each challenge node
  * {name}`Specs.Spec.rbrSound_iff`
* * {name}`Specs.Spec.RBRKnowledgeSound`
  * {name}`Interaction.OracleVerifier.rbrKnowledgeSoundnessOfNodes`, with node-indexed draws and
    errors
  * {name}`Specs.Spec.rbrKnowledgeSound_iff`
* * {name}`Specs.Spec.Complete`
  * {name}`Interaction.completeness` in the classical model
  * {name}`Specs.Spec.complete_iff`
:::

The statements take the challenge draw, the ambient oracles and the input and output problems as
arguments, exactly as ArkLib's do. The front end therefore adds nothing to the meaning of ArkLib's
notions, and a theorem about a specification is literally a theorem about its derived verifier.
{name}`Specs.Spec.Complete` runs the honest prover {name}`Specs.Spec.honestProver`, which pairs the
prover's output with the input oracle data. ArkLib's completeness compares the prover's claimed
output with the verifier's output, and the verifier of a specification outputs its statement
together with the input oracles it keeps.

## Claims as languages

A stage declares its input claim and its output claim as Boolean formulas. Two functions evaluate
them: {name}`Specs.Desc.inClaim` reads the input claim of the first stage before any move, and
{name}`Specs.Desc.outClaim` reads the output claim of the last stage along a full transcript. A
specification without a stage claim has the claim `true`. The two problems below are the ArkLib
problems whose languages these claims denote:

{decl Specs.Spec.InClaim Specs.Spec.inputProblem Specs.Spec.outputProblem}

A soundness statement with these problems reads: if the input claim is false, the verifier accepts
an output whose claim is true with probability at most `ε`.

The output problem judges an output `(o, d)` at a path `p`. Its language holds when some run of the
specification with input data `d` and a transcript on `p` returns `o` and makes the output claim
true. The indirection is needed because ArkLib's output language reads only the output and the
path, while a stage's output claim reads values of the transcript. When the claim reads only values
that the output determines, as sum-check's `p(r) = c_n` does, the language is the claim on the
output. {ref "claims"}[Stage claims] proves the inclusion in ArkLib's output language for
sum-check.

## Generic lemmas

Two lemmas about these statements serve every protocol. Soundness is monotone in the input and
output languages:

{decl Specs.Spec.Sound.mono}

An accepting decision of the derived verifier is an accepting pure verdict. Soundness proofs
through the kit use this for their leaf obligation:

{decl +statement Specs.Spec.verdict_of_validAcceptance}

Its proof rewrites with {name}`Specs.Spec.decide_eq_verdict`, one of the generic theorems of
`Specs/Run.lean` that hold for every specification:

: Decision as evaluation

  {name}`Specs.Desc.run_hom`: a monad morphism that answers the input queries and the message
  queries from the transcript sends the verifier's decision to `pure` of the verdict.
  {name}`Specs.Spec.decide_eq_verdict` is its instance for ArkLib's `decide`.

: Honest acceptance

  {name}`Specs.Spec.verdict_isSome`: on an honest transcript the verdict accepts when every check
  holds on the honest values for every choice of challenges.

: Completeness of a `rounds` block

  {name}`Specs.rounds_complete`: if every round is complete whenever its continuation is complete,
  the block is complete, from any handler table that satisfies the round invariant before round
  `0`.

{decl +statement Specs.Spec.decide_eq_verdict}

{theorems Specs.Spec.sound_iff Specs.Spec.rbrSound_iff Specs.Spec.rbrKnowledgeSound_iff Specs.Spec.complete_iff Specs.Spec.inputProblem_language Specs.Spec.outputProblem_language Specs.Spec.Sound.mono Specs.Spec.verdict_of_validAcceptance Specs.Desc.run_hom Specs.Spec.decide_eq_verdict Specs.Spec.verdict_isSome Specs.rounds_complete}

# The proof kit
%%%
tag := "kit"
%%%

The kit proves round-by-round soundness once, for every protocol made of rounds. A protocol
supplies one obligation about a single round, {name}`Specs.Kit.RoundSound`, and three local laws.
None of these mentions a cursor, a spine or a partial transcript.

Today each security proof in ArkLib walks the partial transcripts of its protocol by hand. For
sum-check, the walk is {name}`Sumcheck.foldPrefix`, a recursion over `Cursor.Spine`:

{decl Sumcheck.foldPrefix}

Per D10, protocol-specific mathematics is 8–45% of each security proof today. The rest is recursion
over `Cursor.Spine`: `foldPrefix` and about eight companion lemmas in `Indexed.lean`. The kit does
that recursion once.

## A protocol made of rounds

A message is plain, which the verifier reads in full, or an oracle message with its query
interface, which the verifier reads only through queries ({name}`Specs.Kit.Msg`). A block is a list
of messages, and a round is a block followed by one verifier challenge:

{decl Specs.Kit.Round Specs.Kit.Round.then}

An iteration of `n` rounds has a prefix block before round `0` and a suffix block after the last
challenge. The kit's own tree of an iteration is {name}`Specs.Kit.iterate`. A protocol that ArkLib
defines by its own recursion is an instance when a certificate says that its tree has this shape:

{decl Specs.Kit.Rounds}

Each constructor fixes the tree up to definitional unfolding. A protocol defined by a recursion in
exactly this shape, such as sum-check's `Sumcheck.protocol R deg n`, is certified by the same
recursion, and every constructor's index agrees with the protocol by definition. Statements
therefore keep the protocol's own name and need no casts. {name}`Specs.Kit.Rounds.ofIter` certifies
the kit's own tree.

The round has exactly one challenge. Every interactive proof in ArkLib that the kit targets
alternates prover blocks and single challenges, and two consecutive challenges are one challenge of
the product type. One challenge per round therefore costs no generality for round-by-round
soundness.

## The obligation a protocol supplies

The protocol describes its analysis by a state type `S i` before round `i`, a pure update for each
round, and a claim `good i` on each state. The update returns `none` when the round's check rejects.
Thus a rejected state never satisfies its claim:

{decl Specs.Kit.Step Specs.Kit.RoundSound}

{name}`Specs.Kit.RoundSound` is the one probabilistic statement a protocol proves: from a state
whose claim is false, every value of round `i`'s block passes round `i` into a state whose claim
is true with probability at most `ε i` over the round's challenge. The update, the claim and the
initial state may all take the input statement, because a claim usually mentions the input, such
as sum-check's polynomial or FRI's input word.

## The iteration theorem

{decl +statement Specs.Kit.Rounds.rbrSoundness}

Besides the obligation `hround`, the theorem has three local hypotheses:

* `hdraw`: the challenge of round `i` is drawn by `chal i`. For the kit's own draw,
  {name}`Specs.Kit.Rounds.drawIs_challengeDraw` discharges it.
* `hroot`: an admissible statement whose initial state holds is in the language.
* `hleaf`: an accepted transcript has an unrejected final state whose claim holds.

The conclusion is ArkLib's {name}`Interaction.rbrSoundness` with error `ε i` at the challenge of
round `i`. Inside the proof, the kit builds the state function by walking each block: the state
stays fixed while a block is incomplete, and the challenge applies the round update.
{name}`Specs.Kit.Rounds.flips` proves the probability bound at every challenge, and
{name}`Specs.Kit.Rounds.leaf` proves the leaf law. Both are short inductions on the certificate,
because the block lemmas compose block by block.

Soundness with error $`\sum_i \varepsilon_i` follows through ArkLib's existing implication
{name}`Interaction.OracleVerifier.soundness_of_rbrSoundness`. Along every path, the errors of the
challenges sum to the sum of the round errors:

{decl Specs.Kit.Rounds.soundness_of_rbrSoundness}

## The kit's verifier

For a protocol without a hand-written verifier, the kit builds one.
{name}`Specs.Kit.Rounds.verifier` runs three query programs: `start` gives the initial state from
the prefix, `check i` gives the state after round `i`, and `finish` gives the output from the final
state and the suffix. Each program may reject, and each sees only the input oracles and the oracle
messages of its own block. As a result, the author of a check never sees a path or a cast.
{name}`Specs.Kit.Rounds.simulate_verifier` proves that, answered from a transcript, the verifier's
decision is the kit's verdict of the programs' pure semantics.

The iteration theorem for this verifier needs the obligation for the checks' pure updates, the root
law for `start`, and that an accepted output of `finish` makes the final claim true. Its proof
applies the iteration theorem and discharges the leaf law with the verifier's acceptance; hover
over a tactic to see the proof state:

{decl Specs.Kit.Rounds.verifier_rbrSoundness}

{name}`Specs.Kit.Rounds.verifier_soundness` is the soundness form, with error
$`\sum_i \varepsilon_i`.

## The claim-reduction step

Many rounds reduce a claim about a polynomial to a claim about its value at a random point. If the
input claim is false, the honest polynomial `h` that a true claim would require differs from the
message `g`, and the output claim can be true only if `g` and `h` agree at the challenge
`r`. {name}`Specs.Kit.claimReduction_le` bounds that event once:

{decl Specs.Kit.claimReduction_le}

Because the lemma mentions only the claims, the check and the two polynomials, a round of any
protocol can use it. Over a finite semiring two distinct polynomials of degree at most `d` can agree
at every point. The lemma therefore takes a point of difference;
{name}`Specs.Kit.agreement_le_field` states the agreement bound over a field for distinct
polynomials.

Per D10, this round argument is proved four times in ArkLib today: `Indexed.lean:117`,
`Spec/SingleRound.lean:560`, RingSwitching's `RoundSecurity.lean:54`, and Binius's
`Steps/Fold.lean:850-890`. The first of these is sum-check's own:

{decl +statement Sumcheck.indexed_round_soundness}

{theorems Specs.Kit.Rounds.drawIs_challengeDraw Specs.Kit.Rounds.flips Specs.Kit.Rounds.leaf Specs.Kit.Rounds.rbrSoundness Specs.Kit.Rounds.soundness_of_rbrSoundness Specs.Kit.Rounds.simulate_verifier Specs.Kit.Rounds.verifier_validAcceptance Specs.Kit.Rounds.verifier_rbrSoundness Specs.Kit.Rounds.verifier_soundness Specs.Kit.agreement_le Specs.Kit.agreement_le_field Specs.Kit.claimReduction_le Specs.Kit.reduction_le}

# Three protocols through the kit
%%%
tag := "kit-instances"
%%%

Three protocols are proved through the kit. Each exercises a different part of it: sum-check the
simplest round, FRI's commit phase message types that change every round, and a two-message
sum-check the blocks of several messages and the kit's verifier.

## Sum-check

Sum-check is the kit's simplest instance: no prefix, no suffix, and each round is one round
polynomial, sent as an oracle, followed by a ring challenge. The certificate says that ArkLib's own
tree `Sumcheck.protocol R deg k` is `k` such rounds, and each case holds by definition:

{decl Specs.Kit.scRound Specs.Kit.scRounds}

The round update checks the indexed sum of the round polynomial and moves the claim to its value
at the challenge. The per-round obligation follows from the claim-reduction step. This is the
whole protocol-specific probability argument:

{decl Specs.Kit.scStep Specs.Kit.sumcheck_roundSound}

Because the main theorem is about ArkLib's own verifier `Sumcheck.indexedVerifier`, not a kit-built
one, it replaces ArkLib's proof without changing the verifier. Its statement is exactly that of
{name}`Sumcheck.indexedVerifier_soundness`, and an `example` in the module checks this with
`type_of% @Sumcheck.indexedVerifier_soundness`:

{decl +statement Specs.Kit.indexedVerifier_soundness_viaKit}

The only fact the kit needs about ArkLib's verifier is ArkLib's `indexed_validAcceptance`, together
with {name}`Specs.Kit.scVerdict_eq`, which proves that the kit's verdict is
`Sumcheck.indexedVerdict`.

Per D10, sum-check's soundness proof through the kit is 118 lines, against 317 lines today, for the
identical statement. The table below counts, when the site builds, the files that sum-check needs
on top of the shared layers:

{sizes SpecSite.sumcheckSpecSizes}

## The FRI commit phase

FRI is the kit's first instance whose message types change every round. Round `i` sends the word
`fᵢ` on the domain `dom ω i`, the evaluation domain halved `i` times, as an oracle, and then the
verifier sends a folding challenge `αᵢ`. Round `0` sends nothing, because the input word `f₀`
plays the role of its message. After the last round the prover sends the final polynomial as a
plain message.

The analysis state is a flag, "no fold so far has failed", and its claim is "if no fold has failed,
the input is close". From a false claim, the next claim is true exactly when the fold fails, and
ArkLib's {name}`Fri.foldingAgreementFailure_prob_le` bounds that probability. The per-round
obligation therefore needs no hypothesis:

{decl Specs.Kit.Fri.fri_roundSound}

{decl +statement Specs.Kit.Fri.commitPhase_rbrSoundness}

From an input that is `δ`-far from the code, the commit phase reaches a transcript on which some
fold fails with round-by-round error `foldError ω d r θ i` at round `i`'s folding challenge, and
{name}`Specs.Kit.Fri.commitPhase_sum_errors` sums the errors along every path. Two variants change
the error:

* {name}`Specs.Kit.Fri.commitPhase_rbrSoundness_of_isMCAGenerator` takes the error of any MCA
  certificate `IsMCAGenerator` for each round's code as the hypothesis `hMCA`.
* {name}`Specs.Kit.Fri.commitPhase_rbrSoundness_johnson` has explicit Johnson-regime errors, for a
  positive final degree bound `d` and a sharpness parameter `m ≥ 3`. Because ArkLib's
  `RSCode.isMCAGenerator_univariatePowersGenerator` discharges `hMCA`, this theorem has no
  hypothesis beyond its parameters.

This is the commit-phase half of FRI's soundness. Its output language is "the input is close or
some fold fails". The query-phase bound {name}`Fri.FoldTrace.query_soundness` assumes the
per-fold condition of ArkLib's {name}`Fri.FoldTrace.Safe`, and the module does not formalize the
link between the two: `FoldTrace` indexes its domains by `subdomain` chains, and relating them to
`dom ω i` needs cast lemmas.

## A round with two messages

`Kit/TwoMessage.lean` is a sum-check in which round `i` sends two messages: the round polynomial
`gᵢ` as an oracle and its claimed sum `σᵢ` as a plain message. After the last round, the prover
sends the claimed final value as a plain message, the suffix:

{decl Specs.Kit.twoRound}

The verifier is built by the kit, {name}`Specs.Kit.twoVerifier`, from three query programs. Its
check compares `σᵢ` with the current target directly from its view, with no query, which a block
of only oracle messages cannot express. The per-round obligation {name}`Specs.Kit.two_roundSound`
reuses the claim-reduction step, and soundness with error `n · deg / |R|` follows from
{name}`Specs.Kit.Rounds.verifier_soundness`:

{decl +statement Specs.Kit.twoVerifier_soundness}

{theorems Specs.Kit.sumcheck_roundSound Specs.Kit.scDrawIs Specs.Kit.scVerdict_eq Specs.Kit.indexedVerifier_rbrSoundness_viaKit Specs.Kit.indexedVerifier_soundness_viaKit Specs.Kit.Fri.fri_roundSound Specs.Kit.Fri.friVerdict Specs.Kit.Fri.commitPhase_rbrSoundness Specs.Kit.Fri.commitPhase_sum_errors Specs.Kit.Fri.commitPhase_rbrSoundness_of_isMCAGenerator Specs.Kit.Fri.commitPhase_rbrSoundness_johnson Specs.Kit.twoCheck_step Specs.Kit.two_roundSound Specs.Kit.twoVerifier_soundness}

# The bridge
%%%
tag := "bridge"
%%%

The bridge proves that a specification whose `rounds` block has the kit's round shape is sound,
from the kit's per-round obligation. The conclusion is {name}`Specs.Spec.Sound` of the specification
itself. Hence a protocol written as a specification needs no hand-written verifier. The bridge has
three steps.

First, {name}`Specs.Bridge.cert` certifies the tree family of a `rounds` block as the kit's rounds.
Each case is a cast along the tree equation. With the `rfl` equations that `rounds` uses by default,
the certificate therefore computes:

{decl Specs.Bridge.cert}

Second, the bridge theorem {name}`Specs.Bridge.verdict_roundsGo` proves that the verdict of the
rounds is the kit's verdict on the certificate, followed by the verdict of what comes after the
rounds. It takes two hypotheses, each for an arbitrary transcript: `hbody` says that one round's
verdict is the kit step, then the continuation; `hnext` says that the continuation's verdict reads
only the final state and the suffix values. Since the kit's state at round `i` is the `rounds`
block's own `State i`, the kit's step is the body's pure meaning and needs no translation.

Third, {name}`Specs.Bridge.rbrSound_of_kit` applies the iteration theorem to the specification's own
verifier. Its hypotheses are those of the iteration theorem plus `hverdict`, the factorisation of
the verdict through the kit. The steps before a `rounds` block, such as input reads and stage
markers, differ between specifications. For that reason each instance proves `hverdict` from
{name}`Specs.Bridge.verdict_roundsGo`. The proof is five tactic lines:

{decl Specs.Bridge.rbrSound_of_kit}

{decl Specs.Bridge.sound_of_kit}

When the verdict factors through the kit with the pure semantics of the kit's programs,
{name}`Specs.Bridge.agrees_of_kit` proves that the specification's verifier and the kit's
{name}`Specs.Kit.Rounds.verifier` agree in ArkLib's sense
({name}`Interaction.OracleVerifier.Agrees`). By
{name}`Interaction.OracleVerifier.Agrees.soundness_iff` and its siblings, every security notion then
transfers between the two verifiers.

## Sum-check through the bridge

`Bridge/Sumcheck.lean` proves soundness of the verifier that `sumcheckSpec` derives, with ArkLib's
error `n · (d / |R|)`. It does not use `Sumcheck.indexedVerifier`, `Sumcheck.indexedVerdict` or the
example's agreement theorems. {name}`Specs.Bridge.sumcheckRound_verdict` gives the bridge's `hbody`:
one round's verdict is {name}`Specs.Bridge.scSpecStep`, then the continuation. The factorisation is
then one application of the bridge theorem:

{decl Specs.Bridge.sumcheckSpec_verdict_eq}

{name}`Specs.Bridge.scSpec_roundSound` moves the per-round obligation from
{name}`Specs.Kit.sumcheck_roundSound`, since the description's state `Claim R i` and ArkLib's
`RoundStatement R n i` hold the same target and challenges. The main theorem has the statement of
`Sumcheck.indexedVerifier_soundness` with `Spec.verifier (sumcheckSpec R d n D)` in place of
`indexedVerifier`:

{decl +statement Specs.Bridge.sumcheckSpec_sound}

The input and output problems here are ArkLib's `indexedInputProblem` and `indexedOutputProblem`,
so that the two theorems can be compared directly. {ref "claims"}[Stage claims] restates the
theorem with the problems that the stage's own claim formulas denote.
{name}`Specs.Bridge.sumcheckSpec_agrees` proves that the specification's verifier agrees with the
kit's verifier for the check program `scCheck`, by the generic {name}`Specs.Bridge.agrees_of_kit`.

{theorems Specs.Bridge.verdict_roundsGo Specs.Bridge.decide_eq_iterVerdict Specs.Bridge.agrees_of_kit Specs.Bridge.rbrSound_of_kit Specs.Bridge.sound_of_kit Specs.Bridge.sumcheckRound_verdict Specs.Bridge.sumcheckSpec_verdict_eq Specs.Bridge.scCert_drawIs Specs.Bridge.scSpec_roundSound Specs.Bridge.sumcheckSpec_rbrSound Specs.Bridge.sumcheckSpec_sound Specs.Bridge.scCheck_step Specs.Bridge.sumcheckSpec_agrees}

# Stage claims
%%%
tag := "claims"
%%%

The stage claims that a figure shows are the languages of the soundness statement. For sum-check,
the input claim `Σ_{x ∈ D^n} p(x) = c_0` and the output claim `p(r) = c_n` are formulas, and
Lean proves soundness and completeness on exactly these formulas.

A stage contract states what the claims mean for the verifier and for the honest prover. Each part
is a thin definition over the statements of {ref "security"}[the security notions]:

{decl Specs.Spec.ClaimSound Specs.Spec.ClaimRBRSound Specs.Spec.ClaimComplete Specs.Spec.StageContract}

The completeness contract is deterministic and takes a witness relation `wit`. Since the stage
claims read the statement and the input oracles, not the witness, the contract must say which
witness the honest prover uses. A description's checks hold or fail for each choice of challenges,
with no probability involved. {name}`Specs.Spec.ClaimComplete.accepts` turns the contract into
acceptance with a true output claim.

A soundness contract follows from soundness on other problems by comparing languages. The input
claim's language must contain the other input language on admissible inputs, and the other output
language must contain the output claim's language:

{decl Specs.Spec.ClaimSound.of_sound}

## Sum-check's contract

The input claim, evaluated, is ArkLib's input relation:

{decl Specs.Claims.sumcheckSpec_InClaim_iff}

On the output side, {name}`Specs.Claims.sumcheckSpec_outputProblem_le` proves an inclusion, not an
equality: the output problem of a specification holds when some accepted transcript returns the
output with a true output claim, while ArkLib's output language holds for every output with
`p(r) = c_n`, including outputs that no accepted transcript returns. Soundness needs only the
inclusion. With both sides, soundness on the stage claims follows from
{name}`Specs.Bridge.sumcheckSpec_sound`:

{decl Specs.Claims.sumcheckSpec_claimSound}

{name}`Specs.Claims.sumcheckSpec_claimRBRSound` is the round-by-round version, with error
`d / |R|` at every challenge, through the bridge. {name}`Specs.Claims.sumcheckSpec_claimComplete`
proves the completeness contract with the input polynomial as the witness: if the input claim
holds, every check holds on the honest values and the output claim holds on every honest
transcript. The stage contract packs both directions:

{decl Specs.Claims.sumcheckSpec_contract}

A contract is about the input claim of the first stage and the output claim of the last stage,
the claims that {name}`Specs.Spec.inClaim` and {name}`Specs.Spec.outClaim` read. The contract of a
single-stage specification is therefore the contract of its stage. A contract for each stage of a
multi-stage specification needs the state between stages and is not stated.

{theorems Specs.Spec.outputProblem_language_of_verdict Specs.Spec.ClaimComplete.accepts Specs.Spec.ClaimSound.of_sound Specs.Claims.sumcheckSpec_inClaim Specs.Claims.sumcheckSpec_InClaim_iff Specs.Claims.sumcheckSpec_inputProblem_iff Specs.Claims.sumcheckSpec_outClaim_of_verdict Specs.Claims.sumcheckSpec_outputProblem_le Specs.Claims.sumcheckSpec_complete Specs.Claims.sumcheckSpec_outClaim_of_honest Specs.Claims.sumcheckSpec_claimSound Specs.Claims.sumcheckSpec_claimRBRSound Specs.Claims.sumcheckSpec_claimComplete Specs.Claims.sumcheckSpec_contract}

# What is not yet proved
%%%
tag := "proofs-open"
%%%

Sum-check is the only specification whose soundness and completeness are proved on its own claims.
The items below are open, as {ref "design"}[the design record] lists them under "What stays open"
and in its {ref "limitations"}[limitations]:

: Soundness of the Spartan and FRI specifications

  The kit proves FRI's commit phase, but the FRI specification groups a round as challenge then
  word, while the kit groups it as words then challenge. Relating them is a regrouping lemma.
  Spartan needs per-stage contracts and their composition.

: FRI's commit-phase output language

  It is "the input is close or some fold fails", the bad event the query phase needs. Linking it
  to ArkLib's {name}`Fri.FoldTrace.Safe` and {name}`Fri.FoldTrace.query_soundness` needs cast
  lemmas between the two ways of indexing subdomains.

: Contracts for inner stages

  Stage contracts read the first stage's input claim and the last stage's output claim. Contracts
  for the inner stages of a multi-stage specification, and their composition along a `StageChain`,
  are stage 3 of the order of work.

: Probabilistic completeness

  Completeness is proved in its deterministic form. ArkLib's `completeness` in the classical model,
  which {name}`Specs.Spec.Complete` states, is not instantiated for any protocol.

: Agreement with hand-written verifiers

  {name}`Specs.Spec.decide_eq_verdict` and {name}`Specs.Spec.verdict_isSome` hold for every
  specification. A protocol that also has a hand-written verifier still compares the pure verdict
  with it by a round induction ({name}`Specs.Bridge.verdict_roundsGo`), and each hand-written form
  that a specification replaces needs one agreement proof until it is deleted.

: Proof support for formulas

  Because `simp` and `rw` do not see through the `Curry` encoding of formula arguments, proofs about
  a formula's value use small `rfl` lemmas at the exact hole list or `change`, and proofs step
  through the interpreters with `erw [Desc.verdict.eq_N]`. Simp lemmas generated per constructor
  would fix both; this is stage 2 work.

: The evaluation theorem for exported syntax

  That the exported syntax tree evaluates like the formula is tested on the examples' formulas,
  not proved in general. A general proof relates a PHOAS term at two carriers and needs
  parametricity, which Lean cannot prove internally.

The first stage of the order of work moves the kit into `ArkLib/Interaction/` and re-proves
sum-check soundness through it. Its exit condition is that the new proof replaces the spine
recursion in `Indexed.lean` and the legacy-equivalence theorems still hold.
