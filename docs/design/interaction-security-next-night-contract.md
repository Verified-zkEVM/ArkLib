# Proposed second eight-hour interaction-security contract

Status: authorized by the user on October 3, 2026. Run started at 17:34:15 UTC
(13:34:15 America/New_York), deadline October 4 at 01:34:15 UTC
(October 3 at 21:34:15 America/New_York). Six-hour checkpoint: 23:34:15 UTC.

The [run record](interaction-security-second-night-results.md) tracks validation and progress.

## Purpose and baseline

Develop general reusable security theory and one executable oracle-elimination bridge.
The first run proved local-to-global native soundness, dependent knowledge-certificate
composition, and fixed-round state-restoration knowledge soundness with uniform and
nonuniform errors. See [the first run results](interaction-security-night-results.md).
Those results are not an end-to-end compiler or an efficient knowledge extractor.

Planning baseline: ArkLib integration branch `integration/interaction-night-20261003`,
head `b2ec8214150121c00f2d4ec468f72f1be34d8f22`. Its VCVio pin is the compatible
weighted-query revision `91386ad88ed72292d0f4e3153a444336920fc565`.
VCVio PR 823 merged as d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0 at 17:31:21 UTC.
The execution baseline is VCVio main bc3433e3, including query-count normalization PR 820.
ArkLib main remains ace55c3e2; its first-night integration is retained above it.
Root owns the downstream pin migration and its validation.
A merged upstream theorem is not available downstream until its pin is updated and checked.
Do not merge PRs as part of this contract.

## MUST 1: expected distinct-query security in the actual cached experiment

### Definitions and hypotheses

Let D be an arbitrary decidable key type, R(t) a finite nonempty response type, and H
an independent uniform random function, implemented by the existing lazy cache.
Let A be a finite oracle computation. Its next query, stopping decision, and output
may depend on all earlier responses. Repeated and out-of-order queries are allowed.
Let epsilon : D -> ENNReal be fixed before the run; zero and infinite charges are allowed.

Define an instrumented actual run returning its output together with the finite set
Fresh(A) of keys first queried during that run. Prove that forgetting this instrumentation
recovers the existing stateful cached execution: require joint equality of returned
outcome, final RO cache, and query log/fresh-key set before projection. Preserve this
state on returned failure too, so continuation uses the same cache. Charge a repeated
query zero.
The empty-cache assumption is explicit; no arbitrary correlated initial-cache claim.

For each key t, let Bad(t,h) be a predicate on a complete answer assignment h. Require:

    for every t and every background h,
      Pr[r uniform in R(t); Bad(t, update h t r)] <= epsilon(t).

Bad may inspect other cells, including unqueried cells. For the target output event E,
require the pointwise implication for every answer assignment:

    E(A^h) -> exists t actually queried by A^h, Bad(t,h).

Neither the resampling bound nor this implication may be replaced by an assumption
conditional on no earlier bad event.

### Main statement

Prove in the actual cached experiment:

    Pr[E(A^H)] <= E[sum t in Fresh(A^H), epsilon(t)].

Required supporting theorem: whether A ever queries t is unchanged when only h(t)
is changed. The returned output and later query sequence need not be unchanged.
Combine that causality fact with own-cell resampling and finite union/expectation bounds.
For infinite D, prove a finite-support reduction for the program; do not assume a uniform
distribution over all functions on an infinite domain.

### Interleaved private randomness

Extend the actual interpreter and theorem to adversaries with independent private sampling
interleaved with cached oracle calls. Repeated private sampling operations draw fresh coins;
they must not accidentally become cached RO queries. Use existing OracleComp/ProbComp syntax
and simulation APIs. For each fixed private random tape, require the same pointwise trace
implication and uniform resampling bound (or its explicitly tape-indexed version).

For this run, prefer Bad independent of private coins; any tape-indexed extension needs
a genuinely RO-independent seed, not conditioning on adaptively realized coin outcomes.

Optional failure is a returned unsuccessful outcome. Instrumentation must retain queries
made before failure. E is false on failure, and expectations are unconditional, not
conditioned on successful runs. No arbitrary divergence or unrestricted measure-valued
randomness is promised by this finite-program theorem.

If proof uses a pre-sampled tape representation, prove joint distribution equality of
returned outcome, final cache, and query log/fresh-key set with the interleaved
interpreter; cost equality follows by projection. A theorem only averaging an
assumed family of deterministic adversaries does not meet this obligation. This is a
semantic theorem; an exponentially expanded tape construction is not a PPT realization.

Reject the existing uncached expected-cost quantity as a substitute for this expectation.
Derive the previous all-path weighted bound as a corollary where appropriate, preserving
its public API. No narrowing to a finite global key domain or nonadaptive adversary.

## MUST 2: randomized state-restoration knowledge security with actual expected cost

Use the existing native fixed-round restoration presentation, endpoint laws, named backward
extractor, same-run closed oracle output, and round error vector epsilon_i. Retain all
previous restrictions explicitly: fixed finite message/challenge alphabets, finite nonempty
uniform challenges, and challenge keys containing input, depth, messages and salts but
not earlier challenges. This milestone does not remove those presentation restrictions.

Define the restoration adversary with interleaved private randomness, adaptive input and
output selection, and optional failure. Prove stateful interpreter correspondence at
the adversary-to-completion handoff, preserving that phase's cache and ordered log;
terminal marginals alone are insufficient. Complete its selected transcript against the same
cache and use the existing native terminal execution and output-closing handler.
No independently reconstructed output behavior may replace the actual closed output.

Let J be this joint adversary-plus-completion game. Let BadExtract mean: a selected input
is in the theorem's domain, the actual closed output claim has the supplied valid witness,
and the named extracted input witness is invalid. Prove:

    Pr[BadExtract(J)]
      <= E[sum t in Fresh(J), epsilon_(round t)]
      <= epsilon_max * E[number of fresh adversary queries] + sum_i epsilon_i.

The fresh adversary count includes work on failed branches; completion runs only when an
output is selected. The second inequality follows from a pointwise charge bound on the
joint game, not a separate probability argument after adaptive output selection.
Recover Q * epsilon_max + sum_i epsilon_i from an almost-sure bound of Q on the actual
fresh adversary count. Keep ENNReal zero/infinity conventions explicit.

Cover both scalar and closed-oracle-output games through shared owner lemmas rather than
duplicating the probability proof. Match the existing extractor semantically; do not
introduce a new extractor whose correctness is assumed.

## Principal SHOULD: an executable terminal-batch Merkle verification bridge

This is the ambitious parallel target. Its native execution bridge makes completion within
eight hours less certain than the MUSTs; incomplete work must remain explicitly incomplete.
It is a restricted first LowerAccesses security theorem, not a general native compiler.
The supported fragment is promise-free raw-digest vectors, a finite configuration family,
adaptive sequential commitments, and one terminal batch of openings. It does not assert
encoded payload extraction, codeword membership, bounded degree, or proximity.

Define an explicit finite query plan identifying commitment slots and leaf positions,
and an arbitrary pure decision function on the ordered answer vector. Define RealVerify:
run the malicious commitment/opening strategy in one cached random oracle, enforce exact
matching of the prescribed public commitment occurrences and positions (including length
and order) in the final acceptance predicate. Run verification on every returned opening
unconditionally, as in the owning VCVio game, then combine its acceptance bits with plan
validity and the decision. Malformed, missing, or misdirected openings reject. Do not
short-circuit before opening verification unless a separate cache/log coupling is proved. The verifier selects roots from its
recorded public commitment sequence.
It never accepts an adversary-supplied private Checkpoint or inspects the extractor log.
The proof attaches the corresponding actual recorded checkpoint and proves that erasing
this private bookkeeping recovers the executable native verifier distribution. This exact
checkpoint provenance is required by the owning disagreement theorem.

Define a named extractA using commitment-time checkpoint extraction from the actual
cumulative RO log. Its total raw-digest vector uses a specified fallback digest for
unrecovered leaves. Each vector is fixed at its checkpoint, before future opening work.
Prove that this instrumented sequential runner preserves the original effect order and distribution.
The ideal verifier reads the prescribed positions of these extracted vectors and applies
the same decision. Its answers must not be taken from the adversary's later opening list.

Prove from the actual executions that outside the existing checkpoint-disagreement event,
acceptance by RealVerify implies acceptance by IdealVerify(extractA). Equality is required
only on well-formed, accepting-opening transcripts: rejected malformed openings can make
unconditional equality false. Prove the marginal equations identifying the two actual
experiments in this coupling; do not assume an execution-correspondence hypothesis.

Then prove:

    Pr[RealVerify(A) accepts] <= Pr[IdealVerify(extractA) accepts] + delta_MT,

where delta_MT is precisely the pinned VCVio expression

    multiCheckpointROMErrorNumerator(N, C, H, Q) / card(Y).

Carry the existing theorem's hypotheses explicitly: Q bounds all adversarial commitment
and terminal-opening queries; H bounds honest opening verification; each configuration's
node budget is at most P; rounds * P <= N; rounds <= C; the node-query model and uniform
finite nonempty digest response assumptions are those of the owning VCVio theorem.
Reuse its existing numerator and accounting, with no invented simplification.

A corollary transfers any ideal acceptance bound eta to eta + delta_MT. Merely wrapping
an already evaluated transcript predicate does not meet this milestone: executable
verifiers, checkpoint-time extraction, selector enforcement, and actual game marginals
are required. Define the supported ArkLib Protocol and strategies, and prove equality
to their `Interaction.Oracle.executeStrategies` execution (or the exact existing native
runner selected and recorded at statement freeze). Equality to VCVio extractabilityGame
alone does not meet this native bridge obligation.
Do not claim an arbitrary dependent native strategy compiler, a public
challenge transformation, or a complete CY iBCS theorem.

## Further SHOULD, after the principal compiler target

1. A real Sumcheck restoration application. For a false input claim over finite field F,
   k rounds and degree bound d, prove the probability that all sum checks pass and the
   final evaluation agrees with the original polynomial is at most (Q+k)*d/card(F),
   or its nonuniform specialization. Prove successful-output correspondence between
   the fixed-F padded presentation and native aborting Sumcheck under coupled coins,
   including its closed original-oracle behavior. This is ordinary soundness. A Unit
   witness does not turn it into substantive knowledge extraction.
2. Strengthen the Merkle query plan to a causal adaptive decision program, provided
   the bridge still proves actual execution and honest verification budgets. Do not
   move to online interleaved openings without a separate source theorem and game.
3. Extend actual-cache accounting to specified nonempty initial caches under explicit
   independence conditions, only after the empty-cache main theorem is complete. This is lowest priority.

## HOPE and deliberately unanswered questions

A general guarded-round adapter would reconcile early abort with fixed-round restoration.
It needs a defined response to invalid prefixes and an explicit budget for ancestor replay;
using uniform Option F is not the native Sumcheck challenge law. Design it if time remains,
but do not assert arbitrary guarded-protocol restoration from a padded success-event lemma.

Nontrivial witness reconstruction applications, ARC challenge-erased extraction, genuine
machine/PPT extractor certificates, arbitrary dependent native compiler lowering,
encoded/salted Merkle payload extraction, hash-chain FS, duplex FS, and Funky/FIOP compiler
security remain open. Do not settle their interfaces through implementation convenience.
The legacy oracle-reduction code is a comparison source, not authority for missing proofs.

## Workstreams, PR order, reviews, and clock

Use Sol High workers with exclusive worktrees and bounded ownership. Root orchestrates,
checks the mathematics, and owns integration. Three initial lanes: VCVio fresh-query
probability; ArkLib randomized restoration definitions/bridge; terminal-batch Merkle bridge.
The restoration lane starts on definitions and exact statements, then consumes the VCVio
result. Reassign a freed slot to independent review; no worker approves its own change.
Avoid concurrent writes to shared dependency builds.

PR order:

1. VCVio expected distinct-query bounds and the interleaved-randomness interpreter.
2. ArkLib randomized restoration and expected query budgets, pinned to the reviewed VCVio
   revision. Update to merged upstream first if compatible; record and review any migration.
3. Terminal-batch Merkle security transfer in the owning compiler/backend layer. Its proof
   may proceed independently of PR 1; choose ownership after the actual verifier interface
   is checked. Keep backend-generic lemmas in VCVio and ArkLib-specific consumers in ArkLib.
4. Sumcheck application, only if the Sumcheck SHOULD is completed and reviewed.

Aim for 500-1500 changed lines per coherent PR. A smaller important theorem is acceptable;
size alone cannot justify fragmentation or bundling unrelated proofs. If a main slice
requires two PRs, split at a real semantic boundary and update the contract ledger.

First hour: freeze public types, inspect merge state/pins, and challenge the new probability
and Merkle bridge statements. Treat the compiler lane as SHOULD from the start,
not as an undisclosed third MUST. Hours 1-5: parallel proofs and early statement review.
Hours 5-6.5: integration and optional application only if MUST proofs are secure.
Final 1.5 hours: independent read-back, repairs, full validation, pushes and PR descriptions.
Start an eight-hour wall-clock deadline on authorization; stop adding scope before review
is crowded out. A failed target is reported as failed, not silently weakened or relabeled.

Every main statement receives an independent Lean read-back under the review skill, followed
by comparison with this contract. Review quantifiers, nonvacuity, actual game identity,
causality, cache sharing, optional failure, and source-only versus full-runtime logs.
Require configured source builds, applicable full validation/tests and axiom regression
checks, and a final combined integration check. No new admissions or native-trust shortcuts.
Record exact reviewed/built/pushed revisions and material limitations. Open substantial PRs;
do not merge them. No toy client or conditional assumption replacing a central theorem
counts as completion of a MUST.
