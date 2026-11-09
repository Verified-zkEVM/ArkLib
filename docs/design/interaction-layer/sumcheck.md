# Sumcheck in the interaction layer

The modules under `ArkLib/ProofSystem/Sumcheck/Core/` define Sumcheck in the interaction layer.
They prove that it is the embedded legacy Sumcheck at the common observation of record
[D8](../interaction-rebuild/D8-legacy-equivalence-observation.md), and they transfer the legacy
security results to it. The legacy specification `Sumcheck.Spec` stays the mathematical source:
the interaction-layer verifier runs the legacy decision fold, and its relations are the legacy
`Spec.relationRound`.

## Modules

| Module | Contents |
|---|---|
| `SingleRound` | One round: an oracle node for the round polynomial, then one challenge in `R`. |
| `Protocol` | `protocol R deg n`, the `n`-fold replication of the round; the honest prover as a fold with `pure` slots. |
| `Execution` | The verifier: the legacy decision fold on the view's challenges, with message queries routed to oracle nodes. Closed forms of runs; the round check `roundCheck` and its accept and reject equations. |
| `Completeness` | Perfect completeness of the interaction-layer honest prover, proved directly, for every challenge implementation. |
| `LegacyEquivalence` | The equivalence with the embedded legacy verifier, and the transport of every security notion along it. |
| `LegacyCompleteness` | Perfect completeness of the embedded legacy honest prover, transferred. |
| `Soundness` | Soundness, transferred, with error `∑ challenges, deg / |R|`, and its form `n * (deg / |R|)`. |
| `Knowledge` | Straight-line knowledge soundness, transferred, with the same error. |
| `RoundByRound` | Round-by-round soundness and knowledge soundness, transferred, with error `deg / |R|` at every challenge. |

## The protocol and the verifier

The shape of `protocol R deg n` does not depend on challenges: every run has `n` rounds, and the
interaction never rejects. The verifier is passive. After the run it decides on the view with
`legacyProgram`, the legacy fold `Spec.oracleVerifierProgram` of the per-round checks. A failed
round check skips only the remaining checks; the prover's messages, the challenge draws and the
prover's effects of every round have already run. The output oracle is the input polynomial.

`run_verifier_foldRounds` gives the run of any prover whose slots are `pure` in closed form: draw
every challenge in round order, then return the transcript, the output and the legacy verdict of
the decoded transcript.

## Equivalence with the legacy Sumcheck

The equivalence runs through three correspondences:

- **Tree and transcripts.** `protocol_eq` identifies `protocol R deg n` with the oracle tree of
  `Spec.pSpec R deg n`, and `oracleDecode_eq_decodeTranscript` identifies the two transcript
  decodings.
- **Decision.** `decide_eq_legacy`: on every completed run, the decision of the Sumcheck verifier
  and that of the embedded legacy verifier `legacyVerifier` are the same `OracleComp` program,
  before any query is answered, so they make the same queries in the same order.
  `outputMap_eq_legacy` says both keep the input polynomial as output oracle, and
  `verifier_agrees` packages the two as `OracleVerifier.Agrees`. `runWithLog_eq_legacy` follows:
  the logged executions are equal, including the decision log of ambient, input and message
  queries. `decide_ambient_trace` is narrower: once the input and message oracles are answered
  from the run's data, both decisions are `pure` of the legacy verdict, so neither makes an
  ambient query. The decisions do query the round messages.
- **Challenges.** `challengeQueryImpl_eq_legacy`: the uniform challenge oracle of the Sumcheck tree
  is the reindexed uniform legacy challenge oracle.

The main results are:

- `run_eq_legacy`: for every prover, the reindexed and finalized Sumcheck run is the reindexed and
  finalized run of the embedded legacy verifier, as a program. It includes every ambient query of
  the prover and the decision, and keeps the decoded transcript, the prover's output and the
  accepted statement apart.
- `run_legacyProver`: against the embedded legacy honest prover, that program is the legacy run
  `OracleReduction.run`. The legacy honest prover's challenge slots are `pure`
  (`legacyProver_pureChallengeSlots`), which is the hypothesis of the program-equality exchange
  between challenge sampling and the prover's challenge step.

`OracleVerifier.Agrees` in `ArkLib/Interaction/Core/Security/Agreement.lean` collects what
decision agreement gives: equal runs and logged runs, and equal completeness, soundness, knowledge
soundness and round-by-round forms. The `*_cast` lemmas there and in
`Core/Legacy/OracleKnowledge.lean` carry each notion along `protocol_eq`. The chain and routing
lemmas for appended legacy oracle specifications are in `Core/Legacy/OracleAppend.lean`, and the
purity of challenge slots under appending is in `Core/Legacy/PureSlots.lean`.

## Security

Each transfer starts from the stated legacy theorem and goes through the legacy embedding's
transfer theorem, the cast lemmas and `Agrees`, and keeps the legacy error. The quantifiers
differ:

- Soundness and round-by-round soundness quantify over every prover, with any prover output type.
- Straight-line knowledge soundness quantifies over every prover with the legacy-compatible
  output type: a pair of the output statement with its oracle data and the `Unit` output witness.
- Round-by-round knowledge soundness quantifies over every prover, with the `Unit` witnesses of
  the legacy relations.
- Completeness concerns one prover, the embedded legacy honest prover `legacyProver`.

No transfer assumes that the ambient oracle's answer types are inhabited. A proof that needs a
default ambient answer takes one from the support of the ambient implementation
(`supportedAnswer` in `Core/Legacy/OracleReduction.lean`).

| Theorem | Statement | Legacy source |
|---|---|---|
| `verifier_soundness` | Soundness for the languages of `relationRound 0` and `relationRound (Fin.last n)`, error `∑ challenges, deg / |R|`. | `Spec.oracleVerifier_rbrKnowledgeSoundness`, through round-by-round soundness and the guarded implication to soundness |
| `verifier_soundness_rounds` | The same, with error `n * (deg / |R|)`. | `card_challengeIdx`: one challenge per round |
| `verifier_knowledgeSoundness` | Straight-line knowledge soundness for the relations, same error. | `Spec.oracleVerifier_knowledgeSoundness` |
| `verifier_rbrSoundness` | Round-by-round soundness, error `deg / |R|` at every challenge. | `Spec.oracleVerifier_rbrKnowledgeSoundness` |
| `verifier_rbrKnowledgeSoundness` | Round-by-round knowledge soundness, same error. | `Spec.oracleVerifier_rbrKnowledgeSoundness` |
| `legacyProver_perfectCompleteness` | The embedded legacy honest prover is perfectly complete; its output statement and witness lie in the final relation. | `Spec.oracleReduction_perfectCompleteness` |

The round-by-round transfers need a terminal certificate for every state function (departure
15). The legacy verifier's guarded form `Spec.oracleVerifierGuardedForm` supplies it through
`StateTerminalCertificate.of_guarded` and `KnowledgeTerminalCertificate.of_guarded`.

`perfectCompleteness` in `Completeness` is proved directly for the interaction-layer honest
prover, for every challenge implementation, and judges the accepted statement. The transferred
`legacyProver_perfectCompleteness` is a different statement: it concerns the legacy honest
prover, assumes uniform challenges, and judges the output witness as well.

The knowledge transfers use a constant output-witness family: the extracted output witness is
`Unit`, read from the prover's output by `fun _ o => o.2`.

## Tests

The acceptance tests are in `ArkLibTest/ProofSystem/Sumcheck/Core/`.

| File | Checks |
|---|---|
| `Protocol`, `Execution`, `Completeness` | Shape, closed-form runs, zero rounds, a bad first round followed by an honest round, completeness. |
| `LegacyEquivalence` | Legacy prover runs, rejection agreement of the two decisions, zero rounds. |
| `SingleRound` | One-round runs: accepting, rejecting, a dishonest message that passes, distributions of one-round runs; the sum of `X` over `{0, 1}`. |
| `Soundness` | Soundness against any one-round prover; a soundness bound over `ZMod 17`; exact probabilities over `ZMod 5`; the adaptive message's endpoint and hit facts; the exclusion of `X ^ 2` from the degree-one carrier. |
| `RoundByRound` | Clients of the round-by-round, knowledge and completeness transfers. |
| `Rounds` | Two- and three-round runs: challenge draws in round order, the accepted claim, a wrong target that still runs every round and rejects. Two honest rounds on the bilinear input `1 + 2 X₀ + 3 X₁ + 4 X₀ X₁` with the challenges `3` and then `5`: exactly two challenge queries, in round order, and the accepted claim `⟨14, ![3, 5]⟩` with the input polynomial as output oracle. The honest messages on that input, `5 + 8 X` and `1 + 2 c + 3 X + 4 c X`, their sums, and the first-round relation transport. |
| `Effects` | A prover with ambient effects before each message and after the last challenge: the run executes them in protocol order, and a recording handler observes the order. An accepted claim that is not in the final relation. A claim whose first check fails still runs both rounds and rejects, and the decision log holds only the first round's check queries (`decide_log_badFirst` for every completed run whose first message fails its check, at every round count; `runWithLog_wrong` for the logged execution of that prover). The round message's oracle interface. |

## Open

The verifier covers rounds `0` to `n`. There is no verifier for an interval of rounds that starts
at round `i` (departure 18). The following are not ported and are deferred to the remaining
Sumcheck ports of part D, commit 7. Open question OQ16 of the part-D decisions settles their
design: the projection `OracleMap` is the round's output map in `Sumcheck/Core/SingleRound.lean`,
with `projectedRoundPolynomial` as its data map, `simulateProjectedRoundPolynomial` as its query
implementation, and the law from `simulateProjectedRoundPolynomial_eq`.

- The projection of the input polynomial to the round polynomial as an `OracleMap`, with its
  answer law.
- A standalone round executed through that projection map: the projected univariate output and
  the derived query handler. The tests state the first-round relation transport on the round-`0`
  check, which retains the original input polynomial; this is not that execution.
- The split of `n + 1` rounds into an appended first round and `n` rounds, as program equality
  through `Prover.append` and `OracleVerifier.append`.
- A two-round composition through an exported oracle, with a first-round verifier that exports a
  transformed oracle: acceptance, rejection in either part, and the output-relation implication,
  for an arbitrary hidden component.
- `relationRound_last_iff`, the evaluation form of the final relation, next to `relationRound` in
  `ArkLib/ProofSystem/Sumcheck/Spec/`. The tests prove it as `relationLast_iff_eval`.

The generic implication from round-by-round soundness to soundness in the interaction layer is
not ported here; it is deferred to part D, commit 6. The Sumcheck soundness theorems do not need
it: they transfer the legacy soundness, which is derived through the legacy guarded implication.

The protocol is not generic in its message carrier, so no computable instance shares its
decision (open question OQ17).

## Migration disposition

The migration list assigns to this work the assertions of the frozen Sumcheck tests in
`ArkLibTest/ProofSystem/Sumcheck/Interaction/`, the four implication assertions of
`ArkLibTest/Interaction/Oracle/Security/Soundness.lean`, and, by open question OQ4, 23 fixture
facts of the frozen Sumcheck tests. Rows are named `File #k` after the frozen test file and the
row number in the migration list. "Covered" means covered by the approved restatement: concrete
data, all `n` rounds, a passive verifier. Tests are in `ArkLibTest/ProofSystem/Sumcheck/Core/`.

### Assertion rows

| Rows | Disposition |
|---|---|
| ArbitraryCompleteness #1–#4 | Covered by `Completeness`: perfect completeness for every challenge implementation, support and closed-form runs. |
| ArbitraryRounds #1 | Covered: the zero-round run draws nothing. |
| ArbitraryRounds #2, #3, #5 | Covered by `Rounds.run_three`: three rounds, draws in round order. |
| ArbitraryRounds #4 | Covered. `Rounds.run_three_wrong` runs all three rounds on a wrong target and rejects. `Effects.decide_log_badFirst` applies to its honest first message: the decision log holds only the first round's check queries. |
| Closing #1 | Covered by the degree subtype `R⦃≤ deg⦄[X]` of the round message. |
| Closing #2, #3, #5–#8 | Covered by `SingleRound.run_oneRound`, the verdict equations, the output-relation examples and their axiom guards. |
| Closing #4, #9 | Covered by direct perfect completeness and its uniform specialization. |
| Legacy #1, #2 | Covered by `legacy_prover_run` and `embedded_prover_generates` in `LegacyEquivalence`, including wrong targets. |
| Projection #3 | Deferred to part D, commit 7: the projection `OracleMap` of OQ16 and its answer law. |
| Projection #7 | Partly covered. The round-`0` check on the bilinear input accepts the claim `⟨12, ![3]⟩` with the original input polynomial. The projected output and the execution through the projection map are deferred to part D, commit 7. |
| Projection #8, ProjectionTransport #2 | Partly covered. `Rounds.firstRound_relation` states the first-round relation transport for every input, and the bilinear instance is checked. The standalone round executed through the projection handler is deferred to part D, commit 7. |
| Protocol #1, #2 | Covered by `Effects.two_rounds` and the recording handler. |
| Protocol #3, #4 | Covered. `Effects.bad_first_rounds` runs both rounds and rejects. `Effects.decide_log_badFirst` and `Effects.runWithLog_wrong` show that the decision log holds only the first round's check queries. |
| Protocol #6, #8 | Covered by the sampled adaptive prover's bound and the soundness axiom guards. |
| Protocol #7 | Deferred to part D, commit 7: program equality of the appended run through `Prover.append` and `OracleVerifier.append`. |
| Protocol #9, #10 | Covered by the completeness axiom guards. |
| RoundByRound #1 | Covered by the round-by-round clients and `false_claim_bound`. |
| Sequential #2, #4 | Covered by `Rounds.run_two_bilinear` and the recording example: challenges `3` then `5`, two challenge queries in round order, target `14`, the bilinear input as output oracle. |
| Sequential #5, #6 | Covered: rejection after both draws, and honest completeness. |
| SingleRound #2–#6 | Covered by the committed-run equations, the acceptance, rejection and dishonest-output examples, and their axiom guards. |
| Soundness #1–#6, #10, #12 | Covered by the accepted and rejected observations, the bound, the exact repair and rejection probabilities, the challenge-first attack and empty-domain rejection. |
| Soundness #15, #16, #21, #23–#28 | Covered by the axiom guards, the committed and randomized prover bounds and the run equations. |
| SourceRouting #1, #2 | Covered by the affine evaluation and oracle-interface tests in `Effects`, over `ZMod 17`. |
| SourceRouting #3 | Covered by the protocol shape. The challenge and abort branches of `Option` are retired. |
| SourceRouting #4–#7 | Deferred to part D, commit 7: the two-round composition through an exported oracle, with an arbitrary hidden component, acceptance, prefix and suffix rejection, and the output-relation implication. |
| `Interaction/Oracle/Security/Soundness.lean` #3–#6 (lines 54, 55, 57, 58) | Deferred to part D, commit 6 (OQ3): the general local-to-global soundness theorem, its uniform-error corollary, the verifier-escape lemma and random-prefix averaging. |

### Fixture rows (OQ4)

| Row | Disposition |
|---|---|
| ArbitraryRounds #6 | Covered in the tests: `Rounds.relationLast_iff_eval`, with an axiom guard. The production lemma `relationRound_last_iff` in `Sumcheck/Spec/` is deferred to part D, commit 7. |
| Projection #1 | Covered: `Rounds.domain_points`. |
| Projection #2 | Covered: `Rounds.suffix_points`. |
| Projection #4 | Covered: `Rounds.bilinear_relation`. |
| Projection #5 | Covered: `Rounds.projected_eval`, the honest first message is `5 + 8 X`. |
| Projection #6 | Covered: `Rounds.projected_sum`. |
| ProjectionTransport #1 | Covered: `Rounds.bilinear_relation`. |
| ProjectionTransport #3 | Covered: the first-round example in `Rounds`, the claim `⟨12, ![3]⟩` with the bilinear input in the round-`1` relation. |
| Protocol #5 | Covered: `Effects.target_seven_not_final`. |
| Sequential #1 | Covered: `Rounds.second_eval`. |
| Sequential #3 | Covered: `Rounds.second_sum`. |
| SingleRound #1 | Covered: `SingleRound.msgX_sum`. |
| Soundness #7 | Covered: `Soundness.excludes_quadratic`. |
| Soundness #8 | Covered: `Soundness.adaptive_endpoints`. |
| Soundness #9 | Covered: `Soundness.adaptive_hits`. |
| Soundness #11 | Covered: `Soundness.fresh_bound_lt_one`. |
| Soundness #13, #14 | Covered: axiom guards of the zero and linear input fixtures `poly0`, `polyX` and `polyXK`. |
| Soundness #17 | Covered: axiom guard of `excludes_quadratic`. |
| Soundness #18 | Covered: axiom guard of the adaptive message `adaptive`. |
| Soundness #19, #20 | Covered: axiom guards of `adaptive_endpoints` and `adaptive_hits`. |
| Soundness #22 | Covered: axiom guard of `fresh_bound_lt_one`. |

## Departures

These entries continue the numbering of [`departures.md`](departures.md).

### 17. The transferred completeness is in its own module

**Plan.** The implementation plan for the Sumcheck modules lists `Completeness` as the home of completeness.

**Code.** `Completeness` keeps the direct proof for the interaction-layer honest prover.
`LegacyCompleteness` holds `legacyProver_perfectCompleteness`, the transfer of the legacy
`Spec.oracleReduction_perfectCompleteness`.

**Why.** `LegacyEquivalence` imports `Completeness`, and the transfer needs `LegacyEquivalence`,
so it cannot live in `Completeness`. The two theorems state different things: the direct one is
for the interaction-layer honest prover and every challenge implementation; the transferred one is
for the embedded legacy honest prover with uniform challenges, and judges the output witness.

### 18. The verifier has no interval start

**Migration.** The migration list of the frozen Sumcheck tests restates several assertions on a run that
starts at round `i`: a single round of a multi-round statement, and the split of `n + 1` rounds
into one round appended to `n` rounds.

**Code.** `verifier R deg n D ambient` decides rounds `0` to `n` from `Spec.StatementRound R n 0`.
The first-round relation transport is stated on the verifier's round-`0` check, `roundCheck`:
from the round-`0` relation, the check on the honest first message accepts a statement in the
round-`1` relation (`firstRound_relation` in the `Rounds` test). This is a statement about the
round check, which keeps the original input polynomial; it is not an execution through the
projection map. The split of `n + 1` rounds is not stated.

**Why.** A verifier for an interval of rounds changes the statement types of the composition and
needs its own equivalence with the legacy single-round verifiers. Restating the interval
assertions for all `n` rounds is allowed. The departure does not retire the append equivalence of
Protocol #7 or the projection execution: both are deferred to part D, commit 7 (see
[Migration disposition](#migration-disposition)).
