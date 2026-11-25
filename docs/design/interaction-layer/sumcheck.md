# Sumcheck in the interaction layer

The Sumcheck core has two verifiers. `indexedVerifier` in `Indexed` is the interaction-layer
verifier over an arbitrary finite indexed domain `D : Fin d → R`. The compatibility `verifier` in
`Execution` runs the legacy decision fold with routed message queries over an injective domain
`D : Fin d ↪ R`. Public theorems about `indexedVerifier` start with `indexedVerifier_`. Results
about the compatibility `verifier` start with `verifier_`, and those transferred from the legacy
soundness theorem end in `_of_legacy`.

`Sumcheck.Core.Soundness` proves full-run soundness of `indexedVerifier`. The verifier sums over
indices. In particular, the constant polynomial one has sum two over `[0, 0]`; neither the
verifier nor its proof deduplicates the list.

The argument is the sum-check analysis of [LFKN92](https://lance.fortnow.com/papers/files/ip.pdf),
as presented in [Thaler, §4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf#page=37)
(Proposition 4.1 for the Boolean domain, Remark 4.1 for a finite subset). The specialization
differs as follows. `D : Fin d → R` counts repeated points with multiplicity. The message type
`R⦃≤ deg⦄[X]` enforces the degree bound, so the verifier makes no degree check. The output
relation `indexedOutputProblem` performs the final evaluation check. The error denominator is the
size of the uniformly sampled challenge type `R`.

The proof first bounds a false-to-true transition of the remaining-sum relation at each fresh
challenge. `indexedVerifier_rbrSoundness` packages these bounds as a core state function.
`indexedVerifier_soundness` then applies the parent stack's
`OracleVerifier.soundness_of_rbrSoundness_uniform`, using exactly one challenge per round.
For every ambient-effectful prover and every output family, the probability that the run
returns a claim satisfying the final evaluation relation, from a false input claim, is at most
`n * (deg / |R|)`. The ring assumptions are a finite
commutative semiring with `IsDomain`; the domain map need not be injective or nonempty.

The three interval contracts have different scopes:

- **Verifier and honest completeness.** `intervalVerifier` and `IntervalCompleteness` apply to
  every bounded interval `start + count ≤ n`, including nonzero starts and zero rounds. A
  zero-round run returns the original claim and still runs the prover's leaf computation
  (`intervalVerifier_run_zero`). Challenge handlers may share state with ambient effects and
  depend on the reached statement.
- **Suffix soundness.** `intervalVerifier_soundness` assumes `start + count = n` and fresh uniform
  challenges. It bounds by `count * (deg / |R|)` the probability that the run returns an accepted
  **true** output claim from a false input claim. Its list and injective corollaries
  `intervalVerifier_soundness_list` and `intervalVerifier_soundness_injective` specialize it.
- **Local round soundness.** `intervalRoundExecute_soundness` gives the one-round bound
  `deg / |R|` at every variable position.

A soundness theorem for an interior endpoint `start + count < n` is follow-up work.

The remaining-claim recurrence and the agreement bound at a fresh challenge follow
[Thaler §4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf#page=34) and
[Proposition 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf#page=37), and
the original development of
[Lund, Fortnow, Karloff and Nisan](https://lance.fortnow.com/papers/files/ip.pdf).
Three details differ here. Domain indices keep repetitions. The verifier returns the endpoint
claim instead of querying the input polynomial. The application checks that claim in its output
relation.

## Modules and ownership

| Module | Contents |
|---|---|
| `SingleRound` | One round: an oracle node for the round message, then one challenge in `R`. `round` is the round at `R⦃≤ deg⦄[X]`; at any message carrier `M` with evaluation `eval` the round is `Interpreted.protocol R M eval 1`. |
| `Protocol` | `protocolOn R M eval n` and its instance `protocol R deg n`, the `n`-fold replication of the round; the honest prover as a fold with `pure` moves. |
| `Execution` | The verifier `verifierOn` over any message carrier, and its instance `verifier`: the legacy decision fold on the view's challenges, with message queries routed to oracle nodes. Closed forms of runs; the round check `roundCheck` and its accept and reject equations. |
| `Completeness` | Perfect completeness of the interaction-layer honest prover, proved directly, for every challenge implementation. |
| `LegacyEquivalence` | The equivalence with the embedded legacy verifier, and the transport of every security notion along it. |
| `LegacyCompleteness` | Perfect completeness of the embedded legacy honest prover, transferred. |
| `Soundness` | Soundness, transferred, with error `∑ challenges, deg / |R|`, and its form `n * (deg / |R|)`. |
| `Knowledge` | Straight-line knowledge soundness, transferred, with the same error. |
| `RoundByRound` | Round-by-round soundness and knowledge soundness, transferred, with error `deg / |R|` at every challenge. |
| `Computable` | The executable instance at CompPoly messages and inputs: protocol, verifier, verdict reader and honest prover. The run correspondence `run_eq_interpret`, perfect completeness and soundness, transported. |
| `Types` | Interaction layer round statements, polynomial oracle data and prefix/suffix coordinates. `roundSuffix` is the interaction layer's only suffix definition; `roundSuffix_eq_spec` shows it is the frozen `Spec.SingleRound.roundSuffix`. |
| `SingleRound`, `MessageTree`, `Tree` | The oracle-message/challenge round, the fixed full-run tree at any message carrier with its uniform challenge sampler, and transcript prepending. `Tree.challengeSampleable` is the sampler at polynomial evaluation. Transcript access uses the `InterpretedPath` helpers. `Tree` owns the decision lift `decisionLift` and its answer law `simulateQ_decisionLift_monad`, which both verifiers use. |
| `Domain` | Indexed remaining sums, honest projected polynomials, the successor identity and final evaluation relation. |
| `Indexed` | The interaction-layer indexed verifier, whose verdict and decision are the interval fold ending at the last round, its actual-run equation, the state function and interaction-layer local-to-global soundness proof. |
| `Soundness` | `indexedVerifier` full-run, arbitrary-list and injective corollaries; actual-run committed and randomized bounds in probability and measure form. |
| `DomainEquivalence` | Agreement of the honest projected polynomials and sum relations with the injective legacy `Spec` representation, full-run verdict and oracle-program equations, and honest interval output correspondence. |
| `Protocol`, `Fold` | Prover folds over any message carrier, and passive final checks that abbreviate the interpreted checks at polynomial evaluation and use their actual-run and bundle-answer equations. |
| `Interval`, `IntervalExecution` | Arbitrary endpoints, public midpoint transport, and one-round and empty-run equations. |
| `IntervalCompleteness`, `IntervalAdaptive` | Support, perfect and measure completeness for every bounded interval and adaptive statement-dependent challenges. |
| `IntervalSoundness`, `IntervalRoundSoundness` | Interaction-layer suffix RBR soundness, implication bounds, list/injective forms, full-run identity and actual one-round bounds at every variable position. |
| `FoldComposition`, `BehaviorComposition` | Append equations for generic folds and public intervals, preserving every prover effect, private output and arbitrary original behavior. |
| `Projection`, `Behavior` | Derived projected handlers, closed execution and the unit-query bound `projectedQuery_isChargeBound`; retained arbitrary original behavior and its final evaluation relation. The polynomial soundness theorems require polynomial input data and do not apply to arbitrary behavior. |
| `InterpretedPath`, `Interpreted`, `InterpretedExecution` | Shape paths, transcript heads and tails, head queries, tail lifts and views for generic message trees, shared with `Tree`, `Indexed` and the legacy route; passive verification for generic message representations, the carrier transport of provers and challenge implementations (`transportFocal`, its constant-output instance `transportProver`, `transportDraw`), and effect-preserving execution interpretation. The polynomial fold in `Fold` abbreviates this verification at polynomial evaluation. |
| `ComputableProjection`, `ComputableInterval`, `ComputableSoundness` | The connection from the CompPoly enumeration of `Impl/IndexedProjection` to the indexed projection, concrete honest interval folds, execution interpretation, completeness and interaction-layer suffix soundness. |
| `LegacyProtocol`, `Execution`, `Completeness` | Compatibility honest prover, decision, closed-form runs and direct completeness. |
| `LegacyProjection`, `Composition` | Separate legacy projection and decision-fold comparisons. |
| `LegacyEquivalence`, `LegacySoundness`, `LegacyCompleteness` | Separate execution and security comparisons with embedded legacy Sumcheck. |
| `Knowledge`, `RoundByRound` | Compatibility knowledge and round-by-round transfers. |

The interaction-layer import graph is `Soundness → Indexed → Interval → Fold → Interpreted`, and
`Interval` also imports `Domain`. It does not import `Sumcheck.Spec`, the compatibility execution
or a legacy security transfer. `IntervalSoundness` imports `Indexed`, so the full-run and interval
verifiers share one interpreted fold. `DomainEquivalence` and `LegacyEquivalence` check agreement
separately. The compatibility `verifier` keeps its old name; the interaction-layer verifier is
`indexedVerifier`. The two verifiers share `decisionLift` in `Tree` and `roundSuffix` in `Types`,
which do not depend on the legacy modules.

## The interaction-layer verifier and its bound

`protocol R deg n` has exactly `n` rounds. Each sends a degree-bounded polynomial and draws a
challenge in `R`. Neither the oracle message nor the challenge selects shape (P2).
The verifier is passive: it queries the messages and decides after the interaction (P1).
A failed sum check skips the remaining decision queries. All prover effects and challenge draws
have already run. Its output oracle is the original input polynomial.

`indexedRelation D i stmt p` states that the indexed remaining sum equals `stmt.target`.
At the last round, `indexedRelation_last` identifies this with polynomial evaluation at the
full challenge vector. If a false current relation passes the message's indexed sum check,
the honest and sent round polynomials differ. A successor relation can hold only at one of
their agreement points, whose uniform mass is at most `deg / |R|`.

| Interaction-layer theorem | Exact scope |
|---|---|
| `indexed_round_soundness` | One false-to-true indexed round, including the sum check. |
| `indexedVerifier_rbrSoundness` | Every full execution prefix, with local error `deg / |R|`. |
| `indexedVerifier_soundness`, `indexedVerifier_soundness_nsmul` | The actual full run, for every prover, with `n` times that error. |
| `indexedVerifier_soundness_list` | `D = domain.get` for any list, retaining repetitions. |
| `indexedVerifier_soundness_injective` | The same interaction-layer bound for an embedding. |
| `indexedVerifier_run_soundness` | Probability that the actual run returns a claim satisfying the final evaluation relation. |
| `indexedVerifier_committed_soundness`, `indexedVerifier_committed_measureSoundness` | An arbitrary polynomial committed before the one-round challenge. |
| `indexedVerifier_randomized_soundness`, `indexedVerifier_randomized_measureSoundness` | An ambient, possibly failing commitment before the fresh challenge, including shared state. |

These bounds concern returned claims that satisfy the final evaluation relation. They do not
assert that every returned claim is valid. A dishonest message can pass a sum check while the
retained input polynomial fails the final relation. Tests retain this distinction.

The final decision of `indexedVerifier` queries the oracle messages in a fixed order. Each
attempted sum check queries the round message once per domain index, in index order and
including repeats. A successful check adds one query at the challenge. A rejection ends the
decision's queries, although every interaction round has already run. The soundness bound
certifies neither a query charge nor an execution cost. #1488 and #1487 must preserve this order
when they share the decision code.

## Arbitrary interval endpoints

`intervalVerifier R deg n D ambient start count bound` retains the earlier challenge prefix and
original polynomial. Its output index is written `count + start`; commutativity identifies it
with `start + count`. This order makes the full endpoint `n + 0` definitionally `n`.

| Theorem | Exact contract |
|---|---|
| `intervalVerifier_supportCompleteness`, `intervalVerifier_perfectCompleteness`, `intervalVerifier_measureCompleteness` | Every `start + count ≤ n`; every supported honest run accepts a true endpoint claim, including stateful challenge handlers. |
| `intervalVerifier_adaptive_perfectCompleteness` | Explicit challenge callbacks from the current round and full statement, without a finite-sampling assumption. |
| `intervalVerifier_evaluation` | For an honest prover and a true starting claim at `start + count = n`, the returned target is the original polynomial's evaluation at the complete prefix. |
| `intervalVerifier_rbrSoundness`, `intervalVerifier_soundness` | Interaction-layer suffix soundness for `start + count = n` and fresh uniform challenges, with local error `deg / |R|` and total error `count * (deg / |R|)` on an accepted true output claim from a false input. `intervalVerifier_soundness_list` and `intervalVerifier_soundness_injective` are its corollaries. |
| `intervalVerifier_full_run` | Actual program equality with the parent's `indexedVerifier` at `start = 0`, `count = n`, for every prover and output family. |
| `run_append_public_intervalVerifier` | Actual append of `intervalVerifier start 1` and `intervalVerifier (1 + start) count`, with explicit endpoint transport. |
| `projectedInput_eq`, `simulateQ_projectedInput`, `projectedExecute_closed`, `projectedExecute_related` | Derived query behavior, arbitrary standalone programs, returned projected behavior and the final evaluation claim. |

`Impl/IndexedProjection` owns the CompPoly enumeration `Impl.Computable.indexedRoundPolynomial`
and its common proofs. `Impl/Projection` specializes it to an injective domain, and
`Computable.indexedRoundPolynomial_toPoly` connects it to the indexed projection of `Domain`.
`Computable.projectedMessage_toMessage` and `Computable.interpret_intervalHonestProver` identify the
computed honest messages with the interaction-layer interval fold. `Computable.execute_soundness`
transfers the interaction-layer suffix bound to every computational-message prover, including
ambient effects and arbitrary private continuations. These modules do not import the legacy `Spec`.

The interval proofs retain the parent's full-run statements. `IntervalTest.nonzero_run`,
`nonzero_rejects`, `zero_count` and `zero_run` instantiate boundary execution at `Nat` with a
repeated domain and explicit deterministic draws. `RoutingTest` also uses `Nat`; its algebraic
export and routing laws require only a commutative semiring.
`Sumcheck.Core.ComputableTest.suffix_soundness_one_seventeenth` applies `interval_soundness` to the
actual computable suffix run over `ZMod 17` with two variables, start one, one round, degree one
and domain `[0, 0]`. The original polynomial is zero, the incoming target is two, and the prover
sends `X + 1` and outputs the challenge it receives. `shiftStart_false` proves the starting claim
false, `shift_sum` shows that the sum check passes, and `shift_endpoint_iff` shows that the
endpoint relation holds only at challenge `-1`. The bound is `1/17`.
`ComputableIntervalTest.computedRun` executes the coefficient-array honest prover after
prefix `![7]`, with a repeated domain and deterministic challenge `3`, and checks
`some (0, 7, 3, 29)`. `ComputableIntervalTest.oneRun` runs the same fixture on the constant-one
input with incoming target `4`, so both repeated domain points count, and checks
`some (2, 7, 3, 29)`. `IntervalTest.repeated_projectedMap` queries `projectedMap` over the
repeated domain `[0, 0]` with one variable left to sum over and gets `2`.
`EffectsTest.public_append_record` runs the public interval append on the effect fixture and
gets `(some 7, [0, 1, 2, 1, 3])`. `InterpretedTest.runExample` executes a coefficient-pair carrier
directly.

The protocol, the round routing, the view's challenges, the decision lift and the verifier are
generic in the message carrier: a type `M` with an evaluation `eval : M → R → R` that answers the
round message's evaluation queries (open question OQ17). `round`, `protocol`, `route`,
`decisionLift` and `verifier` are their instances at `R⦃≤ deg⦄[X]` with `Polynomial.eval`, with
unchanged types. `verifierOn` and the Core `pathLift` are `@[macro_inline]`: the compiler never
receives the input family as a runtime argument, so `verifier` stays executable at a
noncomputable input family.

## Equivalence with the legacy Sumcheck

Every result in this section concerns the compatibility `verifier`, not `indexedVerifier`.
`DomainEquivalence` relates only the honest projected polynomials and sum relations of the two
representations over an injective domain. No theorem relates `indexedVerifier` to the legacy
verifier. A closed-verdict bridge would compare the two decisions after interpreting the
messages. A security transfer would also need the corresponding relations, output maps and
challenge draws, and a comparison of open query traces would need a program law.

The equivalence runs through three correspondences:

- **Tree and transcripts.** `protocol_eq` identifies `protocol R deg n` with the oracle tree of
  `Spec.pSpec R deg n`, and `oracleDecode_eq_decodeTranscript` identifies the two transcript
  decodings.
- **Decision.** `decide_eq_legacy`: on every completed run, the decision of the compatibility
  `verifier` and that of the embedded legacy verifier `legacyVerifier` are the same `OracleComp` program,
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

- `run_eq_legacy`: the reindexed and finalized run of the compatibility `verifier` is the
  reindexed and finalized run of the embedded legacy verifier, as a program. It covers every
  prover whose output is a final statement, its oracle data and a witness of some type `WitOut`.
  It assumes inhabited ambient response types, which the embedding requires. It includes every ambient query of
  the prover and the decision, and keeps the decoded transcript, the prover's output and the
  accepted statement apart.
- `run_legacyProver`: for the embedded legacy honest prover `legacyProver`, with `Unit`
  witnesses and inhabited ambient response types, that program is the legacy run
  `OracleReduction.run`. It requires the legacy honest prover's challenge slots to be `pure`,
  which `legacyProver_pureChallengeSlots` proves. That is the hypothesis of the program-equality
  exchange between challenge sampling and the prover's challenge step.

`OracleVerifier.Agrees` in `ArkLib/Interaction/Core/Security/Agreement.lean` collects what
decision agreement gives: equal runs and logged runs, and equal completeness, soundness, knowledge
soundness and round-by-round forms. The `*_cast` lemmas there and in
`Core/Legacy/OracleKnowledge.lean` carry each notion along `protocol_eq`. The chain and routing
lemmas for appended legacy oracle specifications are in `Core/Legacy/OracleAppend.lean`, and the
purity of challenge slots under appending is in `Core/Legacy/PureSlots.lean`.

## Compatibility security and completeness

The compatibility knowledge theorems concern the compatibility `verifier` and retain the legacy
relations and injective domain. `verifier_knowledgeSoundness` quantifies over legacy-compatible
output statements and witnesses. `verifier_rbrKnowledgeSoundness` is a local certificate with
`Unit` input and output witnesses: it quantifies over statements, receiver prefixes, histories
and challenges, not over provers. The claim about every prover belongs to the run soundness
theorems `verifier_soundness_of_legacy` and `indexedVerifier_soundness`.
`verifier_rbrSoundness` is the separate compatibility round-by-round transfer, also a local
certificate. The interaction-layer round-by-round theorem is `indexedVerifier_rbrSoundness`.
`verifier_soundness_of_legacy` in `LegacySoundness` and its rounds form
`verifier_soundness_rounds_of_legacy` preserve the old transfer for the compatibility `verifier`
as a comparison check. The interaction-layer security statements do not use them.

`perfectCompleteness` proves completeness directly for the compatibility honest prover and
every challenge implementation. `legacyProver_perfectCompleteness` concerns the embedded legacy
honest prover with uniform challenges and also judges its output witness. The compatibility
round-by-round transfers use the guarded certificates of departure 15
(`StateTerminalCertificate.of_guarded` and `KnowledgeTerminalCertificate.of_guarded`). No transfer
requires inhabited ambient response types: `supportedAnswer` obtains answers from support.
The knowledge transfers extract the constant `Unit` output witness from the prover's output.

## The computable instance

`Sumcheck.Core.Computable` instantiates the generic protocol and verifier at the CompPoly message
carrier `Impl.Representation.Message R deg`, whose evaluation queries are answered by Horner
evaluation, and at the input family of CompPoly multivariate polynomials `Computable.Input` with
the individual degree bound. `toOracleStatement` reads an input as the mathematical polynomial
(`interpretInput`).

- **Executable definitions.** `Computable.protocol`, `Computable.verifier`, `Computable.observe`
  and the honest prover `Computable.honestProver` are computable. The honest prover computes each
  round message with `Impl.Computable.projectedMessage` and updates the target by Horner
  evaluation. `foldRounds` computes each message once and passes it to both the send and the
  successor function, so the update evaluates the message already sent instead of projecting
  again.
- **Run correspondence.** `run_eq_interpret` holds at every message carrier `M` with a reading
  `f : M → R⦃≤ deg⦄[X]` that agrees with `eval`. Renaming the challenge queries of a run of
  `verifierOn` at `M` (`renameQueries`) and mapping its outcome gives the run of
  `verifierOn` at the polynomial carrier against the interpreted prover
  `Interpreted.transportFocal f n g P`. The interpreted prover sends the messages read through
  `f`, keeps every effect, and maps the output by `g`. Challenge nodes of the two protocols are different
  types, so challenge implementations move between carriers by `Interpreted.transportDraw`;
  `experiment_renameQueries` turns the renaming into a transported challenge implementation, and
  `transportDraw_challengeQueryImpl` shows that uniform challenges transport to uniform
  challenges.
- **Honest prover.** `interpretProver_honestProver`: the computable honest prover, interpreted
  through `toMessage`, is `Sumcheck.Core.honestProver` on the interpreted input
  (`projectedMessage_toMessage`, `projectedMessage_evaluate`).
- **Security.** `Computable.support_completeness` accepts a true output on every supported
  honest run, before any oracle distribution is chosen. `Computable.perfectCompleteness` follows
  for a stateful ambient handler and every `ProbComp` challenge handler indexed by challenge
  node. `Computable.soundness` holds for uniform challenges, with
  the error of `indexedVerifier_soundness_nsmul`. The relations and languages are those of
  `Spec.relationRound` on the interpreted input; the proofs transport the mathematical core
  results through `run_eq_interpret`.

### Runtime checks

`scripts/SumcheckRuntime.lean` (`lake exe sumcheck-runtime`) compiles and runs the computable
instance over `ZMod 17`. The challenge handler answers a fixed value and logs each draw; the
ambient handler answers prover events from a fixed table and logs each event. The log holds prover
events `.inl i` and challenge draws `.inr j` in execution order.

| # | Check | Expected |
|---|---|---|
| 1 | `quadratic_degree`, compile-time: `x² + 3xy + 2y² + 5` has individual degree at most `2`. | Proved. |
| 2 | Horner evaluation, including a trimmed zero leading coefficient. | `evaluate (affine 7 1) 3 = 5`, `evaluate (affine 0 4) 9 = 4`. |
| 3 | Two rounds of an adaptive prover over the domain `{0}`, challenges `3`: private memory and effect order. | Verdict `(7, 3, 3, 0)`, log `[p0, c0, p2, c1, p3]`. |
| 4 | The same prover over the empty domain: a failed first check still runs every round. | Rejection, log `[p0, c0, p2, c1, p3]`. |
| 5 | Direct evaluation of the quadratic and its first projected message. | Cube sum `15`, value `16` at `(4, 4)`, first message `7` at `4`. |
| 6 | The computable honest prover on the quadratic over `{0, 1, 2}`, challenges `4`. | Verdict `(16, 4, 4, 16)`, log `[c0, c1]`. |
| 7 | The zero-round interval verifier from the final round state `⟨16, ![4, 4]⟩`. | Verifier verdict `some (16, 4, 4, 16)`, empty trace. The prover-only outcome remains an additional check. |
| 8 | `Computable.intervalVerifier` for one round on the constant-one input in three variables over the domain `[0, 0]`, after the prefix `[7]`, challenge `3`. | Target `4`: verdict `some (2, 7, 3, 1)`, log `[c0]`. Target `3`: rejection, log `[c0]`. |

Row 1 is a compile-time check. The executable emits eight checks: rows 2 to 8 and the separate
zero-round prover check. Rows 3, 4 and 6 require P1/P2; row 7 preserves the frozen verifier
assertion ([entry 24](../interaction-rebuild/IMPLEMENTATION-NOTES.md#24-computable-sumcheck-runtime)).
Row 8 is new.

## Tests

The files under `ArkLibTest/ProofSystem/Sumcheck/Core/` retain the existing acceptance, rejection,
exact-probability, adaptive-message, effect-order, routing and axiom checks. Compatibility tests
import the comparison modules explicitly. Interaction-layer tests add arbitrary maps and lists,
committed and randomized actual runs, and an actual final decision with constant message one and target
two over `[0, 0]`. `IndexedSoundnessTest.repeated_run` checks the complete accepting program
on that repeated domain, including the transcript and retained input oracle.
`IndexedSoundnessTest.exact_success_probability` runs `indexedVerifier` over `ZMod 5` with
domain `[0, 0]`, input polynomial zero, target two and committed message `X + 1`. The sum check
passes at every challenge, and `verdict_at_zero` shows the run returns a claim at challenge zero
that fails the final relation (`claim_at_zero_false`). Only challenge `-1` gives a valid final
claim (`success_iff`), so the success event has probability exactly `1/5`. `Domain` also checks the repeated-point sum, its deduplicated contrast and a
two-coordinate indexed sum. Axiom checks permit only `propext`, `Classical.choice` and `Quot.sound`.

| File | Checks |
|---|---|
| `Protocol`, `Execution`, `Completeness` | Shape, closed-form runs, zero rounds, a bad first round followed by an honest round, completeness. |
| `LegacyEquivalence` | Legacy prover runs, rejection agreement of the two decisions, zero rounds. |
| `SingleRound` | One-round runs: accepting, rejecting, a dishonest message that passes, distributions of one-round runs; the sum of `X` over `{0, 1}`. |
| `Soundness` | Soundness against any one-round prover; a soundness bound over `ZMod 17`; exact probabilities over `ZMod 5`; the adaptive message's endpoint and hit facts; the exclusion of `X ^ 2` from the degree-one carrier. |
| `RoundByRound` | Clients of the round-by-round, knowledge and completeness transfers. |
| `Rounds` | Two- and three-round runs: challenge draws in round order, the accepted claim, a wrong target that still runs every round and rejects. Two honest rounds on the bilinear input `1 + 2 X₀ + 3 X₁ + 4 X₀ X₁` with the challenges `3` and then `5`: exactly two challenge queries, in round order, and the accepted claim `⟨14, ![3, 5]⟩` with the input polynomial as output oracle. The honest messages on that input, `5 + 8 X` and `1 + 2 c + 3 X + 4 c X`, their sums, and the first-round relation transport. |
| `Computable` | The honest message is the CompPoly projection; the interpreted honest prover; the run correspondence; the challenge transport round trip and uniformity; support completeness without an oracle distribution, and completeness and soundness over `ZMod 5`; the suffix soundness bound `1/17` over `ZMod 17` from a proved false starting claim, with a private output that depends on the challenge; the equality of `Spec.polynomialFamily` and `Core.polynomialFamily` by `rfl`; computability of the executable definitions and axiom guards. |
| `Effects` | A prover with ambient effects before each message and after the last challenge: the run executes them in protocol order, and a recording handler observes the order. An accepted claim that is not in the final relation. A claim whose first check fails still runs both rounds and rejects, and the decision log holds only the first round's check queries (`decide_log_badFirst` for every completed run whose first message fails its check, at every round count; `runWithLog_wrong` for the logged execution of that prover). The round message's oracle interface. |

## Historical full-run limitations

The following list records the pre-restack limitations. The parent’s indexed interval, projection,
composition and generic implication results above resolve these items; the disposition tables
below retain the parent’s exact statuses.

Previously, the verifier covered rounds `0` to `n`. There is no verifier for an interval of rounds that starts
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

The former migration list deferred the generic implication to part D, commit 6. The parent now
exports it; see the generic soundness disposition below. The Sumcheck soundness theorems do not need
it: they transfer the legacy soundness, which is derived through the legacy guarded implication.
`Rounds` keeps the two- and three-round examples, including the bilinear input and challenge
order. `Effects` checks ambient effects, routed polynomial answers over every commutative
semiring, the `Nat` instance, and decision-query short circuiting after a bad first check.
`SingleRound` keeps honest, dishonest and rejected outputs. `Soundness` retains the exact repair
probability, the challenge-first attack, empty-domain rejection and the degree-carrier check.

## Migration disposition

The test inventory below identifies each frozen test file, migration-list row and source line.
The production inventory that follows lists every source declaration separately. `T/` means
`ArkLibTest/ProofSystem/Sumcheck/Core/`; `C/` means `ArkLib/ProofSystem/Sumcheck/Core/`.
Unqualified target declarations are in `Sumcheck.Core`; test namespaces follow their file names.
The source prefix for the test tables is `ArkLibTest/ProofSystem/Sumcheck/Interaction/`.
Production rows use their complete source paths.
Each row has exactly one migration disposition. The dispositions record how each frozen
assertion maps to the interaction layer. The frozen `Sumcheck.Interaction` modules and their
tests still ship unchanged.

- **equivalent**: the target preserves the source assertion's scope.
- **premise-required (P1)**: the source changes because the passive verifier sends only
  challenges and makes every bundle query in the final decision.
- **premise-required (P2)**: the source changes because challenges and oracle messages never
  select shape.
- **retired**: the interaction layer does not port the row's mechanism, rather than claiming a
  narrower equivalent. This is a migration disposition: the frozen source still ships.
- **unresolved**: the row names a missing parent interface.

Compatibility comparisons do not close interaction-layer soundness rows. The interaction-layer
full-run and interval bounds above close those rows. The targets below replace every interval,
projection and append row formerly assigned to #1488. A status naming P1 or P2 records the required
change to the source's decision timing or abort-dependent shape, including its observable abort
effects. It does not claim equality with the frozen early-aborting program.

### ArbitraryCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `ArbitraryCompleteness.lean` #1, L12 `#print axioms executeRoundsSampled_perfectCompleteness` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_perfectCompleteness` | equivalent |
| `ArbitraryCompleteness.lean` #2, L13 `#print axioms executeRoundsSampled_measureCompleteness` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_measureCompleteness` | equivalent |
| `ArbitraryCompleteness.lean` #3, L14 `#print axioms executeRounds_uniform_measureCompleteness` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_measureCompleteness` | equivalent |
| `ArbitraryCompleteness.lean` #4, L15 `#print axioms executeRounds_evaluation` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_evaluation` | equivalent |

### ArbitraryRounds

| Exact source | Exact target | Status |
|---|---|---|
| `ArbitraryRounds.lean` #1, L50 example (zero rounds) | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_zero` | equivalent |
| `ArbitraryRounds.lean` #2, L55 `three_rounds` | T/Rounds.lean: `RoundsTest.run_three` and recording example | premise-required (P2) |
| `ArbitraryRounds.lean` #3, L85 example (record) | T/Rounds.lean: `RoundsTest.run_three` and recording example | premise-required (P2) |
| `ArbitraryRounds.lean` #4, L93 example (rejection) | T/Rounds.lean: `RoundsTest.run_three_wrong`; T/Effects.lean: `EffectsTest.decide_log_badFirst` | premise-required (P1) |
| `ArbitraryRounds.lean` #5, L105 `#print axioms executeRounds_honest` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerdict_honest; intervalVerifier_honest_run` | equivalent |
| `ArbitraryRounds.lean` #6, L106 `#print axioms closedRelation_last_iff` | C/Behavior.lean: `Sumcheck.Core.behaviorRoundRelation_last; behaviorIntervalVerifier_run_zero` | equivalent |

### Closing

| Exact source | Exact target | Status |
|---|---|---|
| `Closing.lean` #1, L17 example | C/Indexed.lean: `Sumcheck.Core.message_degree`; T/Domain.lean: degree example and axiom checks | equivalent |
| `Closing.lean` #2, L20 example | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest`; T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #3, L28 example | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_complete` (challenge `pure r`); T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #4, L36 example | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_perfectCompleteness` (arbitrary challenge); T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #5, L43 example | T/SingleRound.lean:235, dishonest output retaining input zero | equivalent |
| `Closing.lean` #6, L80 `#print axioms executeCore_closed` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest`; T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #7, L81 `#print axioms executeCore_degree_complete` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_degree_complete` (challenge `pure r`); T/Domain.lean: degree-completeness example and axiom checks | equivalent |
| `Closing.lean` #8, L82 `#print axioms executeSampled_eq` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_honest_eq` (arbitrary challenge); T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #9, L83 `#print axioms executeSampled_perfectCompleteness` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_perfectCompleteness` (arbitrary challenge); T/Domain.lean: execution clients and axiom checks | equivalent |

### Legacy

| Exact source | Exact target | Status |
|---|---|---|
| `Legacy.lean` #1, L29 `prover_generates_transcript` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyProver_run`; T/Soundness.lean: axiom check | equivalent |
| `Legacy.lean` #2, L41 example | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyProver_run`; T/Soundness.lean: axiom check | equivalent |

### Projection

| Exact source | Exact target | Status |
|---|---|---|
| `Projection.lean` #1, L50 `domain_points` | T/Rounds.lean: `RoundsTest.domain_points` | equivalent |
| `Projection.lean` #2, L57 `suffix_points` | T/Rounds.lean: `RoundsTest.suffix_points` | equivalent |
| `Projection.lean` #3, L73 `derived_eval` | C/Projection.lean: `Sumcheck.Core.projectedInput_eq; simulateQ_projectedInput` | equivalent |
| `Projection.lean` #4, L92 `input_sum` | T/Rounds.lean: `RoundsTest.bilinear_relation` | equivalent |
| `Projection.lean` #5, L99 `projected_eval` | T/Rounds.lean: `RoundsTest.projected_eval` | equivalent |
| `Projection.lean` #6, L105 `projected_sum` | T/Rounds.lean: `RoundsTest.projected_sum` | equivalent |
| `Projection.lean` #7, L119 `execute_closed` | C/Projection.lean: `Sumcheck.Core.projectedExecute_closed; projectedExecute_eq` | equivalent |
| `Projection.lean` #8, L139 `execute_related` | C/Projection.lean: `Sumcheck.Core.projectedExecute_related` | equivalent |

### ProjectionTransport

| Exact source | Exact target | Status |
|---|---|---|
| `ProjectionTransport.lean` #1, L19 `input_relation` | T/Rounds.lean: `RoundsTest.bilinear_relation` | equivalent |
| `ProjectionTransport.lean` #2, L36 example | C/Projection.lean: `Sumcheck.Core.simulateQ_projectedInput; projectedExecute_closed; projectedExecute_related` | equivalent |
| `ProjectionTransport.lean` #3, L44 example | T/Rounds.lean:370, next-round bilinear relation example | equivalent |

### Protocol

| Exact source | Exact target | Status |
|---|---|---|
| `Protocol.lean` #1, L78 `two_rounds` | T/Effects.lean: `EffectsTest.two_rounds` and recording client | premise-required (P2) |
| `Protocol.lean` #2, L93 example (record) | T/Effects.lean: `EffectsTest.two_rounds` and recording client | premise-required (P2) |
| `Protocol.lean` #3, L101 `abort_response` | T/Effects.lean: `EffectsTest.bad_first_rounds`, `EffectsTest.runWithLog_wrong` | premise-required (P1) |
| `Protocol.lean` #4, L107 example | T/Effects.lean: `EffectsTest.bad_first_rounds`, `EffectsTest.runWithLog_wrong` | premise-required (P1) |
| `Protocol.lean` #5, L113 example | T/Effects.lean: `EffectsTest.target_seven_not_final` | equivalent |
| `Protocol.lean` #6, L144 example | C/Soundness.lean: `indexedVerifier_run_soundness`; C/Indexed.lean: `indexedVerifier_soundness`; interaction-layer axiom checks | premise-required (P2) |
| `Protocol.lean` #7, L171 example | T/Interval.lean: `EffectsTest.public_append_record`, the public interval append on the effect fixture with result `(some 7, [0, 1, 2, 1, 3])`; C/FoldComposition.lean: `Sumcheck.Core.publicIntervalCompatibility; decideWith_append_publicInterval; run_append_public_intervalVerifier` | equivalent |
| `Protocol.lean` #8, L196 `#print axioms execute_soundness` | C/Soundness.lean: `indexedVerifier_run_soundness`; C/Indexed.lean: `indexedVerifier_soundness`; interaction-layer axiom checks | premise-required (P2) |
| `Protocol.lean` #9, L197 `#print axioms execute_support_completeness` | C/Completeness.lean: `perfectCompleteness`; T/Completeness.lean: axiom checks | premise-required (P2) |
| `Protocol.lean` #10, L198 `#print axioms execute_perfectCompleteness` | C/Completeness.lean: `perfectCompleteness`; T/Completeness.lean: axiom checks | premise-required (P2) |

### RoundByRound

| Exact source | Exact target | Status |
|---|---|---|
| `RoundByRound.lean` #1, L22 example | C/Indexed.lean: `indexedVerifier_rbrSoundness`; C/Soundness.lean: `indexedVerifier_run_soundness` | premise-required (P2) |

### Sequential

| Exact source | Exact target | Status |
|---|---|---|
| `Sequential.lean` #1, L24 `second_eval` | T/Rounds.lean: `RoundsTest.second_eval` | equivalent |
| `Sequential.lean` #2, L36 example | T/Rounds.lean: `RoundsTest.run_two_bilinear` and challenge-order client | premise-required (P2) |
| `Sequential.lean` #3, L59 `second_sum` | T/Rounds.lean: `RoundsTest.second_sum` | equivalent |
| `Sequential.lean` #4, L79 example | T/Rounds.lean: `RoundsTest.run_two_bilinear` and challenge-order client | premise-required (P2) |
| `Sequential.lean` #5, L92 example | T/Rounds.lean: `RoundsTest.run_two` with a wrong target; `verdict_foldTranscript` | premise-required (P1) |
| `Sequential.lean` #6, L108 `#print axioms executeTwo_complete` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_supportCompleteness; intervalVerifier_perfectCompleteness (count = 2)` | equivalent |

### SingleRound

| Exact source | Exact target | Status |
|---|---|---|
| `SingleRound.lean` #1, L23 example | T/SingleRound.lean: `SingleRoundTest.msgX_sum` | equivalent |
| `SingleRound.lean` #2, L27 example | T/SingleRound.lean:209; `SingleRoundTest.run_oneRound` | equivalent |
| `SingleRound.lean` #3, L34 example | T/SingleRound.lean:224; `SingleRoundTest.verdict_fail` | equivalent |
| `SingleRound.lean` #4, L52 example | T/SingleRound.lean:235, dishonest constant-message output | equivalent |
| `SingleRound.lean` #5, L58 `#print axioms executeAt_eq` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_list_eq`; T/Domain.lean: arbitrary-list and `[0, 0]` clients and axiom checks | equivalent |
| `SingleRound.lean` #6, L59 `#print axioms executeAt_honest` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest`; T/Domain.lean: arbitrary-list and `[0, 0]` clients and axiom checks | equivalent |

### Soundness

| Exact source | Exact target | Status |
|---|---|---|
| `Soundness.lean` #1, L29 example | T/SingleRound.lean:253, collision-zero example | equivalent |
| `Soundness.lean` #2, L35 example | T/SingleRound.lean:266, collision-one example | equivalent |
| `Soundness.lean` #3, L41 example | C/Soundness.lean: `indexedVerifier_committed_soundness`; T/Soundness.lean: interaction-layer arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #4, L49 example | T/SingleRound.lean:277, rejection at the collision challenge | equivalent |
| `Soundness.lean` #5, L66 `rejection_probability` | T/Soundness.lean: `SoundnessTest.rejection_probability` | equivalent |
| `Soundness.lean` #6, L77 `exact_repair_probability` | T/Soundness.lean: `SoundnessTest.exact_repair_probability` | equivalent |
| `Soundness.lean` #7, L93 `excludes_quadratic` | T/Soundness.lean: `SoundnessTest.excludes_quadratic` | equivalent |
| `Soundness.lean` #8, L112 `adaptive_endpoints` | T/Soundness.lean: `SoundnessTest.adaptive_endpoints` | equivalent |
| `Soundness.lean` #9, L119 `adaptive_hits` | T/Soundness.lean: `SoundnessTest.adaptive_hits` | equivalent |
| `Soundness.lean` #10, L123 `challenge_first_probability` | T/Soundness.lean: `SoundnessTest.challenge_first_probability` | equivalent |
| `Soundness.lean` #11, L143 `fresh_bound_lt_one` | T/Soundness.lean: `SoundnessTest.fresh_bound_lt_one` | equivalent |
| `Soundness.lean` #12, L148 `empty_domain_rejection` | T/Soundness.lean: `SoundnessTest.empty_domain_rejection` | equivalent |
| `Soundness.lean` #13, L155 `#print axioms zeroPolynomial` | T/Soundness.lean: `SingleRoundTest.poly0` axiom check | equivalent |
| `Soundness.lean` #14, L156 `#print axioms linearPolynomial` | T/Soundness.lean: `CompletenessTest.polyX`, `SoundnessTest.polyXK` axiom check | equivalent |
| `Soundness.lean` #15, L157 `#print axioms rejection_probability` | T/Soundness.lean: `SoundnessTest.rejection_probability` axiom check | equivalent |
| `Soundness.lean` #16, L158 `#print axioms exact_repair_probability` | T/Soundness.lean: `SoundnessTest.exact_repair_probability` axiom check | equivalent |
| `Soundness.lean` #17, L159 `#print axioms excludes_quadratic` | T/Soundness.lean: `SoundnessTest.excludes_quadratic` axiom check | equivalent |
| `Soundness.lean` #18, L160 `#print axioms adaptivePolynomial` | T/Soundness.lean: `SoundnessTest.adaptive` axiom check | equivalent |
| `Soundness.lean` #19, L161 `#print axioms adaptive_endpoints` | T/Soundness.lean: `SoundnessTest.adaptive_endpoints` axiom check | equivalent |
| `Soundness.lean` #20, L162 `#print axioms adaptive_hits` | T/Soundness.lean: `SoundnessTest.adaptive_hits` axiom check | equivalent |
| `Soundness.lean` #21, L163 `#print axioms challenge_first_probability` | T/Soundness.lean: `SoundnessTest.challenge_first_probability` axiom check | equivalent |
| `Soundness.lean` #22, L164 `#print axioms fresh_bound_lt_one` | T/Soundness.lean: `SoundnessTest.fresh_bound_lt_one` axiom check | equivalent |
| `Soundness.lean` #23, L165 `#print axioms empty_domain_rejection` | T/Soundness.lean: `SoundnessTest.empty_domain_rejection` axiom check | equivalent |
| `Soundness.lean` #24, L169 `#print axioms executeCommitted_eq` | T/SingleRound.lean: `SingleRoundTest.run_oneRound`; C/Indexed.lean: `indexedVerifier_run` | equivalent |
| `Soundness.lean` #25, L170 `#print axioms executeCommitted_soundness` | C/Soundness.lean: `indexedVerifier_committed_soundness`; T/Soundness.lean: interaction-layer arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #26, L171 `#print axioms executeRandomCommitment_soundness` | C/Soundness.lean: `indexedVerifier_randomized_soundness`; T/Soundness.lean: interaction-layer arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #27, L172 `#print axioms executeCommitted_measureSoundness` | C/Soundness.lean: `indexedVerifier_committed_measureSoundness`; interaction-layer axiom check | equivalent |
| `Soundness.lean` #28, L173 `#print axioms executeRandomCommitment_measureSoundness` | C/Soundness.lean: `indexedVerifier_randomized_measureSoundness`; interaction-layer axiom check | equivalent |

### SourceRouting

| Exact source | Exact target | Status |
|---|---|---|
| `SourceRouting.lean` #1, L34 private `eval_affine` | T/Effects.lean: `EffectsTest.eval_affine`, `EffectsTest.answer_affine`, `EffectsTest.route_affine` over semirings and `Nat` | equivalent |
| `SourceRouting.lean` #2, L37 private `answer_affine` | T/Effects.lean: `EffectsTest.eval_affine`, `EffectsTest.answer_affine`, `EffectsTest.route_affine` over semirings and `Nat` | equivalent |
| `SourceRouting.lean` #3, L48 example | C/Tree.lean: `protocol_succ`; removed `Option` challenge and abort-selected suffix | retired (`Option` challenge/abort shape) |
| `SourceRouting.lean` #4, L153 `accepted` | T/Routing.lean: `Sumcheck.Core.RoutingTest.accepted` | equivalent |
| `SourceRouting.lean` #5, L198 `abort` | T/Routing.lean: `Sumcheck.Core.RoutingTest.prefix_rejected` | premise-required (P1) |
| `SourceRouting.lean` #6, L241 `suffix_rejected` | T/Routing.lean: `Sumcheck.Core.RoutingTest.suffix_rejected` | equivalent |
| `SourceRouting.lean` #7, L285 `accepted_relation` | T/Routing.lean: `Sumcheck.Core.RoutingTest.accepted_relation` | equivalent |

### Generic soundness implication

These four source rows are in `ArkLibTest/Interaction/Oracle/Security/Soundness.lean`.
The exact parent dispositions, including freshness and failure scope, are in
[soundness-implication-disposition.md](soundness-implication-disposition.md).

| Exact source | Exact target in `ArkLib/Interaction/Core/Security/Implications.lean` | Status |
|---|---|---|
| #3, L57 `executeStrategies_soundness` | `OracleVerifier.soundness_of_rbrSoundness` | premise-required (P1/P2), row T3 of the parent disposition |
| #4, L58 `executeStrategies_soundness_uniform` | `OracleVerifier.soundness_of_rbrSoundness_uniform` | premise-required (P1/P2), row T4 of the parent disposition |
| #5, L60 `OrdinaryState.exists_verifier_escape` | `StateFunction.escapeAlong` | premise-required (P1/P2), row T5 of the parent disposition |
| #6, L61 `LocalSoundness.random_prefix` | `flip_random_prefix_le` | equivalent |

## Remaining work

The `degreeModel` and `degreeGuarantee` rows are retired. Their only client is `message_degree`,
which `Sumcheck.Core.message_degree` proves directly from the degree bound that the message type
`R⦃≤ deg⦄[X]` carries. Core has no counterpart of the generic `OracleModel.satisfies_guarantee`
interface and needs none: #1476 removes the property-symbol languages and keeps degree facts as
carrier guarantees (its rows R23 and R24).
`Interpreted` supplies an interaction-layer passive verifier for arbitrary evaluated message
carriers; `InterpretedExecution` preserves message moves, challenge-response moves and leaf
outputs under interpretation. This generic interface does not make Mathlib polynomial projections
computable. Executable coefficient representations remain in `Sumcheck.Impl`. The interaction-layer
security proofs do not use a legacy fold-to-sequential bridge.

### B and the kept legacy regressions

| Rows | Disposition |
|---|---|
| Virtual V1 (legacy output simulation as an oracle map) | Already covered on this base: `OracleMap.ofLegacySimulation` and `Legacy.simulateQ_ofLegacySimulation_impl`, instantiated at `ToyProblem.SimplifiedIOR.outputSimulation` in `ArkLibTest/Interaction/Core/Legacy/OracleReduction.lean`. No duplicate lemma or fixture is added. |
| LegacyVerifier #1, #2 | Keep the legacy tests `input_relation_false`, `message_sum_passes`. |
| LegacyVerifier #3, #4 (bridge versions through `decide_ambient_trace`) | `LegacyVerifierTest.answered_pair` and `sent_target` check both core and embedded decisions; the next target is the message's evaluation one. |
| LegacyVerifier #5 (bridge version) | `LegacyVerifierTest.run_false_relation` checks the false output relation on each run's returned verdict, retaining input zero. |
| LegacyVerifier #6, #7 (bridge versions) | `LegacyVerifierTest.inconsistent_sum_rejected`, `honest_zero_accepted`, on both verifiers at every challenge. |
| LegacyVerifier #8, #9 (bridge versions) | `LegacyVerifierTest.linearMessage` and `linear_sent_target`: both decisions return `r + 1` for message `X + 1` at every `r : ZMod 5`. |
| LegacyVerifier #10, #11 (bridge versions) | The axiom guard in `Core/LegacyVerifier.lean` checks `linear_sent_target` and `run_false_relation`, together with all four other bridge facts. |
| LegacyVerifier #12, #13 | Keep the legacy RBR knowledge guards. Core transfers remain guarded in `Core/RoundByRound.lean`. |

The original kept `ArkLibTest/ProofSystem/Sumcheck/LegacyVerifier.lean` is outside D7's editable
paths. The deletion of the frozen Sumcheck layer retargeted it from the frozen `legacyTranscript`
to `Sumcheck.Core.simpleLegacyTranscript`, which has the same definition. None of the new Core
tests imports it.

### Supporting declarations added by D7

All names in this table are in `Sumcheck.Core` unless qualified otherwise. They support the rows
above rather than adding independent security claims.

| Module | Declarations and purpose |
|---|---|
| `Spec/PolynomialInterface` | `Spec.polynomialFamily`. The deletion of the frozen Sumcheck layer removed the plain alias `Interaction.MultivariateRound.polynomialFamily`. Core and `Impl/Projection` clients use the neutral name. |
| `LegacyProjection` | `messageFamily`, `projectionMap`, `projectionMap_f`, `simulateQ_projectionMap`: the univariate output interface and lawful projection. |
| `Interaction/Core/OracleVerifier` | `Interaction.Core.pathLift`, `Interaction.Core.simulateQ_pathLift`: the path-query lift of any decision, for any input family and protocol, and its interpretation law in any lawful monad. `decisionLift`, `foldLift` and their laws `simulateQ_decisionLift`, `simulateQ_decisionLift_monad`, `simulateQ_foldLift` are instances. `OracleVerifier.run_eq_decideWith` expresses a run through `decideWith` for any input bundle, at the protocol query universe of `OracleVerifier.run_eq`, using the shared owner lemma `OracleVerifier.simulateQ_decideWith` in reverse. |
| `Interaction/Core/Composition` | `Interaction.Core.TranscriptAt.split_val`: the split of a transcript at a path carries the transcripts of `Transcript.split`. |
| `Composition`, input route | `inputRoute`: the existing `OracleMap.embedding` for the input oracles. |
| `Composition`, round | `checkRoute`, `roundChallenges`, `checkVerifier`, `roundChallenges_eq`, `decideWith_checkVerifier`, `checkVerdict`, `run_checkVerifier`: reuse the legacy per-round check, with no ambient queries in that check. |
| `Composition`, append | `split_toView_round`, `appendHead`, `appendTail`, `prefixRoute_round`, `suffixRoute_round`, `decideWith_append_checkVerifier`, `run_append_checkVerifier`: specialize the Core append routing to one Sumcheck round. The generic routing of part D, commit 1 is not duplicated. |
| `Composition`, fold | `foldLift`, `legacyFoldVerifier`, `verifier_eq_legacyFoldVerifier`, `simulateQ_foldLift`, `decideWith_legacyFoldVerifier`, `foldHead`, `legacyFoldCompatibility`, `decideWith_append_legacyFoldVerifier`, `run_append_legacyFoldVerifier`, `run_append_verifier`: reuse `Spec.oracleVerifierProgram` and C's `simulateQ_oracleVerifierProgram_succ`, allowing a suffix that starts from a round-1 statement. |
| `Composition`, projection | `simulate_roundProver`, `projectedVerifier`, `run_projectedVerifier_roundProver`, `projectedVerifier_relation`: run the standalone projected round with the injective-domain compatibility map `projectionMap`, and reuse `projected_sum_of_relationRound` and `relationRound_projected_output` for its mathematical relation. `projectedVerifier_relation` assumes a true starting claim and the honest projected polynomial in the transcript. The indexed-domain construction is `projectedMap` in `Projection`. |

## Departures

These are the two departures of entry 22 in [`departures.md`](departures.md).

### The transferred completeness is in its own module

**Plan.** The implementation plan puts completeness in `Completeness`.

**Code.** `Completeness` keeps the direct proof for the compatibility honest prover.
`LegacyCompleteness` holds `legacyProver_perfectCompleteness`, the transfer of
`Spec.oracleReduction_perfectCompleteness`.

**Why.** `LegacyEquivalence` imports `Completeness`, so a transfer that needs
`LegacyEquivalence` cannot live there. The direct theorem accepts every challenge implementation;
the transferred theorem uses the embedded legacy honest prover, uniform challenges and an
output witness. Both statements remain available.

### Full-run and interval verifier interfaces

**Migration.** Several frozen assertions execute one round inside a multivariate statement or
split an interval into a first round and a suffix.

**Code.** `indexedVerifier` keeps its full-run interface. The interval verifier
accepts every bounded pair `start`, `count`; its suffix security theorem assumes exactly
`start + count = n`. `intervalVerifier_full_run` identifies the full interaction-layer run with the
zero-start interval. `run_append_public_intervalVerifier` compares actual public interval
interfaces, and `projectedExecute_closed` retains the derived projected input behavior.

**Premises.** P1 moves bundle queries into the final decision. P2 removes public abort shape
selection. Both apply to the changed abort execution rows; neither narrows the endpoint range,
message representation or original-oracle behavior quantified by the corresponding targets.

## Agreement universes and parent limits

`Interaction.Core.OracleVerifier.Agrees` and every law in `Security/Agreement.lean` accept
path-dependent output statements `T p`, oracle indices `J p`, carriers `B p j` and interfaces
`outputs p`. Outcomes and output problems use `OracleVerifier.Output T B`. The decision and
output-map cast laws retain the verifier owner's independent ambient and output-index universes;
ordinary runs retain its move/response universe `u`. `cast_const` identifies the general
transport with ordinary equality substitution for constant output families. Ordinary substitution
keeps those output carriers fixed while changing the tree. Classical probability interfaces specialize
the move and returned-value universe to zero, as their owners require.

Agreement accepts general `OracleBundle.{u, uI, dI}` inputs, with independent query and data
universes. Family-shaped inputs specialize this API through `OracleBundle.ofFamily`.
Round-by-round knowledge agreement and transport retain `Win stmt`, `W stmt tr`, and relations
`relOut stmt tr output witness`, with independent witness universes. They also preserve the
parent's challenge draws, which read the verifier's view of each prefix (`PrefixDraw viewSig`),
and its full-prefix local errors. Sumcheck's compatibility theorem uses
`rbrKnowledgeSoundnessOfNodes`, the parent specialization that ignores prefix history, and
rewrites it to the view form with `rbrKnowledgeSoundnessOfNodes_iff`.

| Reviewed contract | Status | Evidence |
|---|---|---|
| F7: path-dependent outputs throughout Agreement | equivalent | `Agrees`, all agreement consequences and every `*_cast` law reindex the statement and oracle families together. No constant-output replacement remains. |
| 3A: statement-dependent knowledge witnesses and relations | equivalent | `Agrees.rbrKnowledgeSoundness_iff` and `rbrKnowledgeSoundness_cast` use the unchanged owner's argument shapes. Sumcheck passes `fun _ _ t w => (t, w) ∈ Spec.relationRound R n deg D (Fin.last n)`. |

`ArkLibTest/Interaction/Core/AgreementUniverses.lean` imports the public API with statement,
input-index, input-query, output-query and oracle-node-query universes 2, 1, 3, 4 and 5. Its
knowledge client uses statement-dependent input witnesses in `Type 6` and
statement-and-transcript-dependent output witnesses in `Type 7`. Output families depend on the
shape path. Further clients exercise general move, ambient-index and output-index universes.

The remaining restrictions come from these parent interfaces:

| New API | Parent interface | Required restriction |
|---|---|---|
| `OracleVerifier.runWithLog_eq_of_decide_eq` | `OracleVerifier.runWithLog` in `Security/Knowledge.lean` | Bundle-query indices and oracle-node queries are small because the full log is a small run output. Input data and output queries remain independent. |
| `Agrees.run_eq` and `run_cast` | `OracleVerifier.run` in `Core/OracleVerifier.lean` | Ambient and output indices share the move/response universe `u`. Output statements and oracle data are values in `Type u`; node and output queries remain independent. |
| Extraction and classical security laws | `classicalModel`, `extractionGame`, `classicalStraightLine`, `validAcceptance` and the RBR wrappers | Probability computations return small values, including output statements, output indices and extracted witnesses. Input data and queries remain independent. Pure RBR witness carriers retain the owner's independent universes. |
| Legacy tree relation adapter `treeRelationProblem` | `Legacy.relProblem` in `Core/Legacy/Security.lean` | The parent convenience adapter fixes claims to `Type 0`; the tree adapter accepts larger claims. The underlying `Problem` and classical security interfaces already accept larger claims. |

## Production declaration inventory

This inventory covers all 19 production modules in
`ArkLib/ProofSystem/Sumcheck/Interaction/`, including private source declarations and explicit
structure fields. The named sources below are fully qualified. The one anonymous local instance
has no user-facing declaration name; its row identifies its namespace and exact source location.
Compiler-generated recursors, constructors and equation lemmas are not separate source declarations.
`C/` retains the Core source prefix defined above. Each target below names its implemented
interval contract. Each row retains the source
`start`/`count` scope, including arbitrary prefixes and the full endpoint `start + count = n`.
For generic and computable carriers, the execution interpretation preserves endpoints and, for a
fixed output type `Out`, ambient effects, the challenge draws and the private value. Restricting
those rows to this branch’s mathematical polynomial
carrier would not close them.

The one-round execution targets below use arbitrary maps or `domain.get`, without a sampling
assumption. `univariateData` embeds the original univariate input into the interaction layer
one-variable polynomial data and `univariateData_eval` identifies every evaluation. The
execution equations retain that original data independently of the sent message. The
interaction layer total-mass equation and explicit rejection are separate contracts. `ProbComp`
is lossless in the pinned VCVio model; neither the old nor the new total-mass equation asserts a
positive probability of failure.

### Production: ArbitraryCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_support_completeness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:35` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_supportCompleteness` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:87` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_perfectCompleteness` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_measureCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:102` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_measureCompleteness` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_uniform_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:118` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_perfectCompleteness` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_uniform_measureCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:131` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_measureCompleteness` | equivalent |

### Production: ArbitraryRounds

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.roundInterfaces`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:33` | C/Interval.lean: `Sumcheck.Core.IntervalClaim; intervalInitial` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.roundStages`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:44` | C/FoldComposition.lean: `Sumcheck.Core.run_append_public_intervalVerifier; decideWith_append_publicInterval` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.roundStages_run`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:60` | C/FoldComposition.lean: `Sumcheck.Core.run_append_public_intervalVerifier; decideWith_append_publicInterval` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:83` | C/FoldComposition.lean: `Sumcheck.Core.run_append_public_intervalVerifier; decideWith_append_publicInterval` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:95` | C/FoldComposition.lean: `Sumcheck.Core.run_append_public_intervalVerifier; decideWith_append_publicInterval` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_zero`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:108` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_zero` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_one`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:118` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_two`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:134` | C/FoldComposition.lean: `Sumcheck.Core.run_append_public_intervalVerifier; decideWith_append_publicInterval` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_two`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:158` | C/FoldComposition.lean: `Sumcheck.Core.run_append_public_intervalVerifier; decideWith_append_publicInterval` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.honestMessages`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:178` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalMessage` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.roundStages_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:184` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerdict_honest; intervalVerifier_honest_run` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:205` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerdict_honest; intervalVerifier_honest_run` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_evaluation`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:262` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_evaluation` | equivalent |

### Production: Closing

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.outputFamily`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:27` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` (`outputMap := OracleMap.fst`; retained original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.outputOracle`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:31` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` (`outputMap := OracleMap.fst`; retained original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.outputClaim`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:35` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` (`outputMap := OracleMap.fst`; retained original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.degreeModel`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:40` | None; `message_degree` reads the bound from the message type | retired: the guarantee interface is removed, and its only client is ported as `Sumcheck.Core.message_degree` |
| `Sumcheck.Interaction.SingleRound.degreeGuarantee`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:53` | None; `message_degree` reads the bound from the message type | retired: the guarantee interface is removed, and its only client is ported as `Sumcheck.Core.message_degree` |
| `Sumcheck.Interaction.SingleRound.message_degree`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:56` | C/Indexed.lean: `Sumcheck.Core.message_degree` | equivalent |
| `Sumcheck.Interaction.SingleRound.claimVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:62` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.claimReduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:76` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.honestRun`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:86` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult` (`data := fun _ => univariateData p`, `msg := p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:95` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest` (including unchanged original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.honestClaim`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:117` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult` (`data := fun _ => univariateData p`, `msg := p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.honestRun_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:121` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult`; C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:126` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest` (including unchanged original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.closedOutputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:136` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (`point := r`, arbitrary evaluation behavior) | equivalent |
| `Sumcheck.Interaction.SingleRound.closedInputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:140` | C/Domain.lean: `Sumcheck.Core.behaviorInputRelation` (arbitrary evaluation behavior) | equivalent |
| `Sumcheck.Interaction.SingleRound.honestRun_closed_related`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:145` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult_univariate_honest` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_complete`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:151` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_complete` (monad `OracleComp ambient`, challenge `pure r`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_degree_complete`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:161` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_degree_complete` (monad `OracleComp ambient`, challenge `pure r`) | equivalent |
| `Sumcheck.Interaction.SingleRound.sampledClaimVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:171` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.sampledClaimReduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:187` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.simulate_challenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:197` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_eq` (arbitrary lawful monad and challenge computation) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:207` | C/Indexed.lean: `Sumcheck.Core.indexedExecute` (`data := fun _ => univariateData p`, `msg := p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:214` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_honest_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled_support`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:243` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_support` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:258` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_perfectCompleteness` | equivalent |
| `Sumcheck.Interaction.SingleRound.prEvent_eq_evalDist_map_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:268` | `prEvent_eq_evalDist_map` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.SingleRound.executeSampled_measureCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:273` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_measureCompleteness` | equivalent |

### Production: Composition

| Exact source | Exact target | Status |
|---|---|---|
| `Interaction.Oracle.executeStrategiesCore_closed_eq_run` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:27` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.midpointStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:58` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.firstRoundFragment`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:65` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.remainingVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:91` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.composedVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:107` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.firstRound_closingImpl`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:123` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.firstRound_closingImpl_literal` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:131` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.onAppendedRuntime_native` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:142` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.splitPrefix_native` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:151` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.exportedPrefixRun_firstRound`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:179` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_appendExported_succ`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:232` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_eq_appendExported`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:337` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.exportedSuffixRun_some`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:369` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.exportedSuffixRun_none`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:398` | C/BehaviorComposition.lean: `Sumcheck.Core.behaviorPublicIntervalCompatibility`, `Sumcheck.Core.decideWith_append_behaviorPublicInterval`, `Sumcheck.Core.run_append_behaviorIntervalVerifier` | premise-required (P1, P2) |

### CompPoly runtime assertions

The source is `scripts/SumcheckRuntime.lean` at the frozen pre-migration runtime. Targets are
in the current script and `ArkLibTest/ProofSystem/Sumcheck/Core/Computable.lean`.

| Exact source | Exact target | Status |
|---|---|---|
| L92, Horner evaluation check | `SumcheckRuntime.runChecks`, Horner check | equivalent |
| L95, private-memory two-round check | `SumcheckRuntime.adaptiveObserve zeroDomain`, event/draw order `[p0,c0,p2,c1,p3]` | premise-required (P1, P2) |
| L97, public-abort check | `SumcheckRuntime.adaptiveObserve emptyDomain`, rejection after every round has run | premise-required (P1, P2) |
| L176, direct quadratic and cross term | `SumcheckRuntime.quadraticChecks`, independent evaluation check | equivalent |
| L182, honest quadratic run | `SumcheckRuntime.quadraticObserve`, explicit challenge-node log `[c0,c1]` | premise-required (P1, P2) |
| L184, zero-round verifier check from round 2 | `SumcheckRuntime.quadraticZeroObserve`; `Sumcheck.Core.ComputableTest.zero_interval_verdict`: `some (16, 4, 4, 16)` and empty trace | equivalent |

`quadraticZeroProverObserve` and `Sumcheck.Core.ComputableTest.zero_prover_output` are additional
checks of the prover output; they do not replace the verifier assertion.

### Computational-input verifier bridge

`Computable.intervalVerifier` retains the CompPoly input itself. Its
`interval_run_eq_interpret` is the exact oracle-program bridge to the parent's mathematical
`intervalVerifier`, including dependent private outputs. `interval_support_completeness`,
`interval_perfectCompleteness` and `interval_measureCompleteness` accept every interval with
`start + count ≤ n`, under one stateful handler for the ambient and challenge queries.
`interval_soundness` has the suffix endpoint `start + count = n` and error
`count * (deg / |R|)`: with fresh uniform challenges, it bounds the probability of an accepted
output that satisfies the endpoint relation. The bound is the per-round agreement bound with the
final evaluation check of Thaler, *Proofs, Arguments, and Zero-Knowledge*, Proposition 4.1, for
the protocol of Lund, Fortnow, Karloff and Nisan (1992).

`interval_run_eq_interpret` transports the prover's dependent output through a map `g` that the
caller chooses. A caller keeps the original transcript and its private output by mapping them to a
sigma pair, as `interval_soundness` does. `full_run_interval` and
`verifier_run_eq_indexedVerifier` keep the transcript and private output directly and convert the
verdict's statement. All of these equalities compare runs after the verifier's bundle queries are
answered. A statement about the raw decision queries, their order or their charges needs its own
law. The LogUp port of #1341 and resource bounds based on routing need such a law. List and injective
corollaries preserve the parent's domain specializations. The proofs reuse the parent's
interval invariants and security bounds. The parent’s more general original-data executor
contracts remain the targets of the frozen production rows below; these computational-input
specializations do not replace them.

### Full-run compatibility corollaries

The full-run theorem statements retain their original binders, verdict guarantees and error terms.
`DomainEquivalence.legacyVerdict_map_ofSpec` proves equality on every completed transcript;
`verifier_run_full_interval` lifts this to equality of actual oracle computations at endpoints
`0, n`, retaining every dependent private output and original oracle data. `honestFold_eq_intervalFold`,
`RoundStatement.ofSpec_finishState` and `honest_full_interval` identify the honest leaf state and preserve
the equality with the prover output required by `judgement.honest`.

The CompPoly bridge `Computable.full_run_interval` retains the computational input itself.
Completeness uses interaction-layer interval honesty through `honest_full_interval`; soundness
applies `Computable.interval_soundness` at `0, n` and converts its product error to the unchanged
sum. These proofs do not call the compatibility security theorems.

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Core.Computable.support_completeness`, C/Computable.lean, original full-run statement | C/DomainEquivalence.lean: `Sumcheck.Core.honest_full_interval`, `honestFold_eq_intervalFold`, `RoundStatement.ofSpec_finishState`; C/IntervalCompleteness.lean: `intervalVerdict_honest` at endpoints `0, n` | equivalent |
| `Sumcheck.Core.Computable.perfectCompleteness`, C/Computable.lean, original full-run statement | C/Computable.lean: `Sumcheck.Core.Computable.support_completeness`, using `Sumcheck.Core.honest_full_interval` from C/DomainEquivalence.lean at endpoints `0, n` | equivalent |
| `Sumcheck.Core.Computable.soundness`, C/Computable.lean, original full-run statement and sum error | C/Computable.lean: `Sumcheck.Core.Computable.full_run_interval`, `interval_soundness` at endpoints `0, n`; C/DomainEquivalence.lean: `Sumcheck.Core.legacyVerdict_map_ofSpec` | equivalent |

### Production: Computable

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Computable.FinalStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:29` | C/Types.lean: `Sumcheck.Core.RoundStatement` at `Fin.last n` | equivalent |
| `Sumcheck.Interaction.Computable.outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:31` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (arbitrary original evaluation behavior) | equivalent |
| `Sumcheck.Interaction.Computable.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:34` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.transportProver; Interpreted.execute_transport; Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:39` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.transportProver; Interpreted.execute_transport; Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.execute`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:42` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.transportProver; Interpreted.execute_transport; Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.interpretProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:48` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.transportProver; Interpreted.execute_transport; Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.execute_eq_native`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:54` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.transportProver; Interpreted.execute_transport; Interpreted.execute_eq_verifier` | premise-required (P1, P2) |

### Production: ComputableCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Computable.honestProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:37` | C/ComputableInterval.lean: `Sumcheck.Core.Computable.intervalHonestProver` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.interpretProver_honestProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:51` | C/ComputableInterval.lean: `Sumcheck.Core.Computable.interpret_intervalHonestProver` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.execute_honestProver_eq_native`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:81` | C/ComputableInterval.lean: `Sumcheck.Core.Computable.execute_honest_eq_noncomputable` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.execute_support_completeness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:95` | C/ComputableInterval.lean: `Sumcheck.Core.Computable.execute_supportCompleteness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Computable.execute_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:116` | C/ComputableInterval.lean: `Sumcheck.Core.Computable.execute_perfectCompleteness` | premise-required (P1, P2) |

### Production: ComputableSoundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Computable.execute_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean:31` | C/ComputableSoundness.lean: `Sumcheck.Core.Computable.executeExperiment_eq_intervalVerifier`, `Sumcheck.Core.Computable.execute_soundness` | premise-required (P1, P2) |

### Production: Legacy

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.<anonymous-instance>`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:31` | `Interaction.Core.Legacy.oracleChallengeImpl` | retired (local legacy challenge-interface override) |
| `Sumcheck.Interaction.SingleRound.legacy_output_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:35` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_input_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:43` | C/Domain.lean: `Sumcheck.Core.sum_domain_embedding`; C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacyTranscript`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:53` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyTranscript` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacyTranscript_message`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:58` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyTranscript_message` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacyTranscript_challenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:62` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyTranscript_challenge` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_prover_run`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:66` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyProver_run` (separate Simple-protocol compatibility check) | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_verifier_correspondence`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:109` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyVerifier_correspondence` (separate Simple-protocol compatibility check) | equivalent |

### Production: MultivariateRound

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.access`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:32` | C/Fold.lean: `Sumcheck.Core.foldDecision`; C/Interpreted.lean: `Sumcheck.Core.Interpreted.simulate_decision` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.outputOracle`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:36` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:44` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:53` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:66` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.reduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:75` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.acceptedRun`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:85` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.simulate_sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:96` | C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.simulate_terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:116` | C/Fold.lean: `Sumcheck.Core.foldDecision`; C/Interpreted.lean: `Sumcheck.Core.Interpreted.simulate_decision` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeCore_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:132` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_accepted`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:158` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.acceptedRun_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:167` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:174` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.sampledVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:185` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.sampledReduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:197` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.simulate_challenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:208` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:220` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one`; C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalVerdict_one`; C/Interval.lean: `Sumcheck.Core.roundVerdict_intervalCheck` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.closedRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:248` | C/Behavior.lean: `Sumcheck.Core.behaviorRoundRelation` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.honestNext`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:255` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalNext; interval_honest_step; intervalVerifier_honest_run` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeCore_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:262` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalNext; interval_honest_step; intervalVerifier_honest_run` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.honestNext_related`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:276` | C/IntervalCompleteness.lean: `Sumcheck.Core.interval_honest_step` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.closedRelation_last_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:285` | C/Behavior.lean: `Sumcheck.Core.behaviorRoundRelation_last` | equivalent |

### Production: MultivariateSoundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_closed_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:36` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_one` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.acceptedRun_closedRelation_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:54` | C/IntervalRoundSoundness.lean: `Sumcheck.Core.interval_successor_iff` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.projected_sum_iff_closedRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:65` | C/Domain.lean: `Sumcheck.Core.sum_projectedRoundPolynomial`; C/DomainEquivalence.lean: `Sumcheck.Core.indexedRelation_embedding` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:77` | C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalRoundExecute_soundness` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.prEvent_eq_evalDist_map_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:104` | `prEvent_eq_evalDist_map` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_measureSoundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:109` | C/IntervalRoundSoundness.lean: `Sumcheck.Core.intervalRoundExecute_measureSoundness` | equivalent |

### Production: Projection

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.projectionOracle`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:25` | C/Projection.lean: `Sumcheck.Core.projectedQuery; simulateQ_projectedQuery` | equivalent |
| `Sumcheck.Interaction.SingleRound.projectionOracle_eval`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:30` | C/Projection.lean: `Sumcheck.Core.projectedQuery; simulateQ_projectedQuery` | equivalent |
| `Sumcheck.Interaction.SingleRound.projectedInput`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:38` | C/Projection.lean: `Sumcheck.Core.projectedInput; projectedInput_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.projectedInput_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:44` | C/Projection.lean: `Sumcheck.Core.projectedInput; projectedInput_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_projected_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:52` | C/Projection.lean: `Sumcheck.Core.projectedExecute_closed; projectedExecute_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_projected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:67` | C/Projection.lean: `Sumcheck.Core.projectedExecute_closed; projectedExecute_eq` | equivalent |

### Production: ProjectionTransport

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.executeCore_projected_of_relationRound`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProjectionTransport.lean:27` | C/Projection.lean: `Sumcheck.Core.simulateQ_projectedInput; projectedExecute_closed; projectedExecute_related` | equivalent |

### Production: Protocol

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Native.Core.messageInterface`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:35` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.messageInterface` | equivalent |
| `Sumcheck.Interaction.Native.Core.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:41` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.Core.firstRoundProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:50` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.Core.remainingProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:54` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.Core.protocol_succ_eq_append`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:61` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.Core.FinalStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:74` | C/Types.lean: `Sumcheck.Core.RoundStatement` at `Fin.last n` | equivalent |
| `Sumcheck.Interaction.Native.Core.latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:79` | C/InterpretedPath.lean: `Sumcheck.Core.Interpreted.headQuery; Interpreted.simulate_head` | equivalent |
| `Sumcheck.Interaction.Native.Core.latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:86` | C/Interpreted.lean: `Sumcheck.Core.Interpreted.roundVerdict; Interpreted.simulate_decision` | equivalent |
| `Sumcheck.Interaction.Native.Core.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:98` | C/Interpreted.lean: `Sumcheck.Core.Interpreted.verifier; Interpreted.simulate_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.Core.execute`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:123` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute; Interpreted.execute_eq_verifier; Interpreted.execute_input_eq` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.Core.outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:137` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (arbitrary original evaluation behavior) | equivalent |
| `Sumcheck.Interaction.Native.Core.simulate_latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:142` | C/InterpretedPath.lean: `Sumcheck.Core.Interpreted.headQuery; Interpreted.simulate_head` | equivalent |
| `Sumcheck.Interaction.Native.Core.simulate_latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:152` | C/Interpreted.lean: `Sumcheck.Core.Interpreted.roundVerdict; Interpreted.simulate_decision` | equivalent |
| `Sumcheck.Interaction.Native.Core.execute_zero`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:165` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_zero; behaviorRoundRelation_last` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.Core.execute_succ`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:181` | C/Protocol.lean: `Sumcheck.Core.run_succ`; C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.Core.execute_eq_of_originalOracle_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:235` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute; Interpreted.execute_eq_verifier; Interpreted.execute_input_eq` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.Core.transportProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:271` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.transportProver; Interpreted.run_transport` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.Core.execute_transport`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:290` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute_transport; Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:333` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.firstRoundProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:335` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.remainingProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:337` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.FinalStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:339` | C/Types.lean: `Sumcheck.Core.RoundStatement` at `Fin.last n` | equivalent |
| `Sumcheck.Interaction.Native.latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:344` | C/InterpretedPath.lean: `Sumcheck.Core.Interpreted.headQuery; Interpreted.simulate_head` | equivalent |
| `Sumcheck.Interaction.Native.latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:346` | C/Interpreted.lean: `Sumcheck.Core.Interpreted.roundVerdict; Interpreted.simulate_decision` | equivalent |
| `Sumcheck.Interaction.Native.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:348` | C/Interpreted.lean: `Sumcheck.Core.Interpreted.verifier; Interpreted.simulate_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:351` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute; Interpreted.execute_eq_verifier; Interpreted.execute_input_eq` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:354` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (arbitrary original evaluation behavior) | equivalent |
| `Sumcheck.Interaction.Native.protocol_succ_eq_append`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:358` | C/MessageTree.lean: `Sumcheck.Core.Interpreted.protocol; Interpreted.protocol_succ_eq_append` | premise-required (P2) |
| `Sumcheck.Interaction.Native.simulate_latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:369` | C/InterpretedPath.lean: `Sumcheck.Core.Interpreted.headQuery; Interpreted.simulate_head` | equivalent |
| `Sumcheck.Interaction.Native.simulate_latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:378` | C/Interpreted.lean: `Sumcheck.Core.Interpreted.roundVerdict; Interpreted.simulate_decision` | equivalent |
| `Sumcheck.Interaction.Native.execute_zero`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:387` | C/Behavior.lean: `Sumcheck.Core.behaviorIntervalVerifier_run_zero; behaviorRoundRelation_last` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_succ`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:401` | C/Protocol.lean: `Sumcheck.Core.run_succ`; C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute_eq_verifier` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_eq_of_originalOracle_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:427` | C/InterpretedExecution.lean: `Sumcheck.Core.Interpreted.execute; Interpreted.execute_eq_verifier; Interpreted.execute_input_eq` | premise-required (P1, P2) |

### Production: ProtocolCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Native.honestProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:36` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalProver; intervalVerifier_supportCompleteness; intervalVerifier_perfectCompleteness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_support_completeness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:52` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalProver; intervalVerifier_supportCompleteness; intervalVerifier_perfectCompleteness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:110` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalProver; intervalVerifier_supportCompleteness; intervalVerifier_perfectCompleteness` | premise-required (P1, P2) |

### Production: ProtocolSoundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.uniform_successor_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:40` | C/Indexed.lean: `Sumcheck.Core.indexed_round_soundness` | equivalent |
| `Sumcheck.Interaction.Native.midpointRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:71` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; interval_validAcceptance; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.midpointOracleRealized`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:81` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; interval_validAcceptance; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.exportedPrefixRun_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:89` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; interval_validAcceptance; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.exportedPrefixRun_admissibility`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:145` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; interval_validAcceptance; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.execute_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:201` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; interval_validAcceptance; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |

### Production: RoundByRound

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Native.CurrentClaim` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:38` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.PendingMessage` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:41` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.PrefixData` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:44` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.PrefixData.claim` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:45` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.PrefixData.pending` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:46` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.PrefixData.rank` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:47` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.PrefixData.step` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:48` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.TranscriptObserver` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:50` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.rootData` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:57` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.restrictObserver` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:62` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:71` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_root` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:75` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_public` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:78` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_oracle` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:85` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.restrictObserver_comp` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:92` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_comp` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:109` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:117` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.observer_root_rank` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:132` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.observer_root_claim` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:137` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.nextChallenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:146` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.samplePending` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:151` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.modelOf` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:157` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.stateOf` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:164` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.rankOf` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:172` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.nextChallenge_local_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:176` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |
| `Sumcheck.Interaction.Native.transcriptObserver_prover` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:198` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver_schedule` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:224` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.rootBound` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:257` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.LocalCertificate` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:264` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.localCertificate_restrict` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:273` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.localCertificate_root` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:289` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.localCertificate_bound` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:299` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver_local` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:319` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.fresh_prependPublic` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:360` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.fresh_prependOracle` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:392` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver_fresh` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:425` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.executeStrategies_succ` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:495` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.closeExecution` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:549` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.executeStrategies_terminal` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:559` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.execute_eq_closeExecution` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:635` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.roundByRound_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:659` | C/IntervalSoundness.lean: `Sumcheck.Core.intervalStateFunction; intervalVerifier_rbrSoundness; intervalVerifier_soundness` | premise-required (P1, P2) |

### Production: Sequential

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.executeTwo`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:31` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_accepted`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:47` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_rejected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:67` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_second_rejected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:78` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwoSampled`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:96` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwoSampled_accepted`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:114` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwoSampled_rejected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:144` | C/FoldComposition.lean: `Sumcheck.Core.decideWith_append_publicInterval; run_append_public_intervalVerifier (count = 1)` | premise-required (P1) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:161` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_honest_run (count = 2)` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_complete`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:181` | C/IntervalCompleteness.lean: `Sumcheck.Core.intervalVerifier_supportCompleteness; intervalVerifier_perfectCompleteness (count = 2)` | equivalent |

### Production: SingleRound

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.Message`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:32` | `Polynomial.degreeLE` (the same message subtype) | equivalent |
| `Sumcheck.Interaction.SingleRound.polynomialInterface`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:36` | `inferInstance : OracleInterface R⦃≤ deg⦄[X]`, used by C/SingleRound.lean: `Sumcheck.Core.round` | equivalent |
| `Sumcheck.Interaction.SingleRound.inputSpec`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:42` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval`; C/Types.lean: `Sumcheck.Core.polynomialFamily` | equivalent |
| `Sumcheck.Interaction.SingleRound.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:45` | C/SingleRound.lean: `Sumcheck.Core.round` | premise-required (P2) |
| `Sumcheck.Interaction.SingleRound.access`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:50` | `Interaction.Core.pathBundle` (input family and sent oracle messages) | equivalent |
| `Sumcheck.Interaction.SingleRound.sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:56` | C/Indexed.lean: `Sumcheck.Core.indexedDecision` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:65` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:75` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.prover`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:88` | C/Indexed.lean: `Sumcheck.Core.committedProver` | equivalent |
| `Sumcheck.Interaction.SingleRound.inputImpl`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:93` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval`; C/Types.lean: `Sumcheck.Core.polynomialFamily` | equivalent |
| `Sumcheck.Interaction.SingleRound.simulate_sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:96` | C/Indexed.lean: `Sumcheck.Core.simulateQ_indexedSumQueries_monad` (no `DecidableEq` or sampler) | equivalent |
| `Sumcheck.Interaction.SingleRound.simulate_terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:114` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult`; C/Indexed.lean: `Sumcheck.Core.indexedVerifier_run_one` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeAt`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:128` | C/Indexed.lean: `Sumcheck.Core.indexedExecute` (challenge `pure r`; data `univariateData p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeAt_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:134` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_list_eq` (arbitrary original input, arbitrary sent message) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeAt_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:149` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest` | equivalent |
| `Sumcheck.Interaction.SingleRound.honest_outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:157` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_input_sum`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:162` | C/Domain.lean: `Sumcheck.Core.sum_domain_embedding`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |

### Production: Soundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.committedRun`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:35` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult` (`data := fun _ => univariateData p`, `msg := q`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:45` | C/Indexed.lean: `Sumcheck.Core.indexedExecute` (arbitrary challenge; original `p`, sent `q`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:52` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.committedRun_true_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:91` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult_true_iff`; C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted_failure`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:103` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_failure` (specialize `D := domain.get`) | equivalent |
| `Sumcheck.Interaction.SingleRound.committedRun_rejects`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:110` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult_rejects`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |
| `Sumcheck.Interaction.SingleRound.prEvent_eq_evalDist_map_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:118` | `prEvent_eq_evalDist_map` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.SingleRound.prEvent_bind_le_of_forall_le_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:123` | `prEvent_bind_le_of_forall_le` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.SingleRound.executeCommitted_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:131` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_committed_soundness`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeRandomCommitment_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:158` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_randomized_soundness`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted_measureSoundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:169` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_committed_measureSoundness` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeRandomCommitment_measureSoundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:179` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_randomized_measureSoundness` | equivalent |
