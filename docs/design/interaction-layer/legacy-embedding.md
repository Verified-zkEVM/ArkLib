# Embedding the legacy layer into the interaction layer

The modules under `ArkLib/Interaction/Core/Legacy/` embed legacy protocol specifications,
provers, verifiers and oracle verifiers into the interaction layer. They also relate the two
executions and transfer completeness, soundness and knowledge soundness between the layers. Nothing here changes
the legacy layer. The embedding reads legacy definitions and reuses their meaning.

## Modules

| Module | Contents |
|---|---|
| `Protocol` | `protocol pSpec`, the plain tree of a legacy specification, and `oracleProtocol pSpec`, its oracle tree. Also `transcriptEquiv`, which identifies runtime paths with legacy full transcripts. |
| `Prover` | `embedProver`, which turns a legacy prover into a focal strategy slot for slot. Also `legacySampler`, the public-coin sampler indexed by legacy challenge rounds. |
| `Verifier` | `embedVerifier` and `embedReduction`. The verifier decides on the decoded transcript. |
| `OracleReduction` | `embedOracleProver` and `embedOracleVerifier` on the oracle tree, for both legacy oracle-output representations. |
| `Execution` | The common observation, the execution correspondence and its logged form. |
| `Security` | The completeness, soundness and knowledge-soundness transfers. |

## The common observation

An interaction-layer run of a plain tree produces an `Observation`: the runtime path, the
prover's output and the verdict `Option T`. A legacy run produces a value of `OptionT`, where
rejection is missing mass. The two are compared through

```lean
finalize : Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut →
  LegacyResult pSpec StmtOut WitOut
-- LegacyResult = Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)
```

`finalize` decodes the transcript of an accepted run and maps a rejected run to `none`. Each
security transfer compares the legacy probability of an event with the interaction-layer measure
of the event "accepted, and the legacy event holds". Rejection is never treated as missing mass.

Challenges are routed through `challengeReindex`, which answers the challenge node of each
interaction-layer round with the legacy challenge oracle of the same round. Its probabilistic
form is `plainChallengeImpl chImpl`.

## Execution correspondence

- `finalize_observeWith_counterpartFirst` is a program equality. In the counterpart-first
  schedule, the finalized interaction-layer run of an embedded reduction is the legacy run after
  reindexing. It holds for every legacy prover.
- `simulateQ_finalize_observe` gives the same program equality in the default schedule. It
  assumes `PureChallengeSlots`: every `receiveChallenge` is `pure`.
- `experiment_finalize_observe_evalDistEq` and `evalDist_experiment_finalize_observe` hold for
  every prover. They state the equality in distribution and as measures, under any measurable
  structure. The proof moves challenge draws past the prover's effects, which works because
  `plainChallengeImpl` is stateless.
- `runEq_ambientLogged_prover` is the logged form of the prover phase. `ambientLogged` logs a
  program's queries and keeps the shared-oracle entries. `run_ambientLogged` shows that this log
  is the one that `logImpl impl` keeps in the experiment state. The logged prover-sampler run of
  an embedded prover therefore has the distribution of the legacy logged prover run, jointly with
  its shared-oracle log and the final state, from every state. The proof reuses the
  challenge-moving argument with `logImpl impl` as the shared implementation.

## Security transfers

Legacy relations and languages become statement problems with trivial admissibility,
`relProblem` and `langProblem`.

**Completeness** (`completeness_iff`). For a legacy reduction `R`, the following are equivalent:

- `(embedReduction R).completeness init impl (plainChallengeImpl challengeQueryImpl)
  (relProblem relIn) (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)
  (fun _ w => w) ε`
- `R.completeness init impl relIn relOut ε`

The interaction-layer judgement reads the prover's output statement and witness, and
requires the verifier's statement to equal the prover's. This matches the legacy event
`(stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut`.

**Soundness** (`soundness_iff`). For a legacy verifier `V`, the following are equivalent:

- `(embedVerifier V).soundness init impl (plainChallengeImpl challengeQueryImpl)
  (langProblem langIn) (langProblem langOut) ε`
- `V.soundness init impl langIn langOut ε`

Each direction translates every adversary of one layer into the other.

- A legacy prover becomes an interaction-layer prover through `embedProver`.
- An interaction-layer prover with any output family first has its outputs replaced by a fixed
  statement `t₀` and the trivial witness (`mapOut`). It then becomes the legacy prover
  `translate`, whose state is the remaining strategy and whose output is the strategy's output.
  `embedProver_translate` shows that embedding the translation gives back the strategy. If
  `StmtOut` is empty, nothing is accepted and the bound holds trivially.

Neither transfer needs `PureChallengeSlots`, because both use the distributional correspondence.

**Knowledge soundness** (`knowledgeSoundnessWith_iff`, `knowledgeSoundness_iff`). For a legacy
verifier `V` and a legacy straight-line extractor `E`, the following are equivalent:

- `knowledgeSoundnessWith ((embedVerifier V).classicalModel init impl
  (plainChallengeImpl challengeQueryImpl)) (relProblem relIn) (relProblem relOut)
  (knowledgeJudgement relOut) (classicalStraightline (fun _ => WitIn) (embedVerifier V) init
  impl (plainChallengeImpl challengeQueryImpl) (fun _ o => o.2)) (liftExtractor E) ε`
- `V.knowledgeSoundnessWith init impl relIn relOut E ε`

The observation and witness types carry the discrete measurable structure. The prover's output
family is `fun _ => StmtOut × WitOut`. `knowledgeJudgement relOut` judges the verifier's
statement with the prover's output witness, as the legacy bad event does, and the extractor
reads that witness. `liftExtractor E` runs `E` on the decoded transcript, and
`lowerExtractor` is its inverse, so the existential notions are also equivalent.

Both layers' games end with the same phase, `knowledgeTail`: the logged verifier run, then the
extractor after acceptance. `legacy_exec_run` and `extractionGame_embed` are the program
equalities that split each game into its logged prover phase and `knowledgeTail`.
`prEvent_legacy_knowledge` combines them with `runEq_ambientLogged_prover`. It shows that the
legacy probability of the bad event equals the interaction-layer measure of the bad set.
Interaction-layer adversaries are translated with `translate`, which keeps their outputs.

Neither transfer needs a hypothesis on the extractor. Different schedules interleave
challenge entries and shared-oracle entries in a run's log differently. An extractor that read
the interleaving could tell the two executions apart, and a transfer would need it to be
`ChallengeMoveInvariant`. Both layers, however, give the extractor only the shared-oracle part
`QueryLog.fst` of the prover's log. Every such function is invariant
(`challengeMoveInvariant_comp_fst`, `challengeMoveInvariant_extractor`).

## Departures

These entries continue the numbered departures of
[`IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md) for the security
transfers of this embedding. They state each hypothesis or choice beyond the legacy statement.

### 14. The knowledge transfer needs no extractor-invariance premise

The plan for the legacy embedding expected the knowledge-soundness transfer to assume that the
extractor is invariant when challenge queries move relative to shared-oracle queries in the
prover's log. Two executions of the same run under different schedules interleave the two kinds of
entries differently, and the transfer moves challenge draws past the prover's effects. The code
states this property as `ChallengeMoveInvariant` (`Legacy/Execution.lean`). It does not assume it,
because both layers hand the extractor only `QueryLog.fst` of the prover's log: legacy
`knowledgeSoundnessWith` passes `proveQueryLog.fst`, and the core's `Verifier.runWithLog` passes
`proveLog.fst` (see `runWithLog_fst`). Every function of that projection is invariant
(`challengeMoveInvariant_comp_fst`, `challengeMoveInvariant_extractor`). The proof keeps the
shared-oracle log in the experiment state (`logImpl`), so the challenge-moving argument of the
unlogged correspondence applies unchanged (`runEq_ambientLogged_prover`).

`knowledgeSoundnessWith_iff` and `knowledgeSoundness_iff` therefore have the legacy statement's
hypotheses only. They fix an instantiation of the core notion: the prover's output family is
`fun _ => StmtOut × WitOut`, the judgement is `knowledgeJudgement relOut` (the verifier's
statement with the prover's output witness), the extractor reads that witness, and the
observation and witness types carry the discrete measurable structure. The access budget is `0`,
which the classical straight-line interface meets. The qualification of entry 6 does not arise,
because `classicalStraightline_marginal` gives marginal preservation for every extractor.

## Not covered

The round-by-round transfers are not stated. They need a relation between legacy and
interaction-layer prefixes and state functions. The oracle-tree analogue of the execution
correspondence is also not stated.
