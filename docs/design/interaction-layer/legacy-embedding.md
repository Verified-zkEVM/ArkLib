# Embedding the legacy layer into the interaction layer

The modules under `ArkLib/Interaction/Core/Legacy/` embed legacy protocol specifications,
provers, verifiers and oracle verifiers into the interaction layer. They also relate the two
executions and transfer completeness and soundness between the layers. Nothing here changes
the legacy layer. The embedding reads legacy definitions and reuses their meaning.

## Modules

| Module | Contents |
|---|---|
| `Protocol` | `protocol pSpec`, the plain tree of a legacy specification, and `oracleProtocol pSpec`, its oracle tree. Also `transcriptEquiv`, which identifies runtime paths with legacy full transcripts. |
| `Prover` | `embedProver`, which turns a legacy prover into a focal strategy slot for slot. Also `legacySampler`, the public-coin sampler indexed by legacy challenge rounds. |
| `Verifier` | `embedVerifier` and `embedReduction`. The verifier decides on the decoded transcript. |
| `OracleReduction` | `embedOracleProver` and `embedOracleVerifier` on the oracle tree, for both legacy oracle-output representations. |
| `Execution` | The common observation and the execution correspondence. |
| `Security` | The completeness and soundness transfers. |

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
- An interaction-layer prover with any output family first forgets its outputs (`mapOut`). It
  then becomes the legacy prover `translate p t₀`, whose state is the remaining strategy.
  `embedProver_translate` shows that embedding the translation gives back the original
  strategy, with its outputs replaced by `t₀`. If `StmtOut` is empty, nothing is accepted and
  the bound holds trivially.

Neither transfer needs `PureChallengeSlots`, because both use the distributional correspondence.

## Not covered

Knowledge-soundness and round-by-round transfers are not stated. The knowledge transfer needs a
logged version of the execution correspondence. It also needs a hypothesis that the extractor is
invariant when challenge queries move relative to shared-oracle queries in the log. The
round-by-round transfers need a relation between legacy and interaction-layer prefixes and state
functions. The oracle-tree analogue of the execution correspondence is also not stated.
