# D8. The common observation for legacy equivalence, and the Sumcheck equivalence

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** ArkLib PR B (commits 1–3: transcript embedding, slot embedding, finalization
and execution correspondence) and ArkLib PR C (commit 3: Sumcheck equivalence).

## Decision

Legacy equivalence is stated at one named result type, after explicit finalization, in the same
ambient query monad with the same challenge oracle.

**Common result.** For a plain legacy reduction over `pSpec : ProtocolSpec n` this is the legacy
result carrier, `Reduction.run`'s (`OracleReduction/Execution.lean:162`):

```lean
-- intended, not existing
abbrev LegacyResult := Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)

def finalize (r : (tr : PathAlong l (embed pSpec)) × (StmtOut × WitOut) × Option StmtOut) :
    LegacyResult :=
  match r with
  | ⟨tr, outP, some stmtOut⟩ => some ((decodeTranscript tr, outP), stmtOut)
  | ⟨_,  _,    none⟩         => none
```

The new run (record D4) produces the full transcript, the prover's output and the decision's
verdict; finalization decodes the transcript through B's proved transcript equivalence
(`embed pSpec` is the tree of `pSpec`, `decodeTranscript` its transcript map), maps rejection to
`none` and acceptance to the legacy tuple. Terminal actions run in the declared order: focal leaf,
counterpart leaf, then the decision. The new transcript and the separate party outputs are kept
internally, including on rejection; only the observation forgets them.

For an oracle reduction the result additionally contains each side's output oracle statements,
as in `OracleReduction.run` (`Execution.lean:403`). The new side supplies them through the data
component of its output map, `(outputMap stmt p v).f` applied to the input oracles and the run's
oracle messages (record D6). Because the output map reads the view, this is the legacy
`materializeOutput`, which reads the challenges, for both `outputOracle` cases.

**Execution correspondence** (B, commit 3):

```lean
-- intended, not existing
theorem Legacy.runWith_embed (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt wit) :
    (finalize <$> (embed R).runWith .counterpartFirst stmt wit) = (R.run stmt wit).run
    -- equality of programs in OracleComp (oSpec + [pSpec.Challenge]ₒ), for every `pSpec`
```

Legacy execution samples each challenge before running `receiveChallenge`'s effect
(`Prover.processRound`, `OracleReduction/Execution.lean:47–61`), which is the counterpart-first
schedule (record D4). The theorem therefore holds as program equality for every protocol shape,
including protocols that open with a challenge and protocols with consecutive challenges. The
statement for the default `run` follows from the exchange lemma of record D4: as program equality
when the embedded prover's slots at challenge nodes are `pure`, and in distribution for every
prover when the challenge implementation is stateless and separate from the shared-oracle state.

The equality is first proved for programs, before any interpretation; the distributional
statement follows by applying `evalDist` under one interpretation of `oSpec` and of the challenge
oracle, shared by both sides. Pure reindexing (decoding transcripts) uses measurable maps;
terminal actions use bind, and their execution law is proved before `evalDist` is applied. VCVio's
`evalDist` is measure-valued, so each theorem names its result measurable spaces, the
answer-measure instances it needs, and any totality premise. `Option.none` (rejection) is never
identified with missing mass (ambient failure).

**Sumcheck equivalence** (C, commit 3). The new Sumcheck reduction and B's embedding of the legacy
`Sumcheck.Spec.General` produce equal programs, including the decision's query trace, at the
common observation:

- Both sides run the whole interaction first: every round runs, because the interaction never
  rejects.
- Both then run the same decision program: the legacy fold `oracleVerifierProgram`
  (`ProofSystem/Sumcheck/Spec/General.lean:229`), whose `none` branch (lines 238–242) skips the
  remaining round checks, and whose single-round check is the `guard (evals.sum = target)` at
  `Spec/SingleRound.lean:289`. Its agreement with sequential composition is the existing
  `oracleVerifier_verify_eq_seqCompose` (`General.lean:381`).
- The legacy Sumcheck provers have pure outputs (`instOutputIsPureProver`, `SingleRound.lean:243`;
  `instOutputIsPureReduction`, line 958), so the legacy seam hypothesis never binds.
- The honest Sumcheck prover's challenge-node slots are `pure`: legacy `receiveChallenge` is
  `pure fun chal => …` (`SingleRound.lean:236–238`), and the new prover keeps the same form. The
  exchange lemma of record D4 therefore moves B's counterpart-first correspondence to the default
  `run` as program equality, so the equivalence holds as program equality including the query
  trace.

The remaining work is the transcript correspondence and the prover slot embedding (record D4).

## Why

Without a fixed observation "equivalent" has no single meaning. The new run retains things the
legacy run discards: legacy `Reduction.run` is an `OptionT` program in which a rejecting verifier
drops the prover's result and transcript, so raw rejection transcripts and query logs cannot be
compared. Conversely, honest-run equality or equal acceptance probability is too weak for the
security transfers of record D7. The common observation is the strongest statement both sides can
make: the legacy result, exactly, as a program.

For oracle outputs, comparing a handler with a concrete polynomial is not meaningful. The data
map `f` gives the new side concrete output data, so the legacy materialization
(`materializeOutputOracle`, `OracleReduction/Basic.lean:360`) is compared with data, not
reconstructed from behavior.

## Alternatives considered

- **Honest-run equality, or acceptance probability alone.** Does not support the soundness,
  knowledge or round-by-round transfers.
- **Compare full new results, including rejection transcripts and query logs.** The legacy result
  discards them, so no such equality can be stated.
- **A behavioral observation for oracle outputs** (equality of query handlers only). Needed only if
  outputs were represented extensionally; with `f` in the oracle map it is unnecessary.

## Consequences

- B's embedding must use the same challenge oracle index as legacy `[pSpec.Challenge]ₒ` (see the
  open point in record D4).
- An arbitrary effectful sequential legacy verifier, or a legacy composition with an effectful
  prefix output before a challenge, does not get this theorem without additional hypotheses; it
  needs a separate contract.
- Any probability lemma missing from VCVio is a named upstream dependency, not an ArkLib-local
  copy. The availability of every such lemma at the pinned VCVio revision is unverified.

**Acceptance tests.** In B: distinct prover and verifier outputs; `none`; terminal queries; all
message directions, including zero rounds and consecutive same-owner rounds; both legacy oracle
output representations. In C: rejection agreement; `n = 0`; a bad round followed by good rounds
still runs every round and rejects.

## Open points

None for the observation itself. The challenge-oracle index (record D4) affects the embedding.
