# Native state restoration: source and legacy correspondence

This note compares the interaction layer's state-restoration theorems with WARP and with the
legacy oracle-reduction layer. The theorems are in
[`Security/StateRestoration`](../../../ArkLib/Interaction/Security/StateRestoration.lean) and
[`Security/StateRestorationBudget`](../../../ArkLib/Interaction/Security/StateRestorationBudget.lean).
The maintainer has not reviewed their design, and it may change. The
[state-restoration disposition record](../../design/interaction-layer/state-restoration-disposition.md)
maps every declaration of the deleted first implementation to its counterpart on `main`, and
gives the authoritative correspondence with the papers.

Statements about ArkLib code in this note were checked against `main` on November 25, 2026. A
statement that holds only at an earlier commit names that commit.

## How the results reached `main`

The first implementation was proposed on October 3, 2026 as a sequence of pull requests against
the old generic interaction layer under `ArkLib/Interaction/Oracle/`.

| Target | Pull request | Merged (UTC) |
|---|---|---|
| Native round-by-round soundness implies ordinary soundness, with a native Sumcheck instance | [#1261](https://github.com/Verified-zkEVM/ArkLib/pull/1261) | October 8, 2026 |
| Named backward extraction and native append | [#1259](https://github.com/Verified-zkEVM/ArkLib/pull/1259) | October 8, 2026 |
| Sequential composition of knowledge certificates at actual closed middle claims | [#1260](https://github.com/Verified-zkEVM/ArkLib/pull/1260) | October 8, 2026 |
| State-restoration knowledge soundness with `(Q + k) * error`, and pre-sampled private coins | [#1263](https://github.com/Verified-zkEVM/ArkLib/pull/1263) | October 8, 2026 |
| Per-round errors with `Q * max_j error_j + sum_j error_j` | [#1264](https://github.com/Verified-zkEVM/ArkLib/pull/1264) | October 8, 2026 |
| Uniform and weighted adaptive cached-oracle bounds, with bad events on unqueried cells | [VCVio#823](https://github.com/Verified-zkEVM/VCVio/pull/823) | October 3, 2026 |

[#1573](https://github.com/Verified-zkEVM/ArkLib/pull/1573) later deleted that layer. Its last
version is at commit
[`5baa170967`](https://github.com/Verified-zkEVM/ArkLib/tree/5baa1709670941c73817202fabf8b012fe433ad4/ArkLib/Interaction/Oracle).
The results now live in these modules under `ArkLib/Interaction/Security/`, which
[current status](../../design/00-current-status.md#interaction-layer-security) lists with the
pull requests that landed them:

- ordinary soundness from round-by-round soundness: `Implications`
  (`OracleVerifier.soundness_of_rbrSoundness_uniform`), applied by
  `Sumcheck.indexedVerifier_soundness`;
- backward extraction and knowledge composition: `RoundByRound` (`KnowledgeStateFunction`),
  `KnowledgeComposition` and `KnowledgeComposition/Extraction`;
- state restoration, private coins and per-round errors: `StateRestoration` and
  `StateRestorationBudget`.

[`knowledge-composition-disposition.md`](../../design/interaction-layer/knowledge-composition-disposition.md)
and the state-restoration record above map each deleted declaration.

These items were left open in October and remain open on `main`:

- a bound on extraction running time, as opposed to declared instruction counts;
- cached-oracle costs that depend on the query history, or expected rather than worst-case costs;
- adversaries whose private coin sampling interleaves with oracle queries;
- exact adapters to the legacy layer and to the textbook statements;
- the relation between WARP's extractor, which sees the completed challenges, and ARC's
  challenge-erased extractor interface.

## WARP's probability statement and the native statement

The inspected [WARP paper](https://eprint.iacr.org/2025/753), Definitions B.1–B.2 and Theorem B.4,
uses a deterministic adaptive state-restoration prover and a straightline extractor which sees
the completed challenges. The formalization preserves that information contract. It does not
assert the challenge-erased ARC contract or an equivalence between those notions.

| Source clause | Declaration on `main` and what it proves |
|---|---|
| B.1 query: round, input, prover-message prefix, salt prefix | `Key` holds exactly these data; nesting depth identifies the round. Earlier challenges are absent. |
| Independent uniform function per round; repeated requests are consistent | The games run under VCVio's `randomOracle` from an empty cache, which samples on a miss and replays on a hit. One cached table with a dependent key-to-challenge signature (`oracleSpec`) replaces the per-round functions, and answer types may differ by round. |
| Adaptive final input and full message/salt sequence | The adversary returns its input only after its queries. It may have queried other inputs, including inputs outside the admissible set. |
| Final completion from the same functions | `complete` makes one call per round to the same oracle. `complete_queryBound`, `complete_log_keys` and `complete_eval` give its query bound, logged keys and value. |
| Actual deterministic verifier applied to that transcript | The verifier is passive and its decision has no ambient oracle, so `verdict` and `closedVerdict` compute its output from the input data and the transcript's oracle messages. `verificationGame_eq` and `closedVerificationGame_eq` identify the games with these values. `run_scriptedProver`, `run_scriptedProver_of_mem_support` and `closedVerificationGame_eval_run` show that `OracleVerifier.run` on the completed transcript returns the same transcript and verdict. Rejection remains unsuccessful. |
| Supplied output witness and backwards extraction | `KnowledgeStateFunction.extractAlong` runs the backward maps (`extractLeaf`, `extractStep`, `extractRoot`) after `readOut` converts the adversary's witness at the completed transcript. It does not choose valid intermediate witnesses. |
| Input/output proximity relations | The theorems take arbitrary `relIn` and `relOut`, an `admissible` input predicate, and an `outputLaw` implication from a valid closed output to the leaf state. A proximity parameter can index these data pointwise; no extension of its admissible range is implied. |
| Theorem B.4 probability coefficient | `stateRestoration_oracle_knowledge_soundness` bounds admissible input, valid closed output, and failed extraction by `(Q + rounds.length) * error`, under `F.LocallyBoundedOfNodes (uniformDraw rounds) (uniformEps rounds error)`. The error is uniform over admissible inputs and prefixes. |
| Sum of local extraction times | Not proved. `MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform` and its `_withReadOut` form bound declared stage instructions, not running time. |

The first implementation, at `5baa170967`, stated the endpoints differently. Its
`extractInputWitness` used a named terminal witness equivalence, and its output law was an iff
with the terminal state. On `main`, `readOut` is an arbitrary function and `outputLaw` is a
one-way implication, so the certificate obligation is weaker than the old iff. The disposition
record's [endpoint section](../../design/interaction-layer/state-restoration-disposition.md#scope-and-endpoint-correspondence)
gives the details.

The witness carriers of a `KnowledgeStateFunction` may depend on the statement and on the
concrete prefix, oracle messages included. The output witness may depend on the completed
transcript. The verifier reads oracle messages only through its query interface. Its
`outputMap` returns concrete output data with a law that query simulation agrees with that data,
and `closedVerdict` gives the relation the accepted statement together with that output data.

On `main`, the scope is a fixed list of rounds (`protocol : List Round`). Each `Round` has a
message type with an oracle interface, which need not be finite, and a challenge type with a
`SampleableType` uniform sampler. Input and salt types are arbitrary. A fixed salt length is an
instance of the arbitrary salt type; no salt is secretly incorporated into the input statement.
The rounds do not depend on the selected input or on earlier challenges. Input-dependent or
challenge-dependent rounds and persistent hidden verifier state need different proofs and remain
open.

## The unqueried-ancestor difficulty

For an out-of-order request at round j, the reconstructed prefix uses strict-ancestor challenges
which the adversary may never have requested. The bad event is consequently not required to be
measurable from the visible query history. A proof using only that history would miss the source
obligation.

The VCVio result at the pinned revision,
[`FreshQuery.lean`](https://github.com/Verified-zkEVM/VCVio/blob/621d01149403647811ed7b4a46998c15570e4650/VCVio/OracleComp/QueryTracking/RandomOracle/FreshQuery.lean),
proves exact correspondence between execution against a complete eager table and the lazy cache.
It then proves a fresh-query bound, valid when each key's bad event has the required bound under
resampling its own coordinate in every fixed background table. On `main`, `keyHistory_update`
proves that changing the answer at a key leaves the prefix reaching that key unchanged.
`badKey_resample_bound` uses it to derive the resampling premise from local knowledge soundness
at every prefix. `restored_bad_trace` shows that, on every answer table, a run with valid output
and failed extraction queries a bad key. The target key differs from each strict ancestor by its
round tag, even if messages and salts repeat.

VCVio's `prEvent_randomOracle_le_of_bad_queries` allows an infinite key domain. It restricts a
fixed finite-answer oracle program to the finitely many keys it can query (`possibleQueryKeys`,
`restrictQueries`), which preserves its cached execution and query log. Its hypotheses quantify
over every background table, which justifies fixing coordinates outside that finite set. It does
not posit a uniform sample on an infinite function space. Completion's logged keys connect the
deterministic failed-extraction argument to the probability bound. The budget counts all queries,
repeats included. The proof charges fresh bad events without giving the adversary the answers at
unqueried ancestors or adding their reconstruction to its query budget.

## What to retain from the old oracle-reduction layer

The old layer contains useful ingredients, not merely obsolete notation:

- [ProtocolSpec/Basic](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean) defines
  `challengeOracleInterfaceSR` using the input and `MessagesUpTo` at the challenge index.
  The latter stores prover messages, not prior verifier responses. Thus the actual old key
  already has the important challenge-free shape despite prose referring to a transcript.
  `deriveTranscriptSR` also performs completion after the adversary selects its input/messages.
- [Salt](../../../ArkLib/OracleReduction/Salt.lean) pairs each prover message with its salt and
  proves verifier-query/output simulation facts for the transformed interface. This is a useful
  model for a future representation adapter. The new presentation keeps salts in restoration
  keys while leaving the underlying native protocol's messages unchanged. An exact adapter must
  prove prefix-key and completion equations; naming similarity alone is not an equivalence.
- The legacy state-restoration definitions, removed by
  [#1409](https://github.com/Verified-zkEVM/ArkLib/pull/1409), are at
  [`2f713ebb6d`](https://github.com/Verified-zkEVM/ArkLib/blob/2f713ebb6d8ba14c6395def8b959a04b46e2c3a5/ArkLib/OracleReduction/Security/StateRestoration.lean).
  At that commit, the game accepts an adaptively returned statement and a supplied output witness.
  Its partial `OptionT` extractor counts failure to return a valid witness as bad on valid output.
  This is a useful richer extractor interface if effects and partial extraction are later needed.

At `2f713ebb6d`, the legacy definitions also differ materially from the native theorems. The game
is parameterized by an initial distribution on complete challenge implementations and an ambient
stateful handler; those parameters alone do not impose the exact independent cached-uniform
experiment. Its knowledge game passes default query logs to the extractor rather than recording
actual prover/verifier logs there. It has no explicit query-budget parameter. Salts enter through
a separate protocol transformation, with some older comments also suggesting input-level salt
encoding. None of these differences is repaired merely by instantiating the new probability
theorem.

The native theorems reuse the interaction layer's protocol and execution and VCVio's cached
probability semantics. They do not adopt the legacy ambient-state contract or claim that native
and legacy security definitions are interchangeable.

## Runtime remains a separate mathematical bridge

The pinned PolyFun quantitative framework (revision
[`713d8857e4`](https://github.com/Verified-zkEVM/PolyFun/tree/713d8857e49d20927c1447b3ba7397acc5537319/PolyFun/Realizability/Quantitative))
can bound the cost of actual backend execution, including sequential composition and iteration.
Both results take backend code and cost proofs as premises. Neither derives them from a Lean
function.

- **Sequential composition.** `QuantitativeRealization.RunsWithinUnder.seqComp` in
  `BoundedClosure.lean` takes run bounds for both phases, a `SeqCompHandoffBound` for the value
  passed between them, and a `SeqCompCostCertificate` for wiring and phase-switching work. It
  gives the bound `firstBound + handoff.bound + certificate.overhead`. In backward extraction, the
  suffix extractor runs before the prefix extractor.
- **Iteration.** `IterationCode` in
  [`Iteration.lean`](https://github.com/Verified-zkEVM/PolyFun/blob/713d8857e49d20927c1447b3ba7397acc5537319/PolyFun/Realizability/Quantitative/Iteration.lean)
  iterates one fixed step function `next` on one state type `S`. The backend supplies the loop
  code, an `overhead` function and a proof `cost_le` that the loop costs at most the summed step
  costs plus that overhead. To use it, backward extraction must be encoded as one state type and
  one step function, so the varying witness carriers and step maps of a `KnowledgeStateFunction`
  need a common encoding first. `polyRealizer` gives a polynomial bound from
  `PolynomialBounds`, which requires a polynomial bound on the iteration count, a polynomial bound
  on the initial state size, an additive bound on size growth per step, and a polynomial bound on
  the loop overhead. The module notes that a polynomial bound for one step alone is insufficient,
  because repeated size doubling can be exponential.

On `main`, a `KnowledgeStateFunction` carries arbitrary pure backward maps (`extractStep`,
`extractLeaf`, `extractRoot`). To obtain a runtime theorem one must supply executable witness and
transcript representations, realizers for those maps and carrier transports, an actual traversal
implementation, and correspondence with `extractAlong`. Charging one instruction per map or
counting recursive calls would establish a different resource claim. No runtime bound is inferred
from Lean reduction or from the probability proof. The
[accounting boundary](../../design/03a-extractor-efficiency.md#proof-and-accounting-boundary)
states what the measured certificates exclude, and the
[complete-execution contract](../../design/03b-extractor-execution.md#the-complete-execution-contract)
states what a runtime theorem must add.

The `privateCoins` corollaries average these actual games over independently pre-sampled coins.
The coin sampler may fail, and every fixed-coin adversary retains adaptive oracle access and an
all-branch query budget. This is an explicit random-tape-family specialization; equivalence with
arbitrary interleaved private-randomness and oracle effects is not asserted.

## Nonuniform errors and invalid shortcuts

The nonuniform extension assigns error `epsilon_j` to each fixed round and proves
`Q * max_j epsilon_j + sum_j epsilon_j` for the same actual restoration game. It uses
VCVio's worst-case additive query-cost semantics (`WorstCaseCostBound`) with probability charges
as weights; these weights are not CPU extraction costs. The weighted fresh-query theorem,
`prEvent_randomOracle_le_of_bad_queries_weighted`, is in the pinned VCVio `FreshQuery.lean` above.
The following hand-checked counterexamples explain why simpler-looking arguments do not suffice;
they are research observations, not claims of additional Lean separation theorems.

1. **Completion alone does not have error bounded by the sum after adaptive selection.**
   In a one-round binary-challenge protocol, take the bad event to be the true reply, so each
   fixed key has local error 1/2. Query two salted keys and select a true one whenever either
   reply is true. Completion rereads that selected key and is bad with probability 3/4. The
   cached bad reply must be charged to the adversary's earlier access; adding a separate
   completion-only bound without accounting for the cache is invalid.
2. **Conditioning on no earlier bad query can reveal an unqueried ancestor.**
   Let first-round knowledge be the binary challenge `t`, and terminal knowledge be
   `t or not u`; root knowledge is false and backward maps are identity. The round-two bad
   event is `not t and not u`. Query the later key first and observe `u=false`. Conditioning
   additionally on that queried key not being bad forces the still-unqueried ancestor `t`
   to be true. The subsequent bad-event probability is 1 although its unconditional local
   bound is 1/2. The proof must avoid this conditioning.
3. **Expected cost under uncached replies differs from expected cost under the actual cache.**
   Query a zero-weight binary control key twice, then query a weight-one always-bad Unit-answer
   key exactly when the replies agree. Under a cached oracle, success and cost are 1. Under
   independent free replies, their expectations are 1/2. Thus VCVio's free
   `ExpectedCostBound` cannot replace an actual cached-runtime budget without a correspondence
   theorem. The all-path `WorstCaseCostBound` is safe here and gives 1.

The weighted proof retains the all-background-table resampling premise and charges
fresh bad events without conditioning on previous absence. Completion's actual query charges
sum to the round errors, while the adversary's all-branch query bound gives `Q * max`. Infinite
and zero errors and zero-round protocols remain covered. A runtime-expected or genuinely
history-dependent sharpening is a separate future theorem.

`complete_round_cost` bounds the actual completion program's query charges by the sum. It is not
a separate probability bound for completion conditioned on the adversary's selected transcript.
`restoredExecution_round_cost` adds that cost to the all-branch adversary budget before the
weighted probability theorem is applied. `stateRestoration_oracle_knowledge_soundness_nonuniform`
then uses the same closed-game equation and `outputLaw` as the uniform theorem. Thus the
sharpening changes neither the extractor's information nor the output relation's observation.
