# Native state restoration: source and legacy correspondence

This note records the October 3, 2026 implementation boundary. The normative scope remains the
[overnight contract](../../design/interaction-security-night-contract.md); publication and exact
validation revisions are recorded in the [run ledger](interaction-night-20261003.md). Principal
native production proofs and the closed-oracle endpoint have compiled and passed independent
review; final clients and combined canonical validation have passed. See the run ledger for exact heads, CI status and acceptance verdicts.

## WARP's probability statement and the native statement

The inspected [WARP paper](https://eprint.iacr.org/2025/753), Definitions B.1–B.2 and Theorem B.4,
uses a deterministic adaptive state-restoration prover and a straightline extractor which sees
the completed challenges. The formalization preserves that information contract. It does not
assert the challenge-erased ARC contract or an equivalence between those notions.

| Source clause | Native implementation and proof obligation |
|---|---|
| B.1 query: round, input, prover-message prefix, salt prefix | `Key` has exactly these data; nesting depth identifies the round. Earlier challenges are absent. |
| Independent uniform function per round; repeated requests are consistent | VCVio's existing `randomOracle`, started with empty cache, samples on a miss and replays on a hit. Answer types may differ by round. |
| Adaptive final input and full message/salt sequence | The adversary returns its input only after its queries. It may have queried other inputs, including inputs outside the permitted set. |
| Final completion from the same functions | `complete` makes at most one call per selected round to the same oracle; its native-path and query-log equations are proved. |
| Actual deterministic verifier applied to that transcript | `execute_pathReplay` proves the native runner equation; `verificationGame_eq` uses actual completion support. `closedVerificationGame` closes the actual optional open output under that same path's handler. Rejection remains unsuccessful. |
| Supplied output witness and backwards extraction | `extractInputWitness` uses a named terminal witness equivalence followed by the existing recursive extractor. It does not choose valid intermediate witnesses. |
| Input/output proximity relations | The principal theorem takes arbitrary input/output relations and endpoint iff laws. A proximity parameter can index these data pointwise; no extension of its admissible range is implied. |
| Theorem B.4 probability coefficient | `stateRestoration_oracle_knowledge_soundness` bounds permitted input, valid actual closed-output witness, and invalid extracted input witness by `(Q + k) * error`. The error is uniform over permitted inputs and authored prefixes. |
| Sum of local extraction times | Not proved. The implementation supplies a backwards function; no executable runtime realization for its arbitrary supplied maps is present. |

The native witness carrier may depend on the concrete prefix. The endpoint equivalence identifies
its terminal carrier with the adversary's common output-witness type. Its input witness type may
depend on the selected input. These are explicit carrier identifications, not an existential
choice of a witness. The output type may depend on the public transcript, while the verifier can
inspect oracle messages only through the declared source-query interface. The terminal program
may return an open virtual oracle with arbitrarily many possible queries. Canonical post-run
closing supplies its actual behavior to the relation; the verifier is not given the hidden handler.

This endpoint distinction caused a material review correction. The first checked theorem observed
only the source-program's returned value. It could not generically close a virtual output oracle
from a public transcript alone, because that transcript erases concrete oracle messages. Treating
that theorem as arbitrary IOR security would have overstated it. The separate optional
closed-oracle game and its proved equation repair this boundary; they do not assume the missing
correspondence or require enumerating every output query.

The initial scope is a fixed finite round list with finite message alphabets and finite nonempty
uniform challenge alphabets. Input and salt types need not be finite. A fixed salt length is an
instance of the arbitrary salt type; no salt is secretly incorporated into the input statement.
Round alphabets and interfaces are independent of the selected input as well as prior challenges.
Input-dependent or challenge-dependent round presentations and persistent hidden verifier worlds require different
presentation proofs and remain open.

## The unqueried-ancestor difficulty

For an out-of-order request at round j, the reconstructed prefix uses strict-ancestor challenges
which the adversary may never have requested. The bad event is consequently not required to be
measurable from the visible query history. A proof using only that history would miss the source
obligation.

The VCVio result proves exact dependent eager-table/lazy-cache execution correspondence, then a
fresh-query bound valid when each key's bad event has the required bound under resampling its own
coordinate in every fixed background table. Native `keyExtractor_update` proves that changing
the target response preserves the entire ancestor-reconstructed pre-challenge extractor, including
its dependent witness carrier. All-authored-prefix local knowledge soundness then gives precisely
the required resampling premise. The target key is distinct from each strict ancestor by its
round tag, even if messages and salts repeat.

The final unrestricted-key theorem restricts a fixed finite-answer oracle program to its finitely
many possible queries, preserving its exact cached execution and query log. The universal table
hypotheses justify fixing coordinates outside that finite support. It does not posit a uniform
sample on an infinite function space. Completion's actual logged keys connect the deterministic
failed-extraction argument to the probability bound. The conservative budget counts all accesses,
including repeats; the proof charges fresh bad events without granting the adversary hidden
ancestor answers or adding their reconstruction to its query budget.

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
- [Security/StateRestoration](../../../ArkLib/OracleReduction/Security/StateRestoration.lean)
  already accepts an adaptively returned statement and supplied output witness. Its partial
  `OptionT` extractor correctly counts failure to return a valid witness as bad on valid output.
  This is a useful richer extractor interface if effects and partial extraction are later needed.

There are also material differences. The legacy game is parameterized by an initial distribution
on complete challenge implementations and an ambient stateful handler; those parameters alone do
not impose the exact independent cached-uniform experiment. Its knowledge game passes default
query logs to the extractor rather than recording actual prover/verifier logs there. It has no
explicit query-budget parameter in that security definition. Salts enter through a separate
protocol transformation, with some older comments also suggesting input-level salt encoding.
None of these differences is repaired merely by instantiating the new probability theorem.

The new theorem reuses the native protocol/execution layer and VCVio's cached probability
semantics. It does not silently adopt the legacy ambient-world contract, delete that interface,
or claim that native and legacy security definitions are interchangeable.

## Runtime remains a separate mathematical bridge

The pinned PolyFun quantitative framework can prove costs of actual backend execution, including
sequential composition and iteration. Its `RunsWithinUnder.seqComp` requires executable phase
realizations, phase bounds, a handoff bound, and separate wiring overhead. Suffix extraction runs
before prefix extraction. `IterationCode` can sum actual backward-step execution costs with
explicit loop overhead once uniform executable code exists.

Current native `RoundExtractor` data carry arbitrary pure maps. To obtain a runtime theorem one
must supply executable witness/transcript representations, realizers for those maps and carrier
transports, an actual traversal implementation, and correspondence with the named extraction
function. Charging a `tell` once per map or counting recursive calls would establish a different
resource claim. No runtime bound is inferred from Lean reduction or from the probability proof.


The private-coins corollaries average these actual games over independently pre-sampled coins.
The coin author may fail, and every fixed-coin adversary retains adaptive oracle access and an
all-branch query budget. This is an explicit random-tape-family specialization; equivalence with
arbitrary interleaved private-randomness and oracle effects is not asserted.


## Nonuniform errors: proof plan and invalid shortcuts

The optional extension under development assigns error `epsilon_j` to each fixed round and
targets `Q * max_j epsilon_j + sum_j epsilon_j` for the same actual restoration game. It uses
VCVio's existing worst-case additive query-cost semantics with probability charges as weights;
these weights are not CPU extraction costs. A new weighted fresh-query theorem is needed. The
following hand-checked counterexamples explain why simpler-looking arguments do not suffice;
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
   independent free replies, their expectations are 1/2. Thus the library's canonical free
   `ExpectedCostBound` cannot replace an actual cached-runtime budget without a correspondence
   theorem. The existing all-path `WorstCaseCostBound` is safe here and gives 1.

The proposed weighted proof retains the all-background-table resampling premise and charges
fresh bad events without conditioning on previous absence. Completion's actual query charges
sum to the round errors, while the adversary's all-branch query bound gives `Q * max`. Infinite
and zero errors and zero-round protocols should remain covered. A runtime-expected or genuinely
history-dependent sharpening is a separate future theorem.
