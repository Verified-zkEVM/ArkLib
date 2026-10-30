# Current status

**Status date:** 2026-10-29. **Scope:** the supported dependency baseline, what the interaction
layer (`ArkLib/Interaction/`) provides on `main` at this date, and the legacy-layer results that
bear on it. This page is a dated record. The [README](../../README.md#two-layers) gives an overview of
the two layers, [Limitations of the legacy layer](legacy-layer-limitations.md) explains why the
interaction layer replaces it, and the [roadmap](../../ROADMAP.md#priority-replace-the-legacy-layer)
holds the migration plan. Protocol-level status for readers
outside the framework is on the public [roadmap](../../ROADMAP.md); remaining interaction-layer
design work is in the [design roadmap](05-roadmap.md).

The typed core, world-backed execution, and oracle composition have landed; the
[ArkLib tables](#arklib) list them. On top of them the interaction layer now has these generic
results:

- ordinary round-by-round soundness on execution prefixes, with a local-to-global theorem
  for the actual interpreted executor;
- witness-indexed round-by-round knowledge certificates, backward extraction along execution paths,
  and their sequential composition at closed intermediate claims;
- state-restoration knowledge soundness for fixed-round public-coin protocols, including oracle
  outputs, pre-sampled private coins and per-round errors;
- measured extraction stages: operation-count budgets for the named backward witness maps;
- Sumcheck with soundness, completeness, round-by-round soundness, and a computable verifier
  and honest prover.

The knowledge, state-restoration and measured-extraction results are generic certificates and
theorems. What remains open is their use: no protocol under `ArkLib/ProofSystem/` instantiates
them yet, there is no interaction-layer rewinding extractor, and state restoration does not yet
cover an adversary whose private randomness interleaves with its oracle queries (see
[below](#interaction-layer-security)).

No declaration under `ArkLib/` uses `sorry` outside the five solicited proofs recorded in
`scripts/axiom_baseline.json` (coding-theory lower bounds, issue
[#1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352)); none of those is under
`ArkLib/Interaction/` or `ArkLib/ProofSystem/Sumcheck/`.

## Supported baseline

The exact dependency revisions are in [`lake-manifest.json`](../../lake-manifest.json) and the
toolchain in [`lean-toolchain`](../../lean-toolchain); the supported Lean version is `v4.35.0`.

| Repository | Role |
|---|---|
| VCVio | direct ArkLib dependency |
| CompPoly | direct ArkLib dependency (computable polynomials) |
| PolyFun | transitive dependency; revision selected and tested by VCVio |

ArkLib does not override PolyFun independently. A later PolyFun update reaches ArkLib only after
VCVio advances and validates its pin. ArkLib's PMF probability surface is retired; new observation
boundaries use VCVio measure semantics.

## Capability status

### PolyFun

| Capability | Status | Primary evidence |
|---|---|---|
| Typed interaction trees and complete paths | available | `Interaction.TypeTree`, `TypeTree.Path`, append and path execution |
| Node contexts, schemas, and decorations | available | `TypeTree.Node.Context`, `TypeTree.Node.Schema`, decoration maps and context morphisms |
| Syntax, shapes, strategies, and executions | available | `SyntaxOver`, `ShapeOver`, `StrategyOver`, `InteractionOver` |
| Two-party execution and composition | available | roles, focal/counterpart strategies, dependent composition, factorization |
| Partial syntactic paths | available | `PFunctor.FreeM.Cursor`, cursor composition and terminal-path bridges |
| Restriction along a cursor | available | displayed-algebra child projections and decoration restriction |
| Cursor decomposition through append | available | `Cursor.AppendView`, split/join, residual and restriction laws |
| Finite dependent chains | available | `TypeTree.Chain.then`, path split/join, strategy composition, reassociation |
| Generic causal trace transducer | **missing** | no `Transducer` module at the supported pin |
| Operational `DynSystem.Prefix` concatenation | client-gated | add only if an operational-machine client cannot use ordinary monadic sequencing |

The cursor and `TypeTree.Chain` work was merged in PolyFun PRs
[#43](https://github.com/Verified-zkEVM/PolyFun/pull/43),
[#58](https://github.com/Verified-zkEVM/PolyFun/pull/58),
[#59](https://github.com/Verified-zkEVM/PolyFun/pull/59),
[#64](https://github.com/Verified-zkEVM/PolyFun/pull/64), and
[#66](https://github.com/Verified-zkEVM/PolyFun/pull/66).

One compositional boundary remains load-bearing. Pure suffix construction factors under a lawful
monad. General effectful suffix construction requires `LawfulCommMonad`; ordinary `StateT` does not
satisfy that requirement. ArkLib states stateful sequential results using explicit state threading
and history-dependent suffix theorems (#891's split theorem preserves effect order without a
commutativity assumption). It must not restore the legacy unrestricted composition claim.

### VCVio

| Capability | Status | Reuse in ArkLib |
|---|---|---|
| Handler construction and composition | available | build source interpreters and substitution from `QueryImpl` and handler laws |
| Tracing, logging, caching, and cost instrumentation | available | reuse `withTrace*`, `withLogging`, and existing erasure/failure bridges |
| Query and resource accounting | available | reuse query bounds, `ResourceProfile`, `QueryCost`, and `CostModel` |
| Cost-aware reductions | available, cost-only | reuse `SecurityGame.ReductionWithCost`; add no parallel cost hierarchy |
| Closed probability semantics | available | VCVio's native `Measure`/kernel semantics; ArkLib's PMF surface is retired (#913) |
| Probabilistic responders and wired machines | available | reuse `ProbResponder`, oracle strategies, and machine runs |
| Strict oracle-PPT certificates | available | reuse ranked resources and `HandlerCertificate` |
| Shared-ROM Merkle extraction | available | adapt the primitive theorem; do not restate its game in ArkLib |
| Runner-produced resumable execution artifact | available | `OracleRuntime`, `RunResult`, `run`, `resume`, `GeneratedBy` in `VCVio.OracleComp.Runtime`; used by `executeWithRuntime` |
| Failure-to-return mass boundary | available | `evalDistWithFailure` in `VCVio.EvalDist.WithFailure`; used by `Terminal.observe` |
| Certified query-trace transducer specialization | **missing** | waits on the generic PolyFun transducer |
| General conditioning/dynamic-programming facade | not needed so far | the interaction-layer state-restoration proofs use the cached `randomOracle`, `IsTotalQueryBound` and its cost-distribution lemmas directly; add a facade only for a client that needs it |
| Error-bearing and cost-bearing reduction package | incomplete | `ReductionWithCost` handles cost; later clients still need explicit additive/substitution error transport |

Accept/reject/fault classification is protocol-level and lives in ArkLib (`Interaction.Terminal`).
VCVio supplies only the separate failure-to-return mass, so the two kinds of absence are not
identified.

These gaps are integration boundaries, not permission to introduce ArkLib-private probability,
trace, or cost semantics. The first client should either add the smallest upstream API or provide a
temporary adapter with an upstream issue and a deletion test.

### ArkLib

The interaction layer lives under `ArkLib/Interaction/` and
`ArkLib/ProofSystem/Sumcheck/Interaction/`, with acceptance clients under `ArkLibTest/Interaction/`
and `ArkLibTest/ProofSystem/Sumcheck/`.
Naming follows [`docs/wiki/interaction-naming.md`](../wiki/interaction-naming.md).

| Area | Modules | Implementation |
|---|---|---|
| Plain dependent reductions | `Interaction/Reduction.lean` | #851 |
| Oracle type trees, paths, decorations | `Oracle/TypeTree`, `Oracle/TypeTree/Decoration` | #852, #853 |
| Accumulated access and single-run execution | `Oracle/Access`, `Oracle/Execution`, `Oracle/Protocol` | #861, #862 |
| Sources, routing, named contexts | `Oracle/Source`, `Oracle/Resource` (`NamedContext`, `OracleModel`) | #863, #864 |
| Virtual substitution | `Oracle/Virtual` | #869 |
| Open/closed claims and run-derived closing | `Oracle/Claim`, `Oracle/CoreRun` | #870, #871 |
| Concrete prefixes and available contexts | `Oracle/Prefix`, `Oracle/RunSources` | #880 |
| Logged execution and persistent runtime | `Oracle/LoggedExecution`, `Oracle/LoggedRun`, `Oracle/Runtime` | #884 |
| Accept/reject/fault outcomes | `Oracle/Terminal`, `Oracle/TerminalRun`, `Oracle/TerminalMeasure` | #886 |
| Ordered world phases | `Oracle/WorldSegments`, `Oracle/PhasedExecution`, `Oracle/PhasedRun` | #889 |
| Finite ordered composition | `Oracle/Composition` (`ExecutionInterface`) | #891 |
| Direct strategy execution | `Oracle/CoreRun.executeStrategiesCore` | #1216 |
| Direct logged, phased, and persistent-runtime execution | `Oracle/LoggedRun`, `Oracle/PhasedRun`, `Oracle/Runtime` | #1236 |
| Composition inside one persistent runtime | `Oracle/RuntimeSoundness` | [#1237](https://github.com/Verified-zkEVM/ArkLib/pull/1237) |
| General composition soundness | `Interaction/CompositionSoundness` | #1218 |
| Restricted verifier composition for every whole prover | `Oracle/Sequential.executeStrategies_append` | #1233 |
| Composition through exported oracle interfaces and actual claim closing | `Oracle/SourceRouting.executeStrategies_appendExported_close` | #1234 |
| Weighted and uniform soundness for exported oracle composition | `Oracle/CompositionSoundness` | [#1235](https://github.com/Verified-zkEVM/ArkLib/pull/1235) |
| Available query names preserved by continuation and append | `Oracle/Prefix`, `Oracle/Access` | [#1238](https://github.com/Verified-zkEVM/ArkLib/pull/1238) |
| Actual-route access and weighted query budgets | `Data/OracleComp/QueryBounds` | [#1238](https://github.com/Verified-zkEVM/ArkLib/pull/1238) |
| Oracle append paths, runtime roles, access, and query answers | `Oracle/TypeTree`, `Oracle/TypeTree/Decoration`, `Oracle/Access`, `Oracle/RunSources` | #1232 |
| Fixed-prover, reachable, and averaged bounds | `run_appendFlat_soundness_fixed`, `_of_support`, `_ae`, and `_weighted_ae` | #1231 |

Sumcheck on the interaction layer:

| Result | Evidence | Landed in |
|---|---|---|
| One-round honest completeness through closing | `SingleRound`, `Closing` | #872 |
| Legacy correspondence | `legacy_input_iff`, `legacy_output_iff`, `legacy_verifier_correspondence` | #874, #1244 |
| Round relations via multivariate projection | `Projection`, `ProjectionTransport` | #879 |
| One-round reduction soundness, error `deg` over the field size | `executeCommitted_soundness`, `executeRandomCommitment_soundness` and measure forms | #881 |
| Two sequential rounds through the actual closed claim | `MultivariateRound`, `Sequential` | #883 |
| Arbitrary consecutive rounds, honest completeness | `executeRoundsSampled_perfectCompleteness`, `executeRounds_uniform_perfectCompleteness` and measure forms | #892 |
| Actual multivariate round soundness | `MultivariateRound.executeCore_sampled_soundness` in `MultivariateSoundness` | #1214 |
| Full-protocol soundness | `Native.execute_soundness` in `ProtocolSoundness` | #1214 |
| Honest completeness | `Native.execute_support_completeness`, `Native.execute_perfectCompleteness` in `ProtocolCompleteness` | #1214 |
| Computable round messages and verifier | `Impl/Representation`, `Interaction/Computable` | #1242 |
| Soundness for computable-message strategies | `Computable.execute_soundness` in `ComputableSoundness` | #1242 |
| Computable honest messages and original oracle | `Impl/Projection` | #1243 |
| Completeness for the computable honest prover | `Computable.execute_support_completeness`, `Computable.execute_perfectCompleteness` in `ComputableCompleteness` | #1243 |
| Round-by-round soundness, error `count * deg` over the field size | `Native.roundByRound_soundness` in `RoundByRound` | #1261 |

`Sumcheck/Interaction/Protocol` defines one oracle interaction tree. Each round receives a
univariate polynomial oracle, then the verifier publicly aborts or supplies a fresh challenge.
The prover is the ordinary `Interaction.Oracle.Prover.Strategy`: its continuations retain private
memory and may perform effects after receiving the challenge. There is no separate private-state
kernel in the security statement. `Native.execute` passes those strategies directly to
`executeStrategiesCore`, then closes the actual run. A prover strategy is not repackaged as a
reduction witness. The reduction entry point `executeCore` performs prover setup and delegates to
the same strategy entry point. Both paths use `executeStrategies` and the same paired resources.

The verifier queries the sent polynomial for its sum check and next target. It exports the
original polynomial oracle through a virtual view, retaining the accumulated access to earlier
messages. At the last leaf, the output relation says that this retained oracle evaluated at the
full challenge vector equals the final target. This is a relation on the output, not a final
verifier query. From a false initial claim over an oracle realized by a polynomial of individual
degree at most `deg`, soundness bounds the probability of a non-rejected true output by
`count * deg / |F|` for fresh uniform challenges. The honest strategy sends the projected
round polynomials. From a true initial claim, every supported execution returns a true output;
probabilistic completeness is one for any `ProbComp` challenge, whose oracle specification is
normalized. Support preservation alone makes no assertion about total successful mass.

`Native.Core` owns the single protocol and verifier definition, parameterized by the message
carrier and its evaluation operation. `Native` retains the mathematical presentation;
`Computable` specializes it to bounded CompPoly coefficient arrays and Horner evaluation.
`execute_eq_native` proves equality of actual closed executions after interpreting each sent
message, preserving private continuations and effects on public abort. The interpretation is
proof-only: the computational verifier runs directly on CompPoly data. Its soundness theorem
retains the same bound and original-oracle assumptions. `sumcheck-runtime` checks the compiled
execution, including private memory, effect order and rejection, with fixed test challenges.

`Impl/Projection` constructs each honest round message directly from a CompPoly multivariate
polynomial. It splits out the current variable, evaluates the other variables at prior challenges
and every remaining domain point, and sums the resulting univariate polynomials. The proved
correspondence covers arbitrary individual degree bounds and finite domains. `inputImpl` evaluates
the original CompPoly polynomial directly; its equality to the mathematical oracle behavior is a
separate theorem.

`Computable.honestProver` uses this construction in ordinary prover continuations. Its complete
execution equals the mathematical honest execution, giving support completeness and perfect
completeness under the same true-input and original-oracle assumptions. The compiled runtime
client exercises a quadratic with a cross term over a three-element domain, its retained original
oracle, and execution with no rounds left.

This is a computable finite-enumeration prover; it makes no efficiency claim. Optimized multilinear
algorithms remain separate work.

`Native.roundByRound_soundness` re-derives the full-protocol bound `count * deg / |F|` from the
generic round-by-round theorem described [below](#interaction-layer-security). Its scalar state
reconstructs the current claim from each concrete prefix; a failed sum check produces
public abort, and a successful one uses a fresh challenge. The theorem keeps the arbitrary
effectful prover and allows the ambient interpreter to lose mass. Sumcheck has a
`Unit` witness, since its polynomial is an input oracle, so it has no separate
knowledge-soundness theorem.

`Oracle/Composition` and the earlier `ArbitraryRounds` clients execute sequences of separate
reductions across explicit interfaces. Those execution results do not by themselves establish
soundness for arbitrary strategies on a composed interaction tree. The Sumcheck theorem
follows the actual full-tree execution directly.

`Interaction/CompositionSoundness` proves composition for arbitrary strategies on a plain
appended tree. Its exact execution equation extracts the actual suffix strategy and preserves
all effects under any lawful monad. The suffix counterpart is selected purely from the prefix
path and counterpart output; effects inside that strategy remain unrestricted.

Under lawful distribution semantics, a prefix truth-transition bound `ε₁` and a suffix bound `ε₂`
give a final bound `ε₁ + ε₂`. If suffix soundness requires admissibility, a prefix inadmissibility
bound `δ` gives `ε₁ + δ + ε₂`. The original uniform theorem covers every false, admissible prefix
path and output, including unreachable ones, and every suffix strategy.

The fixed-prover forms require a prefix bound only for the chosen whole prover's actual prefix.
The reachable form requires suffix security only on its structurally supported boundary results;
the almost-everywhere form permits a probability-zero exceptional set. The weighted form averages
branch-dependent suffix errors outside a charged prefix event. The boundary includes the actual
returned prover continuation and private memory. `AppendBoundary` is an abbreviation for that
existing runner output, not another strategy or execution representation.

These bounds concern unconditioned successful-output mass; they need neither losslessness nor
commuting effects. Missing mass is not a classified runtime fault. A two-guess client over
`ZMod 17` instantiates the uniform bound as `2/17`.

Oracle append now preserves the runtime tree and its roles. Concrete path append and split agree
with public path projection, and accumulated access agrees with processing the prefix then the
suffix. `closingImpl_append` and `simulateQ_closingImpl_append` prove that the resulting deterministic
handlers answer all queries identically. These laws apply to supplied concrete paths; they do not
assert that a prover and verifier generated those paths.

The acceptance example selects different suffix shapes through a public Boolean move. Queries to
the initial oracle, prefix message, and suffix messages return `[7, 11, 19]` or `[7, 11, 23, 29]`
under both handlers. It also checks mixed prover/verifier roles and hidden message data.

`Oracle/Sequential.executeStrategies_append` now connects restricted verifier append to the
actual paired run, for every whole prover and dependent private output family. Its prefix
returns an ordinary value; a pure function selects the suffix verifier from that value and the
public prefix path. The suffix uses the actual remaining prover strategy and the handler built
from the original inputs and prefix messages. The final verifier action runs once. This is equality
of open oracle programs, so ambient effects retain their order without a commutativity premise.
Read-only source handlers are deterministic and total; this result introduces no probability claim.

The execution clients retain private memory across a challenge and public abort, check prover-owned
and verifier-owned first suffix moves, and check the terminal action occurs once. A separate
counterexample distinguishes an action before a prover send from moving it after that send.

`Verifier.appendExported` lets the suffix query only the prefix's exported interface and its own
new oracle messages. `executeStrategies_appendExported_close` proves that the composed run and
sequential interpretation return the same concrete path, private prover output, and closed claim.
The intermediate handler is the exported oracle evaluated using the actual prefix resources.
The theorem permits public-path-dependent final statements and oracle families, preserves ambient
effect order, and does not require identical raw and exported query logs.

The exported-interface clients hide a source slot, expand one exported query into two source
queries, and retain private prover memory and the ordered ambient log. A separate client chooses
between different final statement and oracle realization types through a public Boolean, then
checks the actual closed statement and answer in both branches.

`Oracle/CompositionSoundness` proves weighted and uniform bounds for this actual composed oracle
execution. It charges true intermediate claims, false intermediate claims outside the next
protocol's assumptions, and suffix success from false admissible claims. The suffix premise
includes the final verifier action and closing with actual resources. It need only hold almost
everywhere under the chosen whole prover's actual prefix distribution. The uniform bound is
`εtruth + εinvalid + εsuffix`; the weighted bound averages the suffix error instead.

A probability example exports the input value plus a public sample. The suffix queries that
exported oracle and makes a fresh random final decision. Its true-midpoint mass is `1/2`, its
false-inadmissible mass is zero, and its average remaining error is `1/4`, giving a `3/4` bound.
A supported probability-zero branch violates the pointwise suffix bound, exercising the weaker
almost-everywhere premise. True midpoint claims need not satisfy the suffix assumptions; they
have already been charged.

`Sumcheck/Interaction/Composition` proves that the existing Sumcheck execution equals its
first round followed by the remaining rounds through `appendExported`. It uses the same whole
prover, including the actual continuation returned after a challenge or abort. Honest full-protocol
completeness now follows through this execution equation, with its exported statements unchanged.
The soundness proof also applies the generic oracle composition theorem at each round, recovering
`count * deg / |F|` under the existing hypotheses. The previous separate induction is retired.
The final original-polynomial equality remains an output oracle relation, with no added query.

The soundness theorem uses total deterministic source handlers and lawful probability semantics
for the ambient computation. `Oracle/RuntimeSoundness` proves composition
inside a persistent runtime when the client bounds average suffix success over the actual prefix
distribution. This is a separate hypothesis about that runtime, not an automatic transfer of the
Sumcheck bound. The access and cost results below provide separate guarantees about the actual
queries a client issues.

Direct provers can now use `executeStrategiesLoggedRun`, `executeStrategiesWithRuntime`,
and `executeStrategiesPhasedWithRuntime`. They reuse the existing interpreters. Reduction setup
stays inside the same initialized runtime, even when setup makes oracle queries. Erasure retains
the core execution and actual final state; the phased/logged comparison retains paired source
observations and ordered ambient history. These execution laws add no probability assumption.

The runtime client checks counter answers `1, 2, 3` across setup and both protocol stages, final
state `3`, and the exact query order. Another actual exported-interface client checks that one
exported query expands to two source queries, followed by a fresh-message query. Its source answers
are `[7, 1, 2]`. `withQueryLog_simulateQ` records the queries made by the routing programs; it does
not equate one exported log entry with one source entry.

The runtime soundness theorem fixes the whole prover before setup. Its prefix distribution
retains the prover continuation, intermediate claim, runtime state, and ambient history together.
Its bound is the probability of a chosen exceptional prefix event plus the average remaining error.
The suffix receives the actual prefix output; hidden state is handled internally by runtime
resumption. Clients prove the average bound for this experiment. A separate execution equality
retains the final state and history while observing the final closed claim.

The hidden-bit runtime client checks both information patterns. Committing a fixed guess before
learning the secret gives success exactly `1/2` and instantiates the main theorem. Reading the
secret first gives success one and violates that theorem's half-error premise. Conditioning on a
matching fixed secret also gives success one. The tests retain the actual ordered query history,
so the proof cannot silently discard what the prover learned.

Canonical source-query names now come from the concrete prefix's available context. Continuing
execution preserves earlier names; appending a later protocol transports the same names and
messages through its cursor map. Initial names identify raw input queries. Names for received
oracles identify their send edges, preserving sharing across query arguments. A future send cannot
be named by a currently available query.

`Data/OracleComp/QueryBounds` proves access and cost bounds for the actual query substitution.
If each allowed exported query routes only to allowed source queries, the whole routed program
satisfies that access condition. If each route fits its exported query's charge, the routed program
inherits the exported program's total budget. Charges may vary by query; repeated calls to one
shared oracle each incur their cost. Prefix and suffix budgets add, and pure output observations
preserve and reflect the same cost bound. These laws need no probability or independence assumption.

Cost bounds cover complete paths allowed by the query types. The separate access condition also
checks a query whose answer type is empty; a vacuous complete-path cost bound does not authorize it.
A two-send client checks a virtual query that reads the same old oracle twice, followed by
one fresh-oracle query: actual source answers `[1, 1, 2]`, private output `3`, closed statement `4`,
and weighted source budget `5` when old calls cost one and fresh calls cost three. Its phased run
supplies the actual join and terminal prefixes used by those certificates. The prior resource name
is preserved by that run's context inclusion, and the fresh resource fails access at the join.
The phased/logged comparison ties the repeated source calls to the same execution; ambient phase
logs remain distinct from source-query logs.

The resource-certified runtime client imports the same hidden-bit fixture and half-bound theorem
as the persistent-runtime composition client.
It proves that the verifier returns the certified export, that the actual routed suffix uses allowed
queries with cost at most five, and that the complete runtime makes exactly one charged
imported-randomness query. Its actual ambient history costs four under separate weights one for the
dummy query and three for revelation. The informed prover costs seven and succeeds surely.
These are guarantees for those fixed provers, not a theorem that access or cost bounds alone
imply soundness for arbitrary adversaries.

The single-round legacy verifier correspondence identifies scalar outputs for arbitrary sent
polynomials and fixed challenges, including rejection. Both relation directions are proved for
arbitrary claims. This does not relate the legacy-layer and interaction-layer security games.

### Interaction-layer security

The security modules live under `ArkLib/Interaction/Oracle/Security/`, with acceptance clients
under `ArkLibTest/Interaction/Oracle/Security/`.

| Result | Modules and principal declarations | Landed in |
|---|---|---|
| Ordinary round-by-round soundness and its local-to-global theorem | `RoundByRound` (`OrdinaryState`, `ChallengeModel`, `LocalSoundness`, `FreshVerifier`); `Soundness` (`executeStrategies_soundness`, `executeStrategies_soundness_uniform`) | #1261 |
| Backward witness extraction on execution paths | `Knowledge` (`KnowledgeState`, `RoundExtractor`, `KnowledgeCertificate`, `extraction_failure_implies_bad_challenge`); `KnowledgeAppend` | #1259 |
| Knowledge composition at closed intermediate claims | `KnowledgeComposition` (`KnowledgeCertificate.append`, `KnowledgeCertificate.sequential`, `native_badChallenge_bound`) | #1260 |
| State-restoration knowledge soundness | `StateRestoration`, `StateRestorationReplay`, `StateRestorationGame` (`stateRestoration_knowledge_soundness`), `StateRestorationOracle` (`stateRestoration_oracle_knowledge_soundness`) | #1263 |
| Pre-sampled private coins | `StateRestorationCoins` (`stateRestoration_knowledge_soundness_privateCoins` and its oracle-output form) | #1263 |
| Per-round errors | `StateRestorationBudget` (`stateRestoration_oracle_knowledge_soundness_nonuniform`) | #1264 |
| Measured extraction stages | `KnowledgeResources` (`RoundExtractor.MeasuredStages`, `MeasuredKnowledgeCertificate`); `StateRestorationResources` | #1397 |

**Round-by-round soundness.** An `OrdinaryState` is false on a false input, cannot become true at
a prover move, and is true at every successful terminal path. `LocalSoundness` bounds the
probability of a false-to-true transition at every authored verifier prefix, including prefixes of
zero execution probability. `FreshVerifier` connects that challenge model to the actual
verifier actions after closing declared access. From these, `executeStrategies_soundness` bounds
the probability that the actual interpreted execution ends in a successful output by the sum of
the local errors along the challenge schedule; `executeStrategies_soundness_uniform` gives
`count * error`. The prover is an arbitrary strategy. The ambient interpreter uses lawful
subprobability semantics, so a prover that fails to return only lowers the success mass.
Sumcheck instantiates this theorem (`Native.roundByRound_soundness`, above).

**Knowledge certificates.** A `RoundExtractor` names, at every authored node, a backward map from a
witness of the knowledge state after a move or oracle message to a witness of the state before it.
A `KnowledgeCertificate` adds a challenge schedule, prover preservation (prover messages cannot
create knowledge under the named maps), and a bound on the bad-challenge event at every authored
verifier prefix. `extraction_failure_implies_bad_challenge` is the deterministic core: if a
terminal witness is valid and its extracted input witness is not, some verifier challenge on the
same path is bad. A certificate bounds no extraction cost.

**Composition.** `KnowledgeAppend` composes backward extraction through dependent append,
preserving each component's prover law and fixed-prefix bound with the same sampler and error.
In `KnowledgeComposition` the suffix certificate may depend on the actual first-stage path and on
the closed middle claim of that execution. `native_badChallenge_bound` applies a certificate's
local bound to the actual interpreted receiver action when the verifier satisfies
`SamplesChallenges`.

**State restoration.** The protocol is a fixed-round public-coin protocol on an interaction tree. Each
restoration key holds the input, round, prover-message prefix and salt prefix, and challenges come
from one cached random oracle. The adversary chooses the input, all messages and salts, and an
output witness after adaptive queries, with at most `Q` queries in total. For `k` rounds,
`stateRestoration_knowledge_soundness` bounds by `(Q + k) * error` the probability that the output
relation holds while the named backward extraction fails. The actual verifier runs on the
completed challenges, and its execution equation is proved from the paired runner.
`stateRestoration_oracle_knowledge_soundness` gives the same bound when the verifier returns an
open oracle claim and the relation observes its closed behavior under that path's handler;
rejection is unsuccessful. With per-round errors `error_j`,
`stateRestoration_oracle_knowledge_soundness_nonuniform` gives
`Q * max_j error_j + Σ_j error_j`. The `privateCoins` forms keep the `(Q + k) * error` bound when
the adversary's possibly failing private coins are sampled before the fresh cached game; they do
not cover arbitrary interleaving of coin and oracle effects. Inputs and salts may have infinite
types; each round's challenges use a finite nonempty uniform sampler.

**Measured extraction.** `RoundExtractor.stageMap` combines the backward maps at a node into one
stage. `RoundExtractor.MeasuredStages` names, for the stage at every authored node, a budgeted
program (`OracleComp.BudgetedProgram`) that realizes it, and `MeasuredKnowledgeCertificate` adds
these stages to a `KnowledgeCertificate` for the same extractor.
`MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` conjoins the
state-restoration bound with a uniform stage budget for that extractor. Budgets count declared
instructions only. Views, handlers, witness-carrier identifications, stage composition and
knowledge predicates are uncharged, and every function has a zero-budget program, so only a named
program with a stated instruction set is evidence. This is the interaction-layer form of the
measured-operation contract in the [extractor-efficiency chapter](03a-extractor-efficiency.md).

**Open.** There is no interaction-layer rewinding extractor and no Fiat–Shamir or BCS bridge from state
restoration. The `privateCoins` forms are the only randomized-adversary state-restoration results;
coin sampling interleaved with oracle queries is not covered. No protocol under
`ArkLib/ProofSystem/` instantiates the interaction-layer knowledge or state-restoration certificates yet;
their clients are the acceptance examples. The [design roadmap](05-roadmap.md) lists this work.

## Legacy oracle-reduction layer

`ArkLib/OracleReduction/` uses `ProtocolSpec n`. The protocol developments on `main` (FRI, Binius,
ring switching, Spartan, Plonk, Hachi and others) use this layer; their status is on the public
[roadmap](../../ROADMAP.md). The following legacy results matter for interaction-layer design.

- **One round-by-round notion.** `Verifier.rbrSoundness` and `Verifier.rbrKnowledgeSoundness`
  in `Security/RoundByRound.lean` bound the bad event at every fixed transcript prefix. The
  prover-averaged and one-shot variants were removed (#1413, #1421).
  `Verifier.forall_rbrSoundness_iff_rbrKnowledgeSoundness_iff` in `Security/Implications.lean`
  shows that round-by-round soundness of the induced languages coincides with round-by-round
  knowledge soundness, for all relations and errors, exactly when
  `Nonempty WitIn ∨ IsEmpty (StmtIn × FullTranscript pSpec × WitOut)` (#1396).
- **Unbounded and measured extraction.** `Security/UnboundedExtraction.lean` proves
  `Verifier.knowledgeSoundness_iff_relationSoundness` through the classical selector
  `Extractor.Straightline.choose` (#1364). `Security/Resources.lean` adds
  `Verifier.knowledgeSoundnessWithResources`, and FRI's
  `knowledgeSoundnessWithResources_extract` certifies operation counts for its named extractor
  (#1370).
- **Guarded composition and bridges.** `Append/Security.lean` proves ordinary soundness and
  knowledge soundness under a guarded first verifier and suffix bounds valid from every
  deterministic shared oracle state, with pure extractors for knowledge soundness.
  `Append/GuardedRoundByRound.lean` and `Sequential/GuardedRoundByRound.lean` compose
  round-by-round knowledge soundness for binary and finite chains. `Security/GuardedBridges.lean`
  and `Security/GuardedSoundness.lean` derive ordinary knowledge soundness and soundness from
  round-by-round guarantees of a guarded verifier, with the sum of the per-challenge errors.
- **End-to-end protocols.** Spartan, Plonk, Binary Basefold, FRI-Binius and the full Sumcheck
  reduction obtain ordinary knowledge soundness through these guarded interfaces; their theorems
  and error bounds are on the public [roadmap](../../ROADMAP.md). For interaction-layer design, they
  fix the statements and errors that a port must reproduce or relate to.
- **Retired.** The legacy state-restoration definitions (#1409) and the duplex-sponge
  Fiat–Shamir skeleton (#1368) were removed; state restoration now exists only in the interaction layer.

These legacy results do not relate the legacy-layer and interaction-layer security games. The single-round
Sumcheck correspondence above identifies verifier outputs, not security notions.

The preserved `archive/oracle-reduction-v2-pre-split` branch contains the earlier interaction-layer
prototype and protocol ports (FRI, Spartan, Fiat–Shamir, BCS, boundary transport, security
notions). It is a source bank, not a merge base. Its code uses pre-`TypeTree` PolyFun names and
older VCVio semantics, so each port is rewritten and re-audited on a fresh ArkLib base.
Spartan and Plonk are now end-to-end on the legacy layer; their interaction-layer ports have not started.

## Where the remaining work is specified

The [roadmap](05-roadmap.md) owns the implementation sequence. The
[core design](02-oracle-reduction-core.md#5-composition) explains oracle-interface and execution
constraints; the [security design](03-adversarial-oracle-execution.md#4-games-and-ordinary-soundness-composition) explains the intended
probability and persistent-world theorems. These are plans beyond the proved results listed here.

Supported execution closes a claim with resources from the same run. The general `closeWith`
helper accepts a handler; its type alone does not establish execution provenance. Security
statements therefore use the actual runner distribution, rather than arbitrary constructed records.
