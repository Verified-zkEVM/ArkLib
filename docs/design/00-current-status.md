# Current status

**Status date:** 2026-09-26. **Scope:** the supported dependency baseline, what the typed
oracle-reduction layer provides in this source revision, and its remaining proof gaps.

The typed core, the first world-backed execution artifacts, and the Sumcheck acceptance slices have
landed (AR-1 through AR-10B; ArkLib #851–#892). Native full-protocol Sumcheck now has a
verifier with explicit abort and soundness against arbitrary native prover continuations. Plain
native interaction now has additive composition soundness, including an explicit admissibility
error. No declaration under `ArkLib/Interaction/` or
`ArkLib/ProofSystem/Sumcheck/Interaction/` uses `sorry`. The [roadmap](05-roadmap.md) defines the next implementation steps and links their tracking issues.

## Results in open PRs

As of 2026-10-04, open PRs add round-by-round soundness, knowledge soundness under composition,
state-restoration knowledge soundness, and a real-to-ideal transfer for Merkle openings. None of
them is merged, so this page does not count them. The
[area roadmap](../../roadmap/interaction-migration.md) lists each PR with its statement and
limits. The missing-capability statements below describe `main`.

## Supported baseline

| Repository | Revision | Role |
|---|---|---|
| VCVio | `d7089e46d69e07640fa23b5ae6b1b966f1d4b949` | direct ArkLib dependency |
| PolyFun | `3710d71b28404a151b8d1f0ce080ea448778dec0` | revision selected and tested by VCVio |
| Lean | `v4.34.0` | common toolchain |

ArkLib does not override PolyFun independently. VCVio owns the tested PolyFun revision. A later
PolyFun update reaches ArkLib only after VCVio advances and validates its pin.

The train moved from the alignment baseline (Lean 4.33.1, VCVio `f9dc47d9`, PolyFun `c0c92369`)
through the VCVio `Runtime`/`WithFailure` additions used by #884 and the Lean 4.34 native-measure
upgrade (#903, #913). ArkLib's PMF probability surface is retired; new observation boundaries use
VCVio measure semantics.

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
| Closed probability semantics | available | native `Measure`/kernel semantics; ArkLib's PMF surface is retired (#913) |
| Probabilistic responders and wired machines | available | reuse `ProbResponder`, oracle strategies, and machine runs |
| Strict oracle-PPT certificates | available | reuse ranked resources and `HandlerCertificate` |
| Shared-ROM Merkle extraction | available | adapt the primitive theorem; do not restate its game in ArkLib |
| Runner-produced resumable execution artifact | available | `OracleRuntime`, `RunResult`, `run`, `resume`, `GeneratedBy` in `VCVio.OracleComp.Runtime`; used by `executeWithRuntime` |
| Failure-to-return mass boundary | available | `evalDistWithFailure` in `VCVio.EvalDist.WithFailure`; used by `Terminal.observe` |
| Certified query-trace transducer specialization | **missing** | waits on the generic PolyFun transducer |
| General conditioning/dynamic-programming facade | incomplete | specific theorems exist, but not the reusable state-restoration boundary |
| Error-bearing and cost-bearing reduction package | incomplete | `ReductionWithCost` handles cost; later clients still need explicit additive/substitution error transport |

Accept/reject/fault classification is protocol-level and lives in ArkLib (`Interaction.Terminal`).
VCVio supplies only the separate failure-to-return mass, so the two kinds of absence are not
identified.

These gaps are integration boundaries, not permission to introduce ArkLib-private probability,
trace, or cost semantics. The first client should either add the smallest upstream API or provide a
temporary adapter with an upstream issue and a deletion test.

### ArkLib

The typed layer lives under `ArkLib/Interaction/` and `ArkLib/ProofSystem/Sumcheck/Interaction/`,
with acceptance clients under `ArkLibTest/Interaction/` and `ArkLibTest/ProofSystem/Sumcheck/`.
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
| Direct native strategy execution | `Oracle/CoreRun.executeStrategiesCore` | #1216 |
| Direct native logged, phased, and persistent-runtime execution | `Oracle/LoggedRun`, `Oracle/PhasedRun`, `Oracle/Runtime` | #1236 |
| Native composition inside one persistent runtime | `Oracle/RuntimeSoundness` | [#1237](https://github.com/Verified-zkEVM/ArkLib/pull/1237) |
| General native composition soundness | `Interaction/CompositionSoundness` | #1218 |
| Restricted verifier composition for every whole native prover | `Oracle/Sequential.executeStrategies_append` | #1233 |
| Composition through exported oracle interfaces and actual claim closing | `Oracle/SourceRouting.executeStrategies_appendExported_close` | #1234 |
| Weighted and uniform soundness for exported oracle composition | `Oracle/CompositionSoundness` | [#1235](https://github.com/Verified-zkEVM/ArkLib/pull/1235) |
| Available query names preserved by continuation and append | `Oracle/Prefix`, `Oracle/Access` | this revision; [#1229](https://github.com/Verified-zkEVM/ArkLib/issues/1229) |
| Actual-route access and weighted query budgets | `Data/OracleComp/QueryBounds` | this revision; [#1229](https://github.com/Verified-zkEVM/ArkLib/issues/1229) |
| Oracle append paths, runtime roles, access, and query answers | `Oracle/TypeTree`, `Oracle/TypeTree/Decoration`, `Oracle/Access`, `Oracle/RunSources` | #1232 |
| Fixed-prover, reachable, and averaged native bounds | `run_appendFlat_soundness_fixed`, `_of_support`, `_ae`, and `_weighted_ae` | #1231 |

Sumcheck on the typed layer:

| Result | Evidence | Landed in |
|---|---|---|
| One-round honest completeness through closing | `SingleRound`, `Closing` | #872 |
| Legacy correspondence | `legacy_input_iff`, `legacy_output_iff`, `legacy_honest_verifier_correspondence` | #874 |
| Round relations via multivariate projection | `Projection`, `ProjectionTransport` | #879 |
| One-round reduction soundness, error `deg` over the field size | `executeCommitted_soundness`, `executeRandomCommitment_soundness` and measure forms | #881 |
| Two sequential rounds through the actual closed claim | `MultivariateRound`, `Sequential` | #883 |
| Arbitrary consecutive rounds, honest completeness | `executeRoundsSampled_perfectCompleteness`, `executeRounds_uniform_perfectCompleteness` and measure forms | #892 |
| Actual multivariate round soundness | `MultivariateRound.executeCore_sampled_soundness` | — |
| Native full-protocol soundness | `Native.execute_soundness` in `ProtocolSoundness` | #1214 |
| Native honest completeness | `Native.execute_support_completeness`, `Native.execute_perfectCompleteness` in `ProtocolCompleteness` | #1214 |
| Computable round messages and verifier | `Impl/Representation`, `Interaction/Computable` | — |
| Soundness for computable-message strategies | `Computable.execute_soundness` in `ComputableSoundness` | — |
| Computable honest messages and original oracle | `Impl/Projection` | — |
| Completeness for the computable honest prover | `Computable.execute_support_completeness`, `Computable.execute_perfectCompleteness` | — |

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
`count * deg / |F|` for fresh uniform challenges. The honest native strategy sends the projected
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
native path, including private memory, effect order and rejection, with fixed test challenges.

`Impl/Projection` constructs each honest round message directly from a CompPoly multivariate
polynomial. It splits out the current variable, evaluates the other variables at prior challenges
and every remaining domain point, and sums the resulting univariate polynomials. The proved
correspondence covers arbitrary individual degree bounds and finite domains. `inputImpl` evaluates
the original CompPoly polynomial directly; its equality to the mathematical oracle behavior is a
separate theorem.

`Computable.honestProver` uses this construction in ordinary native continuations. Its complete
execution equals the mathematical honest execution, giving support completeness and perfect
completeness under the same true-input and original-oracle assumptions. The compiled runtime
client exercises a quadratic with a cross term over a three-element domain, its retained original
oracle, and execution with no rounds left.

This is a computable finite-enumeration prover; it makes no efficiency claim. Optimized multilinear
algorithms, native round-by-round and knowledge-security definitions, and extraction remain
separate work. Legacy declarations with admissions are not repaired by these results.

`Oracle/Composition` and the earlier `ArbitraryRounds` clients execute sequences of separate
reductions across explicit interfaces. Those execution results do not by themselves establish
soundness for arbitrary strategies on a composed interaction tree. The native Sumcheck theorem
follows the actual full-tree execution directly.

`Interaction/CompositionSoundness` proves composition for arbitrary strategies on a plain native
appended tree. Its exact execution equation extracts the actual suffix strategy and preserves
all effects under any lawful monad. The suffix counterpart is selected purely from the prefix
path and counterpart output; effects inside that strategy remain unrestricted.

Under lawful distribution semantics, a prefix truth-transition bound `ε₁` and a suffix bound `ε₂`
give a final bound `ε₁ + ε₂`. If suffix soundness requires admissibility, a prefix inadmissibility
bound `δ` gives `ε₁ + δ + ε₂`. The original uniform theorem covers every false, admissible prefix
path and output, including unreachable ones, and every native suffix strategy.

The fixed-prover forms require a prefix bound only for the chosen whole prover's actual prefix.
The reachable form requires suffix security only on its structurally supported boundary results;
the almost-everywhere form permits a probability-zero exceptional set. The weighted form averages
branch-dependent suffix errors outside a charged prefix event. The boundary includes the actual
returned prover continuation and private memory. `AppendBoundary` is an abbreviation for that
existing runner output, not another strategy or execution representation.

These bounds concern unconditioned successful-output mass; they need neither losslessness nor
commuting effects. Missing mass is not a classified runtime fault. A native two-guess client over
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
actual paired run, for every whole native prover and dependent private output family. Its prefix
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

`Sumcheck/Interaction/Composition` proves that the existing native Sumcheck execution equals its
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

Direct native provers can now use `executeStrategiesLoggedRun`, `executeStrategiesWithRuntime`,
and `executeStrategiesPhasedWithRuntime`. They reuse the existing interpreters. Reduction setup
stays inside the same initialized runtime, even when setup makes oracle queries. Erasure retains
the core execution and actual final state; the phased/logged comparison retains paired source
observations and ordered ambient history. These execution laws add no probability assumption.

The runtime client checks counter answers `1, 2, 3` across setup and both protocol stages, final
state `3`, and the exact query order. Another actual exported-interface client checks that one
exported query expands to two source queries, followed by a fresh-message query. Its source answers
are `[7, 1, 2]`. `withQueryLog_simulateQ` records the queries made by the routing programs; it does
not equate one exported log entry with one source entry.

The runtime soundness theorem fixes the whole native prover before setup. Its prefix distribution
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
A two-send native client checks a virtual query that reads the same old oracle twice, followed by
one fresh-oracle query: actual source answers `[1, 1, 2]`, private output `3`, closed statement `4`,
and weighted source budget `5` when old calls cost one and fresh calls cost three. Its phased run
supplies the actual join and terminal prefixes used by those certificates. The prior resource name
is preserved by that run's context inclusion, and the fresh resource fails access at the join.
The phased/logged comparison ties the repeated source calls to the same execution; ambient phase
logs remain distinct from source-query logs.

The resource-certified runtime client imports C7's same hidden-bit fixture and half-bound theorem.
It proves that the verifier returns the certified export, that the actual routed suffix uses allowed
queries with cost at most five, and that the complete native runtime makes exactly one charged
imported-randomness query. Its actual ambient history costs four under separate weights one for the
dummy query and three for revelation. The informed prover costs seven and succeeds surely.
These are guarantees for those fixed native provers, not a theorem that access or cost bounds alone
imply soundness for arbitrary adversaries.

The legacy verifier correspondence is honest-execution only: the legacy verifier reads the input
polynomial for its next target, while the typed verifier reads the sent polynomial. Both relation
directions are proved for arbitrary claims.

The legacy `OracleReduction` layer remains in use. Its carrier is `ProtocolSpec n`; several
unrestricted stateful composition theorems remain admitted. Existing legacy repairs are tracked
separately in [#676](https://github.com/Verified-zkEVM/ArkLib/issues/676). The native results above
do not remove admissions from legacy clients.

The preserved `archive/oracle-reduction-v2-pre-split` branch contains the earlier interaction-native
prototype and protocol ports (FRI, Spartan, Fiat–Shamir, BCS, boundary transport, security
notions). It is a source bank, not a merge base. Its code uses pre-`TypeTree` PolyFun names and
older VCVio semantics, so each port is rewritten and re-audited on a fresh ArkLib base.

## Where the remaining work is specified

The [roadmap](05-roadmap.md) owns the implementation sequence. The
[core design](02-oracle-reduction-core.md#5-composition) explains oracle-interface and execution
constraints; the [security design](03-adversarial-oracle-execution.md#4-games-and-ordinary-soundness-composition) explains the intended
probability and persistent-world theorems. These are plans beyond the proved results listed here.

Supported execution closes a claim with resources from the same run. The general `closeWith`
helper accepts a handler; its type alone does not establish execution provenance. Security
statements therefore use the actual runner distribution, rather than arbitrary constructed records.
