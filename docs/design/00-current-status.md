# Current status

**Last reviewed:** 2026-11-04. **Scope:** the supported dependency baseline, what the interaction
layer (`ArkLib/Interaction/`) provides on `main`, and the legacy-layer results that
bear on it. The
[README](../../README.md#two-layers) gives an overview of the two layers,
[Limitations of the legacy layer](legacy-layer-limitations.md) explains why the
interaction layer replaces it, and the [roadmap](../../ROADMAP.md#priority-replace-the-legacy-layer)
holds the migration plan. Protocol-level status for readers
outside the framework is on the public [roadmap](../../ROADMAP.md); remaining interaction-layer
design work is in the [design roadmap](05-roadmap.md).

The interaction core, its logged execution and oracle composition have landed; the
[ArkLib tables](#arklib) list them. On top of them the interaction layer now has these generic
results:

- round-by-round soundness on execution prefixes, and the theorem that it implies soundness;
- round-by-round knowledge soundness through knowledge state functions, backward extraction along
  transcripts, and its composition across a deterministic middle claim;
- state-restoration knowledge soundness for fixed-round public-coin protocols, including oracle
  outputs, pre-sampled private coins and per-round errors;
- measured extraction stages: operation-count budgets for the named backward witness maps;
- Sumcheck with soundness, completeness, round-by-round soundness, and a computable verifier
  and honest prover.

The knowledge, state-restoration and measured-extraction results are generic definitions and
theorems. What remains open is their use: no protocol under `ArkLib/ProofSystem/` instantiates
them yet, there is no interaction-layer rewinding extractor, and state restoration does not yet
cover an adversary whose private randomness interleaves with its oracle queries (see
[below](#interaction-layer-security)).

No declaration under `ArkLib/` uses `sorry` outside the one solicited proof recorded in
`scripts/axiom_baseline.json` (a correlated-agreement lower bound, issue
[#1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352)); it is not under
`ArkLib/Interaction/` or `ArkLib/ProofSystem/Sumcheck/`.

## Supported baseline

The exact dependency revisions are in [`lake-manifest.json`](../../lake-manifest.json) and the
toolchain in [`lean-toolchain`](../../lean-toolchain); the supported Lean version is `v4.36.0`.

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
| Failure-to-return mass boundary | available | `evalDistWithFailure` in `PolyFun.Control.Monad.Measure.WithFailure`, which keeps missing runtime mass separate from rejection |
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
| Stateless weighted handler substitution | available | `WorstCaseCostBound.simulateQ` in `VCVio.OracleComp.QueryTracking.CostModel.Simulation`; transfers bounds through stateless handlers with per-query completed-run budgets; availability and termination are separate |
| Named measured programs and composition | available | `MeasuredProgram`, `BudgetedProgram`, and `MeasuredProgram.comp` in `VCVio.OracleComp.QueryTracking.MeasuredProgram` and its `Composition` module; both instruction traces run and weighted budgets add; views, handlers and pure work remain uncharged |
| Cost-aware reductions | available, cost-only | reuse `SecurityGame.ReductionWithCost`; add no parallel cost hierarchy |
| Closed probability semantics | available | VCVio's native `Measure`/kernel semantics; ArkLib's PMF surface is retired (#913) |
| Probabilistic responders and wired machines | available | reuse `ProbResponder`, oracle strategies, and machine runs |
| Strict oracle-PPT certificates | available | reuse ranked resources and `HandlerCertificate` |
| Shared-ROM Merkle extraction | available | adapt the primitive theorem; do not restate its game in ArkLib |
| Runner-produced resumable execution artifact | available | `OracleRuntime`, `RunResult`, `run`, `resume`, `GeneratedBy` in `VCVio.OracleComp.Runtime`; used by `executeWithRuntime` |
| Certified query-trace transducer specialization | **missing** | waits on the generic PolyFun transducer |
| General conditioning/dynamic-programming facade | not needed so far | the interaction-layer state-restoration proofs use the cached `randomOracle`, `IsTotalQueryBound` and its cost-distribution lemmas directly; add a facade only for a client that needs it |
| Error-bearing and cost-bearing reduction package | incomplete | `ReductionWithCost` handles cost; later clients still need explicit additive/substitution error transport |

A core verdict is an `Option`: `none` is rejection. `OracleVerifier.decideCatching` in
`Interaction/Oracle/LoggedExecution.lean` keeps the label of a handler failure. The core keeps
missing runtime mass separate from rejection. PolyFun supplies the failure-to-return mass observed by
ArkLib.

These gaps are integration boundaries, not permission to introduce ArkLib-private probability,
trace, or cost semantics. The first client should either add the smallest upstream API or provide a
temporary adapter with an upstream issue and a deletion test.

### ArkLib

The interaction layer is the interaction core under `ArkLib/Interaction/` (namespace
`Interaction`), with acceptance clients under `ArkLibTest/Interaction/`. Its Sumcheck
client lives under `ArkLib/ProofSystem/Sumcheck/`, with acceptance clients under
`ArkLibTest/ProofSystem/Sumcheck/`. Naming follows
[`docs/wiki/interaction-naming.md`](../wiki/interaction-naming.md).

The old generic layer has been deleted. At commit `8472a86f` it consisted of
`ArkLib/Interaction/Oracle/`, `Interaction/Reduction.lean` and
`Interaction/CompositionSoundness.lean`, beside the core's former `Core/` directory. Some of those
paths now hold core modules. The
[migration list](interaction-layer/migration-list.md) maps every deleted module and test to its
core counterpart or records why it was retired.

| Area | Modules under `Interaction/` | Landed in |
|---|---|---|
| Signatures, protocol trees, transcripts and outcomes | `Signature`, `Protocol`, `Transcript` | #1473, #1564 |
| Provers, passive verifiers and plain execution | `Reduction`, `Execution`, `OracleVerifier` | #1473 |
| Sequential composition | `Composition` | #1473 |
| Finite heterogeneous stage chains | `StageChain` | #1477 |
| Logged execution, queries by move, routing and sent oracle messages | `Oracle/LoggedExecution`, `Oracle/QueriesByMove`, `Oracle/QueriesByMoveLaws`, `Oracle/Routing`, `Oracle/SentOracles` | #1475, #1567 |
| Oracle bundle operations and weighted cost of routed programs | `Oracle/BundleOps`, `Oracle/Cost` | #1476 |
| Completeness, soundness, round-by-round security and extraction interfaces | `Security/Completeness`, `Security/Soundness`, `Security/RoundByRound`, `Security/Knowledge` | #1473 |
| Composition soundness | `Security/CompositionSoundness` | #1485 |
| Round-by-round soundness implies soundness | `Security/Implications` | #1486 |
| Knowledge composition and measured extraction | `Security/KnowledgeComposition`, `Security/KnowledgeComposition/Extraction`, `Security/MeasuredExtraction` | #1482 |
| State restoration with per-round errors | `Security/StateRestoration`, `Security/StateRestorationBudget` | #1483 |
| Agreeing oracle verifiers | `Security/Agreement` | #1484 |
| Embedding of legacy reductions and security transfers | `Legacy/*`, `LegacyAppend`; see [legacy-embedding.md](interaction-layer/legacy-embedding.md) | #1480, #1481 |

Sumcheck on the interaction layer is the Sumcheck core. The frozen Sumcheck interaction layer under
`ArkLib/ProofSystem/Sumcheck/Interaction/` has been deleted; its last version is at commit
[`7cd7828303`](https://github.com/Verified-zkEVM/ArkLib/tree/7cd7828303ca4077dcad586709e604a062d9b57e/ArkLib/ProofSystem/Sumcheck/Interaction/).
[`interaction-layer/sumcheck.md`](interaction-layer/sumcheck.md) lists the core modules, gives the
exact scope of each theorem and maps every deleted declaration to its core counterpart.

| Result | Evidence | Landed in |
|---|---|---|
| Protocol, compatibility verifier and direct honest completeness | `protocol`, `verifier`, `perfectCompleteness` in `Protocol`, `Execution`, `Completeness` | #1474 |
| Full-run soundness of the indexed verifier, error `n * deg` over the size of `R` | `indexedVerifier_soundness` in `Indexed`; `indexedVerifier_run_soundness` and its list and injective forms in `Soundness` | #1484 |
| Round-by-round soundness, error `deg` over the size of `R` at every challenge | `indexedVerifier_rbrSoundness` in `Indexed` | #1484 |
| One-round soundness for a committed or randomized message | `indexedVerifier_committed_soundness`, `indexedVerifier_randomized_soundness` and measure forms in `Soundness` | #1484 |
| Equivalence with the embedded legacy verifier, and transfer of legacy security | `run_eq_legacy`, `verifier_agrees` in `LegacyEquivalence`; `LegacySoundness`, `Knowledge`, `RoundByRound` | #1484 |
| Single-round legacy correspondence | `simpleLegacyVerifier_correspondence` in `LegacyEquivalence` | #1484 |
| Interval verifiers: completeness for every bounded interval, soundness for suffixes | `intervalVerifier_perfectCompleteness` in `IntervalCompleteness`; `intervalVerifier_soundness` in `IntervalSoundness`; `intervalRoundExecute_soundness` in `IntervalRoundSoundness` | #1488 |
| Computable instance at CompPoly messages and inputs | `Computable.verifier`, `Computable.honestProver`, `Computable.perfectCompleteness`, `Computable.interval_soundness` in `Computable` | #1487 |
| Computable honest messages and original oracle | `Impl/Projection` | #1243 |

`indexedVerifier` is a passive verifier over an arbitrary finite indexed domain. Each round sends
a degree-bounded polynomial as an oracle message and draws a challenge. The prover is an ordinary
strategy whose continuations keep private memory and may perform effects after each challenge.
The verifier queries each sent polynomial for its sum check and next target, and its output oracle
is the original input polynomial. The output relation says that this polynomial, evaluated at the
full challenge vector, equals the final target; it is a relation on the output, not a final
verifier query. From a false input claim, soundness bounds by `n * (deg / |R|)` the probability
that the run returns a claim satisfying that relation, for every prover and fresh uniform
challenges, over a finite commutative semiring with `IsDomain`. Sumcheck has a `Unit` witness,
since its polynomial is an input oracle. Its knowledge-soundness theorems in `Knowledge` and
`RoundByRound` are transfers from the legacy layer.

The Sumcheck core now owns a protocol and verifier generic in the message carrier and its
evaluation operation (`protocolOn`, `verifierOn`). The existing polynomial names remain their
Mathlib instances. `Sumcheck.Computable` specializes the same definitions to bounded
CompPoly coefficient arrays, Horner evaluation and CompPoly multivariate input data.
`run_eq_interpret` relates complete runs through the proof-only message interpretation and
challenge-query renaming, preserving private continuations and effects. Its `perfectCompleteness`
holds for arbitrary challenge implementations, and `soundness` keeps the per-challenge error
`deg / |F|` for uniform challenges and arbitrary provers. The relations read the input through its
mathematical polynomial interpretation.

`sumcheck-runtime` runs this computable core instance with fixed test challenges. It checks
private memory and effect order, including both challenge draws after a failed first check,
the honest quadratic run, zero rounds from a final round state with no draws, and one round of
the CompPoly interval verifier after a challenge prefix. The executable emits eight checks, and
the degree bound of the quadratic input is a compile-time proof. The eight runtime rows and their
expected values are listed in
[`interaction-layer/sumcheck.md`](interaction-layer/sumcheck.md#runtime-checks).

`Impl/Projection` constructs each honest round message directly from a CompPoly multivariate
polynomial. It splits out the current variable, evaluates the other variables at prior challenges
and every remaining domain point, and sums the resulting univariate polynomials. The proved
correspondence covers arbitrary individual degree bounds and finite domains. `inputImpl` evaluates
the original CompPoly polynomial directly; its equality to the mathematical oracle behavior is a
separate theorem.

`Sumcheck.Computable.honestProver` uses this construction in ordinary prover continuations.
`interpretProver_honestProver` identifies it with the mathematical core honest prover; the run
correspondence transfers support completeness and perfect completeness on true inputs. The
compiled client evaluates the retained CompPoly input directly.

This is a computable finite-enumeration prover; it makes no efficiency claim. Optimized multilinear
algorithms remain separate work.

**Composition.** `Composition.lean` appends provers, samplers and passive verifiers. The composed
decision runs after the whole interaction: it is the prefix decision followed by the suffix
decision on routed data. `OracleVerifier.run_append` in `Oracle/Routing.lean` splits a run of an
appended oracle verifier against an arbitrary prover into the two interactions and the two
decisions. The statement is an equality of open oracle programs, so the order of ambient and
challenge queries is preserved exactly. `StageChain` composes a finite chain of passive oracle
verifiers whose statement types and oracle families may change at every stage.

Every oracle verifier in the core is passive: its only moves before the final decision are
challenge draws, and every bundle query happens in the final decision. The old layer allowed
verifier queries during the interaction. The [migration list](interaction-layer/migration-list.md)
records which of its results needed this premise and which mechanisms were retired.

`Security/CompositionSoundness.lean` splits an arbitrary strategy on an appended interaction at the
seam into its prefix and the actual suffix strategy that the prefix returns, with its private
memory and effects. The uniform bounds (`Verifier.append_soundness`,
`OracleVerifier.append_soundness_ae`) are `ε₁ + δ + ε₂`: `ε₁` bounds reaching a good boundary,
`δ` bounds reaching an inadmissible one, and `ε₂` bounds the resumed run from almost every other
boundary. The weighted bounds integrate the suffix error over the actual boundary distribution.
The runtime results transport a bound on the resumed success to a persistent `OracleRuntime`.
These bounds concern unconditioned successful-output mass; they need neither losslessness nor
commuting effects.

**Logged execution and cost.** `OracleVerifier.runWithLog` in `Security/Knowledge.lean` records the
prover's ambient queries and every query of the decision, and forgetting both logs gives
`OracleVerifier.run` exactly. `Oracle/QueriesByMove.lean` records the queries of a run move by
move, and `Oracle/QueriesByMoveLaws.lean` proves that erasing the entries gives the aggregate logs.
`OracleMap.withAmbient_worstCaseCost` in `Oracle/Cost.lean` transfers a weighted cost bound through
an oracle map with VCVio's `WorstCaseCostBound.simulateQ`. The full-log runner and the cost lemma
keep some indices in `Type`; ArkLib accepts both restrictions as upstream limits, which the
[migration list](interaction-layer/migration-list.md#unresolved-rows-and-options) records.

The deleted Sumcheck interaction layer applied the old composition theorem in
[`Sumcheck/Interaction/Composition`](https://github.com/Verified-zkEVM/ArkLib/blob/7cd7828303ca4077dcad586709e604a062d9b57e/ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean).
The Sumcheck core does not use it. `FoldComposition` and `BehaviorComposition` prove append
equations for its folds and public intervals, and its soundness proofs go through round-by-round
soundness.

The single-round legacy verifier correspondence identifies scalar outputs for arbitrary sent
polynomials and fixed challenges, including rejection. Both relation directions are proved for
arbitrary claims. This does not relate the legacy-layer and interaction-layer security games.

### Interaction-layer security

The security modules live under `ArkLib/Interaction/Security/`, with acceptance clients
under `ArkLibTest/Interaction/Security/`. The disposition records in
[`interaction-layer/`](interaction-layer/migration-list.md) map every result of the deleted
old-layer security modules to these modules.

| Result | Modules and principal declarations | Landed in |
|---|---|---|
| Completeness, soundness and round-by-round definitions | `Completeness`, `Soundness`, `RoundByRound` (`rbrSoundness`, `KnowledgeStateFunction`, `rbrKnowledgeSoundness`) | #1473 |
| Round-by-round soundness implies soundness | `Implications` (`prEvent_runPrefixChallenges_soundness`, `Verifier.soundness_of_rbrSoundness_uniform`, `OracleVerifier.soundness_of_rbrSoundness_uniform`) | #1486 |
| Composition soundness | `CompositionSoundness` (`Verifier.append_soundness`, `OracleVerifier.append_soundness_ae`, weighted and runtime forms) | #1485 |
| Knowledge composition | `KnowledgeComposition` (`rbrKnowledgeSoundness_append_prefix`, `Verifier.rbrKnowledgeSoundness_append_prefix`, `OracleVerifier.validAcceptance_append`); `KnowledgeComposition/Extraction` (`KnowledgeStateFunction.LocallyBounded`) | #1482 |
| Measured extraction stages | `MeasuredExtraction` (`KnowledgeStateFunction.MeasuredStages`, `MeasuredStages.programAlong`, `MeasuredKnowledgeStateFunction`) | #1482 |
| State-restoration knowledge soundness, with pre-sampled private coins | `StateRestoration` (`stateRestoration_knowledge_soundness`, `stateRestoration_oracle_knowledge_soundness` and their `privateCoins` forms) | #1483 |
| Per-round errors | `StateRestorationBudget` (`stateRestoration_oracle_knowledge_soundness_nonuniform`, `MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform`) | #1483 |
| Agreeing oracle verifiers | `Agreement` | #1484 |

**Round-by-round soundness.** A false statement can be accepted only if some challenge node on the
run's path turns the round-by-round state from false to true. `Implications` bounds soundness by
the supremum, over shape paths, of the sum of the node errors along the path. The bounds apply to
any lawful monad with distribution semantics, and the run may lose mass in a subprobability monad.
`Sumcheck.indexedVerifier_soundness` applies `OracleVerifier.soundness_of_rbrSoundness_uniform`.

**Knowledge state functions.** A `KnowledgeStateFunction` carries intermediate witnesses and names,
at every move, a backward map from a witness after the move to a witness before it.
`rbrKnowledgeSoundness` asks for such a function whose local error at every receiver prefix is
bounded before the challenge is drawn. The backward maps are total functions with no
computational restriction. `KnowledgeComposition` composes these bounds across a deterministic
middle claim.

**State restoration.** Each round sends an oracle message and then draws a uniform public challenge.
Each restoration key holds the input, the prover messages and a salt for every round up to its
own, and challenges come from one cached random oracle. The adversary chooses the input, all
messages and salts, and an output witness after adaptive queries, with at most `Q` queries in
total. For `k` rounds, `stateRestoration_knowledge_soundness` bounds by `(Q + k) * error` the
probability that the output relation holds while the named backward extraction fails.
`stateRestoration_oracle_knowledge_soundness` gives the same bound for the closed-oracle game, in
which rejection is unsuccessful. With per-round errors `error_j`,
`stateRestoration_oracle_knowledge_soundness_nonuniform` gives
`Q * max_j error_j + Σ_j error_j`. The `privateCoins` forms keep the `(Q + k) * error` bound when
the adversary's possibly failing private coins are sampled before the fresh cached game; they do
not cover arbitrary interleaving of coin and oracle effects.

**Measured extraction.** `KnowledgeStateFunction.MeasuredStages` names a budgeted program for every
extraction stage. `MeasuredStages.programAlong` composes those programs along a completed
transcript and returns the extractor's witness; its budget is the sum of the stage budgets.
The state-restoration wrapper combines the probability theorem with the instruction bound
specified in the
[resource contract](03a-extractor-efficiency.md#state-restoration-resource-contract).
The [accounting boundary](03a-extractor-efficiency.md#proof-and-accounting-boundary) applies to all
these certificates. The [native composition priorities](05-roadmap.md#native-resource-composition)
own the remaining client and resource-closure work.

**Open.** There is no interaction-layer rewinding extractor and no Fiat–Shamir or BCS bridge from
state restoration. The `privateCoins` forms are the only randomized-adversary state-restoration
results; coin sampling interleaved with oracle queries is not covered. No protocol under
`ArkLib/ProofSystem/` instantiates the interaction-layer knowledge or state-restoration
certificates yet; their clients are the acceptance examples. Probability bounds use small moves
only, an upstream limit of VCVio's `ProbComp` that the module docstring of
`Security/RoundByRound.lean` records. The [design roadmap](05-roadmap.md) lists this work.

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

These legacy results do not relate the legacy-layer and interaction-layer security games. For
Sumcheck, `Sumcheck.LegacyEquivalence` relates the compatibility verifier to the embedded legacy
verifier and transfers security notions along that equivalence.

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
