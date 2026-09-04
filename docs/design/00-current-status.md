# Current status and first implementation train

**Status date:** 2026-09-03. **Scope:** the supported starting point for implementing ArkLib's
typed oracle-reduction architecture.

The core implementation can begin now. PolyFun's typed interaction, cursor, restriction, append,
strategy, handler, and chain-composition foundations are already available at ArkLib's supported
dependency pin. VCVio also supplies the handler, trace, resource, measure, responder, strict-PPT,
and Merkle foundations needed by the early ArkLib slices. The remaining upstream gaps affect the
general security and compiler phases, not the first typed-reduction and claim work.

## Supported baseline

The first implementation train uses one tested dependency chain:

| Repository | Revision | Role |
|---|---|---|
| ArkLib | `3f3f045dd295834c262bd6f0d9dfdfee07cc8e76` | clean default-branch base |
| VCVio | `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` | direct ArkLib dependency |
| PolyFun | `c0c923693fc827a41d17116579a0c16ed4873b19` | revision selected and tested by VCVio |
| Lean | `v4.33.1` | common toolchain |

ArkLib does not override PolyFun independently. VCVio owns the tested PolyFun revision. A later
PolyFun update reaches ArkLib only after VCVio advances and validates its pin.

## Capability status

### PolyFun

The supported PolyFun revision contains all structural foundations needed for the first ArkLib
train:

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
| Generic causal trace transducer | **missing** | no supported `Control.Transducer` API |
| Operational `DynSystem.Prefix` concatenation | client-gated | add only if an operational-machine client cannot use ordinary monadic sequencing |

The available cursor and `TypeTree.Chain` work was merged in PolyFun PRs
[#43](https://github.com/Verified-zkEVM/PolyFun/pull/43),
[#58](https://github.com/Verified-zkEVM/PolyFun/pull/58),
[#59](https://github.com/Verified-zkEVM/PolyFun/pull/59),
[#64](https://github.com/Verified-zkEVM/PolyFun/pull/64), and
[#66](https://github.com/Verified-zkEVM/PolyFun/pull/66). All are ancestors of the supported
PolyFun revision. They are implementation inputs, not future work.

One compositional boundary remains load-bearing. Pure suffix construction factors under a lawful
monad. General effectful suffix construction requires `LawfulCommMonad`; ordinary `StateT` does not
satisfy that requirement. ArkLib must state stateful sequential security using explicit state
threading and history-dependent suffix theorems. It must not restore the legacy unrestricted
composition claim.

### VCVio

The supported VCVio revision provides a strong execution and resource substrate:

| Capability | Status | Reuse in ArkLib |
|---|---|---|
| Handler construction and composition | available | build source interpreters and substitution from `QueryImpl` and handler laws |
| Tracing, logging, caching, and cost instrumentation | available | reuse `withTrace*`, `withLogging`, and existing erasure/failure bridges |
| Query and resource accounting | available | reuse query bounds, `ResourceProfile`, `QueryCost`, and `CostModel` |
| Cost-aware reductions | available, cost-only | reuse `SecurityGame.ReductionWithCost`; add no parallel cost hierarchy |
| Closed probability semantics | available | use `Measure`/kernel semantics at new observation boundaries |
| Executable discrete semantics | compatibility surface | use `evalSPMF` only where legacy `Pr[...]` statements require it |
| Probabilistic responders and wired machines | available | reuse `ProbResponder`, oracle strategies, and machine runs |
| Strict oracle-PPT certificates | available | reuse ranked resources and `HandlerCertificate` |
| Shared-ROM Merkle extraction | available | adapt the primitive theorem; do not restate its game in ArkLib |
| Runner-produced resumable execution artifact | **missing** | needed before general world-backed security composition |
| Explicit accept/reject/fault materialization | **missing** | needed for one named terminal failure boundary |
| Certified query-trace transducer specialization | **missing** | waits on the generic PolyFun transducer |
| General conditioning/dynamic-programming facade | incomplete | specific theorems exist, but not the reusable state-restoration boundary |
| Error-bearing and cost-bearing reduction package | incomplete | `ReductionWithCost` handles cost; later clients still need explicit additive/substitution error transport |

These gaps are integration boundaries, not permission to introduce ArkLib-private probability,
trace, or cost semantics. The first client should either add the smallest upstream API or provide a
temporary adapter with an upstream issue and a deletion test.

### ArkLib

Current `main` contains a useful migration seam:

- `OracleOutputSimulation` represents derived output oracles query by query;
- its agreement law connects query execution to the materialized family used by legacy relations;
- sequential composition, context lifting, and current protocol clients preserve virtual outputs.

This is not the replacement layer. The carrier remains `ProtocolSpec n`; relation-facing semantics
still materialize output families; legacy embeddings require heterogeneous transport; and
unrestricted stateful composition theorems remain admitted.

The preserved `archive/oracle-reduction-v2-pre-split` branch contains a broad interaction-native
prototype and protocol ports. It is a source bank, not a merge base. Its code uses pre-`TypeTree`
PolyFun names and older VCVio semantics, so each implementation PR must port and re-audit one
coherent slice on a fresh ArkLib base.

## Architecture retained from the design

The current source audit preserves the central model:

1. An open oracle claim contains a public statement and source-scoped virtual output oracles.
2. A virtual oracle is a typed query program over declared source capabilities.
3. Its extensional meaning is obtained under the handler produced by the same execution.
4. Closing is run-derived; callers cannot close a claim with an unrelated handler.
5. Relations consume closed claims, not derivation histories.
6. Composition is typed-tree append plus handler substitution and explicit context morphisms.
7. `SourceCtx` is extensional; `ResourceSchema` separately records identity, origin, aliasing, and
   guarantees.
8. Semantic equivalence and operational trace/resource equivalence remain distinct.
9. Ordinary soundness composition requires output admissibility and a history-dependent suffix
   theorem.
10. Oracle guarantees become explicit backend obligations during compilation.

ArkLib introduces only protocol-specific structure that the supported PolyFun and VCVio APIs do
not already express.

## First ArkLib PR train

Every implementation PR starts from current `main` and leaves the legacy layer working.

| Order | Slice | Required result | Upstream status |
|---|---|---|---|
| 0 | Design and dependency alignment | Land this maintained suite, the tested VCVio pin, and mechanical compatibility fixes | current alignment change |
| 1 | Plain typed reductions | Add a thin prover/verifier/reduction package over PolyFun `TypeTree`, roles, strategies, and execution | unblocked |
| 2 | Oracle type trees | Add public/oracle positions, decorations, `BranchPath`, `ExecutionPath`, and public projection | unblocked |
| 3 | Source contexts and virtual oracles | Add extensional handlers and substitution; adapt `OracleOutputSimulation` | unblocked |
| 4 | Claims and run-derived closing | Add open/closed claims and the smallest core-run witness that prevents unrelated-handler closing | unblocked after slices 1–3 |
| 5 | Single-round Sumcheck | Prove programmatic perfect completeness through closing with a degree-bounded oracle slot | unblocked after slice 4 |
| 6 | Typed composition and legacy bridge | Exercise dependent append and virtual substitution; prove a two-way protocol bridge | unblocked after slice 5 |
| 7 | Execution artifact and ordinary security | Add or upstream the artifact and outcome boundaries; prove admissibility-aware composition | blocked on named VCVio gaps |

AR-1 introduces the smallest plain reduction wrapper whose execution is definitionally the current
PolyFun runner. It supports complete-path-dependent append and exposes the general effectful
factorization boundary through `LawfulCommMonad`; PolyFun's pure-suffix theorem remains available
under `LawfulMonad`. The executable acceptance client selects different suffix message types from
the first complete path. AR-1 does not port the archive's whole `ArkLib/Interaction` tree.

## Deferred work

The first train deliberately excludes:

- state restoration, rewinding, and general conditioned-ROM arguments;
- the oracle-elimination compiler and backend assignment;
- broad FRI, Spartan, Nova, and BCS migration;
- deletion of the legacy `OracleReduction` namespace.

Those phases begin only after the Sumcheck slice and its compatibility theorem show that the new
claim and execution boundary works in a real protocol.

## Acceptance gate for the alignment change

The alignment change is complete when:

- ArkLib resolves exactly the PolyFun revision selected by VCVio;
- the repository builds and the standard validation script passes;
- every live document distinguishes available APIs, missing foundations, and target architecture;
- historical proposals live in the archive rather than masquerading as future PRs;
- the next code PR can begin from current `main` without a dependency override.
