# Current status and first implementation train

**Status date:** 2026-08-29. **Scope:** the supported starting point for implementing the
typed oracle-reduction architecture on ArkLib's current default branch.

This page is the operational entry point to the design suite. The other documents remain the
normative source for the end state and semantic invariants. Their July dependency inventories and
PR identifiers describe provenance; this page records which foundations now exist and what the
next ArkLib PRs should consume.

## Supported baseline

The first implementation train uses one compatible dependency chain:

| Repository | Revision | Role |
|---|---|---|
| ArkLib | `3f3f045dd295834c262bd6f0d9dfdfee07cc8e76` | clean default-branch base |
| VCVio | `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` | direct ArkLib dependency |
| PolyFun | `c0c923693fc827a41d17116579a0c16ed4873b19` | revision selected and tested by VCVio |
| Lean | `v4.33.1` | common toolchain |

ArkLib does not override PolyFun independently. VCVio owns the tested PolyFun revision, so a later
PolyFun update first lands in VCVio and then reaches ArkLib through the VCVio pin.

## What already exists

### PolyFun

The following generic foundations have landed and must not be rebuilt in ArkLib:

- `Interaction.TypeTree`, dependent complete paths, append, chains, and path execution;
- node `Context` and `Schema`, decorations, context morphisms, and restriction;
- `SyntaxOver`, `ShapeOver`, `StrategyOver`, and `InteractionOver`;
- two-party roles, focal/counterpart strategies, dependent strategy composition, and execution
  factorization;
- free-monad cursors, cursor composition, displayed restriction, and append decomposition;
- handler folds and handler composition;
- qualitative and quantitative realizability, ranked execution, and admitted-answer leaf
  contracts.

PolyFun's composition boundary is semantically important. Pure suffix construction factors under a
lawful monad. General effectful suffix construction requires `LawfulCommMonad`; ordinary `StateT`
does not satisfy that requirement. ArkLib must express stateful sequential games by explicit state
threading and conditional suffix theorems, not by restoring the admitted legacy theorem.

The planned generic causal trace transducer has not landed. Operational prefix concatenation remains
client-gated. Neither gap blocks the typed claim and single-round Sumcheck slice.

### VCVio

VCVio now provides more of the execution and resource substrate than the July plan assumed:

- `QueryImpl` handler composition and query-preserving morphism laws;
- response-dependent and response-independent tracing, logging, caching, and cost instrumentation;
- `ResourceProfile` and `ReductionWithCost`;
- kernel-first `ProbResponder`, oracle strategies and machines, and wired runs;
- `Measure` as the primary closed probability semantics and kernels for parameterized/stateful
  semantics;
- strict oracle-PPT witnesses, ranked resource certificates, and proof-bearing handler
  substitution via `HandlerCertificate`;
- repaired shared-random-oracle Merkle semantics and a proved shared-ROM extractability bound.

The design must target these APIs. New security statements use measure/kernel semantics at
observation boundaries; `SPMF` remains an executable compatibility surface rather than the primary
denotation.

The following planned generic boundaries are still missing or incomplete:

- one runner-produced, resumable oracle execution artifact that packages path, handler state,
  trace regions, and the closing evidence derived from that run;
- an explicit generic terminal outcome separating accept, reject, and fault;
- a causal trace-transducer specialization and general conditioning/dynamic-programming APIs for
  state-restoration proofs.

These gaps gate the general execution/security phases. They do not gate the typed syntax,
`VirtualOracle`, claim, or first protocol-slice work.

### ArkLib

Current `main` already contains a useful migration seam:

- `OracleOutputSimulation` represents derived output oracles query by query;
- its agreement law relates query execution to the materialized family used by legacy relations;
- sequential composition, context lifting, and current protocol clients preserve virtual outputs.

This is not the new interaction layer. The carrier remains `ProtocolSpec n`, relation-facing
semantics still materialize output families, legacy output embeddings require heterogeneous
transport, and unrestricted stateful composition theorems remain admitted.

The preserved `archive/oracle-reduction-v2-pre-split` branch contains a broad interaction-native
prototype and protocol ports. It is a proof and API source bank. Its code targets pre-`TypeTree`
PolyFun names and older VCVio semantics, so implementation PRs must port coherent slices onto a
fresh current base. They must not merge the archive wholesale.

## Architecture retained from the design

The source audit did not invalidate the central model:

1. An open oracle claim contains a public statement and source-scoped virtual output oracles.
2. A virtual oracle is a typed query program over declared source capabilities.
3. Extensional meaning is obtained by interpreting that program with a handler from the same run.
4. Closing is runner-derived; callers cannot pair a claim with an unrelated handler.
5. Relations consume closed claims, not derivation histories.
6. Composition is typed-tree append plus handler substitution and explicit context morphisms.
7. Source semantics and resource metadata remain separate: `SourceCtx` is extensional, while
   `ResourceSchema` records identity, origin, aliasing, and guarantees.
8. Semantic equivalence and operational trace/resource equivalence remain distinct.
9. Ordinary soundness composition requires intermediate admissibility and a history-dependent
   suffix theorem. Two standalone `StateT` theorems do not imply it.
10. Oracle guarantees are transported into explicit backend obligations by the later compiler.

Current upstream types should implement these invariants where they fit. ArkLib introduces only
protocol-specific structures that are not expressible by PolyFun or VCVio.

## First ArkLib PR train

Each implementation PR starts from the current default branch and keeps the legacy layer working.

| Order | PR slice | Required result |
|---|---|---|
| 0 | Design and dependency alignment | Land this refreshed suite, the compatible VCVio pin, and mechanical compatibility fixes; no new interaction-layer API. |
| 1 | Plain typed reductions | Add a thin ArkLib prover/verifier/reduction package over PolyFun `TypeTree`, roles, and strategies. |
| 2 | Oracle type trees | Add the oracle-specific public/oracle polynomial, execution lens, decorations, `BranchPath`, `ExecutionPath`, and public projection. |
| 3 | Source contexts and virtual oracles | Add extensional source handlers and substitution; adapt current `OracleOutputSimulation` into the new representation. |
| 4 | Claims and run-derived closing | Add open/closed claims and the smallest core-run witness needed to prevent unrelated handler closing. |
| 5 | Single-round Sumcheck | Prove programmatic perfect completeness through closing, including a degree-bounded oracle slot. |
| 6 | Typed composition and legacy bridge | Exercise dependent append and virtual substitution; bridge the migrated slice in both directions. |
| 7 | Execution artifact and ordinary security | Add or upstream the missing runner artifact and outcome boundary, then prove admissibility-aware composition. |

The first code PR does not port the archive's whole `ArkLib/Interaction` tree. It introduces the
smallest plain reduction wrapper whose execution is definitionally the current PolyFun runner and
whose composition theorem is inherited from PolyFun.

## Deferred work

The following work is intentionally outside the first train:

- state restoration, rewinding, and conditioned ROM arguments;
- the oracle-elimination compiler and commitment backend assignment;
- broad FRI, Spartan, and BCS migration;
- deletion of the legacy `OracleReduction` namespace.

Those phases begin only after the Sumcheck slice and its compatibility theorem establish that the
new claim and execution boundary works in a real protocol.

## Acceptance gates for the alignment PR

The design-and-dependency PR is complete when:

- ArkLib resolves exactly the PolyFun revision selected by VCVio;
- the repository builds and the standard validation script passes;
- the documentation distinguishes landed APIs, missing foundations, and target architecture;
- no document presents the archived implementation or a design sketch as code on `main`;
- the next code PR can begin from current `main` without a dependency override.
