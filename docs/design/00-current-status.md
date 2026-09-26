# Current status

**Status date:** 2026-09-25. **Scope:** the supported dependency baseline, what the typed
oracle-reduction layer already provides on `main`, and the next open work.

The typed core, the first world-backed execution artifacts, and the Sumcheck acceptance slices have
landed (AR-1 through AR-10B; ArkLib #851–#892). Native full-protocol Sumcheck now has a
verifier with explicit abort and soundness against arbitrary native prover continuations. No declaration under `ArkLib/Interaction/` or
`ArkLib/ProofSystem/Sumcheck/Interaction/` uses `sorry`. The next work is protocol evidence beyond
Sumcheck (FRI and Spartan slices) and the admissibility-aware
ordinary soundness composition theorem. State restoration and the compiler remain blocked on the
upstream gaps listed below.

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

| Area | Modules | Landed in |
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
| Native full-protocol soundness | `Native.execute_soundness` in `ProtocolSoundness` | — |
| Native honest completeness | `Native.execute_support_completeness`, `Native.execute_perfectCompleteness` in `ProtocolCompleteness` | — |

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
probabilistic completeness is one for any challenge program.

`Oracle/Composition` and the earlier `ArbitraryRounds` clients execute sequences of separate
reductions across explicit interfaces. Those execution results do not by themselves establish
soundness for arbitrary strategies on a composed interaction tree. The native Sumcheck theorem
follows the actual full-tree execution directly. General world-backed composition, admissibility,
and fault accounting remain separate obligations.

The legacy verifier correspondence is honest-execution only: the legacy verifier reads the input
polynomial for its next target, while the typed verifier reads the sent polynomial. Both relation
directions are proved for arbitrary claims.

The legacy `OracleReduction` layer is unchanged. Its carrier remains `ProtocolSpec n`, and its
unrestricted stateful composition theorems remain admitted.

The preserved `archive/oracle-reduction-v2-pre-split` branch contains the earlier interaction-native
prototype and protocol ports (FRI, Spartan, Fiat–Shamir, BCS, boundary transport, security
notions). It is a source bank, not a merge base. Its code uses pre-`TypeTree` PolyFun names and
older VCVio semantics, so each port is rewritten and re-audited on a fresh ArkLib base.

## Architecture retained from the design

The current source audit preserves the central model:

1. An open oracle claim contains a public statement and source-scoped virtual output oracles.
2. A virtual oracle is a typed query program over declared source capabilities.
3. Its extensional meaning is obtained under the handler produced by the same execution.
4. Closing is run-derived; callers cannot close a claim with an unrelated handler.
5. Relations consume closed claims, not derivation histories.
6. Composition is typed-tree append plus handler substitution and explicit context morphisms.
7. `SourceCtx` is extensional; `OracleModel` assigns meaning and promises to stable names,
   `NamedContext` selects distinct names, and `NamedContext.View` expresses aliasing.
8. Semantic equivalence and operational trace/resource equivalence remain distinct.
9. Ordinary soundness composition requires output admissibility and a history-dependent suffix
   theorem.
10. Oracle guarantees become explicit backend obligations during compilation.

ArkLib introduces only protocol-specific structure that the supported PolyFun and VCVio APIs do
not already express.

## Open work

In roadmap order (see [`05-roadmap.md`](05-roadmap.md)):

| Item | Roadmap phase | Dependency |
|---|---|---|
| One FRI slice (derived virtual view) with a two-way legacy bridge | 3 | unblocked |
| One Spartan-like slice (fresh prover message) with a two-way legacy bridge | 3 | unblocked |
| Admissibility-aware ordinary soundness composition | 4 | unblocked; #889 does not yet connect the world-query classifier to `availableContext` |
| Salted state restoration, extractor calculus, RBR-to-SR implications | 5 | PolyFun transducer; VCVio conditioning facade |
| Oracle-elimination compiler, typed BCS and Fiat–Shamir | 6 | Phase 5 plus the VCVio error-bearing reduction package |
| Broad FRI/Spartan/BCS/Nova migration; deletion of the legacy namespace | after 4 | per-protocol two-way correspondences |
