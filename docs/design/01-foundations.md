# Foundations: ownership, available substrate, and remaining gaps

This document is the normative cross-library contract for the typed oracle-reduction work. It says
which library owns each abstraction, which supported APIs ArkLib must reuse, and which integration
boundaries are genuinely absent.

The exact supported revisions live in [`00-current-status.md`](00-current-status.md). The live PR
sequence lives in [`01a-foundation-pr-plan.md`](01a-foundation-pr-plan.md). Historical July
proposals remain in the archive and are not repeated here as future work.

## 1. Ownership follows parametricity

The useful boundary is not “trees in PolyFun, worlds in VCVio, protocols in ArkLib.” All three
libraries contain things called runs, traces, or games. Ownership follows the structure an object
needs:

> **PolyFun owns domain- and effect-independent interaction structure. VCVio owns
> oracle-specialized probabilistic execution and cryptographic resource semantics. ArkLib owns
> protocol meaning, claims, relations, security notions, backend adapters, and compilers.**

Mixed notions split vertically:

| Concern | PolyFun | VCVio | ArkLib |
|---|---|---|---|
| Partial execution | `FreeM.Cursor`; generic dynamical prefixes | query/world execution state | reachable protocol prefix and verifier forks |
| Trace | generic list/free-monoid structure | dependent query/answer logs and instrumentation | verifier views, state-restoration moves, compiler segments |
| Transducer | generic causal finite-trace algebra | query-log specialization and resource certificate | hash-chain, Merkle, and extractor adapters |
| Phases | generic sequential machine wiring | persistent probabilistic handler state | commit/open, preprocessing, and extractor games |
| Budget | generic ordered/additive algebra | query, cost, and resource profiles | protocol labels and feasibility refinements |
| Commitment | no cryptographic content | primitive algorithms, games, and theorems | compiler-facing capability and transfer theorem |

The dependency direction is strict:

```text
PolyFun  ←  VCVio  ←  ArkLib
```

If a proposed object reverses an arrow, split its structural and specialized parts.

## 2. PolyFun contract

### 2.1 Available at the supported pin

The structural train envisioned by the original design has landed. The merged lineage is:

| Capability | Merged source | Final supported surface |
|---|---|---|
| Partial syntactic paths | [PolyFun #43](https://github.com/Verified-zkEVM/PolyFun/pull/43), `08fd558` | `PFunctor.FreeM.Cursor`, residuals, composition, extensions, terminal bridges |
| Displayed restriction | [PolyFun #58](https://github.com/Verified-zkEVM/PolyFun/pull/58), `609fbc0` | `Displayed.Algebra.ChildProjection`, dependent `Over.Algebra.ChildProjection`, decoration restriction |
| Cursor decomposition through append | [PolyFun #59](https://github.com/Verified-zkEVM/PolyFun/pull/59), `33e673a` | `Cursor.liftAppend`, `Cursor.joinRight`, `Cursor.AppendView`, split/join laws |
| Polynomial normalization and TypeTree naming | [PolyFun #64](https://github.com/Verified-zkEVM/PolyFun/pull/64), `45e4f2c` | `Interaction.TypeTree`, `TypeTree.Path`, substitution and chain foundations |
| Dependent chain concatenation | [PolyFun #66](https://github.com/Verified-zkEVM/PolyFun/pull/66), `ff457e0` | `TypeTree.Chain.then`, flattening, path equivalence, strategy composition, reassociation |

There was no separate merged “PF-6A at PR #62” foundation. PR #62 is a later telescope cleanup;
the normalization and rename landed together in PR #64. Live documentation must cite the merged
history above.

ArkLib must also reuse the broader supported interaction surface:

- `TypeTree.Node.Context`, `TypeTree.Node.Schema`, context morphisms, and decorations;
- `SyntaxOver`, `ShapeOver`, `StrategyOver`, and `InteractionOver`;
- two-party roles, focal and counterpart strategies, dependent composition, and execution
  factorization;
- `FreeM.Path` append/split laws and the `Cursor` occurrence/rewind APIs;
- handler folds and handler composition;
- qualitative and quantitative realizability, ranked execution, and admitted-answer leaf
  contracts.

These are foundations to consume, not abstractions to wrap under ArkLib names.

### 2.2 Distinct notions that must stay distinct

Four nearby path-like objects serve different purposes:

1. `FreeM.Path s` is a complete syntactic path to a leaf.
2. `FreeM.Cursor s` selects any residual syntactic subtree, including the root or an internal node.
3. `DynSystem.Prefix sys st n` is a finite operational orbit of fixed length.
4. `Interaction.Concurrent.Front S` is a currently enabled concurrent event and residual.

ArkLib's later `FullPrefixAt` combines a cursor with protocol decorations, concrete message data,
and reachability. It does not replace any of these generic objects.

### 2.3 Remaining PolyFun gaps

Only two generic proposals remain relevant:

#### Causal finite-trace transducer

The compiler and extractor pipeline eventually needs an effect-free, stateful transducer whose
output chunk depends on the current state and consumed input. The minimum useful contract is:

```lean
structure Transducer (Input Output : Type*) where
  State : Type*
  init  : State
  step  : State → Input → State × List Output
```

It should provide open execution, append/streaming laws, identity, composition, prefix causality,
and behavioral equivalence. A terminal finalizer is separate because flushing can violate ordinary
prefix monotonicity. Cost remains an external certificate supplied by VCVio or ArkLib.

This API is **missing** at the supported pin. It does not block typed claims or the first Sumcheck
slice; it blocks the generic compiled-layer trace pipeline.

#### Operational-prefix concatenation

Dependent concatenation for `DynSystem.Prefix` remains **client-gated**. Ordinary oracle phases can
sequence monadic computations and append query logs. Add a dynamical prefix operation only when a
concrete operational-machine client needs endpoint-preserving segment composition and cannot use
that simpler route.

### 2.4 Composition boundary

PolyFun's current factorization theorem intentionally distinguishes pure and effectful suffix
construction. A pure suffix factors under a lawful monad. A general effectful suffix requires
`LawfulCommMonad`; ordinary `StateT` does not qualify.

This is a mathematical constraint, not an API inconvenience. ArkLib's stateful security theorems
must thread the actual prefix state and quantify the suffix theorem over reachable histories. Two
standalone stateful reduction theorems do not imply a theorem about their sequential composition.

### 2.5 ArkLib acceptance evidence

The PolyFun substrate is accepted for ArkLib only when real clients demonstrate:

- a plain dependent reduction whose execution and composition reuse the PolyFun runner;
- an oracle type tree whose public and execution paths remain distinct;
- cursor restriction on role and oracle decorations;
- cursor decomposition across a two-stage reduction;
- `TypeTree.Chain.then` and `reassoc` are sufficient for the first multi-stage client, or a concrete
  failure explains the smallest missing generic law.

## 3. VCVio contract

### 3.1 Available at the supported pin

VCVio already owns the semantics ArkLib should build on:

| Area | Supported surface | ArkLib rule |
|---|---|---|
| Oracle programs | `OracleSpec`, `OracleComp`, `QueryImpl`, `simulateQ` | do not define a second oracle free monad or evaluator |
| Handler algebra | construction, composition, linking, stateful execution, query-preserving laws | express source routing and substitution through these laws |
| Instrumentation | tracing before/after a query, logging, caching, counting, weighted cost | reuse erasure, failure, support, and bound-transfer theorems |
| Resources | query bounds, `ResourceProfile`, `QueryCost`, `CostModel` | refine with protocol labels; do not create a parallel ledger |
| Probability | measure denotation and kernels; `evalSPMF` compatibility bridge | new observation boundaries use measures; legacy discrete games may retain `Pr[...]` |
| Responders | `ProbResponder`, oracle strategies and machines, wired runs | reuse for probabilistic interaction execution |
| Complexity | ranked certificates, strict oracle-PPT witnesses, `HandlerCertificate` | keep backend-relative evidence explicit |
| Reductions | `SecurityGame` and `ReductionWithCost` | reuse cost transforms; add error transport only when a client needs it |
| Merkle | shared-ROM execution and extractability theorem | adapt as a backend capability instead of restating the primitive game |

`ReductionWithCost` records an adversary map and a monotone cost transform. Its generic security
theorem assumes an advantage-preserving inequality supplied separately. It does not yet package the
additive or substitution-style error transforms required by the final compiler calculus.

### 3.2 Missing integration boundaries

The following are current gaps, not July-era greenfield rewrites.

#### Runner-produced resumable artifact

ArkLib needs one execution result that packages the returned value, final handler state, ordered
query trace or named trace regions, and the evidence used to close derived claims. Resumption must
continue from that final state, and two sequential regions must agree with one sequential run.

VCVio has the component stateful runners and instrumentation laws, but no single supported artifact
with this contract. The first general security client should add the smallest package upstream or a
thin ArkLib adapter that is explicitly temporary.

#### One terminal failure boundary

Missing probability mass retains VCVio's existing failure or nontermination meaning. Protocol
rejection and explicit model faults are returned values. The desired bridge materializes missing
mass only when a caller supplies the named fault value; otherwise the caller proves `NeverFail`
before decoding a terminal outcome.

No supported generic accept/reject/fault materialization currently provides this boundary.

#### Certified query-trace transducers

VCVio should specialize the future PolyFun transducer to dependent query logs and attach external
length, query-bound, or `ResourceProfile` certificates. It must not introduce a second generic
transducer carrier.

#### Conditioning and auditable dynamic programming

VCVio contains concrete conditioned arguments and random-oracle programming tools, but the reusable
finite-partition, query-before-program, and state-restoration interfaces remain incomplete. Add only
the general lemmas demanded by a real salted state-restoration game.

#### Error-bearing cost-aware reductions

The compiler eventually needs a composable reduction object that carries both the existing cost
transform and an explicit advantage error transform. Additive and substitution-style composition
must be separate operations. Failure probability remains experiment-specific; it is not a field of
every adversary.

### 3.3 VCVio acceptance evidence

The VCVio boundary is ready for general ArkLib security when real clients show:

1. a correlated heterogeneous oracle world runs without a special joint-world primitive;
2. traced execution erases to the same output semantics and failure behavior;
3. resumption preserves state and trace order across two phases;
4. query and resource bounds transport through one linked handler and one trace transducer;
5. dynamic programming distinguishes query-before-program from fresh insertion;
6. a reduction composes both cost and advantage error;
7. terminal decoding crosses exactly one named missing-mass boundary;
8. ArkLib adapts the supported Merkle theorem without restating its primitive experiment.

## 4. ArkLib contract

ArkLib owns the structures that give the generic foundations protocol meaning:

- the public/oracle node distinction and its decorations;
- typed prover and verifier packages over PolyFun strategies;
- extensional source contexts, virtual output programs, and substitution;
- resource identity, origin, aliasing, and guarantee schemas;
- open and closed claims, relations, and run-derived closing;
- ordinary, knowledge, round-by-round, and state-restoration security notions;
- commitment-backend adapters and oracle-elimination passes;
- protocol-specific error, feasibility, and running-time theorems.

ArkLib does not own a second handler algebra, probability denotation, generic query log, resource
profile, or causal transducer.

## 5. Release and migration discipline

- Every implementation PR starts from its repository's current default branch.
- ArkLib uses one VCVio pin and accepts the PolyFun revision selected by VCVio.
- Mechanical dependency changes stay separate from semantic API changes.
- A temporary downstream adapter names its upstream destination and carries a deletion test.
- The archived prototype is a proof and API source bank, never a merge base.
- Legacy ArkLib consumers remain until a concrete protocol has a proved two-way bridge.
- Interface names freeze only after a real downstream client exercises all observable components.

We have enough foundation to begin. The remaining work is no longer “build an interaction theory
somewhere upstream”; it is to land the smallest ArkLib semantics that make virtual claims,
run-derived closing, and honest composition unavoidable in the types.
