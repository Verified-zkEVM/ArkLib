# Foundation status and ArkLib landing plan

This is the live implementation plan. It contains only two kinds of work:

1. current upstream gaps with a named ArkLib consumer; and
2. ArkLib PR slices that can be reviewed and validated independently.

Merged PolyFun work is summarized as lineage, not described as a future PR. The original detailed
PolyFun and VCVio proposals remain in the archived design history.

## 1. Rules of execution

1. **Start from current `main`.** Do not use the broad prototype branch as a merge base.
2. **Give each PR one semantic center.** Include the laws, tests, and documentation needed to make
   that center usable, but do not migrate unrelated protocols.
3. **Reuse before wrapping.** A new type that overlaps a supported upstream API needs an explicit
   semantic difference or an equivalence.
4. **Require a real client.** A foundational record freezes only after a downstream protocol or
   security theorem exercises its observable components.
5. **Keep dependency bumps mechanical.** Update pins, manifests, and compatibility proofs without
   mixing in an API redesign.
6. **Add no new `sorry`.** If a theorem cannot be proved, narrow the claim or delay the slice.
7. **Keep migration reversible.** The legacy layer remains until each migrated protocol has a
   two-way correspondence theorem.

## 2. Current dependency graph

The structural path is open; the later security path has explicit upstream gates:

```text
supported PolyFun + VCVio pins
            │
            └─ AR-0 alignment
                 ├─ AR-1 plain reductions
                 ├─ AR-2A oracle type tree → AR-2B decorations → AR-3A access
                 └─ AR-4A sources ─────────────────────┐
                                                   │
AR-1 + AR-2B + AR-3A → AR-3B execution          │
AR-4A → AR-5 virtual substitution              ├─ AR-6A claims
AR-4A → AR-4B resource schemas ─────────────────┘      │
                                                         └─ AR-6B core run
                                                              → AR-7 Sumcheck
                                                              → AR-8 legacy bridge

VCVio artifact + outcome gaps → AR-9A/9B → AR-10B → general security
PolyFun transducer + VCVio specialization → state restoration → compiler
```

AR-1, AR-2A, and AR-4A may begin independently after AR-0. The first acceptance milestone is AR-7,
not completion of every upstream security foundation.

## 3. Upstream status

### 3.1 Completed PolyFun lineage

| Design need | Merged PR | Status at supported pin |
|---|---|---|
| `FreeM.Cursor` | [#43](https://github.com/Verified-zkEVM/PolyFun/pull/43) | available |
| displayed restriction along cursors | [#58](https://github.com/Verified-zkEVM/PolyFun/pull/58) | available |
| cursor decomposition through append | [#59](https://github.com/Verified-zkEVM/PolyFun/pull/59) | available |
| polynomial normalization and `TypeTree` rename | [#64](https://github.com/Verified-zkEVM/PolyFun/pull/64) | available |
| dependent `TypeTree.Chain` concatenation | [#66](https://github.com/Verified-zkEVM/PolyFun/pull/66) | available |

No ArkLib PR waits for these changes. `TypeTree.Chain.then` and reassociation are existing APIs;
extend them only if a concrete multi-stage client reveals a missing law.

### 3.2 Open upstream gaps

| Gap | Owner | First consumer | What it blocks |
|---|---|---|---|
| causal finite-trace transducer | PolyFun | compiled extractor trace pipeline | state restoration and compiler trace composition |
| query-log transducer specialization and certificates | VCVio | ArkLib hash-chain/Merkle adapters | certified trace and resource transport |
| runner-produced resumable artifact | VCVio, possibly introduced by an ArkLib client | AR-9A | general world-backed security composition |
| accept/reject/fault materialization | VCVio | AR-9B | one explicit terminal failure boundary |
| reusable conditioning and dynamic programming | VCVio | first salted state-restoration game | general SR/ROM proofs |
| error-bearing cost-aware reduction package | VCVio | first compiler security transfer | additive and substitution-style loss composition |
| operational `DynSystem.Prefix` concatenation | PolyFun, client-gated | only a future operational-machine adapter | nothing in the first ArkLib train |

The owner is determined by generality. The first ArkLib client may implement the upstream change in
its owning repository, but ArkLib must not stabilize a private duplicate.

## 4. ArkLib PR slices

### AR-0 — align the dependency and design baseline

**Goal.** Pin the tested VCVio revision, accept its PolyFun selection, migrate only the mechanical
probability-surface breakages, and land this maintained design suite.

**Acceptance.** One resolved PolyFun revision; full ArkLib validation; no new interaction-layer
declaration; historical upstream plans no longer appear as live work.

### AR-1 — plain dependent reduction kernel

**Status.** Implemented by the first typed-interaction PR. The next independent core slices are
AR-2A and AR-4A.

**Goal.** Add the smallest ArkLib prover, verifier, and reduction packages over PolyFun
`Interaction.TypeTree`, two-party roles, strategies, and execution.

**Required laws.** Honest execution agrees definitionally with the PolyFun runner. Dependent append
and the supported strategy-composition theorem supply sequential composition. State clearly which
composition theorem is pure and which needs commutative effects.

**Acceptance client.** A genuinely dependent two-stage plain reduction whose second tree depends on
the first complete path.

**Not included.** Oracle nodes, resource metadata, claims, probability, or legacy migration.

### AR-2A — oracle type trees and path projections

**Goal.** Add `Oracle.Position`, `Oracle.TypeTree`, the runtime lens to generic `TypeTree`,
`BranchPath`, `ExecutionPath`, and projection from execution to structural branch.

**Acceptance.** One mixed tree shows that public values choose continuations, oracle payloads remain
present in `ExecutionPath`, and oracle branch indices are `PUnit` in `BranchPath`.

### AR-2B — role and oracle decorations

**Goal.** Decorate the oracle type tree with roles, public/oracle status, and the projections needed
by later prover and verifier views.

**Acceptance.** Restriction along a real `FreeM.Cursor` recovers the correct future decoration on a
mixed public/oracle tree.

### AR-3A — accumulated oracle access

**Goal.** Define the typed access available at each node: input resources, earlier prover messages,
and public values, with no future-message access.

**Acceptance.** Passthrough and one-round derived-query examples prove routing and public-projection
invariance. A negative canary prevents access to a future resource.

### AR-3B — oracle prover, verifier, and execution

**Goal.** Package oracle-aware strategies and execution over AR-1 and AR-2. The executor uses AR-3A
routing and erases to the plain runner.

**Acceptance.** Erasure, routing, and public-view projection are proved on one mixed two-party tree.

### AR-4A — extensional sources and routing

**Goal.** Add universe-polymorphic source families and extensional handlers, plus identity,
renaming, weakening, sum/product routing, and composition.

**Acceptance.** Heterogeneous source types remain in independent universes. Extensionally equal
handlers cannot be distinguished by a virtual query program.

### AR-4B — resource identity and guarantee schemas

**Goal.** Record stable resource identity, origin, ownership, aliasing, and reified ideal
guarantees without polluting extensional source semantics.

**Acceptance.** Two resources with the same query signature remain distinct; explicit aliasing can
identify them; accidental duplication through tensor is unconstructible.

### AR-5 — virtual-oracle substitution

**Goal.** Define typed virtual programs over a source context, interpretation, mapping along source
morphisms, and substitution.

**Required laws.** Evaluation respects identity and composition; substitution agrees with handler
composition; semantic equivalence is extensional under every handler.

**Acceptance client.** Adapt one existing `OracleOutputSimulation` without changing its observable
query behavior.

### AR-6A — open and closed claims

**Goal.** Define open claims carrying virtual plans and closed claims carrying extensional behavior.
Closing interprets every plan with one supplied handler. Relations consume only closed claims.

**Acceptance.** A relation cannot inspect derivation history, and closing commutes with virtual
substitution.

### AR-6B — core execution and run-derived closing

**Goal.** Define the smallest trace-free `CoreRun` that pairs one execution's concrete resources
with its virtual output claim. Its constructor remains controlled by execution.

**Acceptance.** The public API cannot close one run's claim with another run's handler. Existing
oracle-output agreement is recovered as a derived theorem.

### AR-7 — one-round Sumcheck through closing

**Goal.** Port one single-round Sumcheck with a degree-bounded oracle slot and prove programmatic
perfect completeness through `CoreRun` closing.

**Acceptance.** The theorem is sorry-free, exercises the guarantee representation, and uses the
new relation boundary rather than a hand-materialized oracle family.

### AR-8 — first legacy correspondence

**Goal.** Prove a two-way Sumcheck-specific bridge between the typed claim semantics and the legacy
`OracleReduction` presentation.

**Acceptance.** Both presentations agree on honest execution and the relation observed by the
protocol. No generic bridge is claimed.

### AR-9A — logged world-backed execution

**Prerequisite.** AR-6B plus the smallest supported VCVio execution-artifact boundary.

**Goal.** Extend `CoreRun` with ArkLib claim-resource logging and VCVio world state/query evidence
from the same execution. No public constructor accepts split projections.

### AR-9B — terminal outcomes

**Prerequisite.** AR-9A plus the VCVio outcome bridge.

**Goal.** Distinguish acceptance, rejection, protocol fault, and runtime missing mass. A caller either
proves `NeverFail` or explicitly names the fault used to materialize missing mass.

### AR-10A — structural full prefixes

**Goal.** Combine a PolyFun cursor with concrete message-prefix data, reachability, restricted
decorations, and the resource schema available at that point.

**Required laws.** No future resources; monotonicity under witnessed cursor extension; decomposition
through append; compatibility with execution-path projection.

This slice is structurally independent of AR-9 and may land earlier even though it is listed here
by identifier.

### AR-10B — align protocol prefixes with execution artifacts

**Goal.** Relate every protocol cursor/phase boundary to the corresponding world-trace region and
resource profile. Preserve order, multiplicity, and stable resource identity.

### AR-11 — Merkle backend adapter

**Prerequisite.** Resource schemas, world-backed execution, terminal outcomes, and the supported
VCVio shared-ROM Merkle extraction theorem.

**Goal.** Expose the smallest compiler-facing Merkle capability by adapting the VCVio theorem. Do
not restate the primitive game or advertise unsupported proximity, batching, or privacy properties.

## 5. Checkpoints

### Structural checkpoint

AR-0 through AR-6B pass. The records remain provisional, but the public path, source, virtual
oracle, claim, and run-derived closing equations are usable without ArkLib-private upstream copies.

### First semantic checkpoint

AR-7 and AR-8 pass. Sumcheck demonstrates the new carrier and a two-way migration path. At this
point the central record signatures may freeze provisionally.

### General security checkpoint

AR-9A/9B and AR-10A/10B pass against the supported VCVio artifact and outcome boundaries. Ordinary
soundness composition is stated with output admissibility and history-dependent suffix security.

### Compiler checkpoint

The generic transducer, query-log specialization, reduction-error transport, and first backend
adapter pass their real ArkLib clients. Only then does the oracle-elimination compiler stabilize
its trace and capability interfaces.
