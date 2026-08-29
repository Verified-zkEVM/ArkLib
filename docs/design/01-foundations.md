# 01 — Foundations: Ownership, Existing Substrate, and Required Deltas

**Normative architectural contract.** This document says what belongs in each library, records the
foundation inventory behind the design, and isolates the semantic deltas ArkLib actually needs. The
PR-by-PR landing plan is [`01a-foundation-pr-plan.md`](01a-foundation-pr-plan.md). The normative
true-sight naming cutover is
[`01b-type-tree-rename-cutover.md`](01b-type-tree-rename-cutover.md).

The original inventory was checked on 2026-07-13 against:

- ArkLib `main` at `e2c3710` (Lean 4.30 dependency train);
- ArkLib's active Lean 4.31 migration candidate `quang/bump-v4.31.0` at `55a9ccc`;
- VCVio `main` at `cbd4144b` (Lean 4.31; PolyFun pinned at `04a12b6`);
- PolyFun `main` at `2ed730d` (Lean 4.31).

These hashes are historical audit evidence, not dependency pins. The 2026-08-29 source audit found
that the `TypeTree`, cursor, handler, strategy, responder, resource, kernel, and ranked-execution
foundations described below have substantially advanced. The supported revisions and the precise
landed/missing split are maintained in [`00-current-status.md`](00-current-status.md); that page is
authoritative whenever this document's original availability notes differ from current code.

## 0. Ownership is determined by parametricity, not nouns

The old slogan—trees in PolyFun, worlds/traces in VCVio, protocols in ArkLib—was too coarse.
Current PolyFun already contains generic runs, games, traces, handlers, and phased machines. The
rule is:

> **PolyFun owns domain- and effect-independent structural interaction semantics (monad
> polymorphism is strong evidence, not a necessary condition). VCVio owns
> oracle-specialized probabilistic execution, worlds, probability, and cryptographic resource
> semantics. ArkLib owns protocol meaning: roles, claims, relations, security notions, commitment
> adapters, and compilers.**

Mixed notions split vertically rather than being assigned wholesale:

| Concern | PolyFun | VCVio | ArkLib |
|---|---|---|---|
| Partial execution | syntactic `FreeM.Cursor`; generic dynamical prefixes | query/world execution prefix | reachable protocol prefix and verifier fork |
| Trace | generic list/free-monoid and relabel/filter algebra | dependent query/answer log, probabilistic instrumentation | verifier view, SR moves, compiler segmentation |
| Transducer | pure causal stream/list transducer | query-log specialization and resource certificate | hash-chain, Merkle, and SR adapters |
| Phases | generic sequential machine/game wiring | persistent probabilistic world session/checkpoint | commit/open, preprocessing, and extractor games |
| Budget | generic additive/preordered algebra where useful | oracle query/cost profiles and probability bounds | protocol labels and feasibility constraints |
| Commitment | no cryptographic content | standalone primitive algorithms/games/theorems | backend capability adapter and compiler transfer |

Dependency direction remains strict:

```text
PolyFun  ←  VCVio  ←  ArkLib
```

PolyFun imports neither VCVio nor ArkLib. VCVio imports no ArkLib. ArkLib is the integration layer.
If a proposed object would reverse an arrow, split its structural and specialized parts.

## 1. PolyFun contract

### 1.1 What is already present

Do not rebuild the following:

- `PFunctor.FreeM.Path` and `PathAlong` for terminal root-to-leaf paths, with extensive dependent
  append split/pack/unpack laws (`PFunctor/Free/Path.lean`).
- displayed data and decoration maps, dependent `Over.map`, base transport, identity/composition,
  and append naturality (`PFunctor/Free/Displayed/Decoration.lean` and `.../Append.lean`).
- `DynSystem.Prefix`, `Run`, events/tickets, reachability, and generic execution
  (`PFunctor/Dynamical/Run.lean`).
- `PointedMachine.seqComp`, handler-parametric execution, responder/game wiring, simulation, and
  refinement (`PFunctor/Dynamical/*`).
- `Control.Trace` and `PFunctor.Trace` stateless monoid/list emitters, including the polynomial
  list/free-monoid carrier, relabel/filter operations, and sum projections.
- `Interaction.TypeTree.Chain` and `TypeTree.StateChain` as existing n-ary/telescope candidates
  (historically under `Interaction.Spec` before PF-6R).
- `Interaction.Concurrent.Front` and process prefixes for concurrent semantics.

The original audit distinguished three “prefix-like” objects that must not be conflated:

1. `FreeM.Path s` is a **complete syntactic path** to a leaf.
2. `DynSystem.Prefix sys st n` is a **finite operational orbit** of fixed length.
3. `Concurrent.Front S` is a **currently enabled structural event and one-step residual**.

PolyFun has since added free-monad cursors for the missing partial syntactic path. The three objects
above still have distinct meanings and must not be substituted for that cursor API.

### 1.2 Required PolyFun deltas

**PF-1 — Syntactic `FreeM.Cursor` (required).** A cursor selects any residual subtree, including the
root and internal nodes. It has structural descent, residual, composition, unit/associativity laws,
an immediate-edge/witness-bearing extension relation, and an equivalence between terminal cursors
and `Path`. It is not called `Prefix` or `Front`.

Indicative shape:

```lean
inductive FreeM.Cursor : (s : FreeM P α) → Type _
  | root (s) : Cursor s
  | down {a k} (b : P.B a) (tail : Cursor (k b)) : Cursor (.roll a k)

def Cursor.residual : Cursor s → FreeM P α
def Cursor.comp (c : Cursor s) : Cursor c.residual → Cursor s
```

**PF-2 — Cursor restriction (required).** A completely arbitrary `Displayed.Shape` cannot be
restricted along a cursor: from an unconstrained value in `D.node a child` there is no canonical way
to recover `child b`. Add `Displayed.Shape.ChildProjection`, its dependent
`Displayed.OverShape.ChildProjection` counterpart, and define the cursor-spine traversal once
against that capability. Supply the canonical specializations for `Decoration` and
`Decoration.Over`; prove naturality with existing maps and base transport. Restriction returns data
on the cursor's **future residual subtree** only. It does not recover data along the visited spine.
ArkLib separately folds the cursor spine and pairs it with concrete hidden-message prefix data in
`FullPrefixAt`.

**PF-3 — Cursor decomposition through append (required).** Classify a cursor of dependent
`FreeM.append s k` as either:

- a cursor in `s` whose residual is explicitly witnessed to be an internal `.roll`; or
- a completed `p : Path s` plus a cursor in `k p`.

`Cursor.liftAppend` transports the first case through append; `Cursor.joinRight` follows a complete
prefix path into the second case; an `AppendView` packages the disjoint classification. Split/join
must be inverse, expose residual equations, commute with cursor composition, agree with terminal
`Path.append`, and transport decoration restriction. This is the foundation RBR and reduction
composition actually need.

**PF-4 — Operational-prefix concatenation (gated).** If a concrete interaction-machine runtime needs
it, extend `DynSystem.Prefix` with dependent append/segment and endpoint/event/ticket laws. Ordinary
VCVio `OracleComp` phase traces concatenate through monadic execution and `QueryLog.append`; they do
not depend on this PR. The client must specify the phase-boundary witness and any required endpoint
transport before PF-4 is promoted.

**PF-5 — Pure causal transducers (required before compiler trace pipelines).** Add an effect-free
stateful Kleisli–Mealy companion to the existing stateless `Control.Trace`/`PFunctor.Trace` APIs:
`Control.Transducer ι ο` with state, `runFrom`/`runOpen`, identity, and sequential composition. Reuse
the existing list/free-monoid trace carriers and relabel/filter algebra rather than introducing a
second trace representation. Do not encode this as a `MooreMachine`: Moore output is a state
observation made before an input, whereas a transducer's finite output chunk depends jointly on the
current state and consumed input. Ordered-prefix causality follows from `runOpen_append`; it is not
an arbitrary proof field. Terminal `finish` output is a separate `Finalizer`, because flushing can
violate ordinary prefix monotonicity. Cost is an external certificate owned by the specialized
client. Identity and associativity are stated under explicit behavioral equivalence
(`∀ xs, T.runOpen xs = U.runOpen xs`) or a named state isomorphism, not structure equality across
existential state carriers.

**PF-6A — Polynomial interaction normalization (land before the naming cutover).** Identify the
undecorated type-tree polynomial with the free polynomial and expose its substitution-monoid,
finite-chain, stopping-tree, fold, and uniqueness structure. This is PR #62; it deliberately keeps
the historical names so the algebraic change remains reviewable.

**PF-6R — Type-tree true-sight naming (required before further interaction foundations).** Perform
the complete `Interaction.Spec → Interaction.TypeTree` and `Spec.Transcript → TypeTree.Path`
cutover, including module paths, namespace-owned APIs, specialization names, tests, maintained
documentation, and generated imports. Do not retain compatibility aliases. The representation and
all computation/universal-property statements remain unchanged. See `01b` for the exact map and
downstream train.

**PF-6B — N-ary presentation/coherence (gated).** Do **not** add a new
`TypeTree.Presentation` datatype as foundation work. First use existing
`TypeTree.Chain`/`TypeTree.StateChain`; when a concrete three-reduction client needs operational
reassociation, try dependent `Chain.then`, path join/split, and typed reassociation. A new
presentation type requires a recorded failed client and design note.

### 1.3 PolyFun acceptance

PF-1/2/3/5 are accepted only when both local laws and a downstream client pass. PF-6R additionally
requires the exact negative-search and definitional-behavior gates in `01b`:

- constructor and residual equations reduce by `rfl` where promised;
- cursor restriction along composition equals direct restriction;
- append cursor split/join is inverse on a genuinely dependent heterogeneous tree;
- no cast-freedom claim relies on `#print axioms` (`Eq.rec` is not an axiom); use `rfl`, `simp only`,
  and source-level absence of proof-generated transports;
- ArkLib defines one `FullPrefixAt` with PF-1/2 and decomposes composition with PF-3;
- VCVio specializes PF-5 to a query/world trace and proves one resource-transport theorem.

## 2. VCVio contract

### 2.1 Existing semantic center

The following are landed foundations, not missing abstractions:

- `OracleComp`, `QueryImpl`, `simulateQ`, sum/subspec coercions, `evalDist`, and `ProbComp`.
- `QueryImpl.Stateful I E σ`, state-separated frames, `run`/`runState`, state transport, linking, and
  parallel composition (`SimSemantics/StateT/StateSeparating.lean`).
- `SPMFSemantics` as interpretation plus observation, and existing state-oracle/UC runners.
- ordered dependent `QueryLog spec := List ((q : spec.Domain) × spec.Range q)`, logging/tracing
  transformers, output-marginal and failure bridge laws, cache/log projections.
- structural query bounds, per-index bounds, `ResourceProfile`, `CostModel`, pathwise/expected cost,
  and profile substitution.
- caching, lazy/eager random-oracle equivalence, programming policies, replay and seeded forking.
- TV distance, bind/bad-event bounds, birthday/collision kernels, deferred sampling, and many ROM
  probability lemmas.
- `NeverFail` and missing-mass algebra.
- abstract-advantage `SecurityGame`, negligibility, hybrid/reduction theorems, and composable
  `ReductionWithCost`.
- standalone commitment/Merkle algorithms and security theorems, including two-phase extraction.

Consequently V4/V7/V8/V9/V10 below are **consolidation or repair**, not greenfield replacements.

### 2.2 Required VCVio deltas

**V1 — Thin world/session package.** Package existing stateful semantics without creating a second
evaluator. A world contains a surface oracle interface, hidden state, setup computation, and
`QueryImpl.Stateful`; running delegates to `runState`/`simulateQ`. Observation and trace
instrumentation are orthogonal adapters, not fields of the core world.

One heterogeneous interface plus one shared state already represents correlated logical oracles.
Product-state construction and independence are deferred until a client supplies explicit joint
initialization/routing semantics; sequencing two initializers through one imported oracle can itself
correlate them. Initial distributions are setup computations. The first API retains VCVio's current universe-0 runtime boundary;
universe generalization is a separate PR.

**V2 — Query-event regions and traced execution.** Name the existing dependent event type, add
list-boundary/region operations (`take`, `drop`, interval, phase split), and projection along a named
interface embedding. Query position is derived from a list boundary, not stored in every event.
The oracle-domain tag supplies identity within a given interface. Globally stable resource identity
across reassociation is client schema data (ArkLib `ResourceSchema`), mapped into/out of VCVio
events by an adapter.

The traced runner returns output, final state, and trace from one execution. Erasure to the ordinary
runner, failure preservation, trace concatenation, and projection laws are mandatory.

**V3 — World-trace transducer specialization.** Specialize PolyFun PF-5; do not define another generic
transducer. Add external certificates relating input/output event counts or `ResourceProfile`s and
prove certificate composition. Hash/Merkle/SR transducer instances remain ArkLib/backend code.

**V4 — Resource transport consolidation.** Keep `ResourceProfile`, `QueryBound`, `CostModel`, and
`ReductionWithCost` as the vocabulary. Add named bridges from per-handler step bounds to linked
runtime imported-query bounds, from traced artifacts to profile inequalities, and through
instrumentation/transducer composition. Do not introduce a parallel `Budget` or `Ledger` hierarchy.

**V5 — Persistent probabilistic phase artifact.** VCVio VCV-3 implements the common
oracle-computation case: `resume` continues from final handler state and the old trace length becomes
the next region boundary. A separate adapter to PolyFun operational machines/PF-4 is gated on a real
client. This is not a universal “phased adversary” record; commit/open and five-phase interfaces
remain ArkLib or primitive-specific.

**V6 — Auditable dynamic programming.** Preserve existing static `ProgrammingPolicy`, caching,
replay, and fork kernels. Add a dynamic program command with an explicit result
(`fresh`, `alreadyProgrammed`, `queriedBeforeProgram`, conflict according to policy), an audit event,
and preservation/freshness laws. Add replay-policy adapters only where an actual extractor theorem
needs them; do not replace working replay implementations with a taxonomy.

**V7 — Error-bearing reduction composition.** Extend existing `SecurityGame` and
`ReductionWithCost` with a bundled composable security reduction carrying advantage error and cost
transform. Add additive and substitution-style composition for error functions. Do not make
failure probability an intrinsic field of every adversary, and do not stabilize a universal
`AdvCharacteristics` until two non-CY clients demand it. CY-specific extraction-time recurrences
remain ArkLib theorems over generic function algebra initially.

**V8 — Probability facade and repairs.** Add a scalar conditional-probability facade and finite
partition lemmas, and only the generic lemmas demanded by real games. Existing exact birthday bounds and lazy/eager
equivalence count as delivered. Before claiming the ROM kit adequate, repair or quarantine the
currently trivial `probEvent_unqueried_match_le` and the vacuous `Unique ι` collision-win theorem in
`QueryTracking/Unpredictability.lean`.

**V9 — One failure boundary.** Preserve the existing meaning: missing `SPMF` mass is monadic
failure/nontermination. An explicit protocol `fault` is a returned value, not silently identified
with missing mass. Provide one named `materialize (onMissing : RuntimeFault)` bridge to
`Outcome α RuntimeFault`. The default
ArkLib path must either prove `NeverFail` before decoding a `Terminal`, or explicitly choose and
name `onMissing`. For `α = Terminal Claim ProtocolFault`, runtime failure and returned protocol fault
remain two distinct branches. No second semantics is introduced.

**V10 — Complete existing game/reduction calculus.** Keep `SecurityGame Adv` and abstract adversary
class predicates. Add the bundled reduction from V7, dependent/parameter-indexed adversary support
only if a concrete game cannot use the current form, and setup/keygen inside concrete experiments.
Do not add the proposed Boolean-only `GameFamily Params experiment` in parallel. Uniformity,
nonuniformity, and advice are properties of the adversary representation/class, not fields guessed
by the generic game record.

### 2.3 VCVio acceptance

The Γ foundation is adequate for ArkLib's first security phase when:

1. a heterogeneous correlated world runs through V1 with no special joint-world primitive;
2. its traced run erases to the same output distribution and failure mass;
3. two resumed phases produce the same final semantics as sequential execution, and their regions
   concatenate in order;
4. query/profile bounds transport through one linked stateful simulation and one PF-5 transducer;
5. dynamic programming distinguishes query-before-program and preserves unprogrammed answers;
6. one error-bearing `SecurityReduction` composes both advantage loss and cost transformation;
7. a finite conditioned bad-event proof uses the V8 facade;
8. both defective ROM statements named above are repaired or removed from the advertised kit;
9. an explicit-fault game proves `NeverFail` before ArkLib terminal decoding;
10. the existing Merkle extraction theorem can be adapted by ArkLib without restating its primitive
    experiment.

## 3. ArkLib contract

ArkLib owns and must build:

- protocol syntax and the public/oracle observation split;
- concrete oracle-message access and execution;
- extensional source contexts plus a separate resource schema for identity, origin, aliasing, and
  ideal guarantees, with later backend assignment indexed by that schema;
- virtual-oracle interpretation, substitution, claims, and runner-derived closing (`02`);
- protocol security games, relations, extractors, implication maps, and state restoration (`03`);
- commitment-backend adapters, guarantee transport, compiler passes, and concrete proof systems
  (`04`);
- legacy bridges and migration ledgers.

ArkLib must not define private replacements for PolyFun cursor/transducer algebra or VCVio
world/probability/resource/game semantics. A temporary adapter is allowed only when it has:

1. a named upstream issue/PR dependency;
2. no new theorem stated solely in the temporary vocabulary;
3. a deletion/migration test in the consuming ArkLib PR.

Standalone primitive theorems may remain in VCVio even when ArkLib consumes them. For example,
Merkle extraction is a VCVio cryptographic theorem; the ArkLib object is a `CommitBackend` adapter
and transfer proof.

## 4. Resource identity and the real/virtual boundary

Two layers are both necessary:

- `SourceCtx` is the extensional handler presentation used to interpret virtual query programs.
- `ResourceSchema` records stable client identity, origin, guarantee, and sharing/aliasing.
- `BackendAssignment` is a later compiler object indexed by a `ResourceSchema`; it is not intrinsic
  ideal-resource data.

Pure `SourceHom` routes extensional handlers. `SchemaHom` lies over a `SourceHom` and proves identity,
sharing, origin, and guarantee coherence. Virtual-oracle substitution depends only on `SourceHom`;
compiler and trace theorems use `SchemaHom`.

Every reified guarantee descriptor also carries a coherence witness relating it to the slot's
actual ideal object/refined type. Metadata that merely *claims* a degree/codeword guarantee without
this witness is ill formed.

VCVio query events are tagged by the currently executed oracle interface. ArkLib proves that its
schema routing maps those tags coherently across context morphisms. Neither VCVio instrumentation
nor reassociation of nested sum types can manufacture globally stable identity by itself.

This separation is a foundation decision. Enriching `SourceCtx` directly with all compiler metadata
would contaminate semantic substitution; omitting `ResourceSchema` would make aliasing, trace
projection, and guarantee transport prose-only.

## 5. Release and branch discipline

Foundation implementation advances in compatible candidates, not one serialized mega-release.
The current release train is:

```text
Lean 4.33.1 + VCVio f9dc47d9 + VCVio-selected PolyFun c0c92369 → ArkLib alignment
landed TypeTree/cursor/strategy and responder/resource/kernel APIs → AR-1…AR-8
missing transducer/runtime-artifact/outcome APIs → AR-9A/9B and AR-10B
conditioning/dynamic-programming APIs → state restoration and compiler work
```

- Every PR starts from its repository's current default branch.
- The design branch is never merged as an implementation batch.
- Lake manifests use exact/tagged compatible revisions; ArkLib must not override PolyFun with a
  revision inconsistent with the one VCVio was tested against.
- Mechanical toolchain/pin changes are isolated from semantic PRs.
- Candidate revisions are exact commits used for downstream validation; stable tags/frozen
  interfaces are published only after the named clients pass. This avoids a circular requirement
  that an upstream API be frozen before the downstream acceptance client can build.
- CI checks the resolved PolyFun revision and rejects duplicate/inconsistent package instances.

## 6. Freeze discipline

An item freezes only after:

1. its local laws and tests pass;
2. the first downstream client named in `01a` passes;
3. adapters to the pre-existing vocabulary are proved;
4. no parallel type with the same semantics remains unexplained.

The design equations in `02` are **provisional signature sketches** until universe-polymorphic Lean
declarations and two concrete clients elaborate. Directional principles may be stable while field
layouts remain fluid. Changes to an accepted interface require a decision-log entry; unimplemented
or client-unvalidated names do not.

## 7. Cross-library contract tests

The release train is accepted only when these end-to-end checks pass:

1. `restrict (restrict d c) e = restrict d (c.comp e)` and cursor-spine accumulation composes;
2. append cursor split/join is inverse and is consumed by a composite ArkLib reduction;
3. VCVio query tracing erases to the same output distribution and missing mass;
4. ArkLib resource identity survives context routing and maps coherently to VCVio event tags;
5. query/profile bounds transport through `simulateQ`, linked handlers, and a virtual-oracle
   substitution client;
6. world phase regions concatenate in execution order;
7. explicit fault and missing mass cross exactly one named boundary;
8. VCVio Merkle extraction instantiates an ArkLib backend capability without duplicating its game;
9. security experiments are defined over the actual `runArtifact execute` distribution; any theorem
   about an arbitrary artifact requires support/`GeneratedBy` evidence, and the game API exposes no
   split-parts experiment constructor;
10. repository imports preserve `PolyFun ← VCVio ← ArkLib` with no cycle.
