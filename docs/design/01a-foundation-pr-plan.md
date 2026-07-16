# 01a — Foundation Landing Plan: Exact PR Slices

**Operational companion to `01`.** Every item below is intended to be a reviewable PR with one
semantic center. Medium or large proof payloads are acceptable; mixed ownership, speculative
frameworks, and unrelated migrations are not.

## 0. Rules of execution

1. **Fresh bases.** Every implementation PR starts from the repository's current default branch.
   The design branch is a source bank, never a merge base for implementation.
2. **One semantic addition.** A PR may add the definitions, laws, tests, and documentation needed
   for one coherent abstraction. It must not also migrate unrelated protocols.
3. **Mechanical changes are isolated.** Dependency pin/toolchain PRs (`VCV-0`, `AR-0`) are explicit
   non-semantic exceptions and contain no API redesign.
4. **Reuse before wrapping.** A new type that overlaps an existing one requires an equivalence or a
   written reason why the old carrier cannot express the new semantics.
5. **Client acceptance.** Local toy tests are necessary but insufficient for a foundation freeze;
   each item names its first downstream client.
6. **No proof-generated plumbing in core carriers.** Promised computation equations are tested by
   `rfl`/`simp only` and source inspection, not by `#print axioms`.
7. **No new sorries.** Prototype sorries are not copied. A blocked theorem narrows or delays the PR.

## 1. Dependency and landing order

```text
PolyFun
  PF-1 Cursor ─→ PF-2 Cursor restriction ─→ PF-3 Cursor/append
  PF-4 Operational-prefix concatenation             (gated)
  PF-5 Causal transducer                            (parallel)
  PF-6 Chain concatenation                          (gated)
       ↓ candidate revision; tag after downstream acceptance

VCVio
  VCV-0 pin bump to a PF candidate revision
  VCV-1 Trace views ─┐
  VCV-2 Runtime ─────┴→ VCV-3 Runtime artifact ─→ VCV-5A/5B Resource transport
  PF-5 ───────────────→ VCV-4 Trace-transducer specialization
  VCV-3 ──────────────→ VCV-6 Dynamic programming
  VCV-7A/7B Conditioning; VCV-8A/B/C ROM repairs; VCV-9 Outcome; VCV-10 Reductions
       ↓ candidate revision; tag after downstream acceptance

ArkLib
  AR-0 dependency alignment
  AR-1 plain reductions
  AR-2A syntax → AR-2B decorations → AR-3A access → AR-3B concrete execution
  AR-4A SourceCtx/SourceHom → AR-5 virtual substitution
  AR-4B ResourceSchema/SchemaHom ───────────────┐
  AR-5 → AR-6A claims/closing ──────────────────┴→ AR-6B core-run integration
                                                → AR-7 sumcheck → AR-8 sumcheck bridge
  PF-1..3 + AR-2B/3A/4B ───────────────────────→ AR-10A structural full prefixes
  VCV-3 + AR-6B ───────────────────────────────→ AR-9A runtime artifact adapter
  VCV-9 + AR-9A ───────────────────────────────→ AR-9B outcome boundary
  AR-10A + AR-9A ──────────────────────────────→ AR-10B trace alignment
  VCV Merkle + AR-9A/VCV-10 ───────────────────→ AR-11 Merkle backend adapter
```

Useful parallelism:

- PF-1 and PF-5 can start together; PF-4 waits for a machine client.
- VCV-7A, VCV-8A, VCV-9, and VCV-10 can land against the current VCVio substrate.
- After AR-0, AR-1, AR-2A, and AR-4A can proceed independently.
- Compiler and advanced security work is deliberately outside this foundation train; `05` schedules
  it after the first runner-backed security client.

Semantic requirement IDs in `01` intentionally match PolyFun PR IDs. VCVio requirements collect
several slices, so use this mapping rather than assuming numeric equality:

| Requirement | Implementing PRs |
|---|---|
| V1 runtime | VCV-2 |
| V2 trace/artifact | VCV-1, VCV-3 |
| V3 transducer specialization | VCV-4 |
| V4 resource transport | VCV-5A, VCV-5B |
| V5 persistent phases | VCV-3 common case; machine adapter gated |
| V6 programming/replay delta | VCV-6 |
| V7 reduction errors/cost | VCV-10 |
| V8 probability/ROM repair | VCV-7A/B, VCV-8A/B/C |
| V9 outcome boundary | VCV-9 |
| V10 game/reduction completion | VCV-10 |

## 2. PolyFun PRs

### PF-1 — `feat(free): cursors for partial FreeM paths`

**Semantic unit.** A syntactic path prefix that selects any residual subtree.

**Module.** New `PolyFun/PFunctor/Free/Cursor.lean`.

**Declarations.** `FreeM.Cursor s`; `Cursor.residual`; `Cursor.root`; `Cursor.down`;
`Cursor.comp`; `Cursor.length`; `Cursor.IsTerminal`; one-node edge view; witness-bearing
`Cursor.Extends c d := Σ e : Cursor c.residual, c.comp e = d`; equivalence between terminal cursors
and `FreeM.Path s` (including the selected leaf payload).

**Central laws.** Residual at root/down; left/right unit and dependent associativity of `comp`;
length addition; terminal-cursor/`Path` round trips.

**Acceptance.** A heterogeneous dependent tree with an internal cursor and two terminal cursors;
constructor equations by `rfl`; no collision with `DynSystem.Prefix` or `Concurrent.Front` names.

**Not included.** Decorations, append decomposition, operational runs, or protocol meaning.

**Unlocks.** PF-2/PF-3 and ArkLib's reachable-prefix carrier.

### PF-2 — `feat(displayed): restrict displayed data along cursors`

**Prerequisite.** PF-1.

**Module.** New `PolyFun/PFunctor/Free/Displayed/Cursor.lean`.

**Declarations.** `Displayed.Shape.ChildProjection` and its dependent
`Displayed.OverShape.ChildProjection` counterpart; one generic cursor-spine restriction algorithm
parameterized by that capability; canonical `Decoration.restrict` and
`Decoration.Over.restrict` specializations. An unconstrained `Displayed.Shape` does not admit a
generic `restrict`, because `D.node a child` need not expose any `child b`. These operations describe
the future residual subtree, not visited-prefix history.

**Central laws.** Root/down computation; restriction along `Cursor.comp`; naturality with existing
`Decoration.map`, `Over.map`, and `Over.mapBase`; compatibility with `ofOver`/`toOver`. The generic
spine traversal is defined once; decoration layers provide only their local child projections.

**Acceptance.** Constructor examples close by `rfl`; a dependent decoration proof closes with
`simp only`; ArkLib can restrict role and oracle decorations at one protocol cursor.

**Not included.** A claim that every displayed shape is navigable, or a new generic decoration-map
hierarchy—most of P3 in the old plan already exists.

### PF-3 — `feat(free): cursor decomposition through dependent append`

**Prerequisites.** PF-1 and the existing `FreeM.Path.append/split` kit; PF-2 for decoration corollaries.

**Module.** New `PolyFun/PFunctor/Free/Cursor/Append.lean`.

**Semantic unit.** Classify a cursor through `FreeM.append s k` without casts.

**Declarations.** `Cursor.IsNode`; `Cursor.liftAppend`; `Cursor.joinRight`; and a dependent
`Cursor.AppendView` with two disjoint cases: a cursor in `s` carrying an explicit witness that its
residual is an internal node, or completed `p : Path s` plus cursor in `k p`; `split`, `join`, and
residual projections. Include the direct `Decoration` and `Decoration.Over` restriction corollaries.

**Central laws.** Split/join inverses; residual equations; compatibility with terminal
`Path.split/append`; `liftAppend` and `joinRight` respect cursor composition; restriction through
both cases agrees with `Decoration.append` and `Decoration.Over.append`.

**Acceptance.** A dependent two-stage tree exercises both cases. The first ArkLib composition
client decomposes a reachable cursor into stage-one/stage-two cases.

### PF-4 — `feat(dynamical): concatenate finite operational prefixes` (gated)

**Promotion trigger.** A concrete interaction-machine runtime needs phase segments; ordinary
`OracleComp`/`QueryLog` phases do not.

**Module.** `PFunctor/Dynamical/Run/Prefix.lean` or a focused extension of `Run.lean`.

**Declarations.** Dependent `DynSystem.Prefix.append` plus an explicit `segment/drop` carrying the
endpoint equality/transport; optional inclusion relation; bridges from `Run.take`.

**Central laws.** Endpoint of append; unit/associativity; event and ticket list concatenation;
`Run.take (m+n)` decomposition propositionally through the segment endpoint (not promised `rfl`).

**Acceptance.** A two-phase pointed machine with an explicit halting/phase-boundary witness whose
global event list is the append of both segments.

**Not included.** Probabilistic worlds or commit/open games.

### PF-5 — `feat(control): causal finite-trace transducers`

**Module.** New `PolyFun/Control/Transducer.lean`.

**Existing substrate and boundary.** `Control.Trace` and `PFunctor.Trace` already provide stateless
monoid/list emission and the canonical polynomial trace carrier; PF-5 reuses those representations
and their relabel/filter algebra. A transducer is the stateful Kleisli–Mealy companion whose output
chunk depends on both state and input. It is not represented as a `MooreMachine`, whose output is a
state observation before an input is consumed.

**Indicative interface.**

```lean
structure Transducer (ι ο : Type*) where
  State : Type*
  init : State
  step : State → ι → State × List ο

def Transducer.runFrom
def Transducer.runOpen
def Transducer.id
def Transducer.comp
```

Define `BehaviorEq T U := ∀ xs, T.runOpen xs = U.runOpen xs` (or a stronger named state isomorphism
when needed).

`Finalizer` is separate and supplies `finish : State → List ο` only when a client needs terminal
flushing.

**Central laws.** `runFrom_append`; ordered-prefix causality of `runOpen`; streaming law;
identity/composition and associativity under `BehaviorEq`; optional canonical state isomorphisms are
separate stronger results.

**Acceptance.** Compose filter and expand transducers and compare with `PFunctor.Trace.mapPartial`.
VCVio's query-log adapter is thin and attaches its own output-length/resource certificate.

**Not included.** A second trace carrier, a forced `MooreMachine` encoding, or `coherence`/`cost`
fields—causality is a theorem and cost is external.

### PF-6 — `feat(interaction): dependent concatenation of Spec.Chain` (gated)

**Promotion trigger.** A concrete ArkLib triple-reduction client cannot state operational
reassociation using existing `Spec.Chain`/`StateChain`.

**Module.** `PolyFun/Interaction/Basic/Chain/Append.lean`.

**Candidate declaration.**

```lean
Chain.then (c : Chain m) (k : Transcript (toSpec m c) → Chain n) : Chain (m + n)
```

Add propositional `toSpec_then`, telescope transcript join/split, and three-stage typed
reassociation handling `Nat.add` and dependent transcript reindexing explicitly.

**Acceptance.** The actual ArkLib client, not an isolated toy. Only a documented failure of this
route authorizes a new `Presentation` datatype.

## 3. VCVio PRs

### VCV-0 — `chore: advance the tested PolyFun candidate revision`

**Mechanical prerequisite.** Update the exact PolyFun pin after the PF PRs needed by the next VCVio
slice land; refresh the manifest and build/lint/test. This may happen more than once as candidate
revisions advance. No semantic declaration changes. A stable tag is published only after the named
downstream VCVio/ArkLib clients pass.

### VCV-1 — `feat(query-tracking): dependent trace views and boundaries`

**Module.** New `VCVio/OracleComp/QueryTracking/TraceView.lean`.

**Declarations.** Name `QueryEvent E := (q : E.Domain) × E.Range q` while retaining `QueryLog E` as
the carrier; boundary marks `Fin (trace.length + 1)`; `prefixAt`, `suffixAt`, `interval`; predicate
and sum-component projection; typed projection along an existing `SubSpec`/route carrying the
dependent response transport.

**Central laws.** Zero/end; prefix+suffix reconstruction; nested interval; append-boundary equations;
projection over append; length bounds.

**Acceptance.** Slice and project an `E₁ + E₂` trace while preserving order. Position is derived from
boundaries, not duplicated in events.

**Unlocks.** Exact Δ/world trace regions and phase marks.

### VCV-2 — `feat(stateful): reusable oracle runtime package`

**Module.** New `VCVio/OracleComp/SimSemantics/StateT/Runtime.lean`.

**Indicative interface.**

```lean
structure OracleRuntime (I : OracleSpec ιI) (E : OracleSpec ιE) where
  State : Type
  init : OracleComp I State
  handler : QueryImpl.Stateful I E State
```

The first PR uses the currently supported universe-0 runtime boundary. `runState` samples `init` once
and delegates to existing `Stateful.runState`; `run` erases state.

**Central laws.** Map functoriality; `ofHandler`; and the exact sequential law: after `runState A`
returns `(a,s)`, continue `simulateQ handler (f a)` from `s` without resampling `init`.

**Important restriction.** No generic initialized-runtime `link`, product, or independence theorem
is promised. Initializing an outer runtime through an inner handler changes order and can couple
states. Such a constructor requires an explicitly supplied joint initializer in a later client PR.

**Acceptance.** One heterogeneous runtime exposes two logical oracles sharing a sampled secret and
the continuation law shows initialization occurs exactly once. Existing `withStateOracle`/UC
runners are related by adapters, not replaced in this PR.

### VCV-3 — `feat(query-tracking): runner-produced runtime artifacts`

**Prerequisites.** VCV-1 and VCV-2.

**Module.** New `VCVio/OracleComp/QueryTracking/RuntimeArtifact.lean`.

**Declarations.** `QueryImpl.Stateful.withQueryLog`; a core artifact containing output, final state,
and ordered query log; `OracleRuntime.runArtifact`; `resume` from final state. A resume/session view,
not every artifact, records the old log length as a region boundary.

**Central laws.** Trace erasure equals `runState`; state+trace erasure equals `run`; failure mass is
preserved; resumption threads exactly the artifact's state; two runs append traces and place the
checkpoint at the first length.

**Acceptance.** Two phases in one lazy-RO runtime preserve one cache and yield
`globalTrace = phase1Trace ++ phase2Trace`. The artifact is the only input to resumption.

**Unlocks.** ArkLib runner-backed `ExecutionArtifact` and the common `OracleComp` case of semantic
V5. A PolyFun-machine adapter is gated on a later client.

### VCV-4 — `feat(query-tracking): certified query-trace transducers`

**Prerequisites.** PF-5, VCV-0, and VCV-1.

**Module.** New `VCVio/OracleComp/QueryTracking/Transducer.lean`.

**Declarations.** Query-log specialization of `Control.Transducer`; streaming runner; predicate and
component filters; external `OutputLengthBound`/`TransducesWithin` certificate.

**Central laws.** Specialization agrees with PolyFun `runOpen`; certificate identity/composition;
component filtering preserves event order.

**Acceptance.** Compose component filtering with a toy backtracking transducer and prove both
streaming equality and `|out| ≤ f |in|`.

### VCV-5A — `feat(query-tracking): imported-query bounds through stateful handlers`

**Prerequisite.** Existing `QueryBound`/`Stateful.link`; VCV-3 only for artifact corollaries.

**Module.** New `VCVio/OracleComp/QueryTracking/ResourceTransport.lean`.

**Semantic unit.** One exact structural bound; no new ledger.

**Central theorem shape.** Given `IsPerIndexQueryBound A qE` and a uniform-in-state bound
`∀ e s, IsPerIndexQueryBound ((handler e).run s) (qI e)`, the imported-interface query count of the
linked run is bounded by the explicit finite convolution/sum of `qE` through `qI`.

**Acceptance.** A two-component finite handler yields the explicit per-component and global sum.

### VCV-5B — `feat(query-tracking): resource-profile and artifact transport adapters`

**Prerequisites.** VCV-3, VCV-4, VCV-5A. Relate VCV-5A to existing `ResourceProfile`, `CostModel`,
artifact surface-trace counts, and transducer certificates. Keep imported-query bounds distinct from
surface artifact counts. **Acceptance:** ArkLib uses one adapter through virtual substitution.

### VCV-6 — `feat(query-tracking): auditable dynamic oracle programming`

**Prerequisite.** VCV-3.

**Module.** New `VCVio/OracleComp/QueryTracking/DynamicProgrammingOracle.lean`.

**Declarations.** A command interface containing query and `program(q,a)`; cache plus ordered audit
state; disjoint precedence: `inserted` for fresh unqueried points, `alreadySame` for an existing
identical assignment, `conflict` for an existing different programmed assignment, and
`sampledBeforeProgram` when a query sampled the point first. Programming after sampling rejects and
does not overwrite in the foundation policy.

**Central laws.** Inserted points answer the programmed value; failed programming preserves cache;
unrelated points are unchanged; audit events characterize query-before-program/conflict; a preloaded
dynamic world agrees with existing static `withProgramming`.

**Acceptance.** Phase one queries `x`; phase two programs `x` and fresh `y`; `x` reports the policy
failure, `y` is installed, unrelated answers persist.

**Not included.** Rewriting existing `ReplayFork`/`SeededFork` APIs.

### VCV-7A — `feat(eval-dist): scalar conditional probability`

**Module.** New `VCVio/EvalDist/Conditioning.lean`.

**Declarations/laws.** Scalar `condProb A B := Pr[A ∩ B] / Pr[B]` for returned-value events with
`Pr[B] ≠ 0`; missing mass is outside both events. Prove monotonicity, complement, Bayes, and a finite
conditioned union bound. Do not introduce a normalized distribution in this PR.

**Acceptance.** A genuine conditioned bad-event proof uses the facade. It must not merely restate an
unconditioned structural induction.

### VCV-7B — `feat(eval-dist): finite conditional partitions` (split if needed)

**Prerequisite.** VCV-7A. Add total probability over a finite returned-value partition and the
partition lemmas needed by the first salted game. Keep this separate if VCV-7A is already large.

### VCV-8A — `fix(random-oracle): quarantine vacuous unpredictability theorems`

**Prerequisite.** Existing logging/birthday theory only.

Replace or quarantine the trivial `probEvent_unqueried_match_le` and vacuous `Unique ι`
collision-win statement; add the nonvacuous one-oracle distinct-input collision form.

### VCV-8B — `feat(random-oracle): adaptive target-hit and fresh-response bounds`

**Prerequisites.** VCV-5A and existing `HasUnpredictableSample`. Prove adaptive fresh-response and
target-hit ≤ structural query budget × point mass. A nontrivial example uses every hypothesis.

### VCV-8C — `feat(random-oracle): hidden-salt queried bound`

**Prerequisites.** VCV-7A/7B and VCV-8B. Prove the conditioned hidden-salt corollary used by SR/BCS.

### VCV-9 — `feat(eval-dist): explicit outcome observation`

**Module.** New `VCVio/EvalDist/Outcome.lean`.

**Declarations.** `Outcome α RuntimeFault`; `materialize (onMissing : RuntimeFault)` from the
existing `SPMF α`/`PMF (Option α)` representation.

**Central laws.** Success and outer runtime-fault probabilities; `NeverFail` iff the outer
`onMissing` branch has probability zero; map/bind compatibility. If `α` itself contains a protocol fault, that
returned branch remains distinct.

**Acceptance.** A failing `OptionT ProbComp` maps missing mass exactly to the chosen `fault`, while a
never-failing game has zero materialized fault probability.

### VCV-10 — `feat(asymptotics): composable error- and cost-aware security reductions`

**Module.** New `VCVio/CryptoFoundations/Asymptotics/Reduction.lean`.

**Declarations.** `SecurityReduction g h` with adversary map, adversary-class preservation,
pointwise advantage inequality, and adversary/parameter-indexed additive error; identity/composition;
`CostedSecurityReduction` paired with existing
`ReductionWithCost`.

**Central laws.** For `R₁ : G → H` and `R₂ : H → K`,
`εcomp A n = ε₁ A n + ε₂ (R₁.mapAdversary A) n`; cost transforms compose; security transfers when
the target adversary class is preserved and each admissible source adversary's error is negligible.

**Acceptance.** Two toy reductions normalize to the expected composed advantage error and cost
transform.

**Not included.** Boolean-only game experiments, setup fields, universal `AdvCharacteristics`, or a
second `GameFamily` hierarchy.

## 4. ArkLib PRs

All ArkLib PRs below start from current ArkLib `main` after AR-0. Prototype files on the design
branch are source banks; declarations are reintroduced in reviewable slices.

### AR-0 — `chore: align the PolyFun/VCVio/Lean compatibility train`

**Prerequisites.** Exact candidate revisions of PolyFun/VCVio known to build together; this does not
wait for every foundation PR or a post-client stable tag.

Start by reviewing and rebasing the existing `quang/bump-v4.31.0` candidate (`55a9ccc` at the
2026-07-13 audit), which already pins VCVio `cbd4144b` and its tested PolyFun `04a12b6`; do not
duplicate its compatibility fixes. Update Lean/Mathlib, VCVio, CompPoly, and documentation dependencies; eliminate any direct PolyFun
override inconsistent with VCVio; refresh the manifest; add CI checks for resolved revisions and
duplicate packages. Cold clone, cache fetch, full build, lint, and tests must pass. Later runtime and
security candidate revisions arrive in separate mechanical bump PRs.

### AR-1 — `feat(interaction): plain dependent reduction kernel`

**Prerequisite.** AR-0 and existing PolyFun append/strategy APIs.

**Declarations.** `HonestProverOutput`, `Prover`, `Verifier`, `Reduction`, `execute`, identity, and
`comp`. **Theorems:** `execute_comp`, identity laws, transcript split/append. **Acceptance:** two
dependent toy protocols; cast-free constructor equations; no oracle/security content.

### AR-2A — `feat(interaction): oracle syntax and transcript projections`

**Prerequisite.** AR-0. **Declarations:** `Oracle.Position`, `Oracle.Spec`, `PublicTranscript`,
`FullTranscript`, execution lens/public projection, `OracleMessagesAt`. **Theorems:** full transcript
as public transcript plus hidden-message fiber, round trips, payload-independent oracle continuation.
**Acceptance:** public–oracle–public and dependent-public-branch examples using `rfl`/`simp only`.

### AR-2B — `feat(interaction): role and oracle decorations`

**Prerequisite.** AR-2A. **Declarations:** `RoleDeco`, `OracleDeco`, projections, accumulated
visibility, PolyFun-decoration conversions. **Theorems:** map/append/projection naturality.
**Acceptance:** recover exactly the public and oracle nodes of the AR-2A mixed protocol.

### AR-3A — `feat(interaction): accumulated oracle access`

**Prerequisite.** AR-2B. **Declarations:** `answerAt`, query handles, accumulated message interface
and implementation, full-transcript realization. **Theorems:** concrete-answer agreement, public
projection invariance, and future-message unavailability. **Acceptance:** passthrough and one-round
sumcheck access.

### AR-3B — `feat(interaction): oracle prover/verifier execution`

**Prerequisites.** AR-1, AR-2B, AR-3A. **Declarations:** oracle prover/verifier/reduction wrappers and
executor. **Theorems:** routing agrees with AR-3A; erasure agrees with AR-1; public-output projection
commutes with execution. **Acceptance:** end-to-end passthrough and one-round execution.

### AR-4A — `feat(oracle-reduction): extensional sources and routing`

**Prerequisite.** AR-0. **Declarations:** universe-polymorphic `OracleFamily`/`Behavior`, extensional
`SourceCtx`, pure `SourceHom`, tensor/weaken/rename/`asSource`. **Theorems:** `SourceHom`
identity/composition, interpretation naturality, tensor disjointness, handler reassociation.
**Acceptance:** equal-signature components remain distinct by routing; no metadata fields.

### AR-4B — `feat(oracle-reduction): resource identity and guarantee schemas`

**Prerequisites.** AR-4A and an ideal-only guarantee descriptor module. **Declarations:**
`ResourceId`, `ResourceOrigin`, `ResourceSchema`, explicit sharing, `SchemaHom` lying over
`SourceHom`, and a witness connecting every reified guarantee descriptor to the actual slot
object/refined type. **Theorems:** schema composition, stable identity under routing, sharing without
cloning, guarantee-coherence transport. **Acceptance:** incoherent guarantee metadata is
unconstructible. `BackendAssignment` is absent and will later be indexed by this schema.

### AR-5 — `feat(oracle-reduction): virtual-oracle substitution algebra`

**Prerequisite.** AR-4A; schema corollaries may use AR-4B. **Declarations:** `VirtualOracle`, `eval`,
`ofQuery`, reindex/weaken, `subst`, semantic equivalence. **Theorems:** evaluation, identity,
associativity up to source equivalence, and `SourceHom` naturality. **Acceptance:** passthrough,
linear combination, shared/disjoint two-stage substitution.

### AR-6A — `feat(oracle-reduction): claim representations and closing`

**Prerequisite.** AR-5. **Declarations:** `ClaimWith`, open/closed/data claims, `answerData`, generic
`closeWith`. **Theorems:** honest realization, `SourceHom` naturality, data/virtual behavior
equivalence. **Acceptance:** passthrough and linear-combination closing.

### AR-6B — `feat(oracle-reduction): core execution output and run-derived closing`

**Prerequisites.** AR-3B, AR-4B, AR-6A. **Declarations:** trace-free `CoreRun` pairing one execution's
public result, hidden input/message resources, prover payload, and virtual claim outcome;
`executeCore`; `closingEnv`/`closed` projections. **Theorems:** execute/closing realization and honest
data realization. **Acceptance:** supported execution closes by projecting one `CoreRun`. This is an
API discipline, not a nominal run identity; Δ/Γ traces are not fields yet.

### AR-7 — `feat(sumcheck): one-round completeness through closing`

**Prerequisites.** AR-3B, AR-6B. Port one single-round sumcheck with a coherent degree guarantee,
query-derived scalar, honest realization, and perfect completeness through closing. **Acceptance:**
sorry-free; D1 exercised without soundness/compilation.

### AR-8 — `feat(sumcheck): legacy correspondence for the first slice`

**Prerequisite.** AR-7. Add only the sumcheck-specific legacy adapter/correspondence, migration
ledger, execution theorem, and completeness theorem. **Acceptance:** one real consumer migrates
without a flag day. Extract a generic supported-fragment adapter only after a second client.

### AR-10A — `feat(interaction): structural full prefixes at cursors`

**Prerequisites.** PF-1/2/3, AR-2B, AR-3A, AR-4B. **Declarations:** `FullPrefixAt` containing a public
cursor, the concrete hidden-message prefix/fiber accumulated along its spine, reachability evidence,
and prefix resource schema. This is distinct from `Decoration.restrict`, which describes the future
residual subtree. **Theorems:** no future resources, monotonicity under witnessed cursor extension,
and composite split/join. **Acceptance:** two-round protocol, verifier fork, sequential composite.

### AR-9A — `feat(security): logged and world-backed execution artifact adapter`

**Prerequisites.** AR-6B and VCV-1/2/3/5 candidate revisions. **Declarations:** `LoggedRun` adding Δ
`QueryLog` to `CoreRun`, `executeLogged`, and ArkLib `ExecutionArtifact` as a dependent view of the
VCVio runtime artifact. **Theorems:** erasure, phase concatenation, schema/event routing, and
closing/trace projection under the actual runner distribution (or explicit `GeneratedBy`/support
evidence). **Acceptance:** lazy RO and correlated logical oracles; game experiments run the artifact
producer rather than accepting arbitrary split parts; no private duplicate semantics.

### AR-9B — `feat(security): terminal outcomes and the failure boundary`

**Prerequisites.** AR-9A and VCV-9. **Declarations:** `Terminal` decoding/materialization and the
single named missing-mass boundary. **Theorems:** `NeverFail` decoding and outcome probabilities.
**Acceptance:** accept/reject/explicit-fault plus a failing computation materialized only through the
named bridge.

### AR-10B — `feat(security): align protocol prefixes with execution artifacts`

**Prerequisites.** AR-10A and AR-9A. Add instrumentation relating each protocol node/phase boundary
to zero or more Δ/Γ query events; do not assert generic prefix equality. Prove boundary monotonicity,
trace-region concatenation, and agreement of the reachable full prefix with the artifact projection.
**Acceptance:** a node issuing zero queries and a node issuing multiple queries.

### AR-11 — `feat(commitment): adapt VCVio Merkle extraction as a backend capability`

**Prerequisites.** AR-4B, AR-9A/9B, VCVio's existing Merkle extraction theorem, VCV-10. Add a minimal
Merkle `CommitBackend` adapter, event/resource translation, and guarantee-transport proof. Prove the
capability with VCVio's same bound and without restating the primitive game. **Acceptance:** one
compiler-facing conformance theorem; unsupported proximity/batching capabilities remain absent.

## 5. Freeze and release checkpoints

### Checkpoint A — base compatibility and structural candidates

Publish exact candidate revisions sufficient for AR-0; do not wait for all foundation work. When
PF-1/2/3 and PF-5 are locally green, advance VCVio/ArkLib candidate pins. Freeze/tag them only after
the actual AR-10A and VCV-4 clients pass. PF-4 remains gated.

### Checkpoint B — probabilistic runtime

VCV-1/2/3/5A/5B/9 pass their acceptance tests and enable AR-9A/9B through a runtime candidate
revision. VCV-7A/B and VCV-8A/B/C form a later security/ROM candidate; VCV-6 enables reprogramming;
VCV-10 enables computational backend transfer. Stable tags follow downstream acceptance and always
record the tested PolyFun revision.

### Checkpoint C — first ArkLib vertical slice

AR-0 through AR-7 pass, including one-round sumcheck completeness through run-derived closing. At
this point the carrier signatures may freeze provisionally. AR-8 proves migration is possible;
AR-10A accepts the cursor substrate; AR-9A/9B and AR-10B open the security track.

### Checkpoint D — foundation accepted for compiler work

The ten cross-library tests in `01` §7 pass, AR-11 adapts a VCVio Merkle theorem rather than
restating it, and the ordinary-soundness composition theorem in `03` is expressible with exact
resource transport. Only then should `04` capability and compiler interfaces freeze.
