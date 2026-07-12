# Fresh-eyes critique of ArkLib’s oracle-reduction design

## Executive verdict

The behavioral carrier, autonomous closing boundary, substitution-based composition, and Γ/Δ split are coherent choices. The next blockers are below that level:

1. The proposed joint execution result is not actually typed.
2. The transcript half of `SourceCtx.Env` contradicts the document’s claim that malicious prover oracles range over arbitrary behaviors.
3. The relation layer depends on an undefined `ClaimSchema` and alternates inconsistently between `Relation` and `Problem`.
4. Several displayed Lean definitions do not elaborate as written.
5. The RBR and compiler sections still contain architecture names where migration steps require actual interfaces.
6. Migration step 7 is a flag day for downstream protocols despite the plan claiming a gated, green migration.

I would not begin the security cutover until the first three issues have executable skeletons.

---

# Severity-ranked findings

## Critical

### C1. `runClosed` is not a type; it hides three coupled design decisions

References: §6.4, §6.6.2–§6.6.3, §8 steps 1 and 7.

The document gives:

```lean
def runClosed (…) : Dist (Terminal (ClosedClaim Stmt Out) Fault) := …
```

This is insufficient and does not match current ArkLib execution.

Current execution returns an `OracleComp oSpec` whose result is a dependent sigma over the full transcript, honest/adversarial prover output, and verifier output. See [Execution.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Execution.lean:230). The proposed result drops:

- the full transcript needed by offline extractors;
- the public transcript indexing `Stmt`, `Out`, and witnesses;
- the prover’s output witness;
- honest concrete output data needed by completeness;
- the Γ world’s final state and trace;
- the distinction between explicit `Terminal.fault` and missing mass in VCVio’s `SPMF` semantics.

The KS event in §6.6.3 uses `witOut`, but the displayed `runClosed` result contains no `witOut`. Completeness likewise needs prover data and witness, which the result omits.

`Dist` is also not a live ArkLib/VCVio type here. The executable layer is `OracleComp`; probability is obtained through `evalDist : m α → SPMF α`. See [EvalDist Basic](/Users/quangdao/Documents/Lean/VCV-io/VCVio/EvalDist/Defs/Basic.lean:85). `ProbComp` is only `OracleComp unifSpec`, not the general runner.

A minimally credible sketch is needed now:

```lean
structure AcceptedPayload (pt : Spec.PublicTranscript s) where
  closed    : ClosedClaim (Stmt pt) (Out pt)
  proverOut : ProverPayload pt
  view      : ExecutionView pt

abbrev JointResult :=
  (pt : Spec.PublicTranscript s) × Terminal (AcceptedPayload pt) Fault

def runClosed : OracleComp oSpec JointResult := ...
```

If Γ is present, the result needs final Γ state/trace or `runClosed` must be a `StateT`-interpreted computation.

The document must also decide one of:

- monadic failure is impossible, proved by `NeverFails`, and all modeled faults are explicit `Terminal.fault`; or
- `SPMF.none` is another fault channel charged separately; or
- monadic failure is converted to an explicit fault by a specified interpreter.

At present, §6.6.2 says faults are controlled, but the semantics do not say where faults live.

**Classification:** real design decision, not safe to defer.

---

### C2. `AcceptedRun` is not transcript-indexed and does not enforce “same run”

References: §6.4, audit disposition K, §8 step 1.

The displayed record is:

```lean
structure AcceptedRun (Src : SourceCtx) (Stmt : Type) (Out : OracleFamily) where
  env   : Src.Env
  claim : OracleClaim Src.spec Stmt Out
```

But in the actual design:

- `Src = reductionSources shared pt`;
- `Stmt = StatementOut shared pt`;
- `Out = outputFamily shared pt`;
- `pt` is obtained from the run;
- the transcript-message environment is derived from the same full transcript.

Thus `Src`, `Stmt`, and `Out` cannot be fixed independently before the result transcript is known. The record needs to live under a sigma over `pt` or the full transcript.

More importantly, this public constructor does not enforce the promised invariant. Anyone can pair any `env` with any `claim`. Calling `closeWith` “internal” is documentation, not a Lean invariant. Audit disposition K therefore overstates what §6.4 achieves.

The invariant should be enforced by either:

- making the raw constructor private and exposing only a runner-produced dependent result; or
- carrying the full transcript and defining both `env` and `claim` as projections/computations from it, rather than independent fields.

`AcceptedRun` should probably not be a standalone foundational object at all. A single dependent `ExecutionArtifact` should contain the transcript, verifier terminal output, prover payload, Γ trace, and derived closing environment.

**Classification:** real design decision.

---

### C3. The transcript environment is concrete data, contradicting the claimed malicious carrier

References: §0, §1.1, §2.2, §6.2, §6.6.1, audit findings 1–2.

The ontology repeatedly says malicious backing oracles, including prover-sent oracles, may be arbitrary total query behavior and need not come from a polynomial or codeword.

But:

```lean
def Spec.OracleMessagesAt ...
  | .oracle X cont, ... =>
      X × OracleMessagesAt ...
```

stores a concrete `x : X`. `answerAt` then derives behavior through `OracleInterface X`.

That matches the current runtime: a prover physically sends an `X`. It does **not** quantify over arbitrary behavior unless `X` itself is an unrestricted behavior type. Existing protocols do not always have that property: single-round sumcheck sends `CDegreeLE R deg`, so bounded degree is intrinsic to the message type.

This directly conflicts with:

> Degree bounds ... are not refinements of the carrier, because malicious executions must still denote a total behavior.

The document needs to choose explicitly:

1. Protocol message types remain concrete representations, so malicious transcript-oracle behavior is restricted to representable `X`; only input and closed output claims are behavior-general.

2. Security semantics replaces each oracle-message payload by arbitrary behavior for its interface, with honest execution embedding concrete `X`.

3. Protocol ports change their `.oracle X` message types to unrefined behavior/data types, moving validity such as degree bounds into relations.

This is not re-litigating the behavioral output carrier. It is an unresolved inconsistency about whether that decision also applies to prover-sent backing resources.

**Classification:** real design decision.

---

### C4. `ClaimSchema` is undefined, and `Relation` versus `Problem` is inconsistent

References: §6.6.1, §6.6.3, §8 step 7.

The first security-facing structures depend on an undefined object:

```lean
structure Relation (S : ClaimSchema)
structure Problem (S : ClaimSchema)
```

No sketch says whether `ClaimSchema` contains:

- `PublicCtx`;
- transcript/setup indices;
- a dependent `Stmt` family;
- an `OracleFamily`;
- arbitrary claim types, including committed claims;
- reindexing under public-prefix extension;
- universe parameters.

This matters immediately because committed claims are not necessarily syntactically `ClosedClaim Stmt Out`, while the ideal layer is.

There is a second inconsistency: `Relation.language` is defined for `Relation`, but subsequent security text uses `Problem`, `admissible`, `Language R_in`, and `R_out out witOut` interchangeably. `Relation` and `Problem` duplicate `Witness` and `rel`, with no extension or coercion between them.

Define one object, for example:

```lean
structure ClaimSchema where
  PublicCtx : Type
  Claim     : PublicCtx → Type

structure Problem (S : ClaimSchema) where
  Witness    : ∀ ctx, S.Claim ctx → Type
  admissible : ∀ ctx, S.Claim ctx → Prop
  rel        : ∀ ctx claim, Witness ctx claim → Prop
  rel_admissible : ...
```

Then define `language` for `Problem`. If a promise-free relation is wanted, make it an abbreviation with `admissible := True`.

The harder decision is whether an oracle schema is a specialization:

```lean
OracleClaimSchema Stmt Out
```

or whether `ClaimSchema` itself exposes `Stmt` and `Out`. That choice affects compiler relation transformers and must be made before step 7.

**Classification:** real design decision.

---

### C5. `OracleFamily.Behavior` does not elaborate as written

References: §6.3, §6.6.3, §6.11.

The document defines:

```lean
structure OracleFamily where
  ι      : Type
  Obj    : ι → Type
  oracle : ∀ i, OracleInterface (Obj i)

abbrev OracleFamily.Behavior (Out : OracleFamily) :=
  QueryImpl [Out.Obj]ₒ Id
```

The notation `[Out.Obj]ₒ` requires a typeclass instance:

```lean
[∀ i, OracleInterface (Out.Obj i)]
```

An ordinary structure field `Out.oracle` is not automatically installed as that instance. The same problem recurs in `VirtualOracle`, `ProverOutputRealizes`, and other uses of `[Out.Obj]ₒ`.

Use the explicit-interface notation already provided by ArkLib:

```lean
QueryImpl [Out.Obj]ₒ' Out.oracle Id
```

or make an explicitly scoped local instance before every use. See [OracleInterface.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/OracleReduction/OracleInterface.lean:86).

The universe pinning is otherwise plausible: current `QueryImpl` is exactly a dependent function into the target monad, and the current dependency exposes the required composition and sum-handler operations. See [QueryImpl Basic](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/.lake/packages/VCVio/VCVio/OracleComp/SimSemantics/QueryImpl/Basic.lean:25) and [Append.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/.lake/packages/VCVio/VCVio/OracleComp/SimSemantics/Append.lean:22).

---

### C6. The security comparison gate cannot be generic

References: §6.6.8, §8 steps 6–7, success criteria 2 and 9.

Current `OutputRelation` receives both `inputImpl` and the intensional output simulator. See [Security/Basic.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:110). An arbitrary old relation may inspect or depend on the input handler independently of the closed output behavior.

Therefore there is no generic two-way equivalence with an autonomous closed-claim relation. A protocol-specific equivalence is possible only after proving that its old relation is environment-insensitive and behavior-respectful.

Step 6 proves equivalence only for three slices, but step 7 cuts over “basic oracle security” globally. That leaves every other downstream relation and theorem unbridged.

The correct gate is per relation or per protocol family:

```text
old relation
  + Autonomous/ClosesTo proof
  ↔ closed Problem
```

The legacy security namespace must remain available until every downstream consumer has such a bridge or has been ported.

**Classification:** migration blocker.

---

## High

### H1. Scalar `stmt` accesses are outside the proposed compiler IR

References: §6.4, §6.9, §6.10.3.

The document correctly says scalar outputs computed from queries live in `stmt`. Single-round sumcheck already does this: its terminal statement is computed after reading the sent polynomial.

But `TypedPlan` describes only the virtual output oracle. `LowerAccesses` must also compile all oracle reads used to compute:

- verifier challenges;
- acceptance;
- the terminal scalar statement;
- link statements and batching coefficients.

A plan for output-oracle queries alone cannot compile the complete verifier.

Either:

- the compiler operates on the whole verifier `Program`, with `TypedPlan` only for residual output views; or
- the terminal claim is itself produced by a typed effectful plan containing both scalar computation and output-view construction.

The document currently implies both approaches without choosing one.

---

### H2. `Terminal` requires a protocol-wide acceptance migration that is not acknowledged

References: §6.6.2, §8 step 7.

Current verifier outputs are ordinary types; acceptance is protocol-local. Sumcheck uses `Option (RoundClaim R)`. Other protocols use Booleans or relation predicates.

Introducing:

```lean
Terminal Claim Fault
```

is not merely a security-definition change. It changes verifier output families, composition, prover/verifier agreement, and every construction that currently encodes rejection in `StatementOut`.

A compatibility layer needs an explicit per-protocol decoder:

```lean
LegacyOutcome : StatementOut → Terminal Claim Fault
```

with a theorem describing which legacy cases reject and which faults are impossible. Without that, step 7 is a flag day.

---

### H3. RBR’s load-bearing objects remain names

References: §6.6.5–§6.6.7, §8 step 9.

The following are not sketched enough to support migration:

- the type of a full security prefix;
- the cursor tying a prefix to a remaining `Spec`;
- `SourcesAt p`;
- weakening along prefix extension;
- environment restriction;
- stable resource identity under extension;
- conditional challenge kernels;
- “reachable” relative to which adversary and Γ history;
- fork compatibility and common-prefix equality.

Current `PublicTranscript` represents a complete root-to-leaf path, not a partial execution cursor. `toOracleSpec` similarly collects oracle handles along a completed public path. RBR needs a new partial-path/frontier object or an existing PolyFun cursor abstraction.

The challenge kernel cannot be recovered merely from the message type. Current receiver actions are arbitrary `OracleComp` computations. A kernel must be extracted from or supplied by a stronger public-coin verifier surface, and it must include Γ history if challenges are world-dependent.

Step 9 hides a research-sized API and proof development.

---

### H4. Resource identity is ordered after the machinery that depends on it

References: §6.9, §8 steps 9–10, §9 “prefix scoping,” §12 handover.

The document says stable resource identity must be settled before replay, state restoration, or RBRTE. But migration step 9 introduces prefix `SourcesAt`, constrained forks, RBRTE, and state-restoration bridges; stable resource metadata is not added until step 10.

The handover repeats the same reversed order: relaxed RBR security, then provenance.

Split resource work:

- Before RBR: minimal `ResourceId`, named source contexts, prefix inclusion, alias/share semantics.
- During compiler work: origin, key identity, commitment identity, encoding, batching, cost, and policies.

---

### H5. §6.9–§6.10 still overclaim concreteness

References: §6.9, §6.10, audit disposition T.

`TypedPlan` is described in prose, but no datatype is shown. Its signatures refer to undefined:

- `Handler`;
- `TypedTrace`;
- `StagedOpeningProtocol`;
- `FiniteConsumer`;
- `ConsistencyCompiler`;
- `LinkArgument`;
- `Ownership`;
- `EncodesPromise`.

Audit disposition T says a “concrete staged IR” is specified. It is not. The document specifies desired constructors and interpreters, not a concrete dependent datatype or scheduling semantics.

This is acceptable in a separate compiler roadmap. It is not adequate as a resolved disposition or as migration step 10.

---

### H6. Γ largely duplicates existing VCVio stateful-handler machinery

References: §6.2, §6.6.7.

The proposed:

```text
WorldSpec := (State, Request, Response, step, initialDistribution, publicView)
```

is very close to VCVio’s existing:

```lean
QueryImpl.Stateful I E σ :=
  QueryImpl E (StateT σ (OracleComp I))
```

See [StateSeparating.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/.lake/packages/VCVio/VCVio/OracleComp/SimSemantics/StateT/StateSeparating.lean:40).

VCVio already has:

- lazy random-oracle handlers via `StateT QueryCache ProbComp`;
- query logging and tracing;
- handler composition/linking;
- state separation and frames;
- replay/fork machinery;
- distributional equivalence for stateful handlers.

ArkLib may need a package adding initial state distribution, public projection, and trace policy, but it should identify `WorldSpec` as a wrapper around `QueryImpl.Stateful`, not introduce an independent operational semantics.

---

### H7. `stmt` consistency is run-relative, not environment-relative

References: §6.4.

Closing recomputes only `oracles`; it retains the already-produced `stmt`. This is valid, but the document occasionally suggests the closed claim is determined by `env`.

It is not:

- `stmt` may depend on the public transcript;
- it may depend on ambient Γ queries;
- it may depend on verifier randomness;
- the same Δ environment can accompany different public challenges and statements.

No equality between `stmt` and the oracle behavior is needed in the carrier, but the joint execution result must tie them to the same run. Compiler equivalence must preserve scalar statement computation as well as virtual-oracle evaluation.

State this explicitly to avoid trying to prove the false theorem that `ClosedClaim` is a function of `Src.Env`.

---

### H8. Migration steps 5–7 hide months of work

Step 5 combines:

- context morphisms;
- weakening, renaming, aliasing, and sharing;
- source equivalences;
- semantic and operational equivalences;
- substitution laws;
- terminal routing refactors;
- an order-preserving execution decomposition theorem.

That is several milestones, not one.

Step 6 requires relation-specific equivalences for completeness, soundness, and KS, but two of the three proposed slices do not currently have parallel programmatic security developments.

Step 7 changes:

- outcomes;
- relation signatures;
- witness dependency;
- promises;
- extractors;
- execution results;
- soundness events;
- composition theorems.

This is the main migration, not one gated step.

Step 9 is likely months. Step 10 is an independent compiler program likely larger than steps 1–9 combined.

---

## Medium

### M1. §6.5 contains the duplicated paragraph the task suspected

The paragraph beginning “Sum specs are left-associated by convention...” occurs twice, around lines 476 and 501. The second copy adds the reduction-associativity conclusion; merge them into one “Equality and associativity policy” subsection.

---

### M2. A stale rejection contradicts the query-only `VirtualOracle`

Reference: §9, “Rejected: raw pair...”.

It says:

> Two additional fields provide the missing denotation and coherence.

But §6.3 explicitly removed stored denotation and coherence fields. `VirtualOracle` now has only `query`; `eval` is derived.

Replace with:

> Packaging supplies the claim boundary; derived interpretation supplies denotation without stored coherence fields.

---

### M3. `Src` denotes two different kinds of object

- `VirtualOracle (Src : OracleSpec)`;
- `AcceptedRun (Src : SourceCtx)`;
- `Materialization (Src : SourceCtx)`;
- prose such as `VirtualOracle Src Out` calls it a “source context.”

This is not merely cosmetic in a dependent design. Rename parameters:

```lean
VirtualOracle (srcSpec : OracleSpec) ...
AcceptedRun (src : SourceCtx) ...
```

or introduce `SourceSig` as a name for the spec-only layer.

---

### M4. Several displayed notations are undeclared or misleading

- `ρS ++ ρT` is used for handlers, but the live VCVio operation is `QueryImpl.add` or `+`.
- `fault = 0` should be `Pr[fault] = 0`.
- Soundness events written as `runClosed = accept out` need an event function or existential pattern.
- `Spec.answerAt` omits its `OracleDeco` argument.
- `SourceCtx.ofData ... : Env` does not qualify which `Env`.
- `VirtualOracle.subst_assoc` uses `≈sem` before defining an actual relation and its binder/index discipline.

Pseudocode is fine, but these occur in the Lean-facing audited design and should be normalized.

---

### M5. Some audit dispositions do not match the body

Notable examples:

- K says `AcceptedRun` enforces same-run closing; it does not.
- C says outcomes/faults were added to the core security layer; only the inductive is shown, not its execution integration.
- I says `BCSPublicView` is added; it is only requested.
- T says the concrete IR is specified; it remains prose.
- N says output admissibility is added; no predicate/game definition is provided.
- R says order-preserving decomposition is required, but no interface or theorem shape beyond its English name is given.

The traceability table should distinguish “decision accepted,” “interface sketched,” and “implemented/specification complete.”

---

### M6. Line references have drifted

Examples:

- `Program.lean:22` is the docstring; `TerminalOutput` begins at line 28.
- `Spec.lean:771,825` does not point to the two inverse theorems; those are currently around lines 798 and 812.
- Symbol references are more stable than line references.

Use declaration links/names, with lines only as optional snapshots.

---

### M7. “`OracleMessagesAt` is always inhabited” is false as stated

At an `.oracle X` node it contains an `X`. If `X` is empty, the fiber is empty. What is true is:

> Every realized full transcript canonically produces an `OracleMessagesAt s pt`.

That is the theorem the execution layer needs.

---

# Load-bearing object classification

| Object | Classification | Assessment |
|---|---:|---|
| `ClaimSchema` | (c) | Determines public context, claim indexing, committed claims, and reindexing. Must be designed before security cutover. |
| `runClosed` | (c) | Must decide dependent transcript result, prover payload, Γ state/trace, `OracleComp` versus `SPMF`, and fault semantics. |
| `AcceptedRun` | (c) | Current sketch neither type-indexes the transcript nor enforces same-run construction. |
| Challenge kernels | (c) | Requires a public-coin interface and explicit dependence on prefix/Γ history. |
| Reachable prefixes | (c) | Must specify reachability relative to adversary, input, and world history. |
| `SourcesAt p` | (c) | Central to RBR scoping and stable identity; needs a cursor and inclusion maps. |
| Prefix weakening/restriction | (c) | Dependent query handles make this a substantive API, not bookkeeping. |
| `ViewReduction` | (b) | A small record sketch is enough now, but step 7 depends on it. It must distinguish pure view projection from live capability simulation. |
| `Terminal` + probability semantics | (c) | Explicit faults versus `SPMF.none` is unresolved. |
| Query-derived `stmt` | (c) | Joint execution solves semantic consistency, but compiler access lowering must cover it. |
| `FiniteConsumer` | (c) | Must choose syntax, adaptivity, termination, and whether “finite” means per branch or uniformly bounded. |
| `ConsistencyCompiler` | (c) | Encodes the malicious link theorem; different choices produce materially different compiled relations. |
| `LinkArgument` | (c) | Needs protocol, statement/witness, acceptance, soundness, and possibly extraction/ZK interfaces. |
| `StagedOpeningProtocol` | (c) | Scheduling and response adaptivity are core security parameters. |
| `Ownership` | (c) | Changes who supplies data/openings and therefore setup/adversary quantifier order. |
| `EncodesPromise` | (c) | Must say whether it is schema-level compatibility or claim-level admissibility preservation. |
| `TypedPlan` | (c) | The compiler’s viability depends on its actual dependent datatype and erasure/evaluation laws. |
| Detailed cost models | (a) | Fine to defer once `TypedPlan` and trace semantics are fixed. |
| `FaithfulPresentation` instances | (a) | Can be added protocol by protocol. |
| Exact ZK compiler interfaces | (a) | Fine to defer if no ZK theorem is claimed in the core migration. |

---

# Missing “a-ha” unifications

## A. Oracle claims and honest prover output share a representation-indexed claim shape

**Agree, with a refinement.**

`OracleClaim` is not the same thing as `HonestProverOutput`; the latter adds a witness. But `OracleClaim`, `ClosedClaim`, and `StatementWithOracles` are the same “statement plus oracle representation” pattern.

Use a representation-indexed claim:

```lean
structure ClaimWith
    (Rep : OracleFamily → Type)
    (Stmt : Type) (Out : OracleFamily) where
  stmt    : Stmt
  oracles : Rep Out
```

Instantiations:

- open: `Rep Out := VirtualOracle srcSpec Out`;
- closed: `Rep Out := Out.Behavior`;
- honest data: `Rep Out := ∀ i, Out.Obj i`.

Then:

```text
HonestProverOutput = ClaimWith DataRep × Witness
```

Evaluation and answering concrete data are representation morphisms into behavior. This would remove duplicated claim records and make realization theorems visibly natural.

## B. FS and BCS share a transcript-compiler substrate

**Partly agree.**

They should not be one pass: BCS can apply without public-coin replayability, while FS requires it. But they both need a shared typed transcript schedule:

- public events retained for absorption;
- hidden/prover events;
- commitment handles;
- domain separators;
- causal challenge derivation;
- source/target transcript projection;
- replay/equivalence theorem.

Define a small `TranscriptTransform` or `ProtocolPass` interface used by both. BCS supplies a representation-changing pass; FS supplies a public-coin-elimination pass. `BCSPublicView` and FS absorption should be interpretations of the same public event log.

## C. Γ is VCVio’s stateful simulation machinery

**Agree strongly.**

Identify Γ with a packaged `QueryImpl.Stateful` handler plus:

- initial-state computation/distribution;
- public projection;
- trace/log instrumentation;
- allowed replay/equivalence relation.

Do not build a parallel `Request/Response/step/runΓ/Dist` semantics unless VCVio is missing a demonstrated capability.

## D. RBR, `KnowledgeClaimTree`, and special-soundness trees share one constrained execution tree

**Agree.**

The common object should encode:

- a protocol cursor/full prefix;
- shared prover prefixes;
- verifier fork nodes;
- conditional challenge kernels;
- distinctness constraints;
- Γ history agreement;
- stable resource identities.

Decorations then provide:

- `KState`, backward maps, and local error for RBR;
- leaf language/witness data and interpolation for special soundness;
- grafting/extraction data for RBRTE.

The current `ClaimTree` is indexed by the remaining `Spec`, but not by a first-class prefix/world state. It is a useful starting decoration, not yet the common base tree.

## E. `subst`, `rebase`, `tensor`, and `share` form categorical structure

**Mathematically yes; implementing full category theory now would probably increase Lean work.**

For deterministic read-only Δ contexts, the operations resemble a cartesian context calculus:

- tensor: disjoint context extension;
- weakening: discard;
- share: diagonal/contraction;
- rename/rebase: context isomorphism;
- substitution: composition.

But Γ is not cartesian, and indexed transcript families make the full object a fibration. I would state the algebra and laws explicitly, use a canonical n-ary named-context normal form, and avoid Mathlib’s categorical hierarchy until several clients demonstrate a payoff.

## F. `admissible`, promise problems, and accumulator well-formedness

**Mostly agree.**

A claim-only accumulator invariant is exactly an admissibility predicate, with a preservation theorem. Promise-problem promises are also admissibility.

Keep specialized names because their proof roles differ:

- input promise: assumption on adversarial input;
- output admissibility: probabilistic obligation of a reduction;
- accumulator invariant: inductive preservation condition;
- `EncodesPromise`: the compiler’s decoding preserves admissibility.

Witness- or history-dependent accumulator invariants do not fit a claim-only `admissible` and should remain relational state invariants.

## Additional unification: one dependent execution artifact

The document currently risks separate records for accepted runs, extractor views, compiler traces, and Γ results. Define one run artifact and derive all views from it:

```text
ExecutionArtifact
 ├─ public/full transcript
 ├─ verifier terminal output
 ├─ source environment
 ├─ prover payload
 ├─ Γ final state and trace
 └─ explicit outcome
```

Closing, extractor views, compiler traces, and reachability should be projections. This is the cleanest way to make “same run” structural.

## Additional unification: named contexts link composition, RBR, and compilation

Stable named resource contexts should arrive before both RBR and the compiler. Then:

- `SourcesAt p` is a prefix subcontext;
- weakening is inclusion;
- sharing is explicit aliasing by resource ID;
- compiler provenance decorates the same declarations;
- replay equality means equality of named resource histories.

This avoids building structural sum paths first and retrofitting identities later.

---

# Consolidation

The document is carrying conceptual explanation, normative design, migration planning, compiler architecture, and three audit archives at once.

## Material to merge

- Merge §2 and §6.1 into one ontology/glossary.
- Keep §0 as a short executive picture; remove repeated explanations from §7 and §12.
- Merge §3 and §5 into a short “current seam and rejected predecessor” section.
- Merge the two associativity paragraphs in §6.5.
- Fold §7’s resolved questions into the relevant normative sections.
- Reduce §9 to decisions that are still easy to regress on; historical alternatives belong in the archive.

## Material to split

§6.10 should be its own document. It is roughly a quarter of the file and contains a separate research program:

> Oracle-elimination compiler design: plans, schedules, committed boundaries, and security transfer.

The main oracle-reduction document needs only:

- why fixed-consumer and reusable boundaries differ;
- the interface the core exposes to a future compiler;
- the fact that compiler correctness is not part of `VirtualOracle` itself.

The RBR/extractor architecture would also benefit from its own design note once its prefix object is sketched.

## Audit traceability

Move §10 and the delegate-report history in §13 to an appendix or archived audit file. They no longer earn space in the normative document because:

- their dispositions are already drifting from the actual body;
- they encourage reactive prose;
- they obscure which definitions are current;
- the source archive already exists.

The core document should contain unresolved obligations, not a ledger of every prior reviewer.

## Success criteria consolidation

The 15 criteria can become eight:

1. Core representation and substitution algebra typecheck without new `sorry`.
2. Legacy-to-closed relation bridges preserve adversarial quantification for every ported protocol.
3. Sumcheck, Spartan, and FRI provide the three representation slices.
4. Outcomes, promises, closing, and ordinary soundness composition have exact executable games.
5. Prefix/RBR semantics exists before any KS-composition claim.
6. The compiler has a concrete public view, plan/trace semantics, and fixed-consumer lowering.
7. Reusable committed boundaries name their consistency/extraction capabilities; Nova demonstrates `CommitAction`.
8. Persistent-world theorems use stateful handlers and explicit history.

The current `sorry` count and individual slice expectations belong in CI or milestone checklists, not the architectural success criteria.

---

# Migration realism

## What breaks during steps 6–7

Step 6 is additive only if bridges are protocol-specific and the legacy namespace remains.

Step 7 otherwise breaks:

- every `OutputRelation` receiving `inputImpl`;
- every total deterministic extractor;
- every `WitnessOut` not dependent on the produced claim;
- every verifier encoding rejection through `Option`, `Bool`, or a local predicate;
- completeness statements using concrete `StatementWithOracles`;
- soundness events over raw simulator programs;
- composition theorems;
- ProofSystem ports still proved against `ArkLib/OracleReduction` security definitions.

The three slice equivalences are not enough to authorize a global cutover.

## Better ordering

1. Fix the elaborating core: explicit oracle-interface arguments, `OracleMessagesAt`, and `answerAt`.
2. Define the dependent `ExecutionArtifact` and closing projection using current `OracleComp` execution.
3. Prove one closed-claim completeness theorem for programmatic single-round sumcheck.
4. Add the minimal named-resource context and resource IDs.
5. Implement substitution and a two-stage evaluator theorem.
6. Introduce `ClaimSchema`/`Problem` in a parallel `Security.V2` namespace.
7. Port one ordinary-soundness example and prove its legacy equivalence.
8. Port protocols incrementally; keep legacy adapters.
9. Define partial prefixes, kernels, and constrained trees.
10. Move the compiler into its own project plan.

## Minimum viable end-to-end slice

The earliest useful sorry-free result should be smaller than current step 3:

> Programmatic single-round sumcheck perfect completeness through `OracleClaim.closeWith`, including its query-derived scalar statement and passthrough output behavior.

This exercises:

- `OracleFamily`;
- `VirtualOracle`;
- transcript-message closing;
- query-derived `stmt`;
- honest data realization;
- a real `TerminalOutput`.

It does not require Spartan, FRI, context associativity, new soundness, RBR, or compiler metadata.

A second slice should compose two simple/pass-through rounds and prove the closed evaluator equation. Only then add Spartan materialization and FRI fresh-plus-derived outputs.

---

# Lean feasibility spot-checks

## `OracleFamily.Behavior`

Conceptually valid, syntactically invalid as displayed because the interface field is not an installed instance. Use `[Out.Obj]ₒ' Out.oracle`.

## `SourceCtx.tensor`

`OracleSpec` sum and `QueryImpl.add` exist and have the required branch lemmas. Handler composition and `simulateQ_compose` also exist in the pinned VCVio dependency.

What does not exist automatically is the document’s desired symmetric reassociation equivalence. VCVio has one-directional `SubSpec` infrastructure for addition and explicit lift lemmas, but ArkLib still needs its own source equivalence/naturality packaging. `ρS ++ ρT` should be replaced by `ρS + ρT`.

## `Spec.OracleMessagesAt`

The recursion is feasible. `Oracle.Spec` exposes a custom structural recursor, and existing `QueryHandle` and `toOracleSpec` use essentially the same dependent recursion. There is no obvious positivity problem.

Required corrections:

- include `OracleDeco` in `answerAt`;
- state a conversion from a realized full transcript, not global inhabitedness;
- decide whether the fiber stores concrete oracle data or arbitrary behavior.

## `AcceptedRun`

It does not typecheck as the actual run result abstraction because `Src`, `Stmt`, and `Out` depend on the run’s public transcript. Put it under a sigma over `pt` or full transcript.

## Γ/world semantics

Use VCVio’s `QueryImpl.Stateful`, `StateT`, logging, caching, and replay APIs. The proposed independent `Dist` runner would duplicate machinery and create an avoidable semantic bridge obligation.

---

# Concrete edits I would make

1. Rename the document to **Oracle Reduction Core: Claims, Closing, and Composition**.
2. Add **Normative status and deferred components** immediately after the introduction.
3. Replace §§2 and 6.1 with **Core ontology and notation**.
4. Add **Representation-indexed claims** unifying open, closed, and honest-data claims.
5. Replace `AcceptedRun`/`runClosed` with **Dependent joint execution semantics**.
6. Add **Failure and probability model**, explicitly choosing `OracleComp`, `SPMF`, and explicit faults.
7. Add **Malicious semantics of prover-sent oracle messages** and resolve the concrete-data/behavior contradiction.
8. Define **ClaimSchema and Problem** before any security theorem.
9. Add **Statement production and closing**, explaining query-derived `stmt`.
10. Rename every spec-only `Src` parameter to `srcSpec`.
11. Correct `OracleFamily` to use explicit stored oracle interfaces.
12. Merge §6.5’s duplicated associativity discussion into **Context algebra and equality policy**.
13. Introduce **Named resource contexts** before the RBR section.
14. Move extractor/RBR material into **Prefix security design** or a separate companion document.
15. Move all of §6.10 into **Oracle-Elimination-Compiler.md**.
16. Leave only a two-page **Compiler boundary contract** in the core document.
17. Replace §7 with a short **Decisions** table containing only current normative decisions.
18. Replace §8 with a milestone plan centered on the minimum viable sumcheck slice and parallel V2 security namespace.
19. Move §10 and delegate histories to the archived audit document.
20. Replace the 15 success criteria with the eight consolidated milestones above.
21. Remove stale “two additional fields” language.
22. Replace brittle file:line references with declaration names and repository links.
23. Correct audit dispositions to distinguish “accepted,” “sketched,” and “fully specified.”

The core design is ready for a small executable prototype. It is not yet ready for the security cutover or the RBR/compiler migrations described in steps 7–10.