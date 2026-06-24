# Interaction-Native Boundaries: Design Reference

This document is the authoritative design reference for `ArkLib.Interaction.Boundary`.

It covers:

- what problem the boundary layer solves and why it is separate from composition;
- the three-layer architecture: Core, Access, Reification;
- the concrete structures and operations implemented in each layer;
- known issues in the current code;
- what is explicitly deferred (security theorems);
- validation targets;
- literature connections.

---

## 1. The Core Problem

The interaction-native oracle framework supports two distinct ways of combining
protocols:

1. **Sequential composition** — `OracleReduction.comp`, `Continuation.comp`.
   Run phase 1, then run phase 2 on the resulting transcript and outputs.
   The transcript strictly grows.

2. **Same-transcript interface adaptation** — the boundary layer.
   The underlying interaction *stays the same*. The transcript *does not change*.
   We merely reinterpret the protocol through a different outer statement, witness,
   or oracle interface.

These two things are conceptually different and should stay separate in the
codebase.

The old `liftContext` layer conflated them. It was simultaneously a sequential
composition combinator and an interface adapter, which is why its security lemmas
were never finished and its oracle-simulation obligations were perpetually deferred.

The boundary layer is the clean replacement for the second use case only.

### When is a boundary the right tool?

A boundary is right when:

- the interaction spec `Spec`, the transcript shape, and the round structure are
  *unchanged*;
- you want to reinterpret the protocol at a different outer statement or witness
  interface;
- you are *not* appending more rounds.

Typical concrete situations:

- **Sumcheck single-round reuse**: the `SingleRound` view is a projection of a
  richer round statement to a simpler one-round interface. Same transcript,
  different outer statement.
- **FRIBinius witness reinterpretation**: the witness and extractor layer is
  repackaged while the oracle statement layer is largely preserved.
- **BatchedFRI batching boundary**: the inner single-codeword FRI oracle view is
  derived from an outer batched oracle context. (Note: the initial batching round
  itself should be a real protocol phase via composition; only the interface mapping
  from outer batched oracle to inner FRI oracle is a boundary.)

If you find yourself wanting to append rounds, use composition.
If you find yourself wanting to rename or reindex interfaces without changing the
protocol flow, use a boundary.

---

## 2. Three Layers

The boundary design is split into three layers that build on each other.
Each layer adds more oracle structure and a corresponding pullback operation.

```
Reification.lean   OracleContext / OracleStatement   OracleReduction.pullback
                         ↑
Oracle.lean        OracleContextAccess               OracleVerifier.pullback
                         ↑
Core.lean          Context / Statement / Witness      Reduction.pullback
```

You use the lowest layer that suffices for your use case.

| Layer | What it adds | Prover pullback | Verifier pullback |
|---|---|---|---|
| Core | stmt/wit projection + lifting | yes | yes |
| Access | input/output oracle simulation | — (not enough for prover) | yes |
| Reification | concrete oracle materialization | yes | via coherence |

The asymmetry between prover and verifier is intentional and correct.

The verifier never holds concrete oracle data. It only issues queries. So the
verifier can be pulled back using the access layer alone: inner query → outer
query, and the answers flow back the same way.

The prover holds concrete oracle data (the `OracleStatement` family). To pull
back the prover, you need to know how to transform *concrete data*, not just
*queries*. That requires reification.

---

## 3. Core Layer

**File**: `ArkLib/Interaction/Boundary/Core.lean`

### `Boundary.Statement`

```lean
structure Boundary.Statement
    (OuterStmtIn InnerStmtIn : Type)
    (InnerContext : InnerStmtIn → Spec)
    (InnerStmtOut : (s : InnerStmtIn) → Spec.Transcript (InnerContext s) → Type) where
  proj : OuterStmtIn → InnerStmtIn
  StmtOut : (outer : OuterStmtIn) → Spec.Transcript (InnerContext (proj outer)) → Type
  lift : (outer : OuterStmtIn) → (tr : ...) → InnerStmtOut (proj outer) tr → StmtOut outer tr
```

The minimal data needed to bridge two statement interfaces:

- `proj` maps the outer input statement to the inner one.
- `StmtOut` defines the outer output statement type (as a function of outer input
  and transcript). It does not have to equal the inner output statement type
  pushed forward through `proj`; it can be larger.
- `lift` produces an outer output statement from an inner one.

Note that `lift` is one-directional. The outer output statement is lifted from
the inner output statement; there is no "lowering." This is the right shape for
the pullback operation: the prover runs the inner protocol and its output gets
lifted back to the outer interface.

### `Boundary.Witness` and `Boundary.Context`

`Boundary.Witness` adds witness projection and lifting in parallel with
`Boundary.Statement`, depending on the same underlying statement boundary.

`Boundary.Context` bundles both into a single record with combined `proj` and
`lift` operations.

### Pullback operations

```lean
Boundary.Verifier.pullback (boundary : Statement ...) (verifier : Verifier ...) : Verifier ...
Boundary.Prover.pullback (boundary : Context ...) (prover : Prover ...) : Prover ...
Boundary.Reduction.pullback (boundary : Context ...) (reduction : Reduction ...) : Reduction ...
```

These are all transparent. They apply `boundary.proj` on input and
`boundary.lift` on output, with no oracle involvement.

### Smart constructors

`Statement.id`, `Statement.ofInputOnly`, `Statement.ofOutputOnly`,
`Context.id`, `Context.ofInputOnly` cover the common degenerate cases.

---

## 4. Oracle Access Layer

**File**: `ArkLib/Interaction/Boundary/Oracle.lean`

This layer adds verifier-side oracle simulation on top of a plain statement
boundary.

### The two simulation fields

`OracleStatementAccess` carries two simulation functions:

```lean
simulateIn :
  QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
```

Translates a query to an inner input oracle into a computation over outer input
oracles. This is statement-independent: it applies uniformly regardless of which
outer statement we are at.

```lean
simulateOut :
  (outer : OuterStmtIn) →
    (tr : Spec.Transcript (InnerContext (toStatement.proj outer))) →
    QueryImpl [OuterOStmtOut outer tr]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut (toStatement.proj outer) tr]ₒ))
```

Translates a query to an outer output oracle into a computation over *both*
outer input oracles and inner output oracles. It takes the outer statement
and transcript because the outer output oracle type may depend on them.

The asymmetry is meaningful:

- Input oracle simulation (`simulateIn`) can be done without knowing the
  transcript, because the input oracle is fixed before any interaction happens.
- Output oracle simulation (`simulateOut`) happens after the interaction, so
  it can reference both the input and the resulting output oracles.

### What `simulateIn` and `simulateOut` enable

With these two functions, we can rewire any verifier computation that internally
issues inner oracle queries, replacing them with outer oracle queries. The
`pullbackCounterpart` helper (private) walks the `Spec.Counterpart.withMonads`
tree recursively:

- At sender nodes: pure observation, no oracle rewiring needed.
- At receiver nodes: wrap `simulateQ` with `routeInputQueries` to route all
  inner input oracle queries through `simulateIn`.

After the interaction, `pullbackSimulate` rewires the output oracle simulation
through `simulateOut`.

### Verifier and reduction pullbacks

```lean
OracleDecoration.OracleVerifier.pullback
  (stmt : Statement ...)
  (access : OracleStatementAccess stmt ...)
  (verifier : OracleVerifier ...) : OracleVerifier ...
```

```lean
OracleDecoration.OracleReduction.pullbackVerifier
  (stmt : Statement ...)
  (access : OracleStatementAccess stmt ...)
  (verifier : ...) : ...
```

`pullbackVerifier` is private because the public `OracleReduction.pullback` lives
in the reification layer (it needs concrete oracle data for the prover).

---

## 5. Reification Layer

**File**: `ArkLib/Interaction/Boundary/Reification.lean`

This layer adds concrete oracle materialization: instead of simulating oracle
queries, it transforms concrete oracle data directly.

### `OracleStatementReification`

```lean
structure OracleStatementReification ... where
  materializeIn :
    (outer : OuterStmtIn) →
      OracleStatement OuterOStmtIn →
      OracleStatement InnerOStmtIn
  materializeOut :
    (outer : OuterStmtIn) →
      OracleStatement OuterOStmtIn →
      (tr : ...) →
      OracleStatement (InnerOStmtOut (toStatement.proj outer) tr) →
      OracleStatement (OuterOStmtOut outer tr)
```

`materializeIn` maps a concrete outer input oracle to a concrete inner input
oracle.

`materializeOut` maps a concrete inner output oracle (plus the outer input oracle
as context) to a concrete outer output oracle.

The prover uses these directly: it has full concrete access to all oracle data,
so it can materialize rather than simulate.

### The `Realizes` coherence predicate

```lean
OracleStatementReification.Realizes access reification : Prop
```

This predicate says that for every concrete oracle data, the simulation (access
layer) and the materialization (reification layer) agree on every query answer:

1. Simulating an inner input oracle query via `simulateIn` against the concrete
   outer input oracle gives the same answer as materializing the inner input
   oracle via `materializeIn` and answering directly.

2. Simulating an outer output oracle query via `simulateOut` against the concrete
   outer input oracle and inner output oracle gives the same answer as
   materializing the outer output oracle via `materializeOut` and answering
   directly.

This coherence predicate is the replacement for the old `compatStatement` and
`compatContext` conditions. It is deliberately explicit rather than implicit:
the boundary should not be constructible without proving coherence.

### Bundled `OracleStatement` and `OracleContext`

`OracleStatement` bundles a plain `Statement` boundary with an
`OracleStatementAccess`, an `OracleStatementReification`, and a proof of
`Realizes`. `OracleContext` adds the witness layer.

These are the "fully packaged" boundary objects. For most use cases, you build
one of these and pass it to `OracleReduction.pullback`.

### `OracleDecoration.OracleReduction.pullback`

```lean
OracleDecoration.OracleReduction.pullback
  (boundary : OracleContext ...) (reduction : OracleReduction ...) : OracleReduction ...
```

This is the main client-facing operation. It uses:

- `materializeIn` for the prover's input oracle;
- `materializeOut` for the prover's output oracle;
- `pullbackVerifier` (from the access layer) for the verifier;
- `pullbackSimulate` for output oracle simulation.

---

## 6. Known Structural Issue

**`OracleStatement` and `OracleContext` have a forward-reference bug.**

In the current code, both structures reference `toStatement.proj` (respectively
`toContext.stmt.proj`) inside their implicit type parameters (specifically in the
`Outerιₛₒ` parameter), but `toStatement`/`toContext` are declared as *fields*
(after `where`) rather than as type parameters.

In Lean 4, a structure's type parameters cannot reference its fields. This will
produce an "unknown identifier" error when the file is elaborated.

**The fix**: promote `toStatement`/`toContext` to explicit type parameters of the
structure, matching the pattern already used in `OracleStatementAccess` and
`OracleStatementReification`:

```lean
-- incorrect (current):
structure OracleStatement ... where
  toStatement : Statement ...        -- field
  access : OracleStatementAccess toStatement ...
  ...

-- correct:
structure OracleStatement
    ...
    (toStatement : Statement ...)    -- type parameter
    ...
    {Outerιₛₒ : (outer : OuterStmtIn) →
      Spec.Transcript (InnerContext (toStatement.proj outer)) → Type}
    ...
  where
  access : OracleStatementAccess toStatement ...
  reification : OracleStatementReification toStatement ...
  coherent : OracleStatementReification.Realizes access reification
```

The `pullback` implementations reference `boundary.toContext.stmt.proj` etc.;
after this fix, `toContext` will be a type parameter rather than a field, so
those references stay valid via dot-notation on the `boundary` argument (Lean 4
allows this for structure type parameters).

---

## 7. Design Assessment

### What works well

**The three-layer split is well-motivated and correctly implemented.**

The access/reification separation mirrors the existing
`OracleVerifier.Simulates` / `OracleVerifier.Reification` split in
`OracleReification.lean`. The same pattern recurs here at the boundary level,
which is a good sign: the design is coherent with the broader oracle architecture.

**`simulateIn` is statement-independent; `simulateOut` is not.**

This asymmetry is correct and important. The input oracle is fixed before
execution; the output oracle is produced by the interaction and can depend on
the outer statement and transcript. Capturing this in the types makes the
obligations precise rather than implicit.

**The `Realizes` coherence predicate is minimal.**

It expresses exactly what you need: simulation and materialization agree on
every query answer. It does not over-specify. This is the right level of
constraint to impose at the boundary layer.

**`pullbackCounterpart` handles the interaction tree correctly.**

The recursive walk over `Spec.Counterpart.withMonads` (sender: observe, receiver:
rewire via `simulateQ`) is the right implementation of interpreter lifting. It
correctly accumulates the growing oracle access spec as the interaction proceeds.

### What is deliberately absent

**Security theorem transport is deferred.**

The current implementation is purely operational. There are no theorems stating
that `pullback` preserves completeness, round-by-round soundness, or knowledge
soundness. This is not an oversight — it is a deliberate staging decision.

The structural layer must compile and be validated against concrete examples
before security proofs are meaningful. Security theorem transport will be the
next layer of work after validation.

When that work begins, the right conceptual framework is converter/resource
composition from constructive cryptography (Maurer, Basin–Lochbihler–Mödersheim–Sasse)
rather than optics. The key obligations will be:

- **Completeness transport**: if the honest prover satisfies completeness for
  the inner protocol, then the pulled-back prover satisfies completeness for the
  outer protocol.
- **Soundness transport**: the outer verifier rejects at least as often as the
  inner one (up to the cost of the simulation).
- **Knowledge soundness transport**: the extractor for the inner reduction can
  be promoted to an extractor for the outer reduction via the witness lift.

The `Realizes` predicate is the key hypothesis for these transport theorems.

**Extractor witness transport is absent.**

The `Boundary.Witness` layer has `proj` and `lift` for honest prover witnesses
but no structure for the extractor direction (lifting an inner witness out to an
outer one against a malicious prover). This will be needed when knowledge
soundness theorems are proved. The right extension is a `Boundary.Extractor`
structure that mirrors `Boundary.Witness` but carries the reverse-direction
mapping.

**No `OracleDecoration.OracleProver.pullback` at the access layer alone.**

This is intentional. A prover pullback at the access layer is not meaningful
because the prover needs concrete oracle data (`OracleStatement`), not just
query-level simulation. The prover pullback only exists at the full reification
level.

### Naming note

`Boundary.OracleStatement` bundles a `Statement` boundary with oracle data. The
name `OracleStatement` also names the type `∀ i, OStmt i` in
`Oracle.Core` (concrete oracle data for a family). These are distinct and do not
live in the same namespace, so there is no actual name clash, but the coincidence
may cause momentary confusion in imports. Consider `Boundary.OracleBoundary` as
an alternative name for the bundled structure if the distinction causes trouble
in practice.

---

## 8. Validation Targets

Before generalizing further, the boundary layer should be instantiated for these
three cases:

### 8.1 Sumcheck single-round reuse

`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`

The single-round verifier is a projection of a richer multi-round statement to
a simpler one-round interface. This exercises `Boundary.Statement.ofInputOnly`
(no output lifting needed beyond the projection).

### 8.2 FRIBinius witness reinterpretation

`ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`

The statement and oracle layer is largely preserved while the witness layer is
repackaged. This exercises `Boundary.Context` with a non-trivial `Witness.lift`
and a trivial (identity) `Statement`.

### 8.3 BatchedFRI batching boundary

`ArkLib/ProofSystem/BatchedFri/Spec/General.lean`

The outer batched oracle context is mapped to an inner single-codeword FRI oracle
view. This exercises the full `OracleContext` including non-trivial
`materializeIn` and `materializeOut`.

Note: the initial batching round itself should be an ordinary protocol phase
assembled via composition. The boundary describes only the oracle interface
mapping from the batched context to the single-codeword FRI context.

---

## 9. Literature Connections

The closest conceptual matches are:

**Interpreter lifting / handler lifting (PL)**

Xia et al., *Interaction Trees*, and Yoon–Zakowski–Zdancewic, *FRALMI* study
how to lift a partial interpreter over a larger signature while transporting
behavioral facts. The access layer's `pullbackCounterpart` is essentially an
instance of this: it lifts the inner counterpart (an interpreter of the inner
oracle signature) through the outer oracle signature via `simulateIn`.

**Converters and resources (constructive cryptography)**

Maurer, *Constructive Cryptography*, and Basin et al., *Abstract Modeling of
System Communication in CryptHOL*, treat interface boundaries as first-class
converters around resources. The `Realizes` coherence predicate and the eventual
security transport theorems belong in this tradition: the boundary is an internal
converter, and correctness means it preserves the security properties of the
inner resource when composed with a protocol using the outer interface.

**IOP reductions and compiler boundaries**

Kothapalli–Parno, *Algebraic Reductions of Knowledge*, and the IOP literature
(Ben-Sasson–Chiesa–Spooner) motivate why the knowledge soundness transport
theorem requires more than plain soundness preservation. The extractor direction
of `Boundary.Witness` (not yet implemented) is where this becomes critical.

**Optics / open games**

Optics give good shape intuition (lens-like forward/backward pass) but the
preserved invariant in open games is best response / equilibrium, not security
transport. Optics are a secondary analogy here, not the primary one.

---

## 10. File Map

```
ArkLib/Interaction/Boundary.lean           -- top-level import
ArkLib/Interaction/Boundary/
  Core.lean                                -- Statement, Witness, Context, pullback
  Oracle.lean                              -- OracleStatementAccess, OracleContextAccess
                                           -- OracleVerifier.pullback
  Reification.lean                         -- OracleStatementReification, OracleStatement
                                           -- OracleContext, Realizes, OracleReduction.pullback
```
