# Design review: what should an oracle reduction be?

## Executive verdict

The current framework has identified the correct operational idea but has made it the wrong foundational object.

An output oracle of a reduction is usually not a newly transmitted string. It is a derived oracle: a query to it can be implemented using input-oracle queries, transcript-oracle queries, and public challenges. That is exactly what `simulate` captures.

But an arbitrary

```lean
QueryImpl [OStatementOut pt]ₒ
  (OracleComp ([OStatementIn]ₒ + transcriptOracleSpec pt))
```

should be the denotation or execution semantics of an output oracle—not the output oracle itself.

Making that `QueryImpl` canonical causes:

- security relations to range over intensional programs rather than mathematical oracle claims;
- semantic materialization to become an optional, duplicated “reification” layer;
- composition to be implemented by large pieces of bespoke `simulateQ` routing;
- structural provenance to disappear behind arbitrary monadic code;
- no satisfactory path from terminal derived oracles to committed strings in BCS/NARG compilation.

The canonical output should instead be a typed virtual-oracle object bundling:

1. its mathematical denotation as concrete oracle data;
2. a typed query plan over explicit input/transcript sources;
3. a proof that the plan realizes the denotation.

`simulate` then becomes a projection from the output claim, not a separate verifier field.

---

# 1. Reconstruction of the current design

## 1.1 Plain reductions

The plain layer is clean and conventional. A reduction contains:

```lean
structure Reduction ... where
  prover   : Prover ...
  verifier : Verifier ...
```

The honest prover returns a pair of output statement and output witness, while the verifier returns only the output statement. See [Reduction.lean:83](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Reduction.lean:83>) and [Reduction.lean:181](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Reduction.lean:181>).

Sequential composition forwards the honest prover’s intermediate statement and witness to the next prover and the verifier’s intermediate statement to the next verifier. The second protocol is indexed by the first transcript. See [Reduction.lean:274](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Reduction.lean:274>).

The plain security definitions are relations on ordinary output values. For example, knowledge soundness gives the extractor the transcript, verifier output, and prover witness output; see [Security/KnowledgeSoundness.lean:27](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Security/KnowledgeSoundness.lean:27>).

## 1.2 Oracle protocol shape

`Oracle.Spec` distinguishes:

- `.public X rest`, where both parties see `x : X` and the continuation may depend on it;
- `.oracle X cont`, where the prover supplies `x : X`, but the continuation is indexed only by `PUnit`.

This enforces that protocol shape cannot branch on hidden oracle-message data. See [Oracle/Spec.lean:117](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:117>) and [Oracle/Spec.lean:170](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:170>).

Accordingly, the framework has two transcripts:

```lean
PublicTranscript s
FullTranscript s
```

The public transcript records `PUnit` at oracle nodes; the full transcript records the actual prover oracle messages. See [Oracle/Spec.lean:289](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:289>).

Given a public transcript, the protocol exposes all transcript-oracle queries through:

```lean
QueryHandle s od pt
toOracleSpec s od pt
```

and a full transcript supplies their deterministic implementation:

```lean
answerQuery s od tr :
  QueryImpl (toOracleSpec s od (s.projectPublic tr)) Id
```

See [Oracle/Spec.lean:382](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:382>) and [Oracle/Spec.lean:406](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:406>).

This public/full transcript separation is one of the strongest parts of the design.

## 1.3 Oracle statements and input semantics

A concrete indexed oracle statement is:

```lean
abbrev OracleStatement (OStmt : ι → Type) :=
  ∀ i, OStmt i
```

A local statement bundled with concrete oracle data is:

```lean
structure StatementWithOracles ... where
  stmt       : LocalStmt i
  oracleStmt : OracleStatement (OStmt i)
```

See [Oracle/Core.lean:24](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Core.lean:24>) and [Oracle/Core.lean:51](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Core.lean:51>).

Concrete data is turned into a deterministic implementation by `OracleInterface.simOracle0`. More abstract security games instead accept:

```lean
InputImpl OStatementIn shared :=
  QueryImpl [OStatementIn shared]ₒ Id
```

See [Oracle/Security/Basic.lean:24](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:24>).

During execution, verifier receiver nodes can query:

```lean
oSpec + [OStatementIn]ₒ + accumulatedMessageSpec
```

The runner routes these respectively to ambient effects, the supplied input implementation, and concrete prover messages already present in the full transcript. See [Oracle/Execution.lean:55](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Execution.lean:55>).

## 1.4 The asymmetry in outputs

The honest prover explicitly returns concrete output-oracle data:

```lean
StatementWithOracles
  (fun _ => StatementOut shared pt)
  (fun _ => OStatementOut shared pt)
  shared
```

See [Oracle/Core.lean:97](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Core.lean:97>).

The verifier endpoint, however, returns only `StatementOut`. Separately, `Verifier.WithMonads` contains:

```lean
simulate :
  (shared : SharedIn) →
  (pt : PublicTranscript (Context shared)) →
  QueryImpl [OStatementOut shared pt]ₒ
    (OracleComp
      ([OStatementIn shared]ₒ +
       (Context shared).toOracleSpec (OracleDeco shared) pt))
```

See [Oracle/Core.lean:155](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Core.lean:155>) and particularly [Oracle/Core.lean:183](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Core.lean:183>).

`Verifier.run` packages the ordinary verifier statement with this static simulator after the interaction completes; it does not obtain an oracle object from the verifier endpoint. See [Oracle/Execution.lean:693](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Execution.lean:693>).

Thus there are two notions of output:

- honest prover output: concrete oracle data;
- verifier/security output: local statement plus an oracle query program.

Completeness proves that they agree query-by-query through `OutputRealizes`; see [Oracle/Security/Completeness.lean:23](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Completeness.lean:23>).

## 1.5 Reification

Reification attempts to recover concrete output data from the implicit simulator:

```lean
structure Reification (reduction : Oracle.Reduction ...) where
  reify :
    shared →
    OracleStatement (OStatementIn shared) →
    FullTranscript →
    Option (OracleStatement (OStatementOut ...))
  correct : ...
```

See [Oracle/Reification.lean:106](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:106>).

It is optional and partial (`Option`). Correctness says that when materialization succeeds, the concrete output realizes `simulate`.

There is a near-duplicate verifier-side reification API beginning at [Oracle/Reification.lean:321](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:321>).

---

# 2. Consequences of implicit output

## 2.1 Sequential composition

### Honest prover side

The first honest prover already has concrete intermediate oracle statements. They are directly bundled into the input to the second prover:

```lean
let midStmt := ⟨midOut.stmt.stmt, midOut.stmt.oracleStmt⟩
let strat₂ ← (r₂ shared pt₁).prover ... midStmt midOut.wit
```

See [Oracle/Composition.lean:696](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:696>).

That part is straightforward.

### Verifier side

The second verifier expects its input oracle family to be queryable as `[OStatementMid]ₒ`. But the first verifier has produced only a simulator over:

```lean
[OStatementIn]ₒ + s₁.toOracleSpec od₁ pt₁
```

`Verifier.retargetMonads` rewrites every second-stage query through the first simulator, while `Spec.answerQuery` supplies concrete answers for first-stage transcript-oracle queries. See [Oracle/Composition.lean:546](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:546>) and its use at [Oracle/Composition.lean:779](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:779>).

The final composed simulator is then manually assembled through three routes:

- `routeRight` embeds suffix transcript queries;
- `routeLeft` embeds prefix transcript queries;
- `routeMid` replaces middle-oracle queries by the first simulator.

See [Oracle/Composition.lean:790](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:790>).

Operationally, this is correct. Conceptually, it is substitution of one virtual-oracle program into another. The code has no named virtual-oracle composition operation, so that substitution appears as 40 lines of specialized `QueryImpl` plumbing.

### Provenance

There is limited provenance in the source query type:

```lean
[OStatementIn]ₒ + toOracleSpec ...
```

and `QueryHandle.routeLeft`/`routeRight` preserve which protocol phase owns a transcript query. See [Oracle/Spec.lean:1055](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:1055>).

But once an output is represented by an arbitrary `QueryImpl`, provenance is no longer first-class. One can execute the program and observe its source queries, but the output object carries no structural declaration such as “this is a folding of message oracle 3 and input oracle 0.” Composition therefore preserves provenance operationally, not as inspectable data.

### Casts and associativity

The new `Oracle.Spec` representation succeeds at its immediate goal: there are no `cast`, `Eq.mp`, `Eq.mpr`, or `HEq` occurrences in the oracle composition files. Structural recursion and `PublicTranscript.split`/`unliftAppend` avoid them.

For example, output reindexing uses `unliftAppend`, not proof-generated transports, at [Oracle/Composition.lean:731](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:731>).

However:

- composition is not definitionally associative;
- query sums are explicitly left-associated;
- nested composition produces nested `split` terms and differently associated source specifications;
- there is no associativity theorem for `Oracle.Reduction.comp`.

The access layer openly describes its source specification as “standard left-associated” at [Oracle/VerifierAccess.lean:38](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/VerifierAccess.lean:38>).

So casts have been eliminated, but associativity has not been obtained as a canonical law. Proving it would require extensional `simulateQ` reasoning over reassociated source programs.

## 2.2 Security relations over implementations

The behavior-first relations are literally predicates on implementations:

```lean
InputRelation  := stmt → InputImpl → witness → Prop
OutputRelation := inputImpl → pt → stmtOut → OutputImpl → witnessOut → Prop
```

See [Oracle/Security/Basic.lean:92](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:92>).

Soundness and knowledge soundness then pass `verifier.simulate shared pt` directly to those predicates; see [Oracle/Security/Soundness.lean:94](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Soundness.lean:94>) and [Oracle/Security/KnowledgeSoundness.lean:78](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/KnowledgeSoundness.lean:78>).

This is well-typed, but not automatically well-defined extensionally.

Two `OutputImpl`s can answer every query identically after being run against the same input and transcript implementations while remaining different `OracleComp` programs. A relation is free to distinguish them using:

- equality of returned `OracleComp` syntax;
- number or order of queries;
- irrelevant pure/bind structure;
- any intensional property of the implementation.

Function extensionality only helps when `outputImpl₁ q = outputImpl₂ q` as `OracleComp` terms. It does not identify two programs having the same evaluated answers.

Therefore a mathematical relation on oracle statements is represented correctly only if the user proves or assumes that it respects the appropriate observational equivalence. The API currently has no such `Respectful` condition and no quotient.

The reified adapters do not solve this. They existentially choose concrete output data but explicitly discard the realization condition because it needs the full transcript:

```lean
fun ... _outputImpl ... =>
  ∃ oStatementOut, ...
```

See [Oracle/Reification.lean:213](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:213>) and the verifier version’s own warning at [Oracle/Reification.lean:531](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:531>).

The direct reified security games consequently have to repeat `OutputRealizes` inside the probability event; see [Oracle/Reification.lean:611](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:611>).

## 2.3 Extraction

The current extractor can use implicit output oracles.

It receives:

- `inputImpl`;
- the full transcript;
- the verifier’s `outputImpl`;
- the output statement and witness.

See [Oracle/Security/Basic.lean:132](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:132>).

Given the full transcript, `Spec.answerQuery` supplies the transcript-message part of the source implementation, so `simulateQ` can evaluate output-oracle queries. The code’s documentation explicitly relies on this at [Oracle/Security/Basic.lean:146](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:146>).

There are two caveats:

1. The extractor receives the full runtime transcript, including actual oracle-message values—not merely black-box query access. This can be stronger than the intended straightline extractor model.
2. It receives an intensional implementation, so extractor correctness can accidentally depend on the chosen query program rather than only the output oracle’s behavior.

A cleaner interface would give the extractor a typed read capability for the derived output oracle, with full transcript access added only when a theorem genuinely needs it.

## 2.4 BCS, Merkle commitments, and Fiat–Shamir

The current BCS code transforms protocol-message oracle nodes. It knows how to:

- replace an oracle message by a public commitment;
- retain the underlying message as prover witness;
- produce and answer queries to committed message oracles.

See [Oracle/BCS.lean:130](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:130>), [Oracle/BCS.lean:190](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:190>), and [Oracle/BCS.lean:397](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:397>).

It does not currently transform an `Oracle.Reduction`, its output claim, or its `simulate`. `BCS.lean` imports `Oracle.Spec`, not `Oracle.Core`, and stops at protocol strategies/opening decorations.

An implicit output oracle can survive compilation only in the limited sense that its query program may be inlined into a compiled verifier. That is fine while the oracle remains purely virtual.

It is not enough when the output must:

- become an externally visible statement;
- be committed for a later NARG;
- cross a recursive-proof boundary;
- be serialized or handed to another compiled component;
- carry a cost model proving that its queries compile efficiently.

An arbitrary `QueryImpl` says how to answer one query. It provides neither:

- concrete strings to commit;
- an explicit materialization algorithm;
- a serializable provenance graph;
- a compilation/circuit witness;
- a bound on query count or adaptivity.

Fiat–Shamir does not repair this. It can compile verifier randomness, but it does not turn a semantic oracle implementation into committed data.

---

# 3. Precise pain points in the code

## Real issues

1. **Specialized simulator composition.**  
   The final simulator of binary composition is hand-routed at [Oracle/Composition.lean:790](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:790>). This is virtual-oracle substitution implemented ad hoc.

2. **Verifier monad retargeting exists only because the middle claim is not an object.**  
   `Verifier.retargetMonads` rewrites a whole counterpart strategy from middle-oracle access to original-input access at [Oracle/Composition.lean:546](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:546>).

3. **Every chain/choreography must separately supply both concrete output data and a simulator.**  
   `Reduction.ofChain` takes `oStmtResult` and an independent `simulate`; see [Oracle/Chain.lean:329](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Chain.lean:329>) and [Oracle/Chain.lean:337](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Chain.lean:337>).  
   `ReductionProgram` repeats the same split at [Choreo.lean:346](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Choreo.lean:346>) and [Choreo.lean:360](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Choreo.lean:360>).

   Nothing intrinsic ties these two outputs together; completeness must establish their coherence later.

4. **Reification is duplicated and partial.**  
   Reduction-side and verifier-side reification each contain a partial `Option` materializer and correctness theorem. The first starts at [Oracle/Reification.lean:106](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:106>); the second at [Oracle/Reification.lean:437](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:437>).

5. **Concrete relation adapters lose the crucial fact.**  
   The adapters existentially choose concrete oracle data without connecting it to `outputImpl`; see [Oracle/Reification.lean:240](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:240>) and [Oracle/Reification.lean:607](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:607>).

6. **Boundary routing is disproportionately large.**  
   A boundary needs separate:
   - input simulation;
   - output simulation;
   - input materialization;
   - output materialization;
   - two coherence clauses.

   See `OracleStatementAccess` at [Boundary/Oracle.lean:319](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Oracle.lean:319>) and `OracleStatementReification` at [Boundary/Reification.lean:24](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Reification.lean:24>).

   `routeInnerOutputQueries` alone requires a long semantic commuting proof beginning at [Boundary/Oracle.lean:487](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Oracle.lean:487>). This is another instance of composing virtual-oracle morphisms without naming them as such.

7. **Plain and oracle boundary hierarchies are largely parallel.**  
   Plain `StatementProjection`/`Statement`/`Witness`/`Context` begin at [Boundary/Core.lean:66](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Core.lean:66>). Oracle-specific variants reproduce the same organization and then add access/reification/coherence. A claim object with a functorial oracle component would let the ordinary boundary mechanism transport it.

8. **No oracle-level security composition theorem is present.**  
   Plain completeness and soundness have composition theorems. The oracle security directory has monotonicity results, but no corresponding `soundness_comp`, `completeness_comp`, or knowledge-soundness composition theorem for `Oracle.Reduction`. This is notable given how much machinery exists specifically for operational composition.

9. **BCS stops before reduction outputs.**  
   The BCS code builds protocol-level commitment machinery but provides no transformation of `Oracle.Reduction` or its output simulator.

## What is not currently a pain point

The requested oracle files contain no `HEq` and no proof-generated casts. The only explicit `Eq.mpr` under `ArkLib/Interaction` is the compatibility helper at [Compat.lean:27](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Compat.lean:27>).

There is one `sorry`, in the generic claim-tree probability theorem at [Security/ClaimTree.lean:138](</Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Security/ClaimTree.lean:138>). It is not caused by output-oracle simulation.

So the new spec representation has genuinely solved the old cast/`HEq` problem. The remaining weakness is semantic architecture and API size, not dependent equality.

---

# 4. Alternatives

| Alternative | Composition | Security | Compilation |
|---|---|---|---|
| Explicit oracle data only | Simple value forwarding and associativity | Relations are ordinary mathematical relations | Easy to commit, but eagerly materializes virtual oracles and can destroy succinctness |
| Explicit data plus virtual-oracle DSL | Composition is typed substitution; associative by DSL laws | Relations use denotation, proofs use query semantics | Best option: inline views or explicitly materialize/commit |
| Pointer/lens into sources | Excellent for projections and structural reuse | Clear provenance | Too weak alone for linear combinations, quotients, folding, interpolation |
| Quotient of implementations | Extensional composition possible but cumbersome | Mathematically clean behavior equality | Bad executable/compiler interface; quotient representatives and costs are unavailable |
| Pair statement with raw `QueryImpl` | Removes the detached `simulate` field | Still intensional unless relations are restricted | Better packaging, but still no materialization or compiler structure |
| Relations directly over `QueryImpl` | Matches current implementation | Requires every relation to respect observational equivalence | Useful as a low-level derived layer, not as canonical cryptographic semantics |

## (i) Explicit data plus a virtual-oracle language

This should be the foundation.

The virtual language need not be a small closed AST containing only today’s known constructions. It can have:

- structural constructors: input oracle, transcript message, projection, reindexing;
- common algebraic constructors: map, linear combination, batching, quotient, folding;
- a general typed query-plan constructor carrying:
  - mathematical denotation;
  - query program;
  - correctness proof;
  - optional compilation/cost evidence.

Thus the DSL is extensible without reducing all output claims to arbitrary raw `QueryImpl`.

## (ii) Pointer/lens only

This is valuable as the provenance core. It handles:

- selecting existing input or message oracles;
- reindexing;
- appending and splitting contexts;
- holographic access to fixed data.

It does not by itself express a WHIR/FRI fold, quotient oracle, or batched linear combination. Those require computations over one or more source queries. Therefore pointers should be source leaves inside the virtual-oracle language.

## (iii) Full quotient of implementations

One could define output oracles as `QueryImpl` modulo observational equivalence under all source environments.

That makes relations extensional, but it is a poor executable representation:

- equality is hard to use;
- extracting a representative requires quotient lifting;
- cost, provenance, and serializability are lost;
- compilation is not invariant under arbitrary observational equivalence—two equal behaviors may have radically different query complexity.

A quotient is appropriate for a semantic theorem layer, not the canonical executable object.

## (iv) Pair statement and implementation

This is a worthwhile immediate cleanup:

```lean
structure RelativeClaim ... where
  stmt    : StatementOut ...
  oracles : OutputImpl ...
```

The verifier endpoint would return this record, eliminating the detached `simulate`.

But raw `OutputImpl` remains intensional and unmaterializable. This is an incremental migration step, not the end state.

## (v) Relations directly over `QueryImpl`

The current behavior layer is useful for relational oracles, ideal functionalities, and black-box statements that genuinely have no chosen data representation.

It should be explicitly marked as a low-level semantic variant and require:

```lean
def Respectful (R : OutputImpl → Prop) : Prop :=
  ∀ a b, ObservationallyEquivalent a b → (R a ↔ R b)
```

Without this, “language of oracle claims” is not invariant under implementation choice.

---

# 5. Recommended canonical definition

## 5.1 Typed sources and virtual oracles

A sketch:

```lean
structure OracleFamily where
  ι   : Type
  Obj : ι → Type
  oi  : ∀ i, OracleInterface (Obj i)

abbrev OracleFamily.Data (F : OracleFamily) :=
  ∀ i, F.Obj i

structure OracleSources where
  spec : OracleSpec
  Data : Type
  impl : Data → QueryImpl spec Id
```

For a reduction at public transcript `pt`, the source family should be structurally identified as:

```lean
def reductionSources (shared) (pt) : OracleSources :=
  inputSources (OStatementIn shared) ++
  transcriptSources (Context shared) (OracleDeco shared) pt
```

Then:

```lean
structure VirtualOracle
    (Src : OracleSources)
    (Out : OracleFamily) where
  /-- Mathematical oracle represented by the view. -/
  denote :
    Src.Data → Out.Data

  /-- Query implementation used by reductions and compiled verifiers. -/
  query :
    QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)

  /-- Query execution agrees with the mathematical denotation. -/
  query_correct :
    ∀ (src : Src.Data) i
      (q : OracleInterface.Query (Out.Obj i)),
      simulateQ (Src.impl src) (query ⟨i, q⟩) =
        pure (OracleInterface.answer (denote src i) q)
```

This is deliberately more than `QueryImpl`:

- `query` is the current `simulate`;
- `denote` replaces optional reification;
- `query_correct` makes realization intrinsic;
- `Src` records provenance structurally.

Compilation metadata should be separate:

```lean
structure VirtualOracle.Compilation
    (v : VirtualOracle Src Out) where
  queryCost    : ...
  compileQuery : ...
  materialize? : Option (Src.Data → Out.Data)
  encode?      : Option (Out.Data → ByteArray)
```

Not every information-theoretic oracle needs to be serializable, but compilation must be able to demand that evidence explicitly.

## 5.2 The output claim

```lean
structure OracleClaim
    (Src : OracleSources)
    (Stmt : Type)
    (Out : OracleFamily) where
  stmt    : Stmt
  oracles : VirtualOracle Src Out
```

The verifier’s terminal output should be this record:

```lean
abbrev Verifier ... :=
  (shared : SharedIn) →
  StatementIn shared →
  CounterpartStrategy ...
    (fun tr =>
      OracleClaim
        (reductionSources shared (Context shared).projectPublic tr)
        (StatementOut shared (Context shared).projectPublic tr)
        (outputFamily shared (Context shared).projectPublic tr))
```

There should be no separate `simulate` field. For compatibility:

```lean
def Verifier.simulate (v : Verifier ...) shared pt :=
  (v.outputView shared pt).oracles.query
```

but this is a projection or derived operation.

If constructing the complete claim inside the endpoint is inconvenient, the terminal verifier state may be returned first and a single `output` projection may construct the whole `OracleClaim`. The important invariant is that statement and oracle view are one output object.

## 5.3 Honest output

The honest prover should return concrete data plus witness:

```lean
structure HonestOracleOutput ... where
  claimData :
    StatementOut shared pt ×
    OracleStatement (OStatementOut shared pt)
  witness :
    WitnessOut shared pt
```

Completeness compares this directly with the verifier claim’s denotation under the realized source environment:

```lean
proverOut.claimData.1 = verifierClaim.stmt ∧
proverOut.claimData.2 =
  verifierClaim.oracles.denote sourceData ∧
relOut verifierClaim.stmt proverOut.claimData.2 proverOut.witness
```

There is no separate `OutputRealizes` obligation: it follows from `query_correct`.

## 5.4 Composition

Composition becomes substitution of source morphisms:

```lean
def VirtualOracle.bind
    (mid : VirtualOracle Src Mid)
    (out : VirtualOracle (MidSources Mid Msg) Out) :
    VirtualOracle (Src ++ Msg) Out
```

The query component is Kleisli composition with `simulateQ`; the denotation component is ordinary function composition; correctness follows from the two `query_correct` proofs.

The intended laws are then explicit:

```lean
theorem bind_id_left  : ...
theorem bind_id_right : ...
theorem bind_assoc    : ...
```

This is the operation currently spread across `retargetMonads`, `routeLeft`, `routeRight`, `routeMid`, and boundary pullback.

Pointers/lenses become special `VirtualOracle` constructors. Linear combinations, quotient oracles, FRI folds, STIR folds, and WHIR constrained oracles become additional constructors or proved smart constructors.

## 5.5 Security

Canonical relations should be on mathematical claims:

```lean
abbrev InputRelation :=
  ∀ shared,
    StatementIn shared →
    OracleStatement (OStatementIn shared) →
    WitnessIn shared →
    Prop

abbrev OutputRelation :=
  ∀ shared pt,
    StatementOut shared pt →
    OracleStatement (OStatementOut shared pt) →
    WitnessOut shared pt →
    Prop
```

The soundness event uses the denotation of the verifier’s virtual output under the realized input/full-transcript source environment.

This does not make the verifier see hidden data. Denotation is part of the meta-level security semantics, while the executable verifier uses only `.query`.

For black-box input-oracle games, retain a secondary behavior layer over `QueryImpl`, but require extensionality explicitly.

An extractor should normally receive output query access:

```lean
structure Extractor where
  extract :
    shared →
    stmtIn →
    InputOracleAccess →
    publicTranscript →
    stmtOut →
    OutputOracleAccess →
    witOut →
    WitnessIn
```

A stronger full-transcript extractor can be defined separately. This avoids silently granting every extractor direct access to all concrete oracle-message values.

## 5.6 Compilation choices

A compiler encountering a `VirtualOracle` should make an explicit choice:

```text
virtual output
├── inline: compile its query plan into the next verifier
└── materialize: compute data, encode it, commit it, and expose openings
```

FRI/STIR/WHIR folds normally use the first path between information-theoretic stages. A recursive proof boundary or externally visible NARG statement may require the second.

This cleanly separates:

- mathematical oracle claim;
- efficient virtual query implementation;
- concrete serialization/commitment policy.

---

# Final assessment

The current `simulate` idea is fundamentally right: oracle-reduction outputs are often virtual views, and sequential composition should substitute those views rather than eagerly copy enormous oracle data.

The mistake is identifying the view with an arbitrary `QueryImpl` and making concrete meaning an optional afterthought.

The canonical object should be a typed, provenance-aware virtual oracle with both denotation and query semantics. The existing `simulate` becomes its `query` projection. Reification becomes intrinsic denotation. Boundary routing becomes functorial composition. Security relations return to mathematical oracle statements. BCS can either inline or materialize the same object.

In short:

> Keep simulation as the operational semantics of output oracles, but stop treating simulation code as the output claim itself.