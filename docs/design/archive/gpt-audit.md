# 1. Executive verdict

**Verdict: do not adopt the proposal as written.** Adopt the narrower idea—package the public statement together with a source-scoped virtual query plan—but do not make total concrete `Out.Data` denotation canonical, do not demote behavioral semantics, and do not promise ordinary Kleisli or strict associativity laws yet.

The proposal identifies three different notions that the current code deliberately keeps apart:

1. a concrete oracle value such as a bounded-degree polynomial;
2. an arbitrary deterministic oracle behavior;
3. a typed query program over earlier resources.

That identification fails precisely in the malicious-input cases used by the current security definitions.

Severity-ranked findings:

1. **Critical — `denote : Src.Data → Out.Data` is unavailable in the current soundness and knowledge-soundness games.** Those games quantify arbitrary `InputImpl`, not concrete input oracle data. A simulator applied to arbitrary behavior need not correspond to any value of `Out.Data`. Restricting to realizable inputs would silently weaken the security definition.

2. **Critical — the transcript half of `Src.Data` is not defined by the proposed source spec.** `toOracleSpec od pt` records query and response types, but not the underlying oracle-message values. At fixed `pt`, the required data is a fiber of full transcripts—or, better, a recursively defined family of hidden messages along `pt`.

3. **High — sequential composition is not ordinary `VirtualOracle.bind`.** The second output depends on the first virtual output **and new suffix transcript resources**. Its real shape is substitution
   \[
   (S\to A),\;(A\otimes T\to B)\;\mapsto\;(S\otimes T\to B),
   \]
   with weakening, routing, and sum associators. The denotation is `g (f s, t)`, not simple function composition.

4. **High — `query_correct` does not make completeness realization disappear.** It connects the verifier’s query program to `denote`. Completeness must still connect the honest prover’s concrete output to `denote`, normally observationally. Literal equality is stronger than the current API and is unjustified because `OracleInterface.answer` is not assumed faithful.

5. **High — replacing terminal simulation does not eliminate interactive monad retargeting.** The new `Program` layer already packages `stmt + simulate`, but composition still rewrites every suffix verifier-local oracle action. `retargetMonads` or its programmatic successor remains necessary.

6. **High — “sources are a sum spec” is scoped access, not adequate provenance.** It lacks stable resource identity, origin, dependency edges, visibility, binding time, opening strategy, and cost. Therefore the claimed BCS per-handle compilation policy cannot be implemented from the proposed record.

7. **High — the migration plan targets an obsolete seam.** `Verifier.TerminalOutput` already performs the proposed endpoint merge in the newer programmatic layer. Any migration must begin there and preserve compatibility with `Program`, `VerifierAccess`, and programmatic security.

8. **Medium — the proposed extractor default is not the one matched by the cited literature.** Current ArkLib gives the extractor the full transcript, and the literature survey says the canonical formulations expose concrete prover oracle messages or stronger rewinding/tree access. A query-only extractor is a useful stronger theorem notion, but not the literature-default one.

9. **Medium — the two-layer `Respectful` story is underspecified.** Observational equivalence depends on a realized source environment, including hidden transcript messages. The current `OutputRelation` receives only `pt`, so it cannot even state the required equivalence without changing its signature.

10. **Medium — universe generality is not free.** The current interaction stack intentionally pins protocol messages and ambient oracle specs to the default universe. A universe-polymorphic semantic carrier can lift terminal outputs beyond the `Type` expected by current `Program` APIs.

---

# 2. Per-question analysis

## A. Type-theoretic feasibility

### What is transcript `Src.Data`?

It cannot be just `FullTranscript s`, because the virtual oracle is indexed by a fixed public transcript `pt`. `PublicTranscript` contains public messages and only `PUnit` markers at oracle nodes, while `FullTranscript` contains the actual oracle messages ([Spec.lean:291](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:291)). The obvious mathematical definition is

```lean
Σ tr : Spec.FullTranscript s, Spec.projectPublicFull s tr = pt
```

but this introduces equality witnesses and transports throughout denotation and composition—the exact pattern the project guardrails seek to avoid.

A better definition is structural:

```lean
def Spec.OracleMessagesAt :
    (s : Spec) → Spec.PublicTranscript s → Type
  | .done, _ => PUnit
  | .public _ rest, ⟨x, pt⟩ =>
      OracleMessagesAt (rest x) pt
  | .oracle X cont, ⟨_, pt⟩ =>
      X × OracleMessagesAt (cont ⟨⟩) pt
```

This is the hidden-data fiber of the full transcript with the public path fixed definitionally.

Nothing equivalent exists today. `toOracleSpec` produces only the handle-indexed query specification ([Spec.lean:382](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:382)); actual answers require a full transcript ([Spec.lean:406](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:406)). Thus an `OracleSources` structure must retain the original input family and interaction tree, not merely their erased sum `OracleSpec`.

### The malicious input has no `Src.Data`

Current input semantics is explicitly

```lean
InputImpl OStatementIn shared :=
  QueryImpl [OStatementIn shared]ₒ Id
```

([Basic.lean:24](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:24)). Soundness universally quantifies `inputImpl` ([Soundness.lean:86](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Soundness.lean:86)), as does knowledge soundness ([KnowledgeSoundness.lean:71](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/KnowledgeSoundness.lean:71)).

An arbitrary implementation need not equal `simOracle0` for any concrete `OracleStatement`. For example, arbitrary answers at evaluation queries need not arise from any bounded-degree polynomial. Therefore:

- if `Src.Data` contains concrete input values, security games cannot construct it;
- if `Src.Data` contains `InputImpl`, total denotation into structured `Out.Data` is generally impossible;
- if soundness is restricted to realizable `InputImpl`, the definition becomes weaker.

The statement “the prover physically sends messages” solves only the transcript-message half. It does not materialize the externally supplied input oracles.

### Universes

`Oracle.Spec` is intentionally pinned: messages are `X : Type`, `Spec : Type 1`, and ambient query specifications are conventionally `OracleSpec.{0,0}` ([Spec.lean:47](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:47)). `Verifier.TerminalOutput` likewise fixes statement and oracle families in `Type` ([Program.lean:28](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Program.lean:28)).

Thus the first implementation should pin:

```lean
Src.Env : Type
Out.Sem : Type
```

If `Src.Data : Type u` and `Out.Data : Type v` are freely polymorphic, `VirtualOracle` can escape the universe expected at terminal program leaves. Generalizing this means generalizing `Program`, `TerminalOutput`, interaction output families, and downstream protocol clients—not just the new record.

### Decidability and computability

`query_correct` itself requires neither `DecidableEq` nor classical choice. It is an equality in `Id`, and the existing composition lemma only assumes a lawful monad ([Oracle.lean:42](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Oracle.lean:42)).

Noncomputability appears if one tries to obtain concrete `Out.Data` from behavior using choice. That would be particularly harmful for the proposed compiler: a classically chosen denotation is not an executable materializer and carries no cost information. The current reification module is globally noncomputable ([Reification.lean:22](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:22)), but protocol-specific boundary materializers can still be concrete functions.

**A conclusion:** the record is feasible only after replacing concrete `Src.Data`/`Out.Data` with a deliberately chosen semantic environment/carrier, normally broad enough to include arbitrary behavior.

---

## B. Is total `denote` realistic?

### Why current reification uses `Option`

The code describes reification as an optional concrete bridge over behavior-first semantics ([Reification.lean:12](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:12)). Its field returns

```lean
Option (OracleStatement ...)
```

and correctness is required only in the `some` case ([Reification.lean:106](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Reification.lean:106)).

There are no substantive reduction-side constructors in the repository demonstrating a necessary `none` branch. The working Spartan boundaries instead use total `materializeIn` and `materializeOut` functions ([Boundary/Reification.lean:24](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Reification.lean:24)); the first-sumcheck boundary constructs a virtual polynomial concretely and proves pointwise realization ([FirstSumcheck.lean:465](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/ProofSystem/Spartan/FirstSumcheck.lean:465)).

So `Option` is primarily an architectural statement—materialization is optional—not evidence that all existing protocols require partial materialization. The current API is actually too weak in another direction: an always-`none` reification satisfies `correct` vacuously.

### Nevertheless, total concrete denotation is genuinely too strong

Legitimate failure modes include:

- **Arbitrary behavioral inputs.** A point-evaluation behavior may not come from any bounded-degree polynomial.
- **Refinement-valued outputs.** If `Out.Data` is a subtype carrying a degree, code, proximity, or consistency proof, malformed source behavior has no inhabitant.
- **Quotients and rational transformations.** A quotient view can be pointwise meaningful only under a non-vanishing or divisibility condition. Choosing defaults makes it total operationally but changes the mathematical meaning.
- **Relational or ideal resources.** Their truth may be expressed by existence or a predicate on behavior, not by a canonical chosen representative.
- **Non-faithful interfaces.** Several different concrete values may induce the same query behavior; there is no canonical choice among them.
- **Stateful or randomized ideal oracles.** These are outside the current `QueryImpl … Id` model entirely. A concrete `Out.Data` field does not solve that limitation.

Degree and proximity are especially important: the literature catalog explicitly says degree/domain claims must remain separate from raw evaluation semantics ([gpt-literature.md:536](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:536)). Making the output data a bounded-degree object bakes validity into something that must exist even for invalid malicious executions.

The “generic query plan + denotation + proof” escape hatch is not sufficient. It permits arbitrary definable denotations; it does not produce an `Out.Data` inhabitant when none exists.

### Recommended resolution

Keep totality, but totality into an intentionally broad semantic carrier:

- `Out.Sem := QueryImpl [Out.Obj]ₒ Id` as the always-available fallback; or
- an unrestricted mathematical function space;
- with degree, code membership, proximity, and similar properties stated in the output relation.

Concrete `OracleStatement` materialization should remain a separate, optional strengthening. Optional denotation itself is a bad canonical basis for relations: it forces every relation to decide what `none` means. A broad total semantic carrier avoids that ambiguity.

---

## C. Security definitions

### Soundness

Current soundness is behavior-level by construction. It asks whether an arbitrary invalid input behavior can be reduced to an output behavior in the target language ([Soundness.lean:58](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Soundness.lean:58)).

A data-level formulation through total concrete denotation is:

- **equivalent only if** every quantified input implementation has a compatible source datum and the denotation realizes the evaluated query plan;
- **weaker** if quantification is restricted to realizable inputs;
- potentially **stronger or ill-defined** if the chosen `Out.Data` contains refinement proofs or representation-specific information not observable through queries.

The proposal therefore materially reverses the previous design consensus, which explicitly says behavior should be primary and reification secondary ([consensus note:152](/Users/quangdao/Documents/paper-note/notes/ArkLib-Refactor_oracle_reduction_as_ior.md:152)). That reversal needs a proof, not an assertion.

### Knowledge soundness

The current malicious prover returns only the output witness. The verifier defines the output statement and simulator; the extractor receives the arbitrary input implementation, full transcript, statement, simulator, and output witness ([KnowledgeSoundness.lean:25](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/KnowledgeSoundness.lean:25)).

Replacing `outputImpl` by a semantic output behavior evaluated from an actual source environment is coherent. Requiring a concrete output value is not.

The proposed “query-access extractor by default, full-transcript extractor separately” is a defensible new **stronger extraction notion**, but it does not “match” the cited formulations. The local survey concludes that BCS-style rewinding, BGTZ partial transcripts, CDHZ relaxed RBR extraction, and FICS/FACS transcript trees expose concrete prover messages or stronger access ([KS survey:20](/Users/quangdao/Documents/paper-note/notes/arklib-ior-knowledge-soundness-survey.md:20)). The current full-transcript extractor is deliberately aligned with that evidence ([Basic.lean:132](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:132)).

Recommended naming:

- `knowledgeSoundness` or `knowledgeSoundnessFullTranscript`: literature-aligned;
- `knowledgeSoundnessQueryOnly`: stronger, useful when provable;
- explicit implication from query-only to full-transcript extraction.

### Completeness

Current completeness separately checks:

1. public statement equality;
2. query-level realization of the prover’s concrete oracle output;
3. the output relation

([Completeness.lean:23](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Completeness.lean:23)).

`query_correct` proves that the verifier program evaluates like `denote`. It does **not** prove that the honest prover’s concrete output equals or realizes `denote`.

The right remaining obligation is:

```lean
∀ i q,
  OracleInterface.answer (proverOutput i) q =
    Out.answerSem (claim.oracles.denote env) ⟨i, q⟩
```

Literal equality of concrete oracle families should require an additional faithfulness assumption:

```lean
class OracleFamily.Faithful (Out) : Prop where
  eq_of_answers_eq :
    (∀ i q, answer (x i) q = answer (y i) q) → x = y
```

No such assumption exists in `OracleInterface`; it only supplies queries and an answer function ([OracleInterface.lean:49](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/OracleReduction/OracleInterface.lean:49)).

Thus `OutputRealizes` can become a derived lemma, but its **honest-output coherence obligation does not dissolve**.

### RBR and stateful variants

A final `denote` over a full source environment is the wrong primitive for RBR states. At an intermediate prefix:

- future transcript resources do not exist;
- the state relation must be indexed by the current node;
- the extractor may transform a child witness back to a parent witness;
- resource identity must survive replay/restoration.

The catalog requires arbitrary-prefix-indexed state functions ([gpt-literature.md:457](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:457)). The rebuilt oracle layer currently has no RBR security file; only the plain layer does. The virtual-resource design must therefore be prefix-scoped before RBR is added, not retrofitted around final transcripts.

---

## D. Composition laws

### `bind_assoc` will not be definitional

Even the basic simulation composition theorem is propositional and proved by induction over `OracleComp` ([Oracle.lean:44](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Boundary/Oracle.lean:44)).

More importantly, sequential composition introduces new resources. If

```text
v : S → A
w : A + T → B
```

then composition gives

```text
subst v w : S + T → B
```

with denotation

```lean
fun (s, t) => w.denote (v.denote s, t)
```

This is substitution in a monoidal/resource-context category, not ordinary function composition and not ordinary Kleisli bind on the record as proposed.

The current implementation exposes exactly this complexity:

- result types are indexed by `PublicTranscript.split` ([Composition.lean:663](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:663));
- suffix transcript queries are restricted into the combined transcript;
- middle queries are interpreted through the prefix simulator;
- input queries and combined transcript queries are separately routed ([Composition.lean:790](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:790)).

Binary oracle-spec sums also reassociate to different domain types. The code standardizes on left-associated ambient access `(oSpec + input) + acc` ([VerifierAccess.lean:38](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/VerifierAccess.lean:38)). Therefore associativity requires explicit source-context equivalences or a normalized n-ary context representation.

### Public transcript indexing remains a blocker

`PublicTranscript.append` and `split` are mutually inverse only by theorems, not universally by reduction ([Spec.lean:771](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:771)). `liftAppend` computes well on explicitly appended transcripts but needs propositional transport for a general combined transcript ([Spec.lean:825](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Spec.lean:825)).

Threefold composition gives differently nested:

```text
((pt₁, pt₂), pt₃)
(pt₁, (pt₂, pt₃))
```

and output/witness/context families are dependent on those nestings. A `VirtualOracle.bind_assoc` theorem cannot make the containing reductions definitionally equal.

The previous raw-append exploration reached the same conclusion: a `Presentation` layer can expose canonical split structure, but the final transcript-indexed family still requires an explicit equivalence or transport ([raw append note:399](/Users/quangdao/Documents/paper-note/notes/ArkLib-Refactor_raw_append_spec_exploration.md:399)).

### What an honest associativity theorem should say

Not:

```lean
(r₁.comp r₂).comp r₃ = r₁.comp (fun ... => r₂.comp r₃)
```

but approximately:

```lean
Reduction.ExecutionEquivalent
  (reassociateLeft ((r₁.comp r₂).comp r₃))
  (reassociateRight (r₁.comp fun pt₁ => r₂.comp fun pt₂ => r₃))
```

where the equivalence contains:

- an isomorphism of public and full transcript presentations;
- reindexing of statement/oracle/witness families;
- extensional equality of output oracle behavior after source reassociation;
- equality or coupling of execution distributions;
- a provenance-context associator.

An alternative is to make `Chain`, `Telescope`, or a presentation-normalized n-ary composition the canonical associative interface and treat binary `comp` as a convenience view.

### `retargetMonads` cannot be deleted

`retargetMonads` rewrites suffix verifier computations, not merely the final output simulator ([Composition.lean:546](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:546)). The verifier composition invokes it before the final `simulate` field is constructed ([Composition.lean:751](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:751)).

The newer program layer makes this even clearer: `retargetAmbientWithRoute` maps all suffix verifier-local oracle reads through the middle terminal output ([Program.lean:324](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Program.lean:324)). A virtual-oracle projection can replace `midOut.simulate` inside that route, but `mapAmbientOracles` and accumulated-resource routing remain.

---

## E. Protocol stress test

| Protocol family | Query-plan expressibility | What the proposal still needs |
|---|---|---|
| FRI folds | Yes. The current fold trace simulator already routes each output query to either the initial codeword or an earlier sent fold oracle ([FoldPhase.lean:528](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/ProofSystem/FRI/Interaction/FoldPhase.lean:528)). | Total concrete denotation is honest-only when the semantic type is a bounded polynomial/codeword. Fresh sent codewords and virtual folds need distinct origins. |
| STIR/WHIR | Mostly yes: folds, linear combinations, restrictions, and shift views are query plans. | Quotient/OOD semantics need validity predicates; shared batching and compiler-visible dependency graphs are essential. |
| Sumcheck | Yes. The output oracle is currently passed through, while the reduced scalar claim is in `StatementOut` ([General.lean:206](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/ProofSystem/Sumcheck/Interaction/General.lean:206)). | Nothing forces the scalar claim into the oracle denotation; it belongs in `OracleClaim.stmt`. |
| Spartan invoking sumcheck | Yes. The existing boundary builds a virtual sumcheck polynomial from Spartan’s outer oracle family and separately proves materialization coherence ([FirstSumcheck.lean:465](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/ProofSystem/Spartan/FirstSumcheck.lean:465)). | Boundary pullback is resource substitution, not simple `bind`. Preserve the existing total materializer as an optional theorem/compiler witness. |
| Ligero row checks | Yes: row/slice projection and challenge-weighted row combination are multi-source virtual plans. | The plan needs matrix origin, shape metadata, and query/opening cost. |
| Marlin/holographic PIOPs | Not with only “input + transcript” as an untagged source sum. | Setup/indexer/preprocessed oracle origins and setup binding must be explicit. Encoding them as ordinary input slots loses the security distinction. |
| Nova/ProtoStar folding | Partially. Algebraic virtual witness views fit, but much of the output consists of commitments, relaxed R1CS scalars, cross terms, and witness relations. | Fresh commitments and derived virtual resources must coexist. Cryptographic commitment correctness is not an information-theoretic `query_correct` theorem. |
| Shared-challenge batching | Not as sequential `bind` alone. | Needs shared-prefix product, lock-step product, and batched product combinators. A list of sequential invocations duplicates or mis-scopes the challenge. |
| Binius/Lasso-style virtual polynomials | Query behavior is expressible. | Opaque `OracleComp` syntax is insufficient for a compiler unless operations, dependencies, batching compatibility, and cost are recoverable. |

### Where do scalar outputs computed from oracle queries live?

In `OracleClaim.stmt`. The programmatic API already demonstrates the correct pattern: a terminal verifier queries a polynomial at the sampled challenge, stores the resulting scalar in `stmt`, and separately returns an identity simulator for the output oracle ([SingleRoundProgram.lean:83](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/ProofSystem/Sumcheck/Interaction/SingleRoundProgram.lean:83)).

The proposal should state explicitly that `stmt` is produced by a verifier-local computation and may therefore depend on oracle query answers. `VirtualOracle.denote` is not the location for such scalar outputs.

---

## F. The `Respectful`/black-box layer

Two independently authored relation layers will drift. In particular:

- a data relation may inspect representation or proofs invisible through queries;
- an impl relation may accidentally distinguish syntactically different but extensionally equal query programs;
- current `OutputRelation` receives `inputImpl` and `pt`, but no full transcript or hidden-message environment ([Basic.lean:105](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Security/Basic.lean:105)).

Observational equivalence must be relative to an environment:

```lean
def ObsEqAt (env : Src.Env)
    (p q : QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)) : Prop :=
  ∀ h,
    simulateQ (Src.impl env) (p h) =
      simulateQ (Src.impl env) (q h)
```

A meaningful `Respectful` condition is then:

```lean
def Respectful (R : ...) : Prop :=
  ∀ env stmt wit p q,
    ObsEqAt env p q →
      (R env stmt p wit ↔ R env stmt q wit)
```

This cannot be retrofitted onto the current `OutputRelation` signature without adding the source environment or full transcript.

Recommended hierarchy:

1. one canonical output relation over `Out.Sem`;
2. an operational evaluation map from a virtual query plan and source environment to `Out.Sem`;
3. generated impl-facing adapters;
4. optional proof that a legacy handwritten impl predicate equals the generated adapter.

RBR state functions should use prefix-scoped semantic resource handles. Raw implementations should be operational projections, not a second source of semantic truth.

---

## G. Migration risk and effort

### Existing endpoint merge

The proposal’s step (ii) largely already exists in the programmatic layer. `Verifier.TerminalOutput` packages `stmt` and `simulate` ([Program.lean:22](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Program.lean:22)), and `Security/Program.lean` supplies adapters back to legacy split relations.

Therefore the correct target is:

```lean
TerminalOutput.simulate
```

becoming something like:

```lean
TerminalOutput.oracles : VirtualOracle ...
```

with `simulate` retained temporarily as a projection.

### Breakage surface

Changing the legacy core verifier immediately affects:

- [Core.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Core.lean:155)
- [Execution.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Execution.lean:693)
- [Composition.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Composition.lean:605)
- [Program.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Program.lean:28)
- `ProgramExecution`, `ProgramSpec`, and `VerifierAccess`
- [Chain.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Chain.lean:288), where `oStmtResult` and `simulate` are separate inputs
- [Choreo.lean](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Choreo.lean:303)
- FRI, sumcheck, and Spartan construction sites
- all oracle security files
- boundary pullback and reification files
- BCS-facing adapters.

Deleting reification also breaks `Boundary/OracleSecurity.lean` and the working Spartan materialization proofs. Those should be consolidated, not removed until theorem parity exists.

### Single riskiest step

The riskiest step is not mechanical routing. It is changing security semantics from arbitrary behavior to concrete denotation. That can alter theorem statements while leaving Lean goals superficially easier because non-realizable attacks have disappeared.

Before changing `OutputRelation`, require comparison theorems of the form:

```lean
behaviorSecurity → concreteSecurity
```

and, under explicit realizability/faithfulness assumptions,

```lean
concreteSecurity → behaviorSecurity
```

If the reverse direction cannot be proved, the new notion is not a replacement.

### Can step (iii) delete routing?

No. Virtual substitution can simplify the **terminal output** part of composition. Strategy/program-level monad retargeting remains necessary for interactive verifier actions. The programmatic composition code explicitly composes verifier programs with public-path-indexed accumulated access ([Program.lean:446](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/Program.lean:446)).

---

## H. Missing requirements from R1–R35

The main omissions are structural rather than cosmetic.

### Provenance is not a sum-spec position

The catalog requires stable IDs, origin nodes, dependencies, reindexing, visibility, and cost ([gpt-literature.md:332](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:332)). Nested sum positions do not provide these:

- reassociation changes the position;
- two same-typed resources are distinguishable only by fragile injection paths;
- composition flattens away the fact that a resource was derived;
- an opaque query program does not tell the compiler which source commitment should be opened after materialization choices.

The proposed record is **source-scoped**, but not yet provenance-carrying in the literature-catalog sense.

### Fresh and virtual outputs must coexist

FRI/STIR and folding protocols combine newly sent resources with derived views. Origin must distinguish:

```text
input | setup/index | sent-at-node | derived
```

The catalog makes this explicit ([gpt-literature.md:316](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:316)). Treating a freshly sent oracle merely as another leaf of the final source sum loses its binding time and commitment identity.

### State restoration and transcript trees

State restoration must replay the same resource graph and expose query logs and verifier continuations ([gpt-literature.md:487](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:487)). A pure final denotation has no notion of:

- resource allocation identity;
- replay versus fresh allocation;
- logged queries and answers;
- shared prover prefixes;
- resampled challenge continuations.

RBRTE can be implemented later, but the resource identity model cannot safely be postponed until after virtual-oracle composition is frozen.

### Shared-prefix batching

The catalog explicitly separates independent product, shared-prefix product, lock-step repetition, and batched shared challenges ([gpt-literature.md:252](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:252)). `bind` addresses only dependent sequential composition.

### Holographic/setup origins

The current simulator source excludes ambient `oSpec`; it uses only input statement oracles and transcript-message oracles. A holographic index can be encoded as an input oracle, but the resulting type no longer records whether it came from:

- trusted preprocessing;
- a statement-specific indexer;
- public parameters;
- the prover.

That distinction is needed for statement/setup binding and Fiat–Shamir absorption.

### Compiler metadata

BCS compilation needs binding time, commitment scheme, opening compatibility, encoding, domain separation, and an opening plan ([gpt-literature.md:517](/private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md:517)). Current BCS code transforms oracle nodes and public commitments but stops before reduction-output compilation ([BCS.lean:130](/Users/quangdao/Documents/Lean/ArkLib-core-rebuild/ArkLib/Interaction/Oracle/BCS.lean:130)).

A “per-handle inline or materialize” policy also needs:

- an executable materializer, not merely mathematical `denote`;
- construction and commitment cost;
- downstream reuse count;
- batching compatibility;
- proof that materialization and inlining are observationally equivalent.

### Other omissions

The proposal should also acknowledge:

- abort/rejection/malformed/failure distinctions;
- query budgets and adaptivity;
- view-sensitive/ZK semantics;
- exact public serialization and domain separation for Fiat–Shamir;
- interface claims such as degree/domain separately from evaluation behavior.

---

# 3. Concrete amendments

## 3.1 Separate semantic behavior from concrete representation

A schematic design:

```lean
structure SourceCtx where
  ι : Type
  spec : OracleSpec.{0, 0} ι
  Env : Type
  impl : Env → QueryImpl spec Id

structure OracleFamily where
  ι : Type
  Obj : ι → Type
  oracle : ∀ i, OracleInterface (Obj i)

  -- Mathematical semantic carrier, not necessarily concrete Obj data.
  Sem : Type
  answerSem : Sem → QueryImpl [Obj]ₒ Id

structure VirtualOracle (Src : SourceCtx) (Out : OracleFamily) where
  denote : Src.Env → Out.Sem
  query : QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)
  query_correct : ∀ env h,
    simulateQ (Src.impl env) (query h) =
      pure (Out.answerSem (denote env) h)
```

For maximum generality:

```lean
Out.Sem := QueryImpl [Out.Obj]ₒ Id
Out.answerSem := id
```

Structured semantic carriers can be used when totality has genuinely been proved. Degree or proximity remains in the output relation.

## 3.2 Define the actual source environment structurally

For a fixed public transcript:

```lean
def Spec.OracleMessagesAt :
    (s : Spec) → Spec.PublicTranscript s → Type
  | .done, _ => PUnit
  | .public _ rest, ⟨x, pt⟩ =>
      OracleMessagesAt (rest x) pt
  | .oracle X cont, ⟨_, pt⟩ =>
      X × OracleMessagesAt (cont ⟨⟩) pt
```

Then the malicious environment should be approximately:

```lean
InputImpl OStatementIn shared ×
  Spec.OracleMessagesAt (Context shared) pt
```

Its implementation combines the arbitrary input implementation with the message implementation induced structurally by `OracleMessagesAt`.

The honest concrete environment maps into this via:

```lean
OracleStatement OStatementIn →
  InputImpl OStatementIn shared
```

using `simOracle0`.

## 3.3 Keep concrete materialization separate

```lean
structure Materialization
    (v : VirtualOracle Src Out)
    (ConcreteSrc : Type)
    (OutData : Type) where
  forget : ConcreteSrc → Src.Env
  materialize : ConcreteSrc → Option OutData
  answerData : OutData → QueryImpl [Out.Obj]ₒ Id
  correct : ∀ src data,
    materialize src = some data →
      answerData data = Out.answerSem (v.denote (forget src))
```

For compilation, add a stronger executable form:

```lean
structure ExecutableMaterialization extends Materialization ... where
  materializeTotal : ConcreteSrc → OutData
  cost : CostModel
```

Do not use classical choice to fill this record.

## 3.4 State completeness observationally

Replace the proposed concrete equality with:

```lean
def ProverOutputRealizes
    (sem : Out.Sem)
    (data : ∀ i, Out.Obj i) : Prop :=
  ∀ h,
    OracleInterface.answer (data h.1) h.2 =
      Out.answerSem sem h
```

Then:

- `query_correct` connects verifier execution to semantic denotation;
- `ProverOutputRealizes` connects the honest prover’s data to that denotation;
- current `OutputRealizes` follows;
- literal data equality is a separate corollary under faithfulness.

## 3.5 Replace `bind` by resource substitution

The essential operator should have the shape:

```lean
def VirtualOracle.subst
    (v : VirtualOracle S A)
    (w : VirtualOracle (A.tensor T) B) :
    VirtualOracle (S.tensor T) B
```

Its laws are stated up to a source-context equivalence:

```lean
structure SourceEquiv (S T : SourceCtx) where
  envEquiv : S.Env ≃ T.Env
  queryEquiv : ...
  impl_natural : ...
```

Then associativity is:

```lean
subst (subst v w) u ≈
  rebase SourceEquiv.tensorAssoc (subst v (subst w u))
```

This accurately models the suffix transcript resources and makes the required reassociation visible.

## 3.6 Make the canonical security relation semantic

```lean
abbrev OutputRelation :=
  ∀ shared (env : Sources shared pt).Env,
    StatementOut shared pt →
    Out.Sem →
    WitnessOut shared pt →
    Prop
```

The security game evaluates:

```lean
relOut shared env terminal.stmt
  (terminal.oracles.denote env)
  witOut
```

Impl-level predicates should be derived by evaluation. If legacy independent predicates remain, require an explicit equivalence theorem, not only a one-way `Respectful` marker.

## 3.7 Be honest about provenance

Either:

1. rename the first abstraction “source-scoped virtual oracle” and defer provenance/compiler claims; or
2. add a real resource context with stable keys and origins.

At minimum, a compiler-facing extension needs:

```lean
structure ResourceMeta where
  id : ResourceId
  origin : ResourceOrigin
  visibility : Visibility
  bindingPoint : ProtocolPosition
  commitmentPolicy : CommitmentPolicy
  encoding : EncodingMeta

structure CompilableVirtualOracle extends VirtualOracle Src Out where
  dependencies : Finset ResourceId
  plan : TypedPlan Src Out
  erase_plan : plan.erase = query
  cost : PlanCost plan
```

An opaque `query : OracleComp ...` may remain the execution semantics, but it cannot be the only provenance representation if BCS compilation is a stated goal.

---

# 4. Revised migration plan

1. **Specify semantic carriers and source environments first.** Implement `OracleMessagesAt`, its answerer, malicious/honest source environments, and conversion lemmas. Do not touch security definitions yet.

2. **Prototype on `Verifier.TerminalOutput`.** Replace or augment its raw `simulate` with `oracles`, retaining:

   ```lean
   def TerminalOutput.simulate := terminal.oracles.query
   ```

   This exercises the already-packaged programmatic endpoint without destabilizing legacy `Core.Verifier`.

3. **Migrate three vertical slices.**

   - programmatic one-round sumcheck;
   - Spartan first-sumcheck boundary;
   - FRI fold phase.

   These cover scalar outputs from queries, boundary-derived virtual polynomials, multi-stage transcript sources, and passthrough aliases.

4. **Add concrete realization/materialization bridges.** Prove current `OutputRealizes` and programmatic completeness from `query_correct + ProverOutputRealizes`. Preserve existing Spartan materializers.

5. **Implement `tensor`, weakening, rebase, and `subst`.** Use them to simplify terminal simulator routing in `Program` composition. Keep `retargetAmbientWithRoute`, `mapAmbientOracles`, and accumulated-access routing.

6. **Prove security comparison theorems before changing canonical definitions.** In particular, document exactly when data/semantic/behavioral security notions are equivalent and when only one implication holds.

7. **Cut over oracle security to the semantic carrier.** Only after existing completeness, soundness, and knowledge-soundness clients have migrated. Keep query-only extraction as a separately named stronger notion.

8. **Add associativity as equivalence or normalization.** Prefer a Chain/Telescope/Presentation-based n-ary theorem before attempting equality of binary `Reduction.comp`.

9. **Design stable resource provenance before BCS output compilation.** Add setup/index origins, shared resource identities, binding points, materializers, and cost. Only then implement per-handle inline/materialize policy.

10. **Delete legacy duplication last.** Remove reduction/verifier reification duplication and split terminal-output adapters only after boundary security and protocol materialization theorems have replacements.

The old branch is a warning against advancing faster than theorem support: its verifier append compatibility and all major append security theorems remained `sorry` ([Append.lean:187](/Users/quangdao/Documents/Lean/ArkLib/ArkLib/OracleReduction/Composition/Sequential/Append.lean:187), [Append.lean:425](/Users/quangdao/Documents/Lean/ArkLib/ArkLib/OracleReduction/Composition/Sequential/Append.lean:425)). The rebuild should make the semantic comparison and reassociation obligations explicit before declaring composition canonical.

---

# 5. What to cut as overengineering

Cut or defer:

- **Total concrete `Out.Data` from the canonical virtual-oracle record.** This is the central incorrect commitment.
- **The claim that ordinary `bind_assoc`/`bind_id` solves reduction associativity.** Implement resource substitution and equivalence first.
- **A full independent impl-relation hierarchy with generic `Respectful` machinery.** Start with one semantic relation, `ObsEqAt`, and generated adapters.
- **An upfront library of folds, quotients, WHIR constraints, and other smart constructors.** Initially implement identity/selection, tensor weakening, rebase, and substitution. Add algebraic constructors when a protocol uses them.
- **Per-handle compilation policy in the first core migration.** Without stable resource identity, executable materializers, and cost metadata, it is only an aspiration.
- **Immediate deletion of reification.** Consolidate it into an optional materialization layer; do not discard working boundary coherence proofs.
- **Universe polymorphization.** Keep the first design in the current default universe unless a concrete client requires more.

Do not cut:

- packaging `stmt` with the virtual output;
- transcript-indexed output families;
- source scoping;
- separate extensional and intensional equivalence;
- no quotient;
- generic query-plan escape hatch;
- explicit provenance as a later compiler-facing layer.

The sound core is therefore: **a terminal claim packages a public statement and a source-scoped virtual query program, with total semantics into a broad behavior carrier; concrete data, provenance DAGs, and compiler materialization are separate strengthenings.**