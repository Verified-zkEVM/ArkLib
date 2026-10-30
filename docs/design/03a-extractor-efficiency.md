# Extractor efficiency and knowledge soundness

**Implemented measured contracts.** ArkLib states knowledge soundness together with a resource
certificate for the same named extractor. Keep three claims distinct: its probability of
extraction failure, its measured operation counts, and its running time in an explicit
computational model. FRI already supplies the first two. Completing the third requires charging
the computation between its measured instructions, as well as declaring how inputs and witnesses
are represented. The executable Toy IOP extractor needs both resource layers.

This chapter owns the near-term contracts: the unbounded games (E1), the measured-operation
contract (E2), the obligations of each soundness notion that names an extractor, and the FRI/Toy
requirements. The [execution-backend chapter](03b-extractor-execution.md) owns complete
execution bounds (E3, E3a) and uniform families (E7). The
[security chapter](03-adversarial-oracle-execution.md#6-extractors-and-knowledge-composition)
owns extractor access, causality, and knowledge composition. The
[roadmap](05-roadmap.md#extractor-efficiency-repair) owns implementation order and acceptance checks.
The unbounded games (E1) and measured-operation contract (E2) are implemented. Complete execution
bounds (E3) and the execution backend remain proposed.


## Existing guarantees and the repair

[`Verifier.knowledgeSoundnessWith`](../../ArkLib/OracleReduction/Security/Basic.lean)
fixes an extractor before quantifying over arbitrary malicious provers and their arbitrary private
input types. Its bad event is that the output statement-witness pair satisfies `relOut` while the
extractor returns no valid input witness. An extractor's `none` counts as failure. The
existential `knowledgeSoundness` and its typeclass `IsKnowledgeSound` impose no computational
restriction. Naming the extractor preserves the connection to a separate cost proof; it does
not itself prove efficiency.

The `Extractor.Straightline` type permits ambient oracle queries through
`OptionT (OracleComp oSpec)`. Its current description as deterministic and non-querying is
stronger than its type. Document the actual interface and express narrower access as an additional
contract. FRI and the executable Toy extractors use the empty ambient specification; their
retained input words remain separate read-only resources. Straightline access to those words
does not provide rewinding access to the prover.

The academic targets also separate error and time. GMW25 Corollary 5.6 gives deterministic
polynomial-time recovery from a safe FRI prefix with sufficiently many accepting positions,
by interpolation on those positions.
ABF26 Definition A.3 specifies an extraction time in its IOR game, while Definition A.5 specifies
per-round extraction times. Its knowledge-state function may be inefficient. These are distinct
targets: an efficient terminal extractor alone establishes neither round-by-round extraction nor
security of a Fiat–Shamir compilation. See the repository's
[GMW25 provenance](../kb/sources/GMW25/metadata.yml) and
[ABF26 provenance](../kb/sources/ABF26/metadata.yml) for the manuscript versions.

### The precise limitation of unbounded extraction

For any relation, classical choice defines a pure optional selector `chooseWitness x` which
returns a valid witness whenever one exists and `none` otherwise. For this selector the bad
event is exactly

```text
no w satisfies relIn(x, w)  AND  relOut(stmtOut, witOut).
```

Compile this event identity and its game consequence before changing terminology. A resulting
equivalence should first use this relation-aware game, with the actual prover-produced output
witness. The selector turns a bound on that event into unbounded knowledge soundness without
a losslessness premise on arbitrary extractors. The reverse direction requires the extractor's
own execution to be lossless under `impl`, together with the execution/log erasure argument:
otherwise extraction can hide part of the valid-output event by losing mass. The current legacy
interpreter uses `StateT σ ProbComp`; do not silently generalize that argument to a runtime with
missing mass.

An unconditional equivalence with `Verifier.soundness` would be a further, stronger claim.
That definition tests membership in an output *language* and quantifies over arbitrary output
witness types; the knowledge game fixes `WitOut` and tests `relOut` on the witness actually
supplied. An output statement may have a witness that the prover cannot supply at the required
time. A bridge to language soundness must state the relevant witness-supply and execution
assumptions. The trivial output relation of an IOP is an appropriate first specialization.

Keep compatibility declarations during migration. Clarify the existing unbounded contracts and
classical-choice results; expose resource-certified results under explicit new names. Renaming
an executable Toy theorem to ordinary soundness would discard its valid extraction guarantee.
Its missing result is the resource certificate.

## Extraction obligations across soundness notions

Every security notion that names an extractor makes a structural claim and, for an
efficient-extraction claim, a separate cost claim. ArkLib's extractor types are Lean functions or
`OracleComp` computations without a cost bound, so each existential notion below currently states
only its structural claim. The collapse above concerns the terminal straightline game. Each other
notion needs its own statement of what its unbounded form means, with its actual quantifiers.

| Notion | Extractor in ArkLib | Content without a cost bound | Additional obligation for efficient extraction |
|---|---|---|---|
| Terminal knowledge soundness | `Extractor.Straightline` | Relation soundness, by the collapse above | Complete execution of the named extractor in its declared access model |
| Round-by-round knowledge soundness | Legacy `Extractor.RoundByRound`; interaction-layer `RoundExtractor` backward witness maps | The legacy notion coincides with round-by-round soundness of the induced languages when input-witness types are inhabited; interaction-layer certificates retain their local obligations | Execution of each stage on its available prefix, intermediate witness sizes, and their composition |
| Special soundness and CWSS | `Extractor.TreeBased`, from the statement, a transcript tree and its leaf witnesses | Each structured accepting tree with valid leaf witnesses yields an input witness, or exhibits an escape event; with a classical selector, the input statement lies in the language of the input relation | Tree processing; a knowledge corollary also bounds obtaining the tree and producing any escape |
| State-restoration knowledge soundness | Interaction-layer `RoundExtractor` of a `KnowledgeCertificate`, applied backward along the restored path | The bound of `Interaction.Oracle.Security.StateRestoration.stateRestoration_knowledge_soundness` for that named extractor; nothing about its cost | Extraction together with replay and simulation of the restoration oracle; `MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` charges only the stages |

**Round-by-round knowledge soundness.** The legacy existential notion `rbrKnowledgeSoundness`
admits a round-by-round extractor built directly by classical choice, so it carries no efficiency
content. Bare interaction-layer knowledge certificates assert no extraction efficiency;
`Interaction.Oracle.Security.MeasuredKnowledgeCertificate` adds an operation-count budget for each
stage, under the scope limits stated in `KnowledgeResources.lean`. For
inhabited input-witness types, the legacy notion coincides with round-by-round soundness of the
languages of the input and output relations, as proved in
[#1376](https://github.com/Verified-zkEVM/ArkLib/pull/1376). The reverse implication from knowledge
soundness to soundness needs no inhabitation assumption. These results preserve the
prefix quantifiers and terminal semantics; they are distinct from the terminal
relation-soundness equivalence.

`Verifier.forall_rbrSoundness_iff_rbrKnowledgeSoundness_iff` in
`ArkLib/OracleReduction/Security/Implications.lean` characterizes the remaining carrier cases:
the equivalence holds uniformly over
relations and errors exactly when the input-witness type is inhabited or
`StmtIn × FullTranscript pSpec × WitOut` is empty. Otherwise total backward extraction is
impossible, even for rejected transcripts and unrelated output witnesses. This is a constraint of
the extractor type. It is not an additional soundness guarantee. The interaction-layer certificates are not
characterized by these results.

Round-by-round knowledge soundness gains its efficiency content from per-round cost certificates
for named stage extractors, such as those the Toy IOP requires below. ABF26 Definition A.5 bounds
per-round extraction times, while its knowledge-state function may be inefficient.

**Special and coordinate-wise special soundness.** In the published Journal of Cryptology version of
FMN24, Definitions 2.29–2.30 require polynomial-time extraction from a tree, and Lemma 2.31
discusses the resulting knowledge extractor and its expected number of prover executions. The ePrint
version numbers these results differently. ArkLib's CWSS docstrings cite the ePrint numbering, which
has not been rechecked against the published version. Polynomial time in the size of a supplied tree
need not be polynomial in the original instance: the tree's size is the product of its per-round
arities, which is exponential in the number of challenge rounds once every arity is at least two. An
escape disjunct supports a reduction to a computational assumption only together with an efficient
algorithm producing the escape; the event alone is existential. ArkLib has no theorem deriving
knowledge soundness from special soundness or CWSS by tree extraction. That theorem is where the
cost of obtaining the tree must be bounded.

Completing these structural contracts, especially for the interaction-layer knowledge games, precedes the
complete-execution work below; see the roadmap.

## The measured-operation contract

`knowledgeSoundnessWithResources` in `ArkLib/OracleReduction/Security/Resources.lean` packages
the existing game for a named `E` with an explicit instruction program `P`, interpreter `H`,
VCVio `CostModel`, and budget `B`.
Schematically, with an uncharged `view` from the extractor's inputs `x` to the program's view
`v`, its obligations are

```text
knowledgeSoundnessWith(init, impl, relIn, relOut, verifier, E, κ)
(E x).run = simulateQ H (P (view x))                  for every x
WorstCaseCostBound (P v) cm (B params (size v))       for every v.
```

The interpreter targets `OracleComp oSpec`; deterministic handlers can be lifted from `Id`. Allow a
dependent instruction specification when its response types certify the retained input, as FRI's do.
Here `size` describes the charged representation or access contract, not the size of an arbitrary
Lean closure. All representation choices, `view`, the instruction semantics, `cm`, and `B` are
public parameters; `view` is the main uncharged channel. The theorem must name the same `E` as the
game theorem.

The E2 implementation makes three scope choices. They narrow its first instance of this
contract; they do not change the contract.

- **Deterministic handlers.** Handlers have type `QueryImpl (spec v) Id`, and the extractor's run
  is `pure` of their execution. E2 therefore covers extractors that make no ambient `oSpec`
  query, including FRI and the executable Toy extractors. A handler into `OracleComp oSpec` could
  make ambient queries that no instruction charge accounts for. Supporting querying extractors
  needs a bound on those queries after the actual interpreter; it waits for a client.
- **One budget per parameter set.** The budget is a single value that bounds every view at the
  given parameters, which suffices for FRI's `extractorProfileBound`. A per-view budget
  `B params (size v)` remains valid in principle when `B` and `size` are specified independently
  of the program. E2 omits it because its instance needs no size convention, and because a budget
  that may be any function of the view could be defined as the program's own cost on that view.
- **Deferred equality transport.** E2 provides budget monotonicity, but not transport of a
  certificate along a proved program equality. The first step that proves such an equality adds
  the transport for its own use.

The instruction charges are a field of the named measured program rather than a separate
argument, and remain public through it.

Use VCVio's existing `WorstCaseCostBound` or `AddWriterT.PathwiseCostAtMost` after the actual
interpreter. Prefer the former when the structural instruction specification captures all allowed
responses; use the latter when an interpreted environment is essential, with an explicit bridge.
Do not introduce a third cost-bound predicate. An adapter from FRI's deterministic `profile`
should prove equality to the chosen VCVio instrumentation before transporting its bounds.

Retain finite coordinate vectors such as FRI's `CostKind → ℕ`; `CostModel` already supports
them. `ResourceProfile ℕ Capability` is useful when separating intrinsic work from calls to
external capabilities. It need not replace every existing vector. If capabilities are substituted,
use `ResourceProfile.instantiate` and prove the bound for the actual handler programs. Its
algebraic substitution identity alone does not price a handler or establish its semantics.

This contract certifies selected operations, not polynomial time. In particular, VCVio proves
that `pure (f input)` has zero query cost, independently of the computation of `f`. Positive
query charges cannot fix that omission. The contract must say which ordinary computation and
input acquisition costs its profile excludes.

This is the public result for FRI in
`ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean`, independent of the execution
backend. Its label is knowledge soundness for the named extractor with concrete operation-count
bounds, with the profile's exclusions stated beside the claim. It does not need to wait for the
realization or family-level results.

## Complete execution

**Required later.** An unqualified efficient-extraction claim needs a bound on the extractor's
complete execution in a declared model, including the computation between measured instructions.
The measured contract does not supply it. This work (E3) follows the interaction-layer soundness contracts
and their composition, so that terminal, per-round, tree-based and composed extractors share one
interface. No probability theorem waits for it; results proved meanwhile keep their
operation-count label. E3a's algebraic backend in PolyFun is the proposed route. Another execution
model with a reviewed adequacy argument can replace it. A reviewed adequacy argument is distinct
from a proved correspondence to a standard machine, which neither route supplies initially. The
[execution-backend chapter](03b-extractor-execution.md) states the proposed
`knowledgeSoundnessWithin`, the backend requirements, and the uniform-family corollaries.

## API placement and erasure

State the measured program independently of any game: a view of an arbitrary extractor input, a
charged instruction program with its result type, deterministic handlers, and charges. Each game
then states its resource conjunction for its own extractor shape. Design those conjunctions against
the interaction-layer knowledge games first, where new security development takes place; the legacy
straightline game, which FRI's result uses, is an adapter. The generic measured program lives in
`ArkLib/Data/OracleComp/MeasuredProgram.lean`, which imports no game. The legacy game conjunctions
and their erasure lemmas live in `ArkLib/OracleReduction/Security/Resources.lean`. The FRI
certificate lives in `ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean`; the Toy decoding
certificate remains proposed. Interaction-layer games consume the same measured programs through
their own adapter: `ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean` defines
`RoundExtractor.MeasuredStages` and `MeasuredKnowledgeCertificate`, and
`StateRestorationResources.lean` pairs the state-restoration bound with a stage budget, without the
legacy execution machinery.
Reusable arithmetic remains under `ArkLib/ToCompPoly/Univariate/`; generic instrumentation and
realization laws belong in VCVio/PolyFun.

The measured contract retains `E`, `view`, `P`, `H`, `cm` and `B` as parameters. The realized
contract of the execution-backend chapter additionally retains `Q`, `bd`, the response contract and
`T`. Its evidence contains the actual implementing code/realization and its semantic and run-bound
proofs. Operational code must be executable; a proof using classical reasoning is compatible with
that requirement, while using classical choice to manufacture the running witness values is not an
implementation.

The measured contract provides the forgetful implications to the unbounded games. The proposed
execution contract adds the first implication:

```text
knowledgeSoundnessWithin
  → knowledgeSoundnessWithResources
  → knowledgeSoundnessWith
  → knowledgeSoundness.
```

Also provide budget monotonicity, and transport along proved program equality once a step needs
it; E2 defers the transport, as recorded under the measured contract. There is no reverse
implication from a measured profile to realized time. A family certificate supplies its own shared
polynomial; it cannot imply an arbitrarily chosen concrete budget. The public FRI/Toy theorems
should show both their concrete budget and the exact extractor, rather than exposing only an
existential resource-certified corollary.

## FRI integration

Preserve [`knowledge_soundness_with`](../../ArkLib/ProofSystem/Fri/Spec/KnowledgeSoundness.lean)
and its named `Extractor.extract`. The
[program](../../ArkLib/ProofSystem/Fri/Spec/Extraction/Program.lean) already defines
`extractHistory` as the result projection of its measured execution. Its
[full profile](../../ArkLib/ProofSystem/Fri/Spec/Extraction/FullCost.lean) and
[field-operation envelopes](../../ArkLib/ProofSystem/Fri/Spec/Extraction/ClosedCost.lean)
apply to every retained history, including early rejection.
`ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean` packages these theorems without
changing the extraction algorithm or its soundness error.

Write `N = 2^n`, `r = k+1`, `b_i = 2^(s_i)`, and `D = (∏ b_i)d`. Existing bounds include

```text
word reads ≤ N (Σ_i b_i + k) + D
inversions ≤ 1 + N Σ_i b_i(b_i − 1) + D(D − 1)
add/sub, mul, eq ≤ fieldBudget n s d                  each listed category.
```

Other coordinates, including explicit metadata ticks and local coefficient/cache accesses, have
their existing `extractorProfileBound`. This is not a full machine-operation count. Domain and
word handlers are arbitrary retained functions; one measured read does not bound their evaluation.
The [FRI audit](../kb/audits/fri-soundness.md#certified-extraction) records the exclusions.

## Toy IOP integration

Use the executable interleaved-RS
[`transitionExtractor` and `straightlineExtractor`](../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean).
The classical choice extractor remains a proof-side result with no efficient-extraction claim.
Preserve the executable theorem's existing `certifiedExtractorError` and the exact post-challenge
agreement-set construction.

Let `N = Fintype.card ι`, interleaving width be `s`, and scalar row dimension be `L = k/s`.
The algorithm computes the maximal agreement set for the combined message `g`, then decodes
both input words, each with `s` scalar rows. The
[current scalar decoder](../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean)
interpolates over the retained node set and performs a re-encoding check. Its cost depends on the
number of retained nodes, up to `N`, not just `L`.

Build a measured decoder using the reusable arithmetic/interpolation layer currently consumed by
FRI. Move generic reusable components into their owning arithmetic layer, keeping FRI-specific
access operations local. Prove output equality on every input, including insufficient-node and
failed re-encoding cases. Replacing interpolation on all retained nodes by interpolation on the
first `L` nodes is a separate optimization; equality on good histories alone does not preserve
the exact extractor theorem on arbitrary inputs.

The executable outputs are Lean functions over finite indices. In particular, row decoding may be
delayed until a returned function is applied. A cost certificate must materialize the finite
witness tables, or charge each subsequent evaluation under an explicit functional-output
contract. Use eager finite tables for the first certificate, with a proved projection to the
existing witness. Merely returning a closure cannot discharge the cost of producing its values.
Likewise, supply an explicit enumeration/index representation for `ι`; `Fintype` and an arbitrary
domain embedding alone provide no runtime bound.

Separate budgets for agreement-set scanning, scalar interpolation, re-encoding, input access,
and assembling the two witnesses. A suitable proof target is a concrete sum of one agreement
budget and `2s` scalar-decoder budgets with node count at most `N`, plus materialization overhead.
Cubic interpolation and the existing power-sum evaluation give a conservative polynomial target;
derive its actual constants and degree from the measured implementation. Do not assert the paper's
`O(enc_C + ecor_C)` performance for a different decoder without matching its cost conventions.

For the round-by-round theorem, certify each invoked stage and its own available prefix. Retain the
existing knowledge-state function as proof-side data. These per-round certificates give the Toy
IOP's round-by-round knowledge soundness its efficiency content; the existential form alone has no
efficiency content. The terminal certificate and the per-round certificates must identify their
respective public extractors; one does not imply the other without a timing and composition proof.

## Completion criteria and design review

The repair is complete for a protocol only when its public result names the extractor, bounds
its game error, carries the resource certificate for that same computation, and identifies the
representation and computational model. A result carrying only operation profiles must retain
that description. An algebraic execution result may be published before a bit-machine refinement,
provided its primitive assumptions are explicit.
Its adequacy review is not a theorem connecting it to a standard machine; keep that boundary
visible when describing the result.

Review the implementation against counterexamples that expose weak contracts:

- `pure (chooseWitness x)` has zero instruction cost; it gains no realization certificate merely
  from that fact. A genuinely efficient selector can still be certified by actual code.
- A charged query followed by expensive pure computation is not bounded by the query count alone.
- A positive vector charge has zero entries in other coordinates; admissibility uses the intended
  scalar valuation or a full execution-domination theorem, not coordinatewise positivity.
- An unavailable query with no completed run does not establish termination or valid access.
- `none`, timeout, and modeled extraction faults after acceptance count as extraction failure.
- Arbitrarily slow word/domain functions cannot inherit unit-time concrete implementations.
- A returned function whose body performs decoding does not constitute a materialized witness.
- Distinct per-size machines or free code generation do not establish a uniform family theorem.
- Replacing a budget or backend changes the contract; costs cannot be erased while retaining the
  same efficiency claim. Cost erasure may yield only the existing unbounded game theorem.

For composition, add costs or substitute capability budgets only after proving semantic
correspondence, input/output-size bounds and witness availability at the actual boundary. Charge
view conversion, copying and output construction. Reuse the persistent world rather than resetting
it. The existing causal restrictions on knowledge composition continue to apply even when the
individual extractors have resource certificates.
