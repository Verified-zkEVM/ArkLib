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
execution bounds (E3, E3a) and security-parameter families (E7). The
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

The `Extractor.Straightline` type permits ambient oracle queries and `none` through `OptionT
(OracleComp oSpec)`. It runs once after the execution without rewinding the prover; narrower oracle
access is an additional contract. FRI and the executable Toy extractors use the empty ambient
specification; their retained input words remain separate read-only resources. Straightline access
to those words
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

[`Verifier.knowledgeSoundness_iff_relationSoundness`](../../ArkLib/OracleReduction/Security/UnboundedExtraction.lean)
already proves the exact equivalence with `Verifier.relationSoundness` for the current game,
which retains the fixed output-witness type and the actual prover-supplied witness. The classical
selector establishes one direction. The current `StateT σ ProbComp` interpreter is lossless,
so the reverse direction needs no additional theorem premise. An interpreter with missing
probability mass would need the corresponding losslessness condition: otherwise extraction could
hide part of the valid-output event by losing mass.

This relation-aware equivalence does not identify the contract with `Verifier.soundness`.
That definition tests membership in an output *language* and quantifies over arbitrary output
witness types; the knowledge game fixes `WitOut` and tests `relOut` on the witness actually
supplied. `Verifier.relationSoundness_of_soundness` gives the language-to-relation implication.
A converse needs the relevant witness-supply and execution assumptions: an output statement may
have a witness that the prover cannot supply at the required time. The trivial output relation of
an IOP is an appropriate first specialization.

`knowledgeSoundnessWith` retains the extractor's identity in the probability statement.
`knowledgeSoundnessWithResources` additionally names its measured program and instruction budget.
The executable Toy extraction theorem identifies its algorithm but has no operation-count or
complete-execution certificate.

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
| State-restoration knowledge soundness | Interaction-layer `RoundExtractor` of a `KnowledgeCertificate`, applied backward along the restored path | The bound of `Interaction.Oracle.Security.StateRestoration.stateRestoration_knowledge_soundness` for that named extractor; nothing about its cost | Extraction together with replay and simulation of the restoration oracle; the measured wrapper adds declared stage accounting, not a replay or running-time bound |

**Round-by-round knowledge soundness.** The legacy existential notion `rbrKnowledgeSoundness`
admits a round-by-round extractor built directly by classical choice, so it carries no efficiency
content. Bare interaction-layer knowledge certificates assert no extraction efficiency;
`Interaction.Oracle.Security.MeasuredKnowledgeCertificate` adds an operation-count budget for each
stage, under the scope limits stated in `KnowledgeResources.lean`.
`MeasuredStages.programAlong` composes these named programs on a typed execution path.
`programAlong_budget_le` bounds their sum by `path.length • bound` under `BudgetAtMost bound`;
a per-stage bound alone supplies no uniform total on an unbounded-depth tree. For
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
the total extractor type. Unlike the optional terminal extractor, it must return an earlier
witness even on rejected or irrelevant data. ABF26 uses a single inhabited witness carrier, so this
empty-carrier obstruction is an artifact of ArkLib's more general carrier types, not a failure of
the paper's soundness notion. An option-valued legacy round extractor is a possible redesign, not
an implemented fix. The interaction-layer certificates are not characterized by these results.

Per-round measured programs supply declared operation counts for named stage extractors. They
supply extraction-time evidence only after the E3 execution and uniformity obligations are proved.
ABF26 Definition A.5 bounds per-round extraction times, while its knowledge-state function may be
inefficient. The terminal `Proof.knowledgeSoundness`/`Proof.soundness` specialization of the
unbounded characterization is a separate follow-up; no equivalence for it is claimed here.

**Special and coordinate-wise special soundness.** In the checked ePrint 2023/846 of FMN24,
Definitions 2.29–2.30 require polynomial-time extraction from a tree, and Lemma 2.31 discusses the
knowledge extractor and its expected number of prover executions. The combinatorial family occurs in
§2.9 before Definition 2.29; the journal citation is publication metadata. For source context, see
[FMN24](../kb/papers/FMN24.md) and the
[zero-check audit](../kb/audits/noz26-zero-check-lemma10.md). Polynomial time in the
size of a supplied tree
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
the existing game for a named `E` with a named `MeasuredProgram` `P` and budget `B : Kind → ℕ`.
The program contains its view, instructions, deterministic handlers and charges; these are not
separate arguments to the security contract. Public count contracts require `[Finite Kind]`.
For an uncharged `view` from the extractor's inputs `x` to the program's view `v`, the current
obligations are schematically

```text
knowledgeSoundnessWith(init, impl, relIn, relOut, verifier, E, κ)
(E x).run = pure (P.run x)                    for every x
P.CostAtMost B                   (all views, all permitted response paths).
```

`P.run` constructs `P.view x` and uses deterministic `Id` handlers. The legacy contract takes
one budget at fixed parameters, uniformly over its views; a representation-size-dependent budget
is not part of that API. The native state-restoration wrapper instead allows a family
`messageBound challengeBound : Input → Kind → ℕ`. Those state separate bounds for each
statement and role, with no growth-rate
or uniform implementation claim. A dependent specification can certify responses, as FRI's does.
Representation choices, the view, handlers,
charges and budget remain inspectable through the named program. Its output equality connects it
to the same `E` as the game theorem; it is not a backend execution-cost bound or a uniform-code
proof.

The legacy measured contract has the following API scope:

- **Deterministic handlers.** Handlers have type `QueryImpl (spec v) Id`.
  `RealizesExtractor` identifies the extractor's monadic run with `pure` of the measured result;
  ambient `oSpec` queries are outside this contract.
- **Uniform budget.** One budget bounds every view at fixed protocol parameters. The legacy
  contract takes neither an input-size function nor a per-view budget.
- **Certificate operations.** `Verifier.knowledgeSoundnessWithResources.mono` raises the budget.
  The resource API has no dedicated certificate-transport theorem for proved program equalities.

Public operation-count security contracts require `[Finite Kind]` and fix `Kind → ℕ` with
pointwise ordinary addition and order. They bound each coordinate; a scalar total or price is a
separate derived step. Scalar counts can use `Unit → ℕ`. Empty `Kind` records no resources, and
zero charges still record no work. Generic measured stages and VCVio's weighted algebra allow
other additive valuations, including signed, maximum or saturating models; those are not raw
operation counts.

Pricing retains the raw count profile. Finite kinds allow finite sums; more general weighted APIs
need finite support or a proved summability argument. Transporting additive bounds needs
a justified monotone additive valuation, or an explicitly proved alternative bound. A maximum or
saturation may be a useful derived statistic, with that interpretation stated. Neither natural
counts nor positivity proves accounting adequacy: zero charges, free views and omitted pure work
remain possible.

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

### Proof and accounting boundary

This is the authoritative accounting boundary for the current E2 certificates. Each named
program's bound covers **all views and all completed instruction paths permitted by its
specification**, not just views reached in a successful game or the chosen handler's path.
Only declared instruction charges are counted. The **common E2 exclusions** are:

- constructing and evaluating input views, and evaluating handlers beyond their declared charges;
- uninstrumented pure Lean computation, including control flow, allocation, copying, storage and
  index/address arithmetic between charged instructions;
- representation, input-decoding and field bit costs beyond the declared interface charges.

Knowledge and relation predicates are logical security specifications. The count certificates
also give no bound on constructing, evaluating or deciding them. A complete execution certificate
must charge such work when its actual algorithm performs it; it need not decide a predicate
merely because the security game mentions it.

| Certificate | Proven connection and bound | Additional exclusions beyond the common E2 boundary |
|---|---|---|
| Legacy `knowledgeSoundnessWithResources`, instantiated by FRI | The named game extractor equals the deterministic measured run, with its finite natural-vector budget | Retained-history/challenge reconstruction from the statement/transcript, and other input preparation performed in the view |
| Native measured stages and `programAlong` | Each selected stage map is realized; backward path composition returns `extractWitness` and sums the stage budgets | Choosing or constructing programs from prefixes or paths, intermediate witness sizes, carrier conversions, acquiring the path and replay |
| Native state-restoration resource theorem | The original probability theorem, all-witness game-return identity and role-specific count stated below | The native stage exclusions, statement-family code generation and restoration-oracle replay/simulation |

These are selected-operation certificates, not polynomial-time bounds. In particular,
`pure (f input)` has zero query cost independently of the computation of `f`; positive query
charges do not account for that work. E3 instead requires the complete execution/access/termination
contract in the [execution chapter](03b-extractor-execution.md#the-complete-execution-contract).
It accounts for all implementing work in that model's declared units. Bit-machine and physical
claims still require evidence at those layers.

FRI's theorem in `ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean` combines the named
extractor's knowledge game with concrete operation counts under the boundary above. This result
is independent of the proposed execution backend and family-level claims.

### State-restoration resource contract

`MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` in
`Interaction/Oracle/Security/StateRestorationResources.lean` keeps the original game and extractor.
For each allowed statement `z` and every supplied completed path, it also proves:

- for **every** terminal witness, running the composed program on its `terminalWitness`-converted
  input returns exactly the game's `extractInputWitness`;
- the composed program satisfies `CostAtMost (r • (messageBound z + challengeBound z))`, where
  `r = rounds.length`. This covers every view and permitted instruction path of that program.

`MeasuredStages.ProtocolBudgetAtMost` supplies separate message/challenge bounds uniformly over
the prefixes at fixed `z`. `run_programAlong_terminalWitness` is the return-identity bridge.
`length_executionPath_protocol` proves two nodes per round; the helper with one common stage
bound remains available. The two-round acceptance fixture obtains its tight count two from one
charged message stage and one zero-charge challenge stage per round. `_nonuniform` refers to the
round-error schedule. Statement-indexed bounds assert neither a growth rate nor one uniform
executable implementation.

Native contracts and path composition are implemented on `main` and validated by
acceptance fixtures; no production protocol yet instantiates the native measured certificate.
The [native composition priorities](05-roadmap.md#native-resource-composition) own the remaining
client and resource-closure obligations.

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
`knowledgeSoundnessWithin`, the backend requirements, and the security-parameter family corollaries.

## API placement and erasure

A measured program is independent of any game: it contains an input view, a charged instruction
program, deterministic handlers, and charges. Each security layer supplies its resource contract
for that layer's extractor shape. The generic core lives in
`VCVio.OracleComp.QueryTracking.MeasuredProgram`, which imports no game. The legacy game conjunctions
and their erasure lemmas live in `ArkLib/OracleReduction/Security/Resources.lean`. The FRI
certificate lives in `ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean`; the Toy decoding
certificate remains proposed. Interaction-layer games consume the same measured programs through
their own adapter: `ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean` defines
`RoundExtractor.MeasuredStages` and `MeasuredKnowledgeCertificate`, and
`StateRestorationResources.lean` supplies the
[state-restoration resource contract](#state-restoration-resource-contract). Native path
composition lives in
[`KnowledgeResources/Composition.lean`](../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean):
`MeasuredStages.programAlong` returns a budgeted program for the same `extractWitness` on each
typed path and terminal witness. Its accounting boundary and the role/depth bounds are stated
above, rather than being additional execution-time guarantees.

CompPoly owns polynomial algorithms and their generic semantic and size facts. VCVio owns generic
cost instrumentation, measured programs and their composition. ArkLib currently hosts arithmetic
instrumentation adapters under `ArkLib/ToCompPoly/Univariate/` and owns the protocol-specific
extraction/game connections. Extract shared cross-library adapters into an appropriate owner when
a demonstrated API need calls for them; their current location is not a permanent ownership rule.
The deeper execution backend proposed for PolyFun remains later work; these operation profiles
do not establish its adequacy or a full running-time bound.

The measured security contract retains `E`, the named `MeasuredProgram` `P`, and `B` as parameters.
The view, handlers and charges remain public fields of `P`. The realized
contract of the execution-backend chapter additionally retains `Q`, `bd`, the response contract and
`T`. Its evidence contains the actual implementing code/realization and its semantic and run-bound
proofs. Operational code must be executable; a proof using classical reasoning is compatible with
that requirement, while using classical choice to manufacture the running witness values is not an
implementation.

For the terminal straightline game, the implemented count contract erases to
`knowledgeSoundnessWith`, then to existential `knowledgeSoundness`. A proposed complete-execution
certificate also erases to its named game:

```text
knowledgeSoundnessWithin → knowledgeSoundnessWith → knowledgeSoundness
knowledgeSoundnessWithResources → knowledgeSoundnessWith → knowledgeSoundness.
```

Deriving `knowledgeSoundnessWithResources` from a complete-execution result additionally needs its
own E2 evidence for the same named program: `RealizesExtractor`, the deterministic/no-ambient-query
scope, and the required natural-vector count bound. Supply that certificate independently or prove a
bridge that actually yields those obligations. A forward code-cost simulation or bit bound alone
need not bound field-operation counts. The native and round-by-round games retain their own erasure
lemmas; this diagram is not their terminal characterization.

There is no reverse implication from a measured profile to realized time. A proposed family
certificate supplies its own shared polynomial; it does not imply an arbitrarily chosen concrete
budget. FRI's current resource theorem names its extractor and concrete operation-count budget.
The corresponding Toy resource certificates remain proposed.

### Polynomial algorithm accounting

Cost certificates identify the implemented algorithm as well as its result. CompPoly's raw
`eval`/`eval₂` specifications use a power sum, but their `@[csimp]` equations in
`CompPoly.Univariate.Raw.Proofs`
and the canonical equations in
`CompPoly.Univariate.Basic`
dispatch compiled evaluation to the Horner `Array.foldr` in
`CompPoly.Univariate.Raw.Ops`.
ArkLib's measured [`Arithmetic.evalRaw`](../../ArkLib/ToCompPoly/Univariate/ArithmeticEvaluation.lean)
uses repeated [`Arithmetic.power`](../../ArkLib/ToCompPoly/Univariate/Arithmetic.lean) instead.
FRI's `Extraction/Check.lean` invokes this charged evaluator, and `extractHistory` is the result
projection of its measured `extractProgram`. No compiler rewrite has been shown to replace that
instruction program with Horner. Its profile therefore certifies that power-sum algorithm. Ordinary
compiled CompPoly evaluation follows the separate Horner dispatch; equality of values does not
transfer either cost profile. Compiled fixtures exercise outputs and recorded counters, not a
proved bound on host runtime.

Likewise, `Raw.trim` in `CompPoly.Univariate.Raw.Core` uses `lastNonzero` (`findIdxRev?`) followed
by a prefix `extract`. The measured
[`Arithmetic.trimRaw`](../../ArkLib/ToCompPoly/Univariate/ArithmeticPolynomial.lean) recursively
reads, tests and pops trailing coefficients; its [profile
bounds](../../ArkLib/ToCompPoly/Univariate/ArithmeticPolynomialCost.lean) certify that program.
Output equality leaves copying, allocation, indexing and control costs unpriced. These audits
concern the named definitions, with no whole-library machine-time or performance claim.

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
their existing `extractorProfileBound`. This is not a full machine-operation count. The [scope table](#proof-and-accounting-boundary)
applies; in particular arbitrary retained domain/word functions need their own implementation
costs. The [FRI audit](../kb/audits/fri-soundness.md#extraction-correctness-and-operation-profile)
specializes this boundary.

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

The Toy round-by-round extractor is currently the legacy `Extractor.RoundByRound`, whereas
`MeasuredStages.programAlong` consumes interaction-layer `RoundExtractor` maps. Before using that
composition theorem, add a legacy stage-resource contract or port the Toy client to the native
layer with a proved correspondence of the games and extractors. Neither prerequisite is supplied
by the generic measured-program core.

Then certify each invoked stage on its actual available prefix and retain the knowledge-state
function as proof-side data. These certificates give per-round operation counts; extraction time
additionally needs E3, including a uniform program taking the prefix as data. The terminal and
per-round certificates must identify their respective public extractors; one does not imply the
other without a timing and composition proof.

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
- An unrelated lookup-table machine cannot inherit an E2 profile merely from output equality;
  bound the actual named backend code, including its encoded code and data.
- Free per-statement code or prefix-selected programs do not establish a uniform extractor.
- Distinct per-size machines, free embedded tables or code generation do not establish E3.
- A stage budget of one permits arbitrarily large composed cost without a path-depth bound.
- Signed cancellation or a reversed order can bound a weight without bounding operation counts.
- Replacing a budget or backend changes the contract; costs cannot be erased while retaining the
  same efficiency claim. Cost erasure may yield only the existing unbounded game theorem.

Current E2 composition sums declared instruction costs and proves the extractor's output
identity within that declared count model. Its [accounting boundary](#proof-and-accounting-boundary) leaves outer views, prefix-selected
programs and carrier conversions uncharged. To obtain E3 composition, also prove
semantic agreement and execution costs for the named code, program-family uniformity,
intermediate representation sizes and witness availability, charging conversion, copying and
output construction. These are E3 obligations, not additional premises of the existing E2 count
composition theorem. The [native composition priorities](05-roadmap.md#native-resource-composition)
record the further resource-closure work; per-path composition alone does not prove it.
Persistent-world and causal restrictions on knowledge composition still apply.
The [execution chapter](03b-extractor-execution.md#expected-time-rewinding-and-tree-acquisition)
separates expected-time/rewinding composition from these pathwise additive bounds.
