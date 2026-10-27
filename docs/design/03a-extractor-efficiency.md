# Extractor efficiency and knowledge soundness

**Proposed contracts.** ArkLib should state knowledge soundness together with a resource
certificate for the same named extractor. Keep three claims distinct: its probability of
extraction failure, its measured operation counts, and its running time in an explicit
computational model. FRI already supplies the first two. Completing the third requires charging
the computation between its measured instructions, as well as declaring how inputs and witnesses
are represented. The executable Toy IOP extractor needs both resource layers.

This chapter owns the efficiency contracts and the FRI/Toy requirements. The
[security chapter](03-adversarial-oracle-execution.md#6-extractors-and-knowledge-composition)
owns extractor access, causality, and knowledge composition. The
[roadmap](05-roadmap.md#extractor-efficiency-repair) owns implementation order and acceptance checks.
All new API names and theorem signatures below are proposals, not implemented declarations.

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

## Two resource contracts

### Measured operations

The proposed `knowledgeSoundnessWithResources` packages the existing game for a named `E` with
an explicit instruction program `P`, interpreter `H`, VCVio `CostModel`, and budget `B`.
Schematically, for a packaged extractor view `v`, its obligations are

```text
knowledgeSoundnessWith(init, impl, relIn, relOut, verifier, E, κ)
simulateQ H (P v) = (E v).run
WorstCaseCostBound (P v) cm (B params (size v))       for every v.
```

The interpreter targets `OracleComp oSpec`; deterministic handlers can be lifted from `Id`.
Allow a dependent instruction specification when its response types certify the retained input,
as FRI's do. Here `size` describes the charged representation or access contract, not the
size of an arbitrary Lean closure. All representation choices, the instruction semantics,
`cm`, and `B` are public parameters. The theorem must name the same `E` as the game theorem.

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

This is the near-term public result for FRI and should ship independently of the execution
backend. Its label is knowledge soundness for the named extractor with concrete operation-count
bounds, with the profile's exclusions stated beside the claim. It does not need to wait for the
realization or family-level results.

### Realized execution

The proposed `knowledgeSoundnessWithin` additionally requires a quantitative realization of the
same extractor program, a fixed representation boundary, and a concrete run bound. PolyFun/VCVio
supplies the quantitative interface, but an algebraic execution backend still needs to be built.
The concrete cslib backend uses a single-tape Turing machine over Boolean-string encodings;
the generic word-class adapter does not supply field-operation code or semantics.

E3a therefore builds a generic algebraic code type with execution and cost semantics, connected
to the existing quantitative layer. A deep embedding is appropriate for that backend: it makes
the operations between oracle queries visible to the cost semantics. Avoid a protocol-specific
language or a duplicate realizability framework. Gate the backend on realizing one actual FRI
fold-consistency check, proving its output agreement and its execution bound before generalizing.
Put the backend in PolyFun, with the crypto-facing adapter in VCVio as needed. If upstream work
cannot land promptly, a temporary `ArkLib/ToCompPoly` implementation must name its upstream owner
and removal condition; keep FRI-specific operations outside the generic language.

The certificate must account for the realized initialization, control decisions, enabled state
updates, input access and output construction. No unrestricted Lean function may act as a
unit-time instruction. Primitive field operations and read-only oracle access may remain abstract
capabilities, but their types, representations, charges, and implementation obligations are fixed
by the stated model. Proofs and subtype certificates are erased; producing the underlying
coefficient values and finite output tables is charged.

Take the backend `Q`, boundary `bd`, response contract, input-size convention, and budget `T` as
explicit arguments. Existentially choosing an implementing machine or a polynomial is legitimate
after these are fixed. Existentially choosing an arbitrary size convention or a backend that makes
every function primitive is not evidence for an unqualified efficiency claim. Require a separate
statement of what the backend's adequacy review covers and keep its status visible in the
exported theorem's documentation. A standard-machine claim additionally requires a proved
correspondence to that machine; the initial algebraic result does not supply one.

For the initial algebraic model, the formal obligations are correctness of the code's semantics,
its quantitative-layer connection, and the bounds for all modeled execution, including pure-code
initialization, control, updates and storage. Its adequacy acceptance check is a review of the
primitive basis, representations and charges, not a proved simulation of a standard machine.
This review must explain why each primitive is an appropriate algebraic operation, what index
and storage work it covers, and which costs remain abstract. E3's gain over E2 is formal coverage
of pure computation through this declared backend; it is not a bit- or machine-runtime guarantee.

Every modeled operation must be covered, either directly or by a proved amortized charge.
Requiring every coordinate or syntactic construct to have positive cost is unnecessary:
a zero coordinate for an unused resource, or administrative syntax with proved
zero overhead, can be legitimate. What matters is domination of computational work by the
declared resource measure.

Use a fixed first-order primitive basis: field arithmetic/equality, bounded index and address
operations, and explicit storage/control operations. An opcode accepting an arbitrary host
function would reopen the gap. State index widths or charge their growing bit lengths, and
separate read-only input storage from allocated working storage. The E3a code type and its
quantitative adapter must enforce these restrictions; a cost annotation on an arbitrary host
function is insufficient.

Use a worst-case bound on all permitted inputs and responses, including rejected histories.
A bound over successful outputs alone is insufficient if execution can diverge or fault.
Use the upstream finite-prefix/run-bound machinery and prove termination and valid access for
this deterministic client. Never infer these from a complete-path support bound whose support
could be empty. The probability game must count a timed-out or failed extraction as failure
after acceptance; it must not delete the accepted run from the experiment.

### API placement and erasure

Put the legacy game conjunctions and their erasure lemmas in a proposed
`ArkLib/OracleReduction/Security/Resources.lean`. Protocol-specific certificates stay with FRI
extraction and Toy decoding. Native interaction games should consume the same upstream resource
evidence through their own game adapter, rather than inheriting the legacy execution machinery.
Reusable arithmetic remains under `ArkLib/ToCompPoly/Univariate/`; generic instrumentation and
realization laws belong in VCVio/PolyFun.

The measured contract retains `E`, `P`, `H`, `cm` and `B` as parameters. The realized contract
additionally retains `Q`, `bd`, the response contract and `T`. Its evidence contains the actual
implementing code/realization and its semantic and run-bound proofs. Operational code must be
executable; a proof using classical reasoning is compatible with that requirement, while using
classical choice to manufacture the running witness values is not an implementation.

Provide explicit forgetful implications:

```text
knowledgeSoundnessWithin
  → knowledgeSoundnessWithResources
  → knowledgeSoundnessWith
  → knowledgeSoundness.
```

Also provide budget monotonicity and transport along proved program equality. There is no reverse
implication from a measured profile to realized time. A family certificate supplies its own shared
polynomial; it cannot imply an arbitrarily chosen concrete budget. The public FRI/Toy theorems
should show both their concrete budget and the exact extractor, rather than exposing only an
existential resource-certified corollary.

## Computational models and the role of Caliper

| Layer | What the theorem certifies | Required additional evidence |
|---|---|---|
| Instruction profile | Counts of specified arithmetic and input operations | Identity with the game's extractor and actual instruction interpreter |
| Algebraic execution | All local execution work in the declared algebraic backend | Quantitative realization, charged control/storage, fixed access and size conventions; reviewed primitive adequacy, without a standard-machine correspondence |
| Bit or fixed-word execution | Cost of concrete encodings and arithmetic | Implementations and simulation/cost bounds for primitives and input handlers |
| Physical execution | Bounds for an implementation on a specified platform | A compiler/runtime correspondence and platform cost justification |

VCVio already exposes backend-relative `IsOraclePPTBy`, `StrictPPTWitness`, and certified pure
computations. Its source explicitly requires a backend-specific adequacy theorem before claiming
a standard machine interpretation. ArkLib should consume that interface, adding protocol views
and game conjunctions. Generic realization combinators and adequacy machinery belong upstream;
FRI and Toy correctness and resource envelopes belong in ArkLib.

The algebraic backend is new work in E3a, not an existing instance of this facade. Its code type
may be deeply embedded while still reusing the existing realizability and resource interfaces.

Caliper supplies a concrete word-and-buffer language whose control and memory operations appear
in its execution semantics. It is a candidate backend or refinement target, not an automatic
cost model for arbitrary Lean or `OracleComp` code. Its instruction admissibility conditions
include per-word allocation charges and permit some zero charges, including release whose cost
is assigned to acquisition. This is a useful example of justified accounting rather than a rule
that every cost entry must be positive.

Caliper's memory bounds track both net change and peak growth; sequential peaks do not add like
operation counts. Keep a future peak-memory theorem separate from an additive `ResourceProfile`.
Its compilation contract also leaves code-generation work unpriced and does not prove the RISC-V
correspondence. A parameter-dependent builder that emits a different program for every size
therefore needs a uniform-generation argument before supporting an asymptotic claim.

The initial repair should use VCVio/PolyFun and an explicit algebraic execution model. Do not make
it wait for a Caliper port from Lean 4.32.2 to ArkLib's Lean 4.35.0 stack. A later pilot can implement
one field primitive or interpolation kernel in Caliper, prove semantic agreement, and substitute
its operation costs. A 64-bit field modulus still needs a proved modular arithmetic implementation,
including intermediate overflow handling; fitting field elements in one word is insufficient.

Sources: VCVio's pinned
[cost API](https://github.com/Verified-zkEVM/VCVio/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/VCVio/OracleComp/QueryTracking/CostModel.lean),
[resource profiles](https://github.com/Verified-zkEVM/VCVio/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/VCVio/OracleComp/QueryTracking/ResourceProfile.lean),
and [complexity facade](https://github.com/Verified-zkEVM/VCVio/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/VCVio/CryptoFoundations/Asymptotics/ComputationalComplexity.lean);
Caliper's [machine model](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/01-machine-model.md),
[memory semantics](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/02-memory.md),
and [limitations](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/05-limitations.md).

## FRI integration

Preserve [`knowledge_soundness_with`](../../ArkLib/ProofSystem/Fri/Spec/KnowledgeSoundness.lean)
and its named `Extractor.extract`. The
[program](../../ArkLib/ProofSystem/Fri/Spec/Extraction/Program.lean) already defines
`extractHistory` as the result projection of its measured execution. Its
[full profile](../../ArkLib/ProofSystem/Fri/Spec/Extraction/FullCost.lean) and
[field-operation envelopes](../../ArkLib/ProofSystem/Fri/Spec/Extraction/ClosedCost.lean)
apply to every retained history, including early rejection. Package these existing theorems
without changing the extraction algorithm or its soundness error.

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

The realization must cover domain-index enumeration, loop guards and index arithmetic, selected
node/value storage, list traversal and append, interpolation allocation and coefficient access,
prefix/view preparation, and witness construction. Audit these costs as algorithms; a linter for
field syntax cannot establish them. Preserve the early final-degree guard and bound the work
before rejection of an oversized final polynomial. Acquisition or validation of an already
canonical polynomial is a separately stated input cost, not hidden inside a constant-cost read.

Declare the IOP access model explicitly: immutable tables have indexed field-element reads; the
retained prefix and final polynomial have bounded, described representations. The extraction
bound excludes production of the prover's oracle tables. It includes the extractor's own reads
and local computation. A concrete implementation of a function-valued input must supply its own
handler bound before obtaining a bit-runtime corollary.

Prove polynomial domination under the existing `D ≤ N` and positive folding schedule conditions.
These imply `b_i ≤ N`, `d ≤ N`, and `r ≤ n`; all varying parameters must be covered. The
appropriate claim is polynomial in the available oracle/table size, with field-element and
address sizes explicit. It is not polynomial in `log N`. Keep the concrete budget as the main
usable theorem and derive an algebraic polynomial bound after adding local overhead. Bit time
additionally needs polynomial-cost field implementations and uniform input access.

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

For the round-by-round theorem, certify each invoked stage and its own available prefix. Retain
the existing knowledge-state function as proof-side data. The terminal certificate and the
per-round certificates must identify their respective public extractors; one does not imply the
other without a timing and composition proof.

## Uniform families and concrete bounds

E7 is deferred until a concrete consumer fixes the parameter-growth and representation policy.
It is not a dependency of the concrete FRI/Toy results or their public documentation updates.

Use `knowledgeSoundnessWithin` for a concrete budget in a named execution model. Use a separate
proposed `knowledgeSoundnessPPTBy` for the family-level corollary: the game holds at every
parameter, and the packed extractor family satisfies VCVio's
`SecurityFamily.IsOraclePPTBy` for fixed backend, boundary and oracle contract.

That predicate requires one realization and one polynomial for the whole family. A Lean
definition parametric in `n`, `F`, and typeclass instances is not by itself such a certificate:
the instances, field representation, enumeration, setup and any generated code must have the
stated uniform implementations. Choose an explicit field family or state the algebraic primitive
contract; do not existentially choose unrelated representations at each parameter.

An asymptotic security claim further specifies how `N`, degrees, folding schedule, field size
and query count depend on the security parameter. To obtain polynomial time in that parameter,
their encoded sizes and the permitted oracle-access costs must meet the stated bounds. A concrete
error expression does not automatically become negligible. Deterministic strict extraction is
the first target; expected polynomial time and dependence on acceptance surplus are separate
contracts, unnecessary for these deterministic extractors.

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
