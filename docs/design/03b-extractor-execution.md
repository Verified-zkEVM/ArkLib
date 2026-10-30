# Extractor execution backends

**Required later; backend route proposed.** This chapter specifies complete execution bounds for
a named extractor. They turn the operation counts of the
[measured contract](03a-extractor-efficiency.md#the-measured-operation-contract) into a running
time in a declared computational model. E3 is required for unqualified efficient-extraction claims
and is scheduled after the interaction-layer soundness contracts and their composition. E3a's algebraic
backend is the proposed route to it; another execution model with a reviewed adequacy argument can
replace it. E7's uniform families wait for a consumer. The
[efficiency chapter](03a-extractor-efficiency.md) owns the games, the measured contract and the
FRI/Toy requirements; the [roadmap](05-roadmap.md#extractor-efficiency-repair) owns order and
acceptance checks. All API names below are proposals.

Two kinds of evidence stay distinct throughout. A reviewed adequacy argument explains why a
backend's primitives, representations and charges are appropriate. A proved correspondence to a
standard machine is a theorem. The initial backend supplies the first, not the second.

## Realized execution

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
it wait for a Caliper port from Lean 4.32.2 to ArkLib's Lean 4.35.0 stack. A later pilot can
implement one field primitive or interpolation kernel in Caliper, prove semantic agreement, and
substitute its operation costs. A 64-bit field modulus still needs a proved modular arithmetic
implementation, including intermediate overflow handling; fitting field elements in one word is
insufficient.

Sources: VCVio's pinned
[cost API](https://github.com/Verified-zkEVM/VCVio/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/VCVio/OracleComp/QueryTracking/CostModel.lean),
[resource profiles](https://github.com/Verified-zkEVM/VCVio/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/VCVio/OracleComp/QueryTracking/ResourceProfile.lean),
and [complexity facade](https://github.com/Verified-zkEVM/VCVio/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/VCVio/CryptoFoundations/Asymptotics/ComputationalComplexity.lean);
Caliper's [machine model](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/01-machine-model.md),
[memory semantics](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/02-memory.md),
and [limitations](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/05-limitations.md).

## FRI realization requirements

The realization of FRI's named extractor must cover domain-index enumeration, loop guards and index
arithmetic, selected node/value storage, list traversal and append, interpolation allocation and
coefficient access, prefix/view preparation, and witness construction. Audit these costs as
algorithms; a linter for field syntax cannot establish them. Preserve the early final-degree guard
and bound the work before rejection of an oversized final polynomial. Acquisition or validation of
an already canonical polynomial is a separately stated input cost, not hidden inside a constant-cost
read.

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
