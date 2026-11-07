# Extractor execution backends

**Required later; backend route proposed.** E3 adds complete execution bounds to the
[measured-operation contract](03a-extractor-efficiency.md#the-measured-operation-contract).
Operation counts alone do not give running time. This chapter specifies the missing execution
certificate; the [roadmap](05-roadmap.md#extractor-efficiency-repair) owns its order and milestone
legend. New ArkLib execution-contract names below are proposals.

## Cost layers and evidence

The resource layer is independent of two axes: **worst-case/all-path versus expected cost**, and
**concrete parameter bounds versus asymptotic family bounds**. State the quantifier and growth
policy for every claim; papers use different choices. The status column concerns current ArkLib
extractor certificates, not the availability of models or libraries elsewhere. Existing E2
certificates give concrete all-path counts; the [expected-time route](#expected-time-rewinding-and-tree-acquisition)
needs separate probabilistic evidence.

| Layer | Units and scope | Evidence for a claim at this layer | ArkLib extractor status |
|---|---|---|---|
| Selected-operation profile (E2) | Ordinary natural counts per declared instruction kind; excludes uncharged host work | Named program, actual handlers, extractor output agreement and its all-path count bound | FRI extractor certificate implemented; native stage/path API validated by fixtures, no production client |
| Complete algebraic execution (E3) | Declared field/control/storage steps plus separately bounded encoded code/data bits and setup | Named backend code, semantic agreement, complete execution/access/termination bounds and reviewed primitive adequacy | Required later |
| Bit or fixed-word execution | Bit operations or machine-word instructions with fixed operand/encoding sizes | A direct bound for the named implementation, or proved primitive/representation/cost simulation including overhead | No extractor certificate or bridge here |
| Physical execution | Platform cycles/time and memory on specified hardware/runtime | A direct bound under stated platform/runtime assumptions, or compiler/runtime/platform cost correspondence from a lower-level model | No extractor certificate or bridge here |

A protocol may prove a bound directly at its chosen layer. Moving between layers instead needs a
proved cost/refinement bridge with explicit units and overhead; no operation-count-to-bit-time or
bit-time-to-cycle conversion is automatic. Proving every layer is not a prerequisite for using an
honestly labelled result at one layer. Benchmarks alone are not universal execution bounds.
Peak memory remains distinct from additive work.

Use **budget uniformity** for one bound over the views/prefixes allowed at fixed parameters (or
separately at each input statement); **program-family uniformity** for one executable generator
and implementation scheme across parameters/statements; and **challenge uniformity** for the
probability law of a uniform sampler. The first is a quantifier on costs, the second a computation
condition, and the third a sampling assumption. None implies the other two.

## The complete-execution contract

The proposed `knowledgeSoundnessWithin` fixes a backend, input/access representations, permitted
responses, and **named backend code**. It combines the knowledge game with these obligations:

- The code's execution agrees with the game's named extractor `E`: the same returned witness or
  failure and, where applicable, the same resulting oracle state. For randomized execution, state
  the corresponding joint-distribution agreement. Extensional equality is enough for this semantic
  obligation; equality with an arbitrary host Lean source trace is not required.
- A quantitative bound holds for that named code in the backend's execution semantics. Charge
  initialization, control, indexing, storage, input preparation, witness construction and all work
  between E2 instructions. A different implementation needs its own bound.
- A strict bound covers all permitted inputs/responses, including rejected histories. Prove valid
  access and termination separately where the quantitative interface requires them. A bound on
  completed paths alone can be vacuous if no run completes. Timeout/fault after acceptance must
  count as extraction failure, not remove the accepted experiment's mass.

`MeasuredProgram.Realizes` proves output agreement, not the second obligation. To derive backend
costs from an E2 profile, additionally provide an operational translation from the actual measured
instruction program to the named code and prove its cost simulation, including interpreter,
handler, view-conversion and local-work overhead. Otherwise prove the backend bound directly.
Semantic agreement between a power-sum evaluator and Horner evaluation does not transfer either
algorithm's cost profile. Cost transfer is a separate obligation from output agreement.

### Code size, setup and uniformity

Fix computable faithful codecs for backend code and constant data as bitstrings. Decoding after
encoding recovers them up to erased proofs or metadata irrelevant to size and cost, preserving
runtime instructions rather than merely equivalent outputs. Measure size by encoded bit length;
state the generator's description size and the generated code/data bounds.
Runtime and setup are separate bounds in the backend's declared step/resource units; bits are
not added to field-operation counts without an explicit valuation. Precomputed tables, their
construction and their storage cannot disappear into free advice or an unspecified constant.
Declare one-time versus per-extraction setup and any amortization policy.

One fixed executable generator must serve every parameter set, statement and prefix in scope.
Statements, prefixes and witnesses are input data, not permission to select unrelated cheap code.
Specify uniform implementations of the encodings, field instances, enumeration and input access.
This discipline belongs to concrete E3. E7 only defers the security-parameter growth policy; a
parametric Lean definition or statement-indexed certificate family is not this generator proof.

A reviewed adequacy argument justifies the primitive basis, representations and charges. A proved
simulation of a standard machine is stronger, separate evidence. The initial algebraic result
supplies the former. Existential packaging is harmless after fixing the named code/generator and
resource interpretation; it cannot choose a backend, representation or embedded table to make
arbitrary functions cheap.

### Input-size convention

State the encoded input length: parameters, statement, transcript/prefix, retained data and any
actually supplied output-relation witness. Fix how the packed input represents the security
parameter `λ` (for example binary or unary), rather than treating `λ` as a unit-size integer.
Bound the returned input-relation witness separately and charge its materialization; its size is
not part of the input length unless that value is actually supplied. Also specify the resource
contract for external oracle tables. With a chosen
fixed-width field encoding of `w` bits, `N` entries use `N * w` bits plus declared container
overhead; `w` need not be assumed minimal. A succinct description or length index can use
`log N` bits while requiring very different access computation. If tables stay external,
name their available length, read-cost and response-size assumptions rather than treating an
arbitrary function as unit-time access. A polynomial bound in full table size `N` is not a
polynomial bound in a succinct input of length `log N`. Representation size, available table size
and declared code/data size must not be silently substituted for one another.

## Backend route and ownership

VCVio/PolyFun already supplies backend-relative `IsOraclePPTBy`, `StrictPPTWitness` and quantitative
realization interfaces. The concrete cslib backend is a single-tape Turing machine over Boolean
strings; the word-class adapter does not supply an algebraic execution backend.

E3a's proposed route is a generic algebraic code type in PolyFun, with a VCVio adapter as needed.
A deep embedding is appropriate; a protocol-specific language or second realizability framework
is not. A temporary ArkLib adapter must state its upstream destination and removal condition.
Gate this work on one actual FRI fold-consistency check, preserving rejection branches and proving
semantic agreement and a complete backend cost before scaling to the extractor.

Use a fixed first-order basis: field arithmetic/equality, bounded index/address operations, and
explicit control/storage. No opcode may run an arbitrary host function for unit cost. Declare
operand and result sizes for every primitive, or charge their growing bit lengths. Polynomial
multiplication, arbitrary decoding and unbounded-integer arithmetic are not unit field operations.
Separate retained read-only tables from working storage. Zero charges can be justified by erased
proofs or amortization; positivity of every syntactic construct is neither necessary nor sufficient.

Caliper is a possible later word/buffer target, not a cost model for arbitrary Lean functions.
Its admissibility rules permit justified zeros; net/peak memory is separate from additive counts.
Its engineering compilation contract is not a proved RISC-V correspondence and leaves generation
work unpriced. Caliper supplies a word-level model. Physical runtime needs separate platform
evidence. A pilot needs semantic agreement and field arithmetic with overflow handling;
fitting field values in one word is insufficient. This route need not block on porting its pinned
Lean stack to ArkLib's toolchain.

## FRI and family obligations

FRI's code must account for enumeration, guards/index arithmetic, selected-node storage,
interpolation/coefficient access, prefix preparation and materialized witnesses. Preserve the
early final-degree guard and bound work before rejecting an oversized polynomial. State acquisition
or validation cost for the canonical final polynomial rather than hiding it in a unit read.

Use explicit indexed reads on immutable oracle tables, with bounded retained-prefix and polynomial
representations. Producing the prover's tables is outside extraction; the extractor's own reads
and local work are inside. Function-valued input handlers need implementation costs for a bit-time
corollary. Under `D ≤ N` and the positive schedule, `b_i ≤ N`, `d ≤ N` and `r ≤ n`; prove polynomial
domination in the available table size `N`, not merely in `log N`.

At a chosen backend and resource layer, E7 relates the concrete bounds to security-parameter
families through polynomial domination. The ordinary VCVio predicate below is strict/pathwise;
an expected-time-only family needs the separate
[expected-cost and termination contract](#expected-time-rewinding-and-tree-acquisition).
E7's proposed `knowledgeSoundnessPPTBy` has the schematic shape

```text
(∀ λ, knowledgeSoundnessWith(..., E λ, κ λ)) ∧
  OracleComp.Complexity.SecurityFamily.IsOraclePPTBy Q bd contract programFamily
```

Here `programFamily : (λ : ℕ) → Input λ → OracleComp (spec λ) (Output λ)` is the typed named
extractor family, with semantic agreement to `E`. The API packs it internally; `bd` represents
the packed parameter/input and output encodings and oracle boundary, `Q` fixes the execution/size
model, and `contract` fixes allowed responses/resources. The predicate requires one packed
realization and one polynomial across parameters, rather than unrelated pointwise witnesses.
That polynomial is in the packed encoded input size and permitted oracle length envelopes, not
in `λ` alone for arbitrary auxiliary inputs. A consumer needs an input-size growth envelope for a
`poly(λ)` claim, or may instead state a bound polynomial in `λ` and the actual input length.
The code/generator
obligations above remain E3 even while E7's security-parameter growth policy waits for a consumer.

Choose the parameter/input-size policy, substitute it into the **full concrete budget** and prove
polynomial domination in the security parameter. `log N = poly(λ)` does not make `O(N)` extraction
polynomial in `λ`. Bit time additionally needs polynomial-cost arithmetic in `log |F_λ|` and bounded
addresses. A concrete error expression does not automatically become negligible: prove that for
the chosen error family separately. Concrete protocol certificates do not wait for E7.

## Expected time, rewinding and tree acquisition

The strict FRI/Toy target is separate from the existing [rewinding
plan](05-roadmap.md#rewinding-and-compiled-protocol-security), tracked in
[#1410](https://github.com/Verified-zkEVM/ArkLib/issues/1410). Its failed-attempt/expected-time
bridge is not implemented. Existing `expectedCost`, `ExpectedCostBound` and Markov APIs integrate
unnormalized successful-output cost marginals; `AddWriterT.expectedCost` is the interpreted version.
The generic weighted-writer cost-bound bind lemmas are pathwise; no generic expected-time
execution/substitution theorem follows from them. Separately,
`OracleComp.expectedSimulatedQueryCount_bind` in `VCVio.OracleComp.QueryTracking.ExpectedQueryCount`
gives a specialized expected charged-query bind law for stateful handlers. Its recursive accounting
includes the failing query and previously spent queries without a losslessness premise; reuse that
route when its units and failure semantics match the client. For generic writer instrumentation,
operational base failure discards accumulated writer output, giving missing mass cost zero;
returning `Option.none` as a value in a lossless base retains its charge. The canonical `OracleComp`
expectation facade is currently lossless, so the failed-base limitation concerns interpreted partial
computations, not a failure of that facade. Rewinding needs semantics preserving spent cost through
failure and timeout, or an appropriate totalization/prefix-cost proof, with the stated termination
guarantee (normally almost-sure). Fixed sequential expectations can add with integrable scalar costs
and bounds uniform over actual inputs/histories; arbitrary random-call/rewinding composition needs
conditional/stopping-time proofs. A profile valuation must be additive, or have a separately proved
upper-bound law: an arbitrary `val : ω → ℝ≥0∞` need not preserve sums. Keep success, acceptance
surplus and truncation/error policy explicit. Processing a possibly exponential supplied tree,
obtaining it, and producing an escape are distinct costs. These remain obligations of #1410's
bridge, not a second plan or resource framework.

## Source modules and evidence

`VCVio.OracleComp.QueryTracking.CostModel`,
`VCVio.OracleComp.QueryTracking.WriterCost`,
and `VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity`
state the existing interfaces, not completed execution or expected-time extraction certificates.
Caliper's pinned [machine](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/01-machine-model.md),
[memory](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/02-memory.md)
and [limitations](https://github.com/zksecurity/caliper/blob/b62f7c8be35df0aa728e5a6aac7bae85eef67449/docs/05-limitations.md)
record its different execution boundary.

Bellare--Kilian--Rogaway's [concrete-time convention](https://cseweb.ucsd.edu/~mihir/papers/cbc.pdf)
includes description length; Bernstein--Lange's [precomputation analysis](https://eprint.iacr.org/2012/318)
explains why uniformity alone does not resolve every concrete nonuniform model.
Bellare--Goldreich's [knowledge definition](https://cseweb.ucsd.edu/~mihir/papers/pok.pdf) accounts
for acceptance surplus, while Katz--Lindell's [expected-time analysis](https://eprint.iacr.org/2005/379)
warns against unrestricted oracle composition. [FMN24](../kb/papers/FMN24.md) separates supplied-tree
CWSS extraction from its expected-time knowledge bridge; [ABF26](../kb/papers/ABF26.md) includes
terminal/per-round extraction time that ArkLib's bare games omit.
