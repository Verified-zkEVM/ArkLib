# Executable LogUp formalization

The target is a complete, executable interactive oracle argument for lookup inclusion, built from
a reusable argument for field-valued multiset balance. The first implementation follows the grouped
sumcheck construction of Haböck's revised LogUp paper, using native interaction and computable
Sumcheck. It includes weighted balance, scalar lookups, and a tuple-and-bus compression adapter.
Every delivered variant has its own complete correctness theorems and executable acceptance check.

The [reference comparison](../kb/concepts/logup.md) records the paper version and pinned Plonky3,
OpenVM, SP1, and Stwo implementations. This is a proposed implementation contract; the declarations
and improved bounds below are proof obligations, not claims that they already exist.

## Scope and completion boundary

The initial development includes:

- Generic net multiplicities, rational identities, denominator clearing, and fraction folding.
- Field-valued weighted balance, with no characteristic lower bound.
- Scalar table lookups and integer multiset equality as separately proved specializations, with
  explicit assumptions preventing multiplicities from vanishing in the field.
- A complete grouped-sumcheck native protocol, an honest prover operating on evaluation tables,
  an executable virtual polynomial oracle, and the terminal verifier check.
- Base-field data with extension-field challenges; tuple compression and typed bus separation.
- Exact execution correspondence, ordinary soundness against arbitrary native prover strategies,
  honest completeness, query bounds, code-generation gates, and compiled runtime checks.

Full fractional GKR, LogUp*, a STARK AIR compiler, concrete polynomial commitments, Fiat–Shamir,
zero knowledge, and cross-language verification of Rust are separate developments. Shared algebra
and oracle interfaces must allow those consumers without requiring their security theorems here.
No placeholder declarations or conditional claims of having verified these other protocols belong
in the initial merge.

## Semantic statements

For a finite collection of messages `(key_i, weight_i)`, define

```text
netWeight(k) = sum_{i : key_i = k} weight_i
Balanced     = forall k, netWeight(k) = 0
```

Weights live in a field. `Balanced` means equality in that field. It does not assert equality of
integer counts or lookup inclusion by itself. The algebraic API supports arbitrary finite index
types and arbitrary key types with executable equality where an algorithm uses it. Lists and
vectors get thin interoperability lemmas; the protocol does not adopt a list-only semantic API.

The scalar lookup instance has `M` query columns and one table, all with `N = 2^n` rows. Its input
language is exactly

```text
forall column row, exists tableRow, query[column][row] = table[tableRow]
```

The honest prover receives an index for every query as private witness data. The relation checks
that the indexed table value equals the query. Prove that this relation's language is precisely
the inclusion statement. A proof of an existential is never used as a runtime witness constructor.

Construct multiplicities by incrementing a natural-number histogram at those indices and only
then casting counts into the field. Different queries may select different occurrences of the
same table value. The construction needs no division by the table multiplicity, no injectivity of
the table, and no canonical choice among duplicates. A finite-search witness finder may be offered
as a separate checked convenience algorithm; the protocol prover does not depend on it.
This is a deliberate change from the paper's normalized honest assignment. Prove that both
assignments satisfy the same per-value weight equations when the paper's normalizing counts are
nonzero in the field, in particular under its characteristic assumptions. Histogram correctness
itself needs no such assumption. Do not claim the two assignments' messages are equal.

The signed collection has query weights `+1` and table weights `-m`. Forward correctness of the
histogram is characteristic-independent. The converse from balance to inclusion requires every
positive query count that can occur to remain nonzero. The public sufficient condition is
`M * N < ringChar B`; a more precise per-key bound may be exposed separately. A scalar-count
overflow example must demonstrate why this assumption is necessary.

For permutation checks, require injectivity of the natural-count cast on both count ranges.
An extension field increases the challenge space, but does not increase the characteristic or
repair count wraparound.

## Data and executable representations

Use a base field `B` and a challenge field `E` with an injective field embedding. The scalar theory
also specializes to `B = E`. Executable APIs carry the equality, field operations, and samplers
they actually use; generic finite-type enumeration is not the default concrete field sampler.

Use CompPoly's `CMlPolynomialEval`, a `Vector` of `2^n` values, for multilinear oracle data. Reuse
its little-endian row order, `evalMle`, `eval₂Mle`, and `evalMleLayer`. Each round eliminates the
least significant remaining bit. Prove every conversion to Boolean-function and mathematical
polynomial views; an asymmetric fixture must distinguish reversed variable orders.
Use the Boolean domain `{0,1}^n` directly. Relate it to the paper's `{minus one,one}^n` by the
coordinatewise affine equivalence where two is invertible. That correspondence must not impose
an odd-characteristic assumption on the more general weighted-balance protocol.

Reuse the native Sumcheck bounded coefficient-array message and Horner query interface.
Construct round polynomials by coefficient arithmetic, so their construction needs neither
distinct interpolation nodes nor inversions of interpolation denominators.

Keep the mathematical polynomial and rational-function interpretations in the proof layer.
Their representation-specific noncomputability must be documented individually and must never
enter the runtime dependency graph. Every program and value-computing API in this development
must compile, including the generic prover, verifier, virtual oracle, witness construction,
configuration checks, and concrete samplers. Proof erasure may remove classical proofs; runtime
data may not come from classical choice.

## Group plan and fraction algebra

Configuration fixes `n`, a positive number `T` of terms per row, and `1 <= ell <= T`.
The canonical grouping uses consecutive chunks of size at most `ell`, with
`K = ceil(T / ell)`. The scalar lookup specializes to `T = M + 1`.
An executable checked constructor produces the plan and its coverage, disjointness, cardinality,
and ordering certificates. Provers cannot change grouping or message shapes inside a run.

The common algebraic operation combines numerator-denominator pairs:

```text
(a,b) +fraction (c,d) = (a*d + c*b, b*d)
unit                  = (0,1)
```

Prove associativity, commutativity, regrouping, and agreement with fraction addition when
denominators are nonzero. The unnormalized pair operation is polynomial arithmetic and remains
well-defined at zero denominators. Use it for executable scalar reconstruction and univariate
round-polynomial construction, avoiding a separate erased-product computation for each term.
Neutral padding is `(0,1)` when constructing fraction collections; it is not `0/0`.

The mathematical cleared numerator for all `D = T*N` occurrences is

```text
P(X) = sum_a w_a * product_{b != a} (X - v_b)
```

Prove that a nonzero net multiplicity makes `P` nonzero, even with repeated values, and that its
degree is at most `D-1`. Factor this through the generic rational identity and denominator-clearing
bridge. Do not retain a parallel Taylor-coefficient proof unless it earns an independent consumer.

## Protocol and actual verifier execution

For lookup inclusion, the initial table and query oracles are fixed before interaction begins.
The prover first sends its multiplicity oracle. For weighted balance, both value and weight
oracles are already fixed inputs. The remaining scalar protocol is:

1. Draw a uniform `alpha : E`.
2. The prover sends `K` multilinear helper oracles. Honest helper values on a Boolean row are
   `h_k(u) = sum_{i in I_k} w_i(u) / (alpha - v_i(u))`.
3. Draw independent uniform `z : E^n` and `lambda : E^K`.
4. Run existing computable native Sumcheck on the zero-sum claim for the polynomial below.
5. Perform the final oracle query action and accept only if the retained oracle evaluations
   reconstruct Sumcheck's claimed value at its final point.

Public configuration contains the characteristic certificate when the chosen specialization
needs one; its runtime constructor checks the corresponding natural-number budget. That proof
is not repeated in every public statement. The native tree fixes the message and challenge order,
so multiplicities cannot adapt to `alpha` or `beta`, and helpers cannot adapt to `z` or `lambda`.

Write `d_i = alpha - v_i` and define the residual and batched polynomial by

```text
R_k(X) = h_k(X) * product_{i in I_k} d_i(X)
         - sum_{i in I_k} w_i(X) * product_{j in I_k, j != i} d_j(X)

Q(X)   = sum_k h_k(X) + eq(X,z) * sum_k lambda_k * R_k(X)
eq(r,z)= product_j ((1-r_j)*(1-z_j) + r_j*z_j)
```

All value, weight, and helper inputs here are multilinear. Prove the individual degree bound
`degreeOf j Q <= ell + 2`; use that bound in actual message types and soundness, rather than
charging the worst-case number of columns.

Define the virtual `Q` oracle by querying the retained input and helper sources and applying this
scalar formula. Prove it realizes the same degree-bounded polynomial for arbitrary well-typed
oracle data, including malicious helper messages. It must not rebuild a mathematical polynomial
or enumerate Boolean rows to answer a verifier query.

Use native interaction trees, ordinary native prover continuations, exported claims, and the
existing composition and source-routing laws. Initial input resources and sent messages are the
ones used by the later queries. Preserve private continuations and their effects after challenges
and public aborts. Prototype this complete composition before freezing the public API.

Expose two endpoints: a reduction returning the retained evaluation claim for composition, and
a complete argument whose terminal action checks it and returns accept or reject. The latter's
security event is the acceptance of a false initial statement. Returning an unchecked opening
claim is not completion of that argument. The final check has no fresh randomness and zero
additional soundness error.

Malformed runtime configuration and array shapes return explicit errors. Typed messages rule
out excess polynomial degree. Any raw-array convenience interface validates lengths before
constructing those messages; it must not silently truncate them or panic on malformed input.

## Soundness proof targets

The new proof should avoid the old division-based bad-event machine. Establish this deterministic
implication first, allowing zero denominator values:

```text
(forall k u, R_k(u) = 0) and (sum_{k,u} h_k(u) = 0)  ==>  P(alpha) = 0
```

Indeed, regroup the global denominator product by `(group,row)`. Substituting every group numerator
by its helper times its denominator turns the global cleared numerator into
`(sum_{k,u} h_k(u)) * product_a (alpha-v_a)`. This is a polynomial identity, with no division or
nonzero-denominator hypothesis. Consequently a false balanced-sum claim can escape through a root
of `P`; a separate pole event need not be charged in this protocol's outer soundness proof.

After `alpha` and the helpers are fixed, either the helper total is nonzero or some residual table
is nonzero. In the second case with zero helper total, select one nonzero residual before drawing
`z`. Its multilinear extension has total degree at most `n`, so hiding it costs at most `n/|E|`.
There is no need to union-bound over all `K` residuals. Conditional on the remaining coefficients
being nontrivial, the independent affine batching equation costs at most `1/|E|`.

The intended scalar error ledger is therefore:

| Event | Target upper bound |
| --- | --- |
| Cleared numerator vanishes at `alpha` | `(D-1)/|E|` |
| A selected nonzero residual is hidden at `z` | `n/|E|` |
| Nontrivial affine batching equation vanishes | `1/|E|` |
| Native Sumcheck turns a false claim into a true final claim | `n*(ell+2)/|E|` |
| Terminal oracle check | `0` |

For `D >= 1`, the sum is `(D + n*(ell+3))/|E|`. Each entry must be proved for the actual sampling
stages and actual arbitrary prover continuation at that history. The claimed result is a `<=`
bound, with an optional cap at one, not an imported numerical statement from the paper.
If a sharper target needs correction during proof, settle the mathematical contract explicitly
before implementing its consumers; do not add an assumption asserting the desired bound.

Use existing native Sumcheck soundness and exported-oracle composition. Prove that every reachable
export satisfies the polynomial-realization premise, making its admissibility error zero.
Initial statement truth must not be an admissibility premise. The theorem quantifies over every
well-typed whole native prover, with arbitrary private continuation memory.

Round-by-round results may be exposed where proved useful, but ordinary soundness must not depend
on the admitted legacy implication from round-by-round soundness. No legacy security or lifting
admission may appear in the dependency closure of a new declaration.

## Completeness and poles

Sample `alpha` from all of `E`, with no verifier table scan and no rejection sampler. The honest
helper algorithm uses total field inversion, including its defined zero case. Its correctness
lemma assumes the relevant denominators are nonzero; the protocol adds no extra oracle message
or prover-triggered restart when that hypothesis fails.

For a true scalar lookup, every queried value is a table value, so all needed denominators are
nonzero except when `alpha` equals a table value. The intended completeness error is at most
`number of distinct table values / |E| <= N/|E|`. Away from that event, prove that the actual honest
execution accepts for every subsequent challenge sequence. Then use losslessness of the honest
samplers and execution to derive the probability bound.

For general weighted balance, charge the corresponding support of denominator values. Perfect
completeness through modified constraints is a distinct protocol variant and is outside the first
implementation. A seeded test handler is an execution fixture, not evidence of uniform sampling.

## Tuple and bus adapter

Represent a schema by a finite bus type, an injective base-field tag assignment, and one declared
payload width per bus, bounded by `W`. The key type is the dependent pair of a bus and its payload.
Widths are fixed by the schema across all producers and consumers. Runtime schema construction
checks this contract and tag uniqueness; a table-provider registry checks ownership for the lookup
specialization. Several physical pieces may implement one declared table collection.

A simple canonical fingerprint is

```text
c_beta(bus,payload) = tag(bus)*beta^W + sum_{j < width(bus)} payload_j*beta^j
```

First prove injectivity as a map from semantic keys to formal polynomials. Evaluation at a sampled
`beta` is probabilistic, not injective: even bus separation can degenerate at a particular value.
Prove transport of weights through compression and isolate one key with nonzero net weight before
the challenge. Against a collection with `s` distinct keys, the proposed compression error is
`(s-1)*W/|E|`. This avoids a union bound over every pair of keys.

All value, weight, and multiplicity data is fixed before independent `(beta,alpha)` are drawn.
The adapter feeds compressed multilinear values into the scalar weighted protocol. Prove
completeness for every `beta` away from denominator poles, and add the compression term only to
soundness. For a common row domain the group degree remains `ell+2`.

The Plonky3 power order and bus offset are connected by explicit translation lemmas. Stwo's
power order gets its own translation. SP1's multilinear combiner is a different hash family;
record its contract and do not claim the univariate fingerprint theorem verifies it.

The first protocol adapter uses a common Boolean row domain, as in the scalar construction.
Finite-message balance and fraction-fold algebra remain independent of row layout. Packing
heterogeneous trace heights into a single committed domain, with authenticated mappings back to
the original traces, is a later adapter; it is not implicitly verified by zero-weight padding.

For enabled lookups or bounded signed counts, Boolean selectors and natural/integer magnitude
bounds are semantic obligations proved by the caller or checked by the specialized input
relation. A field element carrying a claimed bound is insufficient. Derive per-bus natural-number
budgets before field casting. Zero-weight padding does not justify changing payload schemas.

## Honest prover and cost targets

Construct helper tables from the original evaluation data. A checked batch-inversion primitive,
with a theorem covering its zero-handling behavior, can replace elementwise inversions. Reuse or
upstream that generic algorithm rather than place it inside LogUp. The off-pole helper values
must agree with the mathematical formula under either implementation.

For Sumcheck, initialize challenge-ring denominator tables `D_i=alpha-f(value_i)` and
weight tables once after receiving `alpha`. Retain their folded versions, the helper tables,
and one cached equality-kernel table. The formal identity
`MLE(D_i)=C(alpha)-MLE(f(value_i))` connects this private state to the original retained source.
After the joint challenge, build the kernel table with the shared fast Lagrange construction.
Fold it with the same received challenges as the other tables; zero kernel factors need no division.

At each round, adjacent entries give affine univariate coefficient arrays. Bind every row's
denominator, weight, helper and kernel arrays once. In each fraction convolution, place the fresh
affine factor on the left to control padded-array work. Compute one row circuit and add it
directly into a single accumulator; canonicalize only the final bounded message. No list of all
row coefficient arrays is needed at runtime. Fold the tables using the received challenge.

Prove formal substitution and coefficient equality with the existing mathematical honest
Sumcheck projection of `Q`, then transport the whole honest strategy to reuse native completeness.
Equality of evaluations on a finite field is insufficient: the coefficient regression must
distinguish `X^3` from `X` over the two-element field, even though their field evaluations agree.

The local scalar reconstruction uses a linear scan through each group. The final lookup check
needs at most `M+K+2` source openings; Sumcheck uses at most `3n` message evaluations on the Boolean
domain. The general weighted instance uses at most `2T+K` source openings. Prove these counts
through virtual substitution and the terminal action, including the zero-round case.

Target prover storage linear in the retained and folded table sizes. For the direct coefficient
algorithm, target field work `O(N*T*ell)` for the Sumcheck portion: the remaining row counts halve
each round, and folding a group of affine factors costs quadratically in its size with basic
coefficient multiplication. Prove loop-size and operation-count recurrences before claiming this
bound; include the cost of equality-kernel construction and all helper generation separately.
Concrete timings validate engineering choices but are not complexity proofs.

Count verifier-local arithmetic and source queries separately from the work of the source handler.
A transparent dense-table handler takes linear time to answer a multilinear opening. An oracle
query bound alone does not make that transparent end-to-end runner a succinct verifier.

## Module ownership and implementation order

Proposed homes, refined to existing owner modules during implementation:

| Layer | Responsibility |
| --- | --- |
| `Data/` generic multiplicity modules | Net weights, histograms, index witnesses, list/vector bridges |
| `Data/Fraction.lean` | Executable unnormalized fraction pairs and division-free regrouping |
| `Data/Polynomial/` and rational-function modules | Partial fractions, denominator clearing, degree and root bounds |
| `Data/MvPolynomial/` and CompPoly | Equality kernel, evaluation-table interpretation and folding, reusable message-construction lemmas |
| `ProofSystem/Logup/Algebra/` | Grouped residuals, `Q`, degree bounds, scalar reconstruction agreement |
| `ProofSystem/Logup/Protocol/` | Native tree, oracle families, exports, verifier, complete terminal action |
| `ProofSystem/Logup/Impl/` | Histogram-based prover, helpers, direct round messages, code-generation gates |
| `ProofSystem/Logup/Security/` | Actual-execution correctness, completeness, outer soundness, composed soundness and query bounds |
| `ArkLibTest/ProofSystem/Logup/` | Caller acceptance, boundaries, adversarial continuations, axiom checks |
| `scripts/LogupRuntime.lean` | Compiled end-to-end fixtures and checked failure cases |

Deliver in this order, with no admitted definitions in merged slices:

1. **Algebra contract.** Extract the useful mathematics from the two earlier PRs into its owners.
   Prove the division-free regrouping implication and characteristic-sensitive specializations.
   Freeze the scalar error ledger and the tuple-compression contract.
2. **Executable oracle boundary.** Build representations, the grouping constructor, scalar
   reconstruction, the virtual `Q` oracle and its realization theorem. Compile a minimal native
   Sumcheck-plus-terminal composition and test actual source routing before building the full
   honest prover.
3. **Complete scalar argument.** Implement the histogram witness path, helpers, direct round
   messages, native lookup tree and terminal verifier. Close exact execution, completeness,
   soundness, query bounds, code generation, and compiled execution together.
4. **Complete tuple and bus argument.** Add the schema constructor, compression and its probability
   bound, typed lookup/permutation specializations, and corresponding full-protocol fixtures.
   Expand the module and paper correspondence documentation around the delivered API.

Generic improvements to CompPoly or VCVio belong upstream or in their established owner layers.
No LogUp-private replacement probability, interaction, or polynomial library is introduced.

## Acceptance evidence

Require all of the following before calling the scoped development complete:

- Every new declaration depends only on a subset of `propext`, `Classical.choice`, and
  `Quot.sound`; no inherited `sorryAx`, custom axiom, or native-compiler trust is allowed.
- External caller probes outside noncomputable sections compile the actual algorithms and
  composed protocol. IR assertions cover the computational roots and concrete samplers.
- A concrete base-field/extension-field fixture uses the existing KoalaBear and `KoalaBear.Ext6`
  computational field and sampler implementations. Small prime-field fixtures make exact bad-event
  enumeration practical; they do not substitute for checking the extension-field runtime path.
- A compiled `logup-runtime` executes complete honest and adversarial native runs through the
  actual verifier, with independent expected values and query/effect logs.
- Fixtures cover repeated table values with different valid index witnesses, unused rows,
  `M=0`, `n=0`, `ell=1`, `ell=T`, a short final group, and unequal coordinate data.
- Negative fixtures cover false inclusion, incorrect witness indices, helper corruption,
  a forged final claim with otherwise valid Sumcheck data, malformed lengths, wrong bus,
  inconsistent widths, and missing final opening authentication.
- Explicit cases exercise zero denominators and characteristic wraparound. A kernel fixture
  distinguishes a degree-`n` zero bound from an unjustified `1/|E|` bound.
- Tuple fixtures distinguish bus tags, reversed coefficient order, and zero-padding aliases.
  Source-comparison vectors carry the exact Rust revision and the equation they exercise;
  they do not claim Rust program equivalence.
- Adaptive-prover tests retain private state across every phase and observe effects on public
  abort. A suffix cannot replace the original oracle with a freshly chosen one.
- At least one fully instantiated scalar and tuple theorem has satisfiable premises and a
  calculated total soundness bound below one. For scalar parameters `E=ZMod 257`, `n=2`,
  `M=2`, `ell=1`, the proposed bound is `20/257`, with completeness error at most `4/257`.
- Full repository validation, axiom validation, test warning checks, and the appropriate docs
  and citation checks pass on the final head. Stage newly added Lean paths before validation;
  regenerate the root import file through the repository tool.

The initial complete artifact is the grouped native lookup argument with these acceptance checks.
Fractional GKR can then consume the same fraction algebra, weighted relation, compression layer,
computable table operations, and authenticated-opening boundary in a separately proved protocol.
