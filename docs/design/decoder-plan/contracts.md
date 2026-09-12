# Shared producer and consumer contracts

These are semantic requirements for the [parallel workstreams](workstreams.md).
The existing tower and recovery interfaces are implemented. New chart, field and producer record
layouts are proposals until coordinator task I0 lands compiled clients. The first payload-only
boundary is `FastTaylor.ChartData`; its tested producer/consumer clients fix coordinate order and
Taylor-coefficient conventions, but do not freeze full validity or coverage records. Do not independently
create competing versions of these records in several workstreams.

The payload dependency is commit `21310026e27b9c13ea64999c095b7770cda22bad`.
Teams should record adoption of this exact checkpoint; it does not freeze full chart validity
or coverage. Local numerator indices are ascending Taylor powers; final `ExactOutput`
vectors retain the descending fixed-width convention.

## Freeze procedure

1. Inventory existing types and reuse their source owners.
2. Choose one owner for each new runtime record and its semantic predicate.
3. Make universe, characteristic, equality and executable arithmetic inputs explicit.
4. Compile a representative producer and consumer using the proposed public imports.
5. Record the exact interface commit and owned files in the task board.
6. Route later breaking changes through the coordinator and update dependent clients together.

Runtime records hold computable data. Correctness, validity and coverage belong in theorem
statements about that data. A conditional composition theorem is acceptable intermediate work;
it does not discharge the missing producer. Record every such obligation at handoff.

## Field model and deterministic prefixes

Provide actual arithmetic, decidable equality, characteristic and cardinality data, an embedding
from the preceding field, and a computed prefix with distinctness and size proofs. Higher-order
extensions are constructed over the current center field, not only over a prime field.

A supplied basis package is not an extension-field constructor. Proof-only algebraic closures,
roots and embeddings are permitted; executable data cannot be extracted from them by classical
choice. Avoid full field-alphabet materialization in center/prefix construction. Inverse Frobenius
must use explicitly certified computational cardinality data or a proved concrete field kernel.

## Regular chart

Agree on data for the center field and base embedding, center, invertible projection matrix `M`,
monic equation `h`, separant `s`, denominator `B₀`, exactly `k` coefficient numerators, and indexed
agreement residuals. Fix polynomial variable order, Hasse-jet conventions and precision bounds.

The semantic contract records:

- retained initial coordinates and the projection inverse;
- the required degree bounds and `B₀ = s^(2k)` modulo `h`;
- at `h=0` and `s≠0`, each agreement residual equals `B₀` times the corresponding message residual;
- reconstruction of every regular degree-`<k` wanted solution, including ramified projection fibers;
- the distinction between a chart point and a global differential-equation solution.

The confluent sample is a computation device. Coverage is for the entire regular chart, not only
for that sample or an unramified open subset. Empty regular locus is a proved-empty outcome;
unsupported construction is an explicit failure, never silently an empty successful family.

## Nonreduced coefficient and series rings

Reuse `BoxAlgebra.Carrier` and its stored canonical representatives. The next coefficient ring is
the executable monic quotient by `h(a+ε,z)`, with constant-fiber specialization and polynomial-degree
bounds. Do not assume it is a field.

Derive nilpotence of the whole parameter ideal; individual identities `ε_i^N=0` do not imply that
an arbitrary parameter residual has exponent `N`. A bound such as `r*(N-1)+1` must be proved for the
chosen representation. Obtain the constant-fiber Bézout inverse computationally and lift it.

Series algorithms expose precision, residual order and certified scalar units. Integration must
justify every inverse index from the characteristic guard. Newton and fundamental-matrix routines
must execute precision doubling. Global shifts are division-free and must handle degrees at least
the characteristic when those degrees occur in the parameter variables.

## Generic polynomial components, norms and decomposition

G01 also owns executable bounded-degree multivariate gcd, exact division and primitive
normalization needed to compute the arbitrary-order regular component from `H` and its partial
derivatives. Its function-field univariate interface alone is insufficient for that operation.

The generic component splitter works over `E(U)[V]`, but returns descended polynomial factors with
coverage over all relevant projection fibers. Finite D5 remains the later owner over `E[U]/G`.
Generic components may meet in special fibers; do not assert unjustified geometric uniqueness.

The norm producer returns the actual determinant polynomial of multiplication in the monic
`V`-basis. Prove base change, nonzero norm from generic coprimality, and point vanishing implying
norm vanishing, including ramified fibers. A supplied array of norm polynomials is not this producer.

The decomposition producer returns positive multiplicity labels and normalized squarefree,
pairwise-coprime factors with exact reconstruction, including the scalar unit if needed. Define
zero and constant input policies. Execute the appendix's multiplicity-residue calculation,
bounded residue-gcd loop, balanced stratum product and product/remainder-tree refinement of
recursive factors. Prove these stages refine the labelled factorization; output reconstruction
alone is not the required algorithm correspondence. Threshold retention consumes those labels and refines
the existing Hasse-multiplicity specification. Before using natural subtraction `A-|U_b|`, prove
`|U_b| ≤ k-1 < A` for the universal-agreement set.

## Candidate families and common recovery

Reuse `TowerRepresentation`, `WellFormed`, materialization and the batched recovery APIs. Every
returned packet has the prescribed width, reduced coefficients and valid base/fiber moduli.
Constructor coverage represents every wanted regular chart point by an output point specifying
the same message. Extra candidates and repeated images are permitted before final recovery.

Rojas candidates may use the existing univariate representation and its tower embedding. Families
may have different explicitly constructed auxiliary fields. Recovery returns base-field message
coefficients; a common computational algebraic closure or primitive element is unnecessary.
Combining separately recovered families requires a refinement proof for the collection scan.

## Higher-order systems and isolated roots

The current chart system has exactly `r+1` variables and equations: `h=0` and `r` selected
agreement equations. It has no higher Taylor tail rows or affine-to-torus translation wrapper.
Prove cotangent capture and nonsingularity for wanted points before invoking the solver.

Rojas must compute its perturbation/resultant from the supplied system, derive the factorization
needed by specialization, then assemble coordinate maps. Cover isolated affine roots with zero
coordinates even when other components are positive-dimensional. Temporary downstream
factorization assumptions must be discharged by the producer before final acceptance.

Expander selection preserves loops and edge multiplicities of the executed graph, then proves
its spectral/powering certificate, padding/position labels, rejection rules and independent
selection property. All-subsets is a separate authorized mode, not a replacement for this mode.

## Final decoder contract

Reuse `ExactOutput`: fixed-width coefficient vectors, complete membership and duplicate freedom.
Prove successful termination for supported supplied-equation and certified-support inputs, with
certificate failure unreachable under advertised certificate conditions. Compose the executed
separant/center loop with concrete order-specific constructors and shared recovery.

Prove branch equations against the paper procedures as well as output exactness. Unsupported
symbolic work never activates exhaustive fallback. List-size corollaries reuse the existing
mathematical counting results. Paper citation and literal-excerpt migration follow a verified
complete capstone and separate publication authorization.

## First stored chart payload

`HiddenDerivative/RootFinding/FastTaylor/ChartData.lean` owns `FastTaylor.ChartData E r k`.
Its sparse polynomials have `r+1` variables ordered `[t₀,…,tᵣ₋₁,z]`. The two stored matrices
map chart coordinates to the original Hasse jet and back; inverse identities are semantic
obligations, not constructor fields. `numerators : Fin k → CMvPolynomial (r+1) E` prevents
width ambiguity. Numerator index `j` refers to `Z^j` at `center+Z`.

The agreement consumer computes `sum_j N_j*(alpha-center)^j-received*B₀`. Its evaluation
identity holds after every coefficient ring homomorphism. No sampled-fiber or projection
discriminant guard occurs in this identity. The payload does not certify monicity, degree
bounds, `B₀=s^(2*k) mod h`, initial-jet retention or wanted-solution coverage. Those are still
required from concrete producers. Exact accepted interface commit replies are recorded in the
coordinator handoff when the checkpoint is published.
