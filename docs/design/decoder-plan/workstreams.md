# Ten decoder workstreams

The verified source baseline for this reference is
`3c67cb3fa669985b2add6c5d080a3060c4728789`. Launch from the coordinator's exact
revision containing this plan and accepted interfaces, as specified in the workflow. The branches and new source directories below are
**proposals**, not created branches or assigned workers. The coordinator grants ownership before
work starts. Read the [plan overview](README.md), [shared contracts](contracts.md), and
[execution workflow](workflow.md) before taking a package.

The audience is a Lean contributor implementing a named paper algorithm. Each group has work
that can start before every upstream constructor is finished. A conditional theorem is an
acceptable intermediate result when its remaining assumptions are explicit. It does not close a
group whose final acceptance requires a computed producer.

## Ownership and acceptance shared by all groups

Own only new files under the proposed directories and corresponding new `ArkLibTest/` paths.
Existing source owners are read-only unless the coordinator transfers them explicitly. This
includes the existing box algebra, nilpotent correction, D5, tower recovery, rational Taylor
recurrence, chart, and Rojas extraction owners. Suggest required changes to those owners separately.
The coordinator owns shared contracts, generated imports, integration, and repository-wide gates.

Generic polynomial, algebra, graph, and field owners do not import Reed–Solomon application
modules. Decoder adapters import the generic owners in the other direction. A directory in this
page denotes a proposed module family; settle exact Lean namespace names through the contracts
before adding public declarations.

All final producers need executable code, semantic refinement, termination, and meaningful tests.
Named algorithm implementation is required: a different exhaustive algorithm, supplied output
oracle, or a correctness theorem about an unexecuted reference does not satisfy acceptance.
Complexity proofs are excluded from this implementation plan. That exclusion does not permit
substituting dense interpolation for the prescribed fast interpolation, all centers for the
single-center algorithm, or all subsets for the expander branch. Reuse existing executable
arithmetic; a fresh instruction machine or cost ledger is not required for every function.

## Dependency map

| Group | Proposed branch | Main integration dependencies |
| --- | --- | --- |
| G01 Function-field algorithms | `quang/decoder-function-field` | Generic polynomial and fraction-field foundations |
| G02 Full squarefree decomposition | `quang/decoder-full-decomposition` | Concrete inverse Frobenius; G07 for constructed field instances |
| G03 Taylor geometry | `quang/decoder-taylor-geometry` | G01 for computed component operations; G07 for required field setup |
| G04 Taylor local algebra and lift | `quang/decoder-taylor-local` | Existing box/correction foundations; G03 good-fiber output |
| G05 Taylor global reconstruction | `quang/decoder-taylor-global` | G03 degree certificates and G04 local coefficients |
| G06 First-order norm candidates | `quang/decoder-norm-candidates` | G01, G02, G03–G05; integrated tower recovery |
| G07 Explicit fields and prefixes | `quang/decoder-explicit-fields` | Generic finite-field arithmetic and irreducibility |
| G08 Rojas producer | `quang/decoder-rojas-producer` | G07 for required candidate field/prefix |
| G09 Higher-order selection and candidates | `quang/decoder-higherorder-selection` | G03–G05, G07, G08; generic graph foundation |
| G10 Zeroth-order decoder | `quang/decoder-zeroth-order` | G01, G07; existing ordinary quotient Newton and recovery |

The dependency column describes final integration, not a requirement to leave workers idle.
G01, G02, G07, and the system-to-resultant slice of G08 can begin independently. G03 can prove
projection invariants while G01 develops its producer; G04 can develop over a certified monic
input; G05 can establish shift recovery from degree bounds. G06 can implement norm arithmetic
on certified inputs. G09 can build direct systems and the executed graph. G10 can start its
interpolation and obstruction stages. Follow the workflow's concurrency limits and avoid shared
writable build directories.

## G01 — Function-field algebra, multivariate gcd, and descent

**Proposed ownership.** Generic `ArkLib/Data/Polynomial/FunctionFieldAlgorithms/` and
`ArkLib/Data/MvPolynomial/BoundedGCD/`, with matching tests. No decoder imports. Reuse the existing fraction-field and factorization owners read-only.

**Start now.** Implement normalized stored rational functions and polynomial arithmetic over
`E(u)`. Provide computed gcd/exact division with refinement to the semantic fraction field.
In a separate owned slice, implement bounded-degree multivariate gcd/exact division and primitive
normalization for G03's `H/gcd(H,H_u₀,…,H_uᵣ)` and subsequent separant-factor removal.
The univariate-over-`E(u)` interface alone does not supply this arbitrary-order operation.
Then implement factor normalization and descent for monic factors of the relevant polynomial
in `E[u][v]`. Return divisibility and product certificates with the descended factors.

**Interface and dependencies.** Consumers supply stored polynomials and explicit hypotheses
such as monicity. Outputs include descended factors, their generic product identity, and the
specialization facts needed by G03 and G06. Keep this generic split distinct from D5 over the
finite algebra `E[u]/G`.

**Acceptance.** Execute the component splits used by the paper. Prove normalization and descent
without discarding projection fibers at zeros of an intermediate denominator. Establish coverage
of all required specialized points; do not promise pointwise uniqueness where distinct generic
components can meet. A supplied generic factor list is only a conditional consumer contract.

**Decisive tests.** Nonconstant rational denominators; nontrivial gcd; factors whose special fibers
meet; a regular point above a ramified projection fiber; exact division and normalization of units.

**Final versus conditional.** The generic arithmetic/gcd slice can close before full descent.
The group closes only when its executed split produces the descended components and specialization
coverage required by consumers. Algebraic existence of factors alone leaves the producer open.

## G02 — Full characteristic-safe squarefree decomposition

**Proposed ownership.** Generic `ArkLib/Data/Polynomial/FullSquarefreeDecomposition/` and tests.
Keep the existing Hasse-threshold implementation as a read-only specification bridge.

**Start now.** Implement a multiplicity-labelled decomposition for stored univariate polynomials.
Make the derivative-zero branch recurse through a concrete coefficientwise inverse Frobenius and
restore multiplicities correctly. Specify zero and constant inputs separately. Execute the
appendix's multiplicity-residue calculation: `u=gcd(f,f')`, `v=f/u`, `w=f'/u`, and
`q=w*(v')⁻¹ mod v` when `v≠1`. Run the bounded residue-gcd loop with exact division, reduction
of `q`, and early stop; form the weighted stratum product with a balanced product tree.
Refine overlaps with recursively returned factors by the prescribed product/remainder-tree
routing, rather than an unrestricted all-pairs gcd loop.

**Interface and dependencies.** Return factors with positive multiplicity labels, squarefreeness,
pairwise coprimality, and the product identity including the scalar unit. A generic implementation
may accept a certified executable inverse-Frobenius operation; final finite-field instantiation
must use a concrete implementation, coordinated with G07.

**Acceptance.** The actual threshold-product runtime calls the full decomposition. Prove its
retained product equal, or root-equivalent with the needed multiplicity statement, to the existing
Hasse-threshold specification. Handle multiplicities divisible by the characteristic recursively. Prove the residue identity,
loop termination/stratum invariant, and recursive tree-routing refinement. Full labelled output
alone does not establish correspondence with this named algorithm.

**Decisive tests.** Zero and constants; squarefree input; mixed multiplicities; derivative-zero
polynomials; multiplicities divisible by several powers of the characteristic; nonprime coefficient
fields where inverse Frobenius changes coefficients.

**Final versus conditional.** A decomposition parameterized by certified inverse Frobenius is a
useful generic result. Final acceptance includes the concrete finite-field operation in the
executed call graph; neither an inverse oracle nor only a radical computation closes this group.

## G03 — Regular Taylor geometry and good confluent sample

**Proposed ownership.** Generic `ArkLib/Data/MvPolynomial/RegularProjection/`; application adapter
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FastTaylor/Geometry/`; tests.

**Start now.** Define certified outputs for regular-component reduction, a linear coordinate map,
and a monic projection. Implement finite-grid selection of a direction with nonzero top homogeneous
part. Prove the weighted coefficient bounds `deg h_i ≤ b-i` for monic `h(t,z)`.

**Interface and dependencies.** Consume computed gcd/descent operations from G01 when available.
Produce `H_*`, invertible `M`, monic `h`, reduced separant `s`, and a sample `a` with a computed
constant-fiber coprimality certificate. Prove nonvanishing of the separant resultant and implement
the proved bounded-grid sample search. G07 supplies a field meeting the required guard.

**Acceptance.** The executed reduction and searches preserve the regular locus. Distinguish
proved-empty chart outcomes from unsupported guards or a failed construction. The sample is an
implementation device: returned global formulas must eventually cover all regular points, including
ramified projection fibers. A projection discriminant guard cannot replace the separant condition.

**Decisive tests.** Zero/constant equations with their explicit outcome; empty regular locus;
nontrivial regular-component removal; direction search that rejects an early grid point; a valid
sample with repeated-root projection fiber but invertible separant.

**Final versus conditional.** Projection lemmas for certified `H_*` can land before G01. The group
closes when `H_*`, the coordinate map, and good sample are computed from the equation, with the
paper's hypotheses proving the required outcomes rather than supplying them.

## G04 — Nonreduced local algebra and Newton Taylor lift

**Proposed ownership.** Generic `ArkLib/Data/Polynomial/ConfluentAlgebra/` and
`ArkLib/Data/Polynomial/TruncatedSeriesAlgorithms/`; application adapter
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FastTaylor/Local/`; tests.

**Start now.** Build canonical monic quotient arithmetic over the existing
`CPoly.BoxAlgebra.Carrier r N E`. Prove specialization to the constant fiber and nilpotence of its
parameter kernel. Add bounded-series operations over a commutative ring, including series inversion
from a certified unit constant term and integration with explicit scalar-unit certificates.

**Interface and dependencies.** Accept monic `h(a+eps,z)` and the G03 constant-fiber Bézout result.
Compute and certify the lifted separant inverse. Existing `NilpotentInverse` proves finite geometric
correction from a nilpotence certificate; derive that certificate here and implement the paper's
Newton lifting. Return local coefficients with precision and initial-jet invariants to G05.

**Acceptance.** Execute both the `r=0` algebraic Newton branch and the `r>0` zero-initial-data
linear differential correction using Newton-doubled fundamental matrices. Prove residual doubling,
all required truncated identities, and preservation of initial data. Derive invertibility of all
integration indices from the characteristic guard. Do not assume the coefficient algebra is a field
or assert an unrestricted formal-series solution.

**Decisive tests.** Mixed parameters retained while individual powers vanish; a mixed residual
whose nilpotence exponent exceeds `N`; a repeated-root constant fiber with unit separant; algebraic
and differential branches; clipped final precision; zero-precision helper behavior.

**Final versus conditional.** The box ring and finite geometric correction already exist at the
checkpoint. They do not close this group. Generic monic algebra and linear-solver lemmas can be
accepted separately; final acceptance executes the named local Newton construction and discharges
its unit/nilpotence hypotheses from the G03 output.

## G05 — Global Taylor reconstruction and chart coverage

**Proposed ownership.** Generic `ArkLib/Data/MvPolynomial/TaylorReconstruction/`; application
adapter `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FastTaylor/Global/`; tests.

**Start now.** Implement division-free affine parameter shifts and inverse shifts. Prove that
shifting into the parameter box is injective for total degree at most `L` when `N>L`. Prove weighted
monic reduction preserves total degree. Establish exact recovery interfaces for arrays of coefficients.

**Interface and dependencies.** Consume G03's monic degree bounds and G04's local coefficients.
Compute `B_0=s^(2k)` and cleared numerators in the quotient, recover their global normal forms, and
construct agreement polynomials. Use the existing rational Taylor chart and computed numerator
recurrence as semantic/uniqueness references, not as a replacement runtime path.

**Acceptance.** Return normal forms with `z`-degree below `b`, total degree at most
`L=1+2k*(Bjet-1)`, common-denominator identities in the localized coordinate ring, and coverage of
every regular degree-`<k` solution. Prove identities globally, rather than only at the chosen sample.
Do not add tail equations above coefficient `k-1`.

**Decisive tests.** A mixed parameter term whose total degree reaches the coordinate precision;
exact shift/unshift recovery; characteristic-safe shifts with input `X`-degree at least the
characteristic; reconstruction evaluated at a regular point away from the sample, including a
ramified fiber; agreement polynomial coefficient checks.

**Final versus conditional.** Shift injectivity and recovery on certified degree-bounded inputs
can close independently. Final chart coverage requires the G03/G04 producer certificates and the
executed clearing/reconstruction path, not a supplied family of global numerators.

## G06 — First-order norms and candidate producer

**Proposed ownership.** Generic `ArkLib/Data/Polynomial/NormProducts/`; application
`ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/FirstOrderNormProducer/`; tests.

**Start now.** Compute multiplication matrices and determinants for norms on monic polynomial
algebras. Refine the norm product to its semantic definition on certified component inputs. Develop
the multiplicity argument connecting nonuniversal agreements to roots of that actual product.

**Interface and dependencies.** Implement the universal-agreement loop using G01's gcd/descent operations; consume G05's chart,
and G02's multiplicity-labelled decomposition. Return well-formed candidate towers for existing
preprocessing and materialization. Coordinate field setup with G07.

**Acceptance.** Implement `firstOrderNormCandidates` from the chart and received pairs, including
actual norms, their product, full decomposition, and threshold selection. Prove `|U_b| ≤ k-1 < A`
before using natural subtraction in `A-|U_b|`. Derive unconditional wanted-point coverage for the
computed towers. Preserve all regular projection fibers throughout descent and specialization.

**Decisive tests.** Universal and nonuniversal agreements in the same input; repeated norm roots;
positive-characteristic multiplicities; components meeting in a special fiber; ramified regular
points; extension-defined parameters yielding base-field messages; a nontrivial symbolic first-order
run with fallback visibly excluded.

**Final versus conditional.** Matrix norm correctness on supplied components is an independent
slice. The group closes when the executed component split, norm/decomposition path, and tower
construction supply coverage; a norm oracle or supplied component partition remains conditional.

## G07 — Explicit finite fields and deterministic prefixes

**Proposed ownership.** Generic `ArkLib/Data/FiniteField/ExplicitConstruction/`; application
`ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/ConstructedFields/`; tests.

**Start now.** Build concrete stored quotient-field arithmetic and embeddings from a computed
irreducible polynomial. Implement the deterministic candidate prefix with a distinctness proof.
Separate the quadratic center-field construction from the general bounded-degree extension needed
by Rojas. Agree on inverse-Frobenius instances with G02.

**Interface and dependencies.** Return the actual field representation, executable arithmetic,
irreducibility certificate, base embedding, and a prefix meeting the requested cardinality bound.
The higher-order constructor chooses the least sufficient allowed extension degree over the current
center field. Consumers use these outputs, not a supplied basis package.

**Acceptance.** Execute prime-field center selection when sufficient and construct the quadratic
center field otherwise. Construct the required higher-order extension and prefix. Reuse the existing proved characteristic-two dispatch exclusion (`n≤2<N_*`)
and connect it to the eventual concrete Rojas call path. Audit the arithmetic dictionaries for hidden field enumeration or
classical witness extraction.

**Decisive tests.** Prime-field-only path; genuinely needed quadratic extension; nontrivial base
embedding; least-degree boundary; prefix distinctness; inverse Frobenius over a nonprime field;
characteristic-two dispatch reaches fallback before Taylor/Rojas.

**Final versus conditional.** A quotient arithmetic package conditional on irreducibility is a
useful slice. Final acceptance computes that polynomial/certificate and required prefix. The unused
characteristic-two Rojas shift construction can remain deferred only after its unreachability proof.

## G08 — System-to-resultant Rojas producer

**Proposed ownership.** Generic `ArkLib/Data/Polynomial/Rojas/Producer/` and tests. Existing
Rojas extraction/representation owners remain read-only; request their adapters through the coordinator.

**Start now.** Fix a stored sparse-system input contract. Implement the prescribed toric generalized
characteristic/resultant construction and extraction of its perturbation coefficient. Prove the
first system-dependent identity on a small nontrivial system before broadening the producer.

**Interface and dependencies.** Consume an explicit coefficient field and G07's candidate
field/prefix. Produce the polynomials and coordinate data consumed by existing representation
extraction, with factorization and isolated-root coverage derived from the original system.
Implement deterministic specialization and Rojas's internal coordinate-map steps.

**Acceptance.** The executed call graph contains the named resultant/perturbation algorithm,
specializations, and representation construction. Its coverage theorem has no resultant oracle,
supplied solution list, or missing backend-correctness premise. Do not add the superseded
affine-to-torus wrapper; internal Rojas coordinate specializations remain part of the algorithm.

**Decisive tests.** Isolated wanted roots with zero coordinates; an unrelated positive-dimensional
component; specialization rejection and later success; extension-defined isolated roots; returned
representations checked against the original equations. Small exhaustive reference computations
are permitted in tests only.

**Final versus conditional.** A certified perturbation coefficient or one supported system family
is a bounded slice. An arbitrary concrete exhaustive solver satisfying the downstream interface
does not close the group. Final acceptance proves the prescribed producer's general isolated-root
coverage on the guarded domain.

## G09 — Higher-order systems, selection, and candidates

**Proposed ownership.** Generic `ArkLib/Data/Graph/GabberGalilConstruction/` and
`ArkLib/Data/LinearAlgebra/IndependentSelection/`; application
`ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/HigherOrderProducer/`; tests.

**Start now.** Construct direct affine systems with exactly `r+1` variables and equations:
`h=0` and `r` selected agreements. Implement all-`r`-subsets as the default selection mode. In a
separate generic slice, execute the Gabber–Galil graph and prove its graph interpretation, preserving
loops and edge multiplicities.

**Interface and dependencies.** Consume G05 charts and G08 representations over G07's fields.
Supply selected systems with wanted-point nonsingularity certificates. The fixed-gap mode includes
`ceil(sqrt(n))^2` padding, labels, graph powering until the normalized second eigenvalue is below
`epsilon/12`, and edge tuples with dummy/duplicate-label rejection.

**Acceptance.** Prove tangent/cotangent spanning at wanted regular points and the independent-selection
argument. Prove the spectral/expansion certificate for the actual executed graph. Execute both
selection modes and connect the concrete Rojas outputs to recovery with full wanted-point coverage.
There are no `K-k` tail rows and no extra torus coordinates.

**Decisive tests.** Default subset mode; paired mode exercised separately; padded vertices;
loops/multiple edges; duplicate and dummy labels rejected; exactly `r+1` equations; zero coordinates;
wanted isolated root accompanied by an unrelated positive-dimensional component.

**Final versus conditional.** The all-subsets path can close first. The fixed-gap branch remains
open until it executes the specified graph and independent selection; silently delegating it to
all subsets is not completion. Conditional system coverage becomes final after G08 is instantiated.

## G10 — Specialized zeroth-order decoder

**Proposed ownership.** Generic `ArkLib/Data/Polynomial/FastGSConstruction/` for missing reusable
interpolation machinery; application
`ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/ZerothOrderDecoder/`; tests.

**Start now.** Implement the named fast GS interpolation construction and its certificate.
Develop the leading-coefficient/resultant obstruction and batched regular-center search over a
certified deterministic prefix. Keep this program separate from the general-order decoder.

**Interface and dependencies.** Consume G01 content removal and gcd-based repeated-`Y`-factor
removal over the rational function field. Reuse G02 only where its coefficient-field contract
applies; a rational function field is not automatically perfect. Use G07 for center fields and prefixes,
the existing `OrdinaryQuotientDecoder` Newton implementation and agreement recovery.
This group need not wait for G04's multivariate differential lift. Factor and obstruction contracts must retain the specialized algorithm's coverage.

**Acceptance.** Execute one regular-center selection, root-free Newton lifting in the squarefree
univariate quotient algebra, shift to global message coefficients, and `RecoverAgreement`. Prove
coverage, agreement soundness, duplicate freedom, and no failure under fixed-gap inputs. Expose its
own public exact-output theorem. A bounded fallback runs only under its explicit guard.

**Decisive tests.** A nontrivial symbolic zeroth-order run; rejected center followed by a selected
regular center; center-field extension genuinely needed; repeated `Y`-factors/content removed;
quotient lifting without root extraction; duplicate candidate images; fallback boundary. Assert
intermediate branches so a passing test cannot merely exercise fallback.

**Final versus conditional.** Interpolation and center-search slices can close independently.
Existing `OrdinaryInterpolation` executes Lee–O'Sullivan with a verified fast
Mulders–Storjohann reducer; it is not merely dense elimination. Reuse those correctness facts and
the existing quotient Newton path, but establish the prescribed interpolation-basis algorithm
correspondence. A generic loop over all centers is not the single-center program.
Final acceptance includes the specialized executed path and exact-output theorem; the list-size
corollary belongs to the coordinator's final mathematical bridge.

## Coordinator closeout after group integration

The ten groups do not independently own the public global driver. After their accepted outputs
are integrated, the coordinator instantiates the constructors in the separant-chain loop, proves
regular-center selection and all dispatch cases, removes missing-backend and supplied-coverage
premises from public exactness, and adds the relevant list-size corollaries. See the
[shared contracts](contracts.md) for handoff obligations and the [workflow](workflow.md) for review
and validation. Report conditional slices and excluded runtime proofs explicitly at every checkpoint.
