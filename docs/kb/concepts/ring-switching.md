# Ring switching

Ring switching changes the coefficient algebra used to represent or verify a polynomial claim.
ArkLib separates coordinate packing in `ProofSystem/RingSwitching/Packing/`, quotient lifting in
`Lift/`, and Hachi's deterministic trace head in `Commitments/Functional/Hachi/TraceHead/`.
The [coverage audit](../audits/ring-switching-model-coverage.md) gives source versions, equations
and detailed proof boundaries.

## Construction map

| Construction | Input → output | Interaction |
|---|---|---|
| [DP24/Binius](../papers/DP24.md), [Flock](../papers/BRW26.md) | Scalar claim on a base-valued table → packed-polynomial opening | Partial values, weighted reconstruction, coordinate batching and sumcheck |
| [Generalized packing](../papers/RSG.md) | Full family of evaluations over E → packed opening over P or a compatible extension C | Coordinate slices, batching and sumcheck |
| [Hachi §3.1](../papers/NOZ26.md) | Fixed-subring scalar evaluation → cyclotomic-ring evaluation | One ring-element message and a scaled trace check |
| [HMZ/Hachi lift](../papers/HMZ25.md) | Linear equality modulo a monic polynomial → evaluated lifted identity | Commitment, scalar challenge and commitment-consistent output relation |

## Shared packing algebra

Take finite bases `β : Basis I B P` and `ε : Basis J B E` over a commutative ring B. The
packing and opening algebras P and E may have different ranks and need no embedding between them.
Coordinate transposition gives a B-linear equivalence `T : (I → E) ≃ₗ[B] (J → P)`.
For arbitrary finite tables `v : Y → P` and weights `a : Y → E`, it satisfies

```text
T(i ↦ Σ_y [v(y)]β,i • a(y)) = (u ↦ Σ_y [a(y)]ε,u • v(y)).
```

[`FiniteObservation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/FiniteObservation.lean)
proves this identity, including empty Y and rings with zero divisors. Boolean interpolation and
Hachi monomial evaluation instantiate it through their concrete layouts. The tensor
carrier uses rows for partial evaluations and columns for packed slices.

[`CheckedObservation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/CheckedObservation.lean)
shares deterministic scalar reconstruction. An adapter supplies an exact source/output witness
equivalence, an unconditional honest-evaluation identity, and correspondence with its actual guard
and relations. Read-back preserves the supplied commitment/witness predicate. The generic scalar
head, Binius tensor head and Hachi trace head use these common lemmas.

Hachi's weights are monomials at fixed-subring points. Its trace is unnormalized:

```text
Tr_H(ψ(a) · σ₋₁(ψ(b))) = (d/k) · ⟨a,b⟩.
```

The trace head proves d/k is a unit and retains the same norm-conditioned weak opening. Its
completeness and CWSS proofs use the fixed subring as a ring, independently of its unfinished
identification with an external finite field.

## Component guide

| Module under `Packing/` | Role |
|---|---|
| `Coordinates`, `Polynomial`, `Relations` | Independent bases, polynomial packing inverses and full-family/slice equivalence |
| `Profile`, `ProfileCoordinates`, `ProfileLayout`, `BatchingAlgebra` | Tensor representation, tensor DP24 table layout and scalar/round-zero relation correspondence |
| `ScalarHead/` | DP24 packed-prefix, Flock packed-suffix and quirky Lagrange/Boolean reconstruction |
| `FullFamily/`, `ScalarFamily/` | Checked-slice phase and its composition with a scalar head |
| `Batching`, `FullFamily/Separation` | Fixed-family and functional-compatibility separation bounds |
| `Multiplier` | Multiplication-matrix evaluation of the public multiplier's multilinear extension |
| `Tail/` | Degree-two product sumcheck, deterministic terminal and composed opening reductions |
| `PackedCommitment`, `ExactCommitment` | Oracle relation and honest coverage; separate functionality specialization |
| `Opening` | Downstream reduction contract on precisely the same commitment's `evalRel` |

The matrix evaluator maps B-valued entries to C without an `E → C` embedding or a multiplicative
coordinate observation. Its instrumented count is one matrix-vector action per retained variable,
excluding preprocessing.

`FullFamilyOpening` and `ScalarOpening` end at a C-valued opening of the same packed polynomial.
The checked-slice variant sends a message that the generalized note derives publicly.
`ScalarOpening` sends partial values and then checked slices, whereas DP24/Flock use one family
message. Binius's tensor head retains its one tensor message and vector challenge before its own
interleaved FRI/sumcheck suffix.

## Security and implementation boundaries

Deterministic algebra and completeness use `PackedCommitment` without uniqueness. The randomized
knowledge bounds require its explicit `Functional` property, finite-domain challenges, and
injective compatible `P → C` transport at the family head. The generic tail's aggregate error is
`batching error + m * (2/|C|)`. Its terminal contributes no challenge error and forwards the packed
value itself even when the public multiplier is zero. Rejection is absorbing.

The generic opening pipelines have proved state-aware completeness and worst-case-per-prefix
knowledge contracts through guarded binary and finite-sequence composition. `PackedOpening`
requires the downstream verifier's own worst-case contract on `pc.evalRel`; completeness also
requires guarded verification, correctness from every seam state and the stated prover seam
condition. Concrete packing prefixes use the empty ambient oracle.

Binius's real codeword commitment supplies honest coverage and unique-distance functionality to
the generic adapter and the tensor batching head. Tensor batching and the profile-based terminal
have proved completeness and knowledge contracts. The profile-based loop and unrestricted
composition retain admissions. FRI-Binius's final verifier has execution and rejection proofs;
its downstream interleaved security and full completeness assembly remain partly admitted.

Flock's ordinary and quirky heads are implemented; a production Flock PCS and list/OOD security
are separate. Hachi uses CWSS with norm-conditioned collision escape. Its semantic trace head
is not packaged as an executable scalar Scheme,
and its §3.2/§4.5 same-field recombination lacks sound read-back. The quotient lift proves the
field-target CWSS specialization; HMZ exceptional-set security over Galois rings is outside that
contract. See the paper pages and audit for the precise source correspondences.
