# Ring Switching

Ring switching is a family of proof reductions that change the coefficient algebra used to
represent or verify a claim. ArkLib has two construction folders, `Packing/` and `Lift/`.
Hachi's deterministic trace relocation is a further packing protocol, implemented in
`Commitments/Functional/Hachi/TraceHead/` using the fixed-subring algebra.
The [model and coverage audit](../audits/ring-switching-model-coverage.md) records the exact
relations, source versions, security assumptions, and implementation gaps.

## The constructions

| Construction | Input and output | Interaction and security boundary |
|---|---|---|
| DP24/Binius and Flock coordinate packing | A scalar evaluation on a base-field table becomes an opening of its packed table. | Prover supplies partial values; verifier checks their weighted reconstruction, batches their coordinates, runs sumcheck, then opens the packed polynomial. |
| Generalized coordinate packing | A full family of evaluations over E becomes one packed opening over P, or an extension supporting the opening. | E and P are separately based algebras over a common base; slices are publicly derived, then randomly batched. |
| Hachi §3.1 trace relocation | A subfield-valued scalar evaluation becomes a cyclotomic-ring evaluation. | One ring-element message and a scaled trace check; no challenges or sumcheck in this head. The downstream Hachi chain uses CWSS and a short-collision escape. |
| HMZ25 / Hachi §4.3 quotient lift | A linear relation modulo a monic polynomial becomes a checked evaluation of a lifted polynomial identity. | Commit to a lifted witness, then sample a scalar challenge. ArkLib proves the field-target specialization with CWSS and a collision escape. |

Sources: [DP24](../papers/DP24.md),
[generalized note](../papers/RSG.md),
[Flock Appendix B](../papers/BRW26.md), [Hachi](../papers/NOZ26.md), and
[HMZ25](../papers/HMZ25.md).

## Common packing algebra

The coordinate core in `Packing/Coordinates.lean` uses a commutative base ring B and finite bases
`β : Basis I B P`, `ε : Basis J B E`. Packing turns an I-indexed block of B-coefficients into
one P-element. The opening algebra E and packing algebra P need no embedding between them.
Neither an integral-domain condition nor a power-of-two rank is needed for this algebra.

For base-valued tables `f_i(y)` and an opening point `r : E^m`, expand the public Boolean weights
`eq(r,y)` in the ε-basis. Each claimed E-value `α_i` then has B-coordinates. Transpose that
coordinate matrix and pack each row using β. Both basis inverse laws give a linear equivalence
between the original family and the resulting P-valued slices. The slice identities are inner
products against the packed table. Random batching and sumcheck subsequently check them.

`Packing/Polynomial.lean` proves both packing inverses, and `Packing/Relations.lean` proves
the full-family/slice equivalence over commutative rings. A compatible challenge algebra C
can receive batched packed values; injectivity of `P → C` is required separately when
transporting the separation bound in `Packing/Batching.lean`.

`Packing/Multiplier.lean` evaluates the public multilinear multiplier using the actual
opening-basis multiplication matrices, whose B-valued entries can be mapped to an independent
challenge algebra C. The proof allows a nonmultiplicative final coordinate observation and
certifies one matrix-vector action per retained variable, excluding preprocessing. It needs
no embedding of E into C.

An optional tensor carrier `E ⊗[B] P` mathematically represents the same transport; a
formal carrier-equivalence adapter is separate from these coordinate proofs. DP24 specializes
to `E = P = L` and `L ⊗[B] L`. The legacy `RingSwitchingProfile` has a single L and two
coordinate directions. Its repaired laws require two-sided decomposition/recomposition inverses
and agreement of the embeddings on B. They imply coordinate linearity and pure-tensor formulas.
Rows recover the original partial values; columns retain packed values for batching. The
[coverage audit](../audits/ring-switching-model-coverage.md) records counterexamples to the former
one-sided laws and the former swapped coordinate uses.

## Claims and security must stay explicit

The generalized note starts with a **full family** of public evaluations. DP24 and Flock start
with **one scalar claim**, so they need a prover message and a checked reconstruction equation
before the full-family tail. Flock's quirky claims use Lagrange/Boolean product weights instead
of ordinary equality weights. Hachi §3.1 uses monomial coefficients and monomial weights;
transporting it to Boolean evaluation tables requires a proved basis change and a matching
commitment and norm interpretation.

Hachi's trace is unnormalized:

```text
Tr_H(ψ(a) · σ₋₁(ψ(b))) = (d/k) · ⟨a,b⟩.
```

The verifier must keep this factor or use an explicitly normalized trace. Sound read-back needs
scalar cancellation. The trace-head implementation proves that d/k is a unit in R_q under
its odd-characteristic and power-of-two assumptions, retaining the actual trace equation.

Field batching and sumcheck obtain root-count bounds from their challenge distribution. A
commutative ring alone does not justify `degree / |ring|`. HMZ additionally uses Galois rings with
exceptional challenge sets, whose distinct elements have invertible differences; ArkLib's `Lift`
security currently targets fields. `PackedCommitment` records an oracle relation and honest
coverage. Functionality is a separate security proposition; `ExactPackedCommitment` adds its
proof. Flock needs its list/OOD binding accounting, and Hachi needs
norm-conditioned binding with a collision escape. An identity commitment is only an algebraic
example.

## Implementation boundaries

The separately based coordinate core, polynomial round trips, ring-valid read-back, and
fixed-family batching strategies are implemented. `Packing/FullFamily/` implements the checked
slice-message variant as an actual reduction to a sumcheck relation, with state-uniform perfect
completeness and exact-extractor worst-case knowledge soundness. The phases and completeness
retain a base commitment relation on the same oracles; only the randomized bounds require
functionality. `Packing/ScalarHead/` proves concrete DP24 and Flock
scalar heads, including lossless prefix/suffix layouts and the quirky interpolation-weighted
case. Their one-message checks, original-source extractors, completeness and zero-error knowledge
contracts are proved. `ScalarFamily/` composes those actual heads with both checks, exact
extractors and state-aware completeness. `ScalarOpening` sends two consecutive head messages:
original partial values followed by redundant checked slices. This documented composition variant
differs from the single-family message in DP24 and Flock. A permanent client uses a genuine two-candidate
commitment oracle throughout execution. Randomized list-binding security is a separate contract.

`Packing/Tail/` implements the actual product-sumcheck rounds, finite-sequence composition and
terminal multiplier check. `FullFamilyOpening` and `ScalarOpening` compose the full-family or
original scalar head with this tail and end exactly at the same commitment's C-valued opening
relation. Their proved state-aware completeness uses the base commitment; fixed-prefix knowledge
requires its explicit functionality proof and finite-domain challenges, with injective P→C
transport at the family head. The batching challenge retains its strategy error and each of the
m scalar challenges has error `2/|C|`. `Tail/Accounting.lean` proves their exact aggregate
`batching error + m * (2/|C|)`. The final message contributes no challenge error and
forwards the packed value itself even when the multiplier is zero.

`Packing/Opening.lean` defines `PackedOpening` on precisely that commitment's `evalRel`.
Its actual append wrapper composes supplied worst-case knowledge contracts with the exact
extractors and knowledge states; arbitrary effects in the downstream verifier are supported.
Its separate completeness theorem requires guarded verification, completeness from every seam
state and the stated first-message or pure-output condition. The ambient oracle is explicit:
the concrete packing prefixes use the empty ambient oracle. Concrete scalar and full-family
clients close through a verifier that reads the actual polynomial oracle and checks its
evaluation. A separate nonempty-ambient fixture proves an accepted front executes the downstream
state change, while a rejected front prevents it. This interface does not itself prove the
security of an arbitrary downstream PCS.

Permanent tests include a nonconstant family over `ZMod 6`, unequal ranks, actual rejection in
the verifier and full reduction, zero retained variables, rank-one batching, incompatible GF(4)
and GF(8) algebras, and an enlarged GF(9) challenge algebra with nonzero batching error.

The legacy DP24 verifier now forwards the packed value itself and aborts failed batching, loop,
and final checks. Its repaired profile laws and coordinate directions have permanent regressions,
including an honest nonzero source previously rejected by the verifier. Two auxiliary knowledge
states were corrected: a sampled accidental root need not make the previous claim true, and the
final state must retain its structural witness invariant. These operational and algebraic fixes
now support proved ring-valid final-leaf completeness and zero-error knowledge soundness.
The legacy batching/loop and general-composition admissions remain separate.

The actual FRI-Binius initial compatibility relation now has proved uniqueness and honest coverage.
The adapter `FRIBinius/RingSwitchingCommitment.lean` supplies the generic base commitment, its
separate functionality proof, exact specialization and legacy functionality using that same
relation, oracle and honest codeword constructor. A concrete
GF(16) client runs the complete generic full-family and sumcheck pipeline on the production
oracle, with its original source relation and the same packed opening endpoint. It instantiates
exact-extractor knowledge and state-uniform completeness, and a false original family rejects
for every later tail transcript. Separate commitment tests distinguish two nonconstant witnesses. The downstream interleaved
FRI-Binius opening proofs remain separate.
The proved `Append/Knowledge.lean` specialization composes a deterministic guarded first
verifier with an arbitrary right verifier, using worst-case-per-prefix component knowledge
bounds. Its averaged wrappers do not accept averaged-only component premises. `Sequential/KnowledgeNary.lean` extends this to actual finite guarded sequences, with explicit
recursive extractors, knowledge states and canonical component error indexing. The unrestricted
shared RBR knowledge-composition theorem remains admitted.

Hachi's §3.1 trace head now proves monomial packing, actual one-message execution, same-opening
CWSS and completeness. Every original scalar polynomial has honest source coverage by the real
committer applied to its packed coefficients, with the existing weak-opening norm bounds. These
proofs use the fixed subring as a ring and do not depend on its admitted field identification.
The semantic head remains noncomputable with the existing ring/trace infrastructure; integration
into a scalar Scheme is separate. The §3.2/§4.5 same-field Z recombination has a false
soundness pull-back; it needs a proved protocol repair, not an instance of the existing carrier.
See the [Hachi paper page](../papers/NOZ26.md) for the current proof and composition boundaries.

## Main ArkLib touchpoints

- [`RingSwitching/Basic.lean`](../../../ArkLib/ProofSystem/RingSwitching/Basic.lean) — family taxonomy.
- [`Packing/Coordinates.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Coordinates.lean),
  [`Polynomial.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Polynomial.lean),
  [`Relations.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean), and
  [`Batching.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean) — independent
  finite-free algebras, polynomial transport, full-family read-back, and fixed-family separation.
- [`Packing/Multiplier.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Multiplier.lean) —
  multiplication-matrix evaluator, correctness and instrumented action count.
- [`Packing/FullFamily/Phase.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/FullFamily/Phase.lean),
  [`Completeness.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/FullFamily/Completeness.lean), and
  [`Knowledge.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/FullFamily/Knowledge.lean) — actual
  checked-message phase, execution, state-uniform completeness, and fixed-prefix knowledge bound.
- [`Packing/ScalarHead/Layout.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Layout.lean)
  and [`Quirky.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Quirky.lean) — concrete
  scalar-source layouts; `Phase.lean` and `Security.lean` prove the actual checked head.
- [`Packing/Tail/FullFamilyOpening.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Tail/FullFamilyOpening.lean)
  and [`ScalarOpening.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Tail/ScalarOpening.lean) —
  actual full-family/scalar reductions through sumcheck to the same packed opening relation.
- [`Packing/Opening.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Opening.lean) —
  actual downstream append on the same packed evaluation relation.
- [`Hachi/TraceHead/Basic.lean`](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Basic.lean) — actual
  monomial trace head, honest committer coverage, completeness and CWSS.
- [`Packing/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean) and
  [`Packing/General.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean) — existing profile and DP24 pipeline.
- [`Packing/SumcheckPhase.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean) — residual opening and failure-handling obligations.
- [`Lift/Presentation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean) and
  [`Lift/Reduction.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean) — quotient algebra and field-target CWSS.
- [`Subfield/TraceInnerProduct.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield/TraceInnerProduct.lean) — Hachi's scaled trace pairing and packing injectivity.
- [`Hachi/RingSwitch/Reduction.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean) — Hachi lift instance, digit commitment, and short-collision boundary.
- [`RoundVerifiers.lean`](../../../ArkLib/ProofSystem/RingSwitching/RoundVerifiers.lean) and
  [`Transport.lean`](../../../ArkLib/ProofSystem/RingSwitching/Transport.lean) — shared round shapes and evaluation transport; neither establishes protocol equivalence by itself.
