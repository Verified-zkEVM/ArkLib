---
kind: paper
bibkey: BGKLSW26
title: "BitZ: proofs and commitments in arbitrary rings through binary fields"
year: 2026
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/2141
source_metadata: ../sources/BGKLSW26/metadata.yml
status: seeded
related_modules:
  - ArkLib/Commitments/Functional/BitZ/ExponentLift.lean
  - ArkLib/Commitments/Functional/BitZ/Round1.lean
  - ArkLib/Commitments/Functional/BitZ/Round2.lean
  - ArkLib/Commitments/Functional/BitZ/OutOfDomain.lean
  - ArkLib/Commitments/Functional/BitZ/Bitification.lean
  - ArkLib/Data/MvPolynomial/PrimeFingerprint.lean
  - ArkLib/Data/MvPolynomial/PrimeFingerprintProbability.lean
  - ArkLib/Data/MvPolynomial/LinearMvExtension.lean
  - ArkLib/ToMathlib/MvPolynomial/CoeffBound.lean
---

# BGKLSW26

## At A Glance

BitZ commits to a bit decomposition over a binary field and proves linear claims over an
arbitrary finitely generated ring. ArkLib provides the exponent lift, the algebraic implications
for Rounds 1 and 2 of Construction 4.4, the out-of-domain collision bound of Lemma B.2, and the
bitification of a witness over a finitely generated ring.
These are supporting results for the protocol; there is no BitZ `Commitment.Scheme` instance or
composed round-by-round knowledge-soundness theorem.

The statement numbering below follows the **4 October 2026 ePrint revision**. The implementation
extends several algebraic statements to more general rings and keeps counting separate from
sampling.

## What ArkLib Uses From This Paper

| Paper statement | Lean interface | Scope |
| --- | --- | --- |
| Phase 3 of Construction 4.4; no-overflow argument in Theorem 4.7 | `BitZ.prod_bitFactor_eq_pow`, `BitZ.prod_bitFactor_eq_pow_iff_of_lt_orderOf`, `BitZ.prod_bitFactor_eq_pow_iff` | A bit-dependent grand product equals the generator raised to the integer dot product. Below the generator's order, equality of powers is equivalent to equality of the integers. |
| Lemma 4.8 | `MvPolynomial.avg_zeroCountMod_div_le`, `MvPolynomial.avg_zeroCountMod_div_le_logb` | The count separates primes killing every coefficient from ordinary Schwartz–Zippel zeros. |
| Sampler of Lemmas 4.3 and 4.8 | `MvPolynomial.modPointSample`, `MvPolynomial.prEvent_fingerprint_eq_average`, `MvPolynomial.prEvent_fingerprint_le` | Native `Pr{…}` bounds for a uniform prime followed by a uniform point in that prime's field. |
| Round 1; Theorem 4.7 proof, equations (43)–(44) | `BitZ.claimPoly_ne_zero`, `BitZ.totalDegree_claimPoly_le`, `BitZ.natAbs_coeff_claimPoly_le`, `BitZ.prEvent_claim_le` | For a fixed false witness claim and a bounded prover message, the reduced claim succeeds with at most the fingerprinting error. |
| Honest Round 1 message bound | `BitZ.natAbs_coeff_honestMessage_le` | The honest message meets the verifier's bound `T · ℓ · N²`; the difference polynomial has bound `2 · T · ℓ · N²`. |
| Round 2; Theorem 4.7 proof, equation (45); Remark 4.5 | `BitZ.sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow` | Range checks, grand products and the verifier's weighted-sum check imply the tensor claim over any commutative target ring. |
| Lemma B.2 | `BitZ.card_collisionSet_le`, `BitZ.prob_not_injOn_eval_le` | A fixed list of multilinear polynomials has collision probability at most `choose(Lδ, 2) · (2^r - 1) / |F|` at the structured OOD point. |
| Definition 4.9 (standard bitification matrix, closure); equation (46) | `BitZ.boundedCombos`, `BitZ.bitMatrix`, `BitZ.bitMatrix_mulVec_mem`, `BitZ.exists_bitification`, `BitZ.coeffBits`, `BitZ.bitMatrix_mulVec_coeffBits` | For every vector of bits, `L · g` has entries in the bounded set of sums `∑ⱼ hⱼ · γⱼ` with `hⱼ < 2^B`; every vector with entries in that set is `L · g` for the bits `coeffBits` of its coefficients. The family `γ` need not be injective. |
| Lemma 4.12; equation (47) | `Matrix.dotProduct_map_mulVec`, `BitZ.bitWeights`, `BitZ.bitMatrix_map_transpose_mulVec`, `BitZ.exists_witness_iff_exists_bits` | A ring homomorphism moves `L` across the inner product, the weights of the bitified claim are `v ⊗ (1, …, 2^{B-1}) ⊗ ψ(γ)`, and bitification preserves satisfiability of the claim. |

For Round 1, `T = choose(D + k, k)` counts monomials of total degree at most `D` in `k`
variables, and `ℓ` is the number of bits. The difference polynomial has degree at most `2D`.
Its nonvanishing follows from the false claim after applying the canonical ring homomorphism.

Writing `M = 2 · T · ℓ · N²`, the native Round 1 probability bound is
`floor(log_{qmin} M) / |P| + 2D / qmin`. The `_logb` counting form gives the paper's
`κ₀ = log₂ M / (floor(log₂ qmin) · |P|) + 2D / qmin`.

## Main ArkLib Touchpoints

- [`ExponentLift.lean`](../../../ArkLib/Commitments/Functional/BitZ/ExponentLift.lean) owns
  the bit-factor identity and its general-ring and finite-field converses.
- [`Round1.lean`](../../../ArkLib/Commitments/Functional/BitZ/Round1.lean) owns the claim
  polynomial, honest-message bound, reduction at a sampled point, and fixed-witness error
  bounds. Lifts along the canonical map are supplied pointwise; the map is an arbitrary ring hom.
- [`Round2.lean`](../../../ArkLib/Commitments/Functional/BitZ/Round2.lean) owns the deterministic
  implication from the grand products and verifier check to the reduced tensor claim.
- [`OutOfDomain.lean`](../../../ArkLib/Commitments/Functional/BitZ/OutOfDomain.lean) instantiates
  the existing polynomial point-collision bounds with `LinearMvExtension.powAlgHom`.
- [`Bitification.lean`](../../../ArkLib/Commitments/Functional/BitZ/Bitification.lean) owns the
  standard bitification matrix, its closure, the explicit bitified weights and the equivalence of
  the original and bitified claims; `Matrix/DotProduct.lean` supplies the ring-homomorphism step.
- [`PrimeFingerprint.lean`](../../../ArkLib/Data/MvPolynomial/PrimeFingerprint.lean) contains
  counting bounds without a sampler dependency;
  [`PrimeFingerprintProbability.lean`](../../../ArkLib/Data/MvPolynomial/PrimeFingerprintProbability.lean)
  supplies the sampling bridge. See the fingerprinting provenance in [CHA24](CHA24.md).
- [`LinearMvExtension.lean`](../../../ArkLib/Data/MvPolynomial/LinearMvExtension.lean) owns
  coefficient recovery, nonvanishing and injectivity of `powAlgHom` on multilinear polynomials.
- [`CoeffBound.lean`](../../../ArkLib/ToMathlib/MvPolynomial/CoeffBound.lean) bounds coefficients
  of integer-polynomial products using the existing `Finsupp.degreeLEFinset` monomial count.
  [`Nat/BitSum.lean`](../../../ArkLib/Data/Nat/BitSum.lean) and
  [`Matrix/DotProduct.lean`](../../../ArkLib/Data/Matrix/DotProduct.lean) own the range and injectivity
  of binary encoding (`Nat.eq_of_sum_pow_two_mul_eq`) and the tensor-pairing rearrangement.

Acceptance clients under
[`ArkLibTest/Commitments/Functional/BitZ/`](../../../ArkLibTest/Commitments/Functional/BitZ/)
exercise the range hypotheses and their failure at the overflow boundary, round bounds,
semiring injectivity, the OOD theorem applied to CompPoly evaluation tables, and the bitification
range at `2^B` with executable runs of the matrix, digits and weights, and the semiring case
`S = R = ℕ`. The separate
[sampler regression](../../../ArkLibTest/Data/MvPolynomial/PrimeFingerprintProbability.lean)
distinguishes the intended distribution from uniform sampling over all prime/point pairs.
The clients pin headline theorem dependencies to `propext`, `Classical.choice` and `Quot.sound`.

## Generalizations and Conventions

- The paper uses a binary field. The exponent identity works in any commutative ring; its
  converse uses the element's order. The finite-field specialization accepts a generator of
  `Fˣ`. Round 2's target ring can be `ℤ`, covering Remark 4.5.
- The no-overflow condition `ℓ₁ · (q - 1) < |F| - 1` is sufficient and weaker than the paper's
  bound using `ℓ₁ · max P`. The inequality must be strict.
- The `Nat.log` fingerprint bound is an integer floor and is stronger than the paper's real-log
  expression. The `_logb` counting variants expose the paper's `κ₀` expression. Empty prime sets
  are permitted by counting; sampling requires a nonempty sample type.
- Sample `q` uniformly from `P`, then `α` uniformly from `Fin k → ZMod q`. Uniform sampling over
  all dependent pairs instead weights `q` by `q^k` and changes the distribution.
- `powAlgHom` substitutes `Xᵢ ↦ X^(2^i)` with zero-based indices. Multilinearity prevents exponent
  collisions, giving coefficient recovery and injectivity over a commutative semiring.
  At `r` variables the univariate degree is at most `2^r - 1 = ℓ/ν - 1`.
- The OOD challenge is uniform over all of `F`. Lemma B.2's choose-two bound implies Theorem
  B.1's coarser `Lδ²` bound. The polynomial candidate set is fixed before this challenge.
- A packed vector supplies the Boolean-cube **values** of its MLE. Use CompPoly's existing
  `CMlPolynomialEval.eval_eq_MvPolynomial_MLE` bridge when passing computational tables to the
  polynomial theorem; do not treat those entries as a coefficient vector.
- The bitification matrix has columns indexed by `(i, k, j)`, as `bits(f)` in equation (46). The
  digits of a coefficient `h` determine it only below `2^B`, which is the range of the bounded set.
  The algebra needs no subtraction, so it holds over commutative semirings.

## Open Formalization Gaps

- Construction 4.13 and Theorem 4.15: the tensor weights of Remark 4.14, the soundness error and
  honest messages of the general-ring reduction. Bitification itself (Definition 4.9, Lemma 4.12)
  is covered above. This scope is tracked in
  [issue 1331](https://github.com/Verified-zkEVM/ArkLib/issues/1331).
- Source/target relations, named interaction verifiers, rejection behavior, honest execution,
  the knowledge-state function and extractor for Construction 4.4.
- The transition from a fixed witness to an existential witness. Unique decoding, or OOD
  separation together with the prover's OOD answer, must fix the candidate before the later
  prime/point challenge. The OOD polynomial bound leaves code-list cardinality and injective
  encoding/packing as explicit obligations.
- Composition with the grand-product reduction and the opening protocol, retaining the round
  errors in order: `κ_OOD` when Round 0 runs, then `κ₀`, then the deterministic Round 2 step and
  downstream protocol errors.
- A uniform global error bound across admissible public inputs. The paper's initial
  `θ(P, M, ℓ)` and `κ₀` depend on the public input through the lift bounds.

## Source Access

- [Public ePrint paper and revision history](https://eprint.iacr.org/2026/2141)
- [Source metadata](../sources/BGKLSW26/metadata.yml)
- [Repository bibliography](../../../blueprint/src/references.bib)

## Computability audit

The supporting theorems do not yet constitute an executable BitZ protocol. The cleanup audits
ordinary callers outside `noncomputable section`, and records these results (ratings follow
[make-computable](../../skills/make-computable.md)):

| Declaration | Kind / rating | Status and evidence or blocker |
| --- | --- | --- |
| `LinearMvExtension.bitExpo` | Leaf / 2 | Executable after replacing classical support filtering with a decidable Boolean filter. Its existing pointwise theorem still specifies every bit; three-bit encoding of `5` runs as `[1, 0, 1]`. |
| `LinearMvExtension.bitsValue` | Leaf / 1 | Already executable; the blanket noncomputable section is removed. The encoding of `5` evaluates back to `5`. |
| `MvPolynomial.modPointSample` | Leaf / 1 | Redundant marker removed. Deterministic oracle endpoints at modulus `3` run as `[0, 0]` and `[2, 2]`. The probability theorem independently certifies uniformity. |
| `BitZ.reduceAt` | Leaf / 2 | Executable fused `eval₂Hom`; `reduceAt_apply` proves agreement with mapping then evaluating. Runtime cases evaluate `3X` at `4` and `0` modulo `5` to `2` and `0`, and at `-2` over `ZMod 0` to `-6`. |
| `LinearMvExtension.linearMvExtension`, `linearMvExtensionLMap` | Architectural / 8 | Mathematical views use Mathlib's noncomputable polynomial addition. An executable conversion needs a computational polynomial representation and an agreement bridge. |
| `LinearMvExtension.partialEval` | Architectural / 8 | Its polynomial-valued substitution uses noncomputable Mathlib constructors. Use a computational representation for an executable implementation. |
| `LinearMvExtension.powAlgHom`, `powContraction` | Architectural / 8 | Mathematical substitution uses Mathlib's noncomputable `Polynomial` semiring instance. A computational representation and bridge are needed for an algorithm. |
| `BitZ.claimPoly` | Architectural / 8 | Mathematical error polynomial uses noncomputable polynomial ring operations; it is a proof object, not the prover implementation. |
| `MvPolynomial.zeroCountMod` | Architectural / 9 | `Nat.card` of roots permits `q = 0` and an infinite integer domain. Finite enumeration would need a positive modulus and a separate computational API. |
| `BitZ.collisionSet` | No gap | Its existing finite filter generates code from the supplied field, finite enumeration and decidable equality. |
| `BitZ.bitMatrix`, `BitZ.bitWeights` | Leaf / 1 | Executable (`Matrix.of` with a decidable index test, and pointwise products). The test runs them on concrete data: `L` applied to the digits of coefficients `((5, 3), (7, 0))` with `γ = (1, 10)` evaluates to `(35, 7)`, and a weight over `ZMod 5` evaluates to `2`. |
| `BitZ.coeffBits` | Leaf / 1 | Executable through CompPoly's `Nat.getBit`; the digits of `5` and `3` run as `[1, 0, 1]` and `[1, 1, 0]`. At the boundary `h = 2^B` the digits vanish, so the agreement theorem requires `h < 2^B`. |
| `BitZ.boundedCombos` | Architectural / 8 | A `Set` of an arbitrary ring `S`: membership has no decision procedure without a representation of `S`. A member carries its coefficient vector as data, which is what `coeffBits` consumes. |

Runtime checks live in the existing Round 1/2, fingerprint-probability and bitification acceptance
modules.
The future protocol implementation must use executable representations (including the existing
CompPoly MLE APIs where appropriate), carry sampler data explicitly, and prove agreement with
these mathematical views. An abstract nonempty finite prime set alone does not supply an
executable choice of a prime; callers should provide an executable `SampleableType` instance.
None of the architectural entries is a claim of completed protocol implementation.
