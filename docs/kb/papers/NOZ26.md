---
kind: paper
bibkey: NOZ26
title: "Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/156
source_metadata: ../sources/NOZ26/metadata.yml
status: active-audit
related_modules:
  - ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean
  - ArkLib/Commitments/Functional/Hachi/TraceHead/Basic.lean
  - ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean
  - ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean
  - ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean
  - ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean
  - ArkLib/Commitments/Functional/Hachi/ZeroCheck/Reduction.lean
---

# NOZ26

## At A Glance

Nguyen, O'Rourke and Zhang's *Hachi* is a lattice multilinear polynomial commitment over extension
fields, built from power-of-two cyclotomic rings and norm-conditioned commitments. ArkLib
formalizes its commitment components, nonrecursive opening chain, deterministic trace head and
quotient lift. These use coordinate-wise special soundness (CWSS) and short-collision escape.

## What ArkLib Uses From This Paper

### Commitment and subfield algebra

The commitment layer uses `R_q = Z_q[X]/(X^d+1)`, balanced base-b gadget digits and the inner-outer
commitment. Its weak-binding hypotheses include `q ≡ 5 (mod 8)` and `κ² < q` for the
shortness parameter κ.
The subfield layer supplies the fixed subring `R_q^H`, its cardinality, the packing bijection ψ,
the scaled trace pairing and Lemma 6's packing norm bound.

Theorem 2 packs d/k fixed-subring elements. The trace is unnormalized:

```text
Tr_H(ψ(a) * σ₋₁(ψ(b))) = (d/k) * ⟨a,b⟩.
```

The p.13 prose saying the trace fixes the subfield omits this scale; the displayed pairing and
verifier equation retain it. Lemma 5's field/isomorphism conclusion depends on the admitted
`no_selfReciprocal_factor`. The cardinality, pairing and norm results are independent of that gap;
Lemma 6 uses the weaker odd-characteristic assumption of its coefficient proof.

### Monomial trace head (§3.1)

`TraceHead/` packs the original monomial coefficients using ψ. A single ring-element message Y
is checked by `Tr_H(Y·σ₋₁(v))=(d/k)·y`, yielding a ring evaluation at the retained point.
The point lies in the fixed subring, and d/k is proved to be a unit in R_q.

The concrete ψ basis and numeric monomial indices instantiate the shared finite-observation
identity. `unpack_eval_eq_observation` feeds the trace equality and `CheckedObservation` adapter;
its guard equivalence holds for arbitrary Y. Honest checking, source read-back, completeness and
CWSS preserve the same `VerifiedOpening`, including its norms and message-shortness variant.
Honest source coverage uses the real committer on every original polynomial's packed coefficients.
These proofs use the fixed subring as a ring and do not assume it is a field or require a functional
commitment. The existing ring/trace definitions are noncomputable, and an executable scalar-Scheme
package is separate.

### Quotient lift (§4.3, Figure 4/Lemma 9)

Hachi instantiates the generic [HMZ lift](HMZ25.md): a quotient-ring identity is represented by
`M(X)z(X)=y(X)+φ(X)r(X)` and evaluated at a field challenge. The generic kernel uses raw `(z,r)`
as its relation witness. Hachi commits z together with balanced digits of r, of width
`μ+n·δ`, where `δ=clog_b q`. `rhoDigits_reconstruct` and `rhoDigits_evalAt` prove reconstruction;
per-digit shortness is bounded by `⌊b/2⌋` for arbitrary r.

`liftPackage.isCWSS` instantiates `RingSwitching.Lift.coordinateWiseSpecialSoundWithEscape`.
The escape targets `LiftCom.Collision`, a pair of distinct short openings of one commitment.
`moduleSIS_relation_of_mem_Collision` maps it to the Module-SIS relation for the supplied Ajtai
key at radius `2·bound`. Sampling that key in the full scheme remains a separate integration
obligation. Honest completeness uses the image relation carrying the protocol's z bound and
the unconditional quotient-digit bound.

### Nonrecursive opening and zero-check

`Composition.lean` composes the evaluation, lift, batched identities, sumcheck and terminal
relations with their named extractors and collision events. The nonrecursive chain has CWSS and
perfect completeness through proved state-aware composition; `Correctness.lean` supplies the
composed completeness and perfect-correctness theorems.

The zero-check uses one two-child scalar round per coordinate and a nested evaluation tree.
Its leaves form a full product grid, as required for multivariate multilinear interpolation.
The identities are stored as `CMlPolynomialEval` Boolean-value vectors; the public Eq. (22)
contraction is proved equal to the α-defect in the table. The batching relation derives shortness
from the range identity, while later relations retain shortness as the index needed for
norm-conditioned commitment binding.

## Main ArkLib Touchpoints

- [`CyclotomicRing/Subfield.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean) — Lemmas 5–6, ψ and the trace pairing.
- [`Hachi/TraceHead/Basic.lean`](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Basic.lean) — monomial scalar head and real-committer coverage.
- [`Hachi/InnerOuter/Security.lean`](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean) — norm-conditioned weak binding.
- [`Hachi/RingSwitch/Reduction.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean) — quotient lift and short-collision boundary.
- [`Hachi/ZeroCheck/Reduction.lean`](../../../ArkLib/Commitments/Functional/Hachi/ZeroCheck/Reduction.lean) and
  [`Constraints.lean`](../../../ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean) — nested zero-check and its polynomial identities.
- [`Hachi/Composition.lean`](../../../ArkLib/Commitments/Functional/Hachi/Composition.lean) and
  [`Correctness.lean`](../../../ArkLib/Commitments/Functional/Hachi/Correctness.lean) — nonrecursive soundness and completeness composition.
- [`Hachi/Params.lean`](../../../ArkLib/Commitments/Functional/Hachi/Params.lean) — deterministic parameter bounds.

## Source Correspondence And Remaining Boundaries

| Source point | ArkLib interpretation or limitation |
|---|---|
| §3.1 coefficient packing | Monomial coefficients and fixed-subring points; a Boolean-table formulation requires explicit basis, commitment and norm transport |
| §3.2 and §4.5 recombination | `Σ_i y_i Z^i` is not injective on field-valued partials: errors `(Zδ,−δ)` cancel but change reconstruction at a by `δ(Z−a)`; `ZBatchBridge` lacks a sound pull-back |
| Lemma 5 | Field identification depends on `no_selfReciprocal_factor`; the trace head does not use it |
| Lemma 10 | An axis cross does not determine a multivariate multilinear; the formalization uses a nested product grid |
| Eq. (23) range identity | Range checking includes quotient-digit rows as well as z rows, matching H₀ and the domain of w̃ |
| §4.4 / Figure 9 | The deterministic rule `b^τ>β` gives τ=5 at the listed parameters; the table's τ=4 needs a separate justified abort/completeness analysis |

For the last row, the paper's bound is `β=2^r·ω·b=262144` at `b=16`, `r=10`, `ω=16`.
ArkLib proves the sharper balanced-digit bound `2^r·ω·⌊b/2⌋=131072`; both exceed `16^4`.
`Params.lean` uses τ=5 and proves its minimality. The other Figure 9 parameters are retained.

The detailed [Lemma 5–6 audit](../audits/noz26-subfield-lemmas5-6.md) and
[Lemma 10 audit](../audits/noz26-zero-check-lemma10.md) record the source equations, challenge
cardinalities and domain choices. The [ring-switching audit](../audits/ring-switching-model-coverage.md)
compares the trace head with coordinate packing and quotient lift.

The §4.5 recursion adapters remain outside the nonrecursive chain: partial evaluation,
same-field Z recombination and trace handoff require further proofs. Full key-sampling security
is separate from the local collision-to-Module-SIS implication.
Packing RBR bounds over finite domains are not applicable to uniform challenges in the
non-domain ring R_q; Hachi retains its CWSS and norm-conditioned collision contracts.

## Source Access

- [Cryptology ePrint Archive, 2026/156](https://eprint.iacr.org/2026/156).
- [Source metadata](../sources/NOZ26/metadata.yml) and [bibliography](../../../blueprint/src/references.bib).
- The 33-page January 30, 2026 PDF is the source for §3.1 pp.11–13, §3.2 p.14,
  Figure 4/Lemma 9 p.20 and §4.5 p.26; its hash is in the coverage audit.
- [FMN24](FMN24.md) supplies CWSS; [HMZ25](HMZ25.md) the quotient lift; [NS24](NS24.md)
  the inner-outer commitment lineage.
