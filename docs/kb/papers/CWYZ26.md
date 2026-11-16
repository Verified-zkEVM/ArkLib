---
kind: paper
bibkey: CWYZ26
title: "Affine Combiners for {Reed--Solomon} Proximity Gaps"
year: 2026
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/2863
source_metadata: ../sources/CWYZ26/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Basic.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Separation.lean
---

# CWYZ26

## At A Glance

The paper combines two received words `f g` by the affine multiplier `α + β x`, forming
`f + (α + β x) g` with independent uniform `α β`. The witnesses have degrees `d` and `d - 1`, so
the combined polynomial still has degree `d`. With one coordinate of agreement loss, the mutual
correlated agreement error at the threshold `A = ⌈(√ρ + η) n⌉` is
`4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)` (Theorem 1.1), over every finite field and every domain.
Scalar combiners have worst-case error `Ω(n / q)` at the same threshold and loss (Section 6), so
for `q ≥ n²` affine combiners save a factor `n`.

The statement numbering below follows the **13 November 2026 ePrint revision**.

## What ArkLib Uses From This Paper

| Paper statement | Lean interface | Scope |
| --- | --- | --- |
| Section 1.1, definition of the MCA error with agreement loss; Definition 3.1 | `ReedSolomon.combinedWord`, `ReedSolomon.affineMultiplier`, `ReedSolomon.agreementLoss`, `ReedSolomon.IsLossWitness`, `ReedSolomon.IsAffineExceptional`, `ReedSolomon.IsScalarExceptional`, `ReedSolomon.affineMCAError`, `ReedSolomon.scalarMCAError` | The error is the worst-case fraction of exceptional challenges over all pairs of received words, which is the uniform probability of the paper. The domain is any finite index type embedded in the field. |
| Proposition 6.1 | `ReedSolomon.scalarMCAError_ge` | With agreement loss `s` and `d + s + 1 < A ≤ n`, the scalar error is at least `(1 + ⌊(n - A) / (s + 1)⌋) / q`. The blocks of size `s + 1` are consecutive positions in a fixed enumeration of the domain. |
| Proposition 6.2 | `ReedSolomon.affineMCAError_zero_loss_ge`, `ReedSolomon.affineMCAError_zero_loss_ge_half` | Without agreement loss and with `d + 1 < A ≤ n`, the affine error is at least `(n - A + 1)(q - 1) / q²`, hence at least `(n - A + 1) / (2q)`. |

## Port Ledger

Each row is one pull request. A row is done when its declarations are on `main`.

| Unit | Paper | Content | Depends on | Status |
| --- | --- | --- | --- | --- |
| 1 | §1.1, Def 3.1, Props 6.1, 6.2 | Definitions; scalar `Ω(n / q)` lower bound with loss `s`; affine lower bound without loss | — | in review |
| 2 | Lemmas 4.4, 4.5 | Exceptional challenges of one rational pair; persistent triples and their count by the Johnson bound for set families | 1 | planned |
| 3 | Theorem 5.1 | Equal-degree combiner and linear claims, reduced to the affine error plus `ℓ₀ / q` | 1 | planned |
| 4 | Prop 6.3 | Scalar `Ω(n / q)` lower bound with constant fractional loss on additive domains (subspace polynomials) | 1 | planned |
| 5 | Lemma 4.2 | Trivariate interpolation along affine lines: `(1, 1, d)`-weighted degree, multiplicity `m` at `(z, f(z) + Y g(z))`, vanishing of `Q(X, α + βX, P(X))` | 1 | planned |
| 6 | §4 factorization, Lemma 4.3 | Factorization with Frobenius normalization, excluded pairs `|E| ≤ D²`, simple roots outside `E` | 5 | planned |
| 7 | Lemma 3.11 | Hensel lifting along `Y + V X` with coefficients `N_j / S^(2j-1)` | — | planned |
| 8 | Claims 4.8, 4.9, Lemma 4.7 | Agreement-hyperplane induction; cover by algebraic sets of dimension at most two; nonpersistent count | 2, 6, 7 | planned |
| 9 | Lemma 4.1, Theorems 1.1, 4.10 | Parameter arithmetic and the final bound | 2, 5, 6, 8 | planned |
| 10 | Theorem 5.2 | Interleaving through packing into `F_{q^t}`; needs the core count with words over an extension field | 9 | deferred |
| 11 | §7, Appendix A | Reed–Muller extension through the Pellikaan–Wu reduction | 9 | deferred |

## Main ArkLib Touchpoints

- [`AffineCombiner/Basic.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Basic.lean)
  owns the combined words, the witnesses with agreement loss, the exceptional predicates and the
  two error functions.
- [`AffineCombiner/Separation.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Separation.lean)
  owns the two lower bounds of Section 6: the scalar combiner with agreement loss and the affine
  combiner without loss.
- The core count reuses the Johnson bound for set families
  (`Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le`), the rational Hensel numerators of
  `Data/Polynomial/RationalFunctions/` and `Data/Polynomial/Differential/RationalTaylor.lean`, the
  Frobenius pullback of `ToMathlib/MvPolynomial/FrobeniusPullback.lean`, resultant degree bounds of
  `Data/Polynomial/ResultantDegree.lean`, and the agreement-incidence induction of
  `ToMathlib/RingTheory/Nullstellensatz/AgreementIncidence.lean`.

## Known Divergences From ArkLib

- The error is a worst-case fraction of challenges rather than a probability under a sampler; for
  the uniform distribution the two agree.
- Persistence is stated with an explicit numerator `H` and denominator `L` of `G`. The first
  rational function `F = P - (α + β X) G` agrees with `f` at every agreement point of `P` where
  `G` agrees with `g`, so only the condition on `G` is stated.

## Open Formalization Gaps

The units marked planned or deferred in the port ledger. The paper's own Lean formalization covers
Theorem 1.1 and is not public; Sections 5 and 7 are not covered by it.

## Source Access

- Source metadata: [`../sources/CWYZ26/metadata.yml`](../sources/CWYZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
