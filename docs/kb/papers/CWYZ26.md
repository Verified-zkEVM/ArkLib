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
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Probability.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/RationalPair.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Persistent.lean
---

# CWYZ26

## At A Glance

Fix a domain `D ⊆ Fq` of size `n` and an integer output degree bound `1 ≤ d < n`.
The affine combiner samples `α, β` independently and uniformly and forms `f(x) + (α + βx) g(x)`.
Its witnesses have degrees at most `d` and below `d`, so their combination has degree at most `d`.

Set `ρ = d/n` and `A = ⌈(√ρ + η)n⌉`.
If `0 < η < 1 - √ρ` and `nη² ≥ 4/ρ`, Theorem 1.1 bounds the error with one lost agreement by
`4/(ηq) + 2¹⁴ n²/(ρ³ η¹⁰ q²)`.
This bound holds for every such domain in every finite field of size `q ≥ n`.
Theorem 1.1 is a planned unit in the port ledger below.

For fixed `ρ, η` in that range and sufficiently large `n`, scalar combiners have error
`Ω_{ρ,η}(n/q)` at the same threshold and loss.
For `q ≥ n²`, the affine bound is `O_{ρ,η}(1/q)`, giving an improvement by a factor of `Ω_{ρ,η}(n)`.
Proposition 6.2 also shows that affine combiners have error `Ω_{ρ,η}(n/q)` when no agreement
loss is allowed.

All statement numbers refer to the **13 November 2026 ePrint revision**.

## What ArkLib Uses From This Paper

Here `n = Fintype.card ι` and `q = Fintype.card F`, with `domain : ι ↪ F`.
The embedding already implies `n ≤ q`.

| Paper statement | Lean interface | Scope |
| --- | --- | --- |
| Section 1.1 and Definition 3.1 | `ReedSolomon.combinedWord`, `ReedSolomon.affineMultiplier`, `ReedSolomon.agreementLoss`, `ReedSolomon.IsLossWitness`, `ReedSolomon.IsAffineExceptional`, `ReedSolomon.IsScalarExceptional`, `ReedSolomon.affineMcaError`, `ReedSolomon.scalarMcaError` | The errors are suprema over received word pairs of the uniform probability that some candidate is exceptional. Definition 3.1 is the affine predicate at loss `s = 1`. |
| Proposition 6.1, error lower bound | `ReedSolomon.le_scalarMcaError_of_degree_add_loss_add_one_lt` | For `d + s + 1 < A ≤ n`, the scalar error is at least `(1 + ⌊(n - A)/(s + 1)⌋)/q`. The proof constructs words using a vanishing polynomial and blocks of size `s + 1`. It does not export the proposition's separate global agreement claim or its exact-agreement probability bound. |
| Proposition 6.2 | `ReedSolomon.le_affineMcaError_zero_loss`, `ReedSolomon.le_affineMcaError_zero_loss_div_two` | For `d + 1 < A ≤ n`, the affine error at loss zero is at least `(n - A + 1)(q - 1)/q²`, hence at least `(n - A + 1)/(2q)`. |
| Lemma 4.4 | `ReedSolomon.card_isAffineExceptional_add_mul_le`, `ReedSolomon.card_ratFunc_combination_le`, `ReedSolomon.card_isAffineExceptional_ratFunc_le` | At loss one, a polynomial pair within the witness degree bounds gives at most `n choose 2` exceptional challenges. A rational pair outside those bounds has at most `q` compatible challenges, even without requiring exceptionality. Every rational pair gives at most `max q (n choose 2)` exceptional challenges. |
| Lemma 4.5 | `ReedSolomon.affinePersistenceSet`, `ReedSolomon.IsAffinePersistent`, `ReedSolomon.card_isAffineExceptional_persistent_le` | The real count is at most `n (B - d - 1)/(B² - n(d + 1)) · max q (n choose 2)` under `d + 1 < B` and `n(d + 1) < B²`. It covers all persistent exceptional challenges at loss one. The paper first removes its excluded set `E`. |

## Port Ledger

The units describe the port plan, including results without Lean declarations.
A unit is done when its declarations are on `main`.

| Unit | Paper | Content | Depends on | Status |
| --- | --- | --- | --- | --- |
| 1 | §1.1, Definition 3.1, Propositions 6.1–6.2 | Definitions and error lower bounds for scalar combiners with loss `s` and affine combiners without loss | — | in review |
| 2 | Lemmas 4.4–4.5 | Counts for one rational pair and for persistent exceptional challenges | 1 | in review |
| 3 | Theorem 5.1 | Equal-degree error `≤ εaff + ℓ₀/q` and linear-claim error `≤ εaff + 2ℓ₀/q` | 1 | planned |
| 4 | Proposition 6.3 | Scalar lower bound with constant fractional loss on additive domains | 1 | planned |
| 5 | Lemma 4.2 | Trivariate interpolation of `(1,1,d)`-weighted degree below `mA`, with multiplicity `m` along each received line, and vanishing after substitution | 1 | planned |
| 6 | Section 4 factorization and Lemma 4.3 | Frobenius normalization, excluded challenges `#E ≤ D²`, and simple roots outside `E` | 5 | planned |
| 7 | Lemma 3.11 | Simple-root Hensel lifting along affine substitutions, with coefficients `Nⱼ/S^(2j-1)` for `j ≥ 1` and numerator degree bounds | — | planned |
| 8 | Claims 4.8–4.9 and Lemma 4.7 | Agreement-hyperplane induction, a cover of dimension at most two, and the nonpersistent count | 2, 6, 7 | planned |
| 9 | Lemma 4.1 and Theorems 1.1, 4.10 | Parameter bounds and the final affine error bounds | 2, 5, 6, 8 | planned |
| 10 | Theorem 5.2 | For `k = 2ʳ` rows, shared folding with degree `d + r`, threshold `A + r`, loss `r`, and error at most `rε`, where `ε` bounds every round. The proof packs rows into `F_{q^t}` with base-field challenges | 9 | deferred |
| 11 | Theorem 7.1 and Appendix A | Reed–Muller extension on subfield grids through the Pellikaan–Wu reduction | 9 | deferred |

In unit 3, `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋` is the Johnson list bound from Theorem 5.1.
The quotient is real, and the floor rounds down.
Unit 10 applies the equal-degree guarantee in each folding round.

## Main ArkLib Touchpoints

- [`AffineCombiner/Basic.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Basic.lean)
  defines combined words, witnesses with agreement loss, exceptional candidates, and the error values.
- [`AffineCombiner/Separation.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Separation.lean)
  proves the two error lower bounds from Section 6.
- [`AffineCombiner/Probability.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Probability.lean)
  identifies the errors with native probabilities.
  Its zero-loss scalar equivalence and error equality use `CoreDefinitions.IsMCA` and
  `CoreDefinitions.mcaError` for the affine-line generator and `ReedSolomon.code domain (d + 1)`.
  `ReedSolomon.le_mcaError_affineLine_of_ceil_eq` gives a lower bound on this value.

- [`AffineCombiner/RationalPair.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/RationalPair.lean)
  bounds the exceptional challenges compatible with one rational pair.
- [`AffineCombiner/Persistent.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Persistent.lean)
  defines persistence and bounds persistent exceptional challenges using the Johnson bound
  `Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le`.

The planned algebraic units can use the Hensel numerator bounds in
[`RationalFunctions/`](../../../ArkLib/Data/Polynomial/RationalFunctions/), the affine Taylor
expansion in [`RationalTaylor.lean`](../../../ArkLib/Data/Polynomial/Differential/RationalTaylor.lean),
and the Frobenius substitutions in
[`FrobeniusPullback.lean`](../../../ArkLib/ToMathlib/MvPolynomial/FrobeniusPullback.lean).
Other available primitives include the resultant degree bounds in
[`ResultantDegree.lean`](../../../ArkLib/Data/Polynomial/ResultantDegree.lean) and the incidence
induction in [`AgreementIncidence.lean`](../../../ArkLib/ToMathlib/RingTheory/Nullstellensatz/AgreementIncidence.lean).
The planned units have not yet connected these primitives into the paper's complete argument.

## Representation Choices

The error values have type `ENNReal` and counting definitions without sampler assumptions.
`ReedSolomon.affineMcaError_eq_iSup_prob` and `ReedSolomon.scalarMcaError_eq_iSup_prob` identify
them with suprema of native uniform probabilities.
`ReedSolomon.scalarMcaError_zero_eq_mcaError` identifies the scalar error at loss zero with
`CoreDefinitions.mcaError` at the matching integer agreement threshold.

The output and first affine witness have degree at most `d`, which gives message length `d + 1`.
The second affine witness has degree below `d`, which gives message length `d`.
`ReedSolomon.evalOnPoints_mem_code_succ_of_degree_le` and
`ReedSolomon.evalOnPoints_mem_code_of_degree_lt` provide these code memberships.

Persistence uses `G = H/L`, with `deg H ≤ d`, a nonzero denominator of degree at most one,
and at least `B` candidate agreement points where `L` does not vanish and `H = Lg`.
The rational partner `F₀ = P - (α + βX)G` then agrees with `f` there too.
The persistence predicate does not bound the degree of `P`.
Exceptionality supplies that bound.
The paper fixes `B = ⌈(√ρ + η/2)n⌉ - 1`, while the interface allows any `B` satisfying the
counting theorem's hypotheses.
Each rational pair is assigned the persistence set of one chosen candidate.
These sets suffice for the Johnson bound because they are large and pairwise almost disjoint.

## Open Formalization Gaps

The planned and deferred units in the ledger have no complete formalization in this port.
The lower bound from Proposition 6.1 is exported, while its constructed received words and
separate global agreement assertion are internal to the proof.

The paper reports a Lean formalization of Theorem 1.1.
It states that the equal-degree reductions in Section 5 and the Reed–Muller extension in
Section 7 and Appendix A are outside that formalization.
The paper does not cite a formalization artifact.

## Source Access

- Source metadata: [`../sources/CWYZ26/metadata.yml`](../sources/CWYZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
