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
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Computable.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/RationalPair.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Persistent.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/LineEvaluation.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/PersistenceDescent.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Interpolation.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/InterpolationParams.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/LineRoots.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/FrobeniusFactor.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/TaylorChart.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/ChartIncidence.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/ExceptionalCount.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Theorem.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegree.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegreeSampling.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegreeComputable.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/SubspaceSeparation.lean
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
Theorem 1.1 is formalized by `ReedSolomon.affineMcaError_le`.

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
| Claim 4.8, case `c > B` | `ReedSolomon.exists_lineRatioWitness_of_map`, `ReedSolomon.isAffinePersistent_of_commonAgreement`, `Matrix.exists_mulVec_eq_zero_apply_ne_zero_of_map` | A persistence proof using the chart can construct a pair over an extension field. Linear algebra descends the identities `H(x) = L(x)g(x)` to `F_q`, with `L` a nonzero polynomial. The denominator can vanish at an agreement point. Common agreement on `B + 1` points gives persistence at `B`, since `L` has at most one root. |
| Lemma 4.2 | `ReedSolomon.IsAffineInterpolant`, `ReedSolomon.exists_isAffineInterpolant` | The interpolant exists once the unknowns outnumber the constraints. The paper's bound `deg_Z Q ≥ 1` is not stated, since the later count does not use it. |
| Lemma 4.2, inequality (4.5), and §4.1 parameters | `ReedSolomon.AffineParams`, `ReedSolomon.AffineParams.surplus`, `ReedSolomon.AffineParams.bounds` | The formal sufficient surplus sums constraints over all `s < m`, whereas (4.5) stops at `min(m - 1, M)`. It can be stronger for freely chosen `M`. `AffineParams.surplus` proves it for the chosen parameters. The surplus holds under `1 ≤ d < n`, `0 < η < 1 - √ρ` and `4 / ρ ≤ n η²`. The bounds give `3 ≤ m`, `D ≤ m A`, `d ≤ B < A ≤ n` and `n / (A - B) ≤ 2 / η`. |
| Lemma 4.3, first condition | `ReedSolomon.affineNested`, `ReedSolomon.affineLineEval_eq_nested`, `ReedSolomon.card_filter_affineLine_eq_zero_le` | A nonzero `G` free of `Z` vanishes on at most `deg_Y G` lines. The lines come from any finite set of challenges mapped injectively into `E × E`. |
| Lemma 4.3, second condition | `ReedSolomon.affineDiscriminant`, `ReedSolomon.affineDiscriminant_ne_zero`, `ReedSolomon.natDegree_affineDiscriminant_le`, `ReedSolomon.affineLineEval_pderiv_ne_zero` | The `Z`-discriminant is a resultant with declared degrees. It stays valid when the line makes the leading `Z`-coefficient vanish. Its `Y`-degree is at most `h (h - 1)`. The simple-root statement needs `0 < deg_Z R`. |
| Section 4, factorization: `Q_i(X^s, Y^s, Z) = R_i^s` | `ReedSolomon.exists_affineFrobeniusFactor` | Over a perfect field of exponential characteristic `p`. The exponent is `s = p^e ≤ deg_Z Q`, and `R` keeps the `(Y, Z)`-degree bound. |
| Lemma 3.11, coefficients and polynomial-root case | `ReedSolomon.affineChartCoefficient`, `ReedSolomon.affineChartNumerator`, `ReedSolomon.affineChartPolynomial_point`, `ReedSolomon.totalDegree_affineChartNumerator_le` | At a center with nonzero separant, polynomial roots are reconstructed from the rational Taylor coefficients. The numerator bound is `1 + τ(h - 1)` for `2l - 1 ≤ τ`, where `h` is any upper bound on the `(Y, Z)`-degree. This interface does not state the paper's existence and uniqueness theorem for formal power series. |
| Claim 4.9, chart map and agreement cuts | `ReedSolomon.affineChartPolynomial`, `ReedSolomon.affineChartCut`, `ReedSolomon.affineChartCut_eq_zero_iff`, `ReedSolomon.totalDegree_affineChartEquation_le`, `ReedSolomon.totalDegree_affineChartCut_le` | The three coordinates are `(y₀, a, b)`. The hypersurface has degree at most `h`, and the cuts have degree at most `2sdh` for `s = p^e` and positive `d`. `ChartIncidence.lean` uses these degree bounds to count nonpersistent challenges. |
| Claim 4.8, case `c > B`, in the chart | `ReedSolomon.affineChartExcluded`, `ReedSolomon.regularLocus_subset_affineChartExcluded`, `ReedSolomon.isAffinePersistent_of_mem_affineChartExcluded` | A positive-dimensional prime with `B + 1` cuts has infinitely many regular points. Two of them lie on different challenges, since `B + 1 ≥ d + 1` cuts fix the reconstruction on a given challenge. The second triple lives over the algebraic closure, and the descent gives persistence over `F_q`. |
| Claims 4.8 and 4.9, Lemma 4.7 for one factor | `ReedSolomon.card_le_of_affineNonpersistent_roots`, `ReedSolomon.exists_affineNonpersistent_finset_card_le` | The incidence bound in the chart `(y₀, a, b)` gives `h (n · 2 p^e d h / (A - B))²` challenges with a simple, nonpersistent root. Hypotheses: `1 ≤ d ≤ B < A ≤ n` and `h` the `(Y, Z)`-degree of the factor. One center where every separant is nonzero is chosen per finite set. |
| Lemma 4.1, without the numerics | `ReedSolomon.exists_affineFactor_finset_card_le`, `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant` | Over the algebraic closure, the content free of `Z` vanishes on few lines. Each factor of positive `Z`-degree adds `h (h - 1)` discriminant lines and its nonpersistent challenges. Summing with `deg content + Σ h ≤ D` and `p^e ≤ M` gives `D² + 4 d² M² D³ (n / (A - B))²` beyond a given set of persistent challenges. |
| Theorem 4.10 | `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolation`, `ReedSolomon.affineMcaError_le_of_interpolation` | For `1 ≤ d < n`, `0 < η < 1 - √ρ`, and budgets satisfying the full-constraint surplus described above, with `n (d + 1) < B²`. For free `M`, that sufficient hypothesis can be stronger than the paper's (4.5). `AffineParams.surplus` establishes it for the paper's parameter choice. The paper's `M ≥ 1` and formula for `M` are not needed. The Johnson factor is the real number `n (B - d - 1) / (B² - n (d + 1))`, not its floor. |
| Theorem 1.1 | `ReedSolomon.exists_affineExceptional_finset_card_le`, `ReedSolomon.affineMcaError_le` | The paper's hypotheses `1 ≤ d < n`, `0 < η < 1 - √ρ` and `4 / ρ ≤ n η²`, and its bound `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)`. The crude estimates give a constant below `9824`. |
| Theorem 5.1, first inequality of (5.4) | `ReedSolomon.equalDegreeWord`, `ReedSolomon.IsEqualDegreeExceptional`, `ReedSolomon.equalDegreeMcaError`, `ReedSolomon.equalDegreeMcaError_le_affineMcaError_add` | For loss one and `nd < (A - 1)²`, the error is at most the affine error plus `ℓ₀/q`, with the rounded-down Johnson bound `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`. The linear-claims assertion is not included. |
| Proposition 6.3 | `ReedSolomon.le_scalarMcaError_of_addSubgroup` | In characteristic two, let the domain be an additive subgroup of size `n = 2^k ≥ 16`. For `d = n/4`, `A ≤ 9n/16`, and `s < 3n/16`, the scalar error is at least `(n - 8)/q`. |

## Port Ledger

The units describe the port plan, including results without Lean declarations.
A unit is done when its declarations are on `main`.

| Unit | Paper | Content | Depends on | Status |
| --- | --- | --- | --- | --- |
| 1 | §1.1, Definition 3.1, Propositions 6.1–6.2 | Definitions and error lower bounds for scalar combiners with loss `s` and affine combiners without loss | — | done ([#1504](https://github.com/Verified-zkEVM/ArkLib/pull/1504)) |
| 2 | Lemmas 4.4–4.5 | Counts for one rational pair and for persistent exceptional challenges | 1 | done ([#1505](https://github.com/Verified-zkEVM/ArkLib/pull/1505)) |
| 3 | Theorem 5.1 | Equal-degree error `≤ εaff + ℓ₀/q` and linear-claim error `≤ εaff + 2ℓ₀/q` | 1 | equal-degree bound on `main` ([#1506](https://github.com/Verified-zkEVM/ArkLib/pull/1506)); linear claims open |
| 4 | Proposition 6.3 | Scalar lower bound with constant fractional loss on additive domains | 1 | done ([#1507](https://github.com/Verified-zkEVM/ArkLib/pull/1507)) |
| 5 | Lemma 4.2 | Trivariate interpolation of `(1,1,d)`-weighted degree below `mA`, with multiplicity `m` along each received line, and vanishing after substitution | 1 | done ([#1508](https://github.com/Verified-zkEVM/ArkLib/pull/1508)); positive `Z`-degree conclusion open |
| 6 | Section 4 factorization and Lemma 4.3 | Frobenius normalization, excluded challenges `#E ≤ D²`, and simple roots outside `E` | 5 | done ([#1508](https://github.com/Verified-zkEVM/ArkLib/pull/1508)) |
| 7 | Lemma 3.11 | Rational Taylor coefficients `Nⱼ/S^(2j-1)` for `j ≥ 1`, numerator degree bounds, and polynomial-root reconstruction | — | coefficient and polynomial-root interfaces on `main` ([#1508](https://github.com/Verified-zkEVM/ArkLib/pull/1508)); power-series existence and uniqueness open |
| 8 | Claims 4.8–4.9 and Lemma 4.7 | Nonpersistent count through a three-coordinate chart and persistence descent | 2, 6, 7 | done ([#1509](https://github.com/Verified-zkEVM/ArkLib/pull/1509)) |
| 9 | Lemma 4.1 and Theorems 1.1, 4.10 | Parameter bounds and the final affine error bounds | 2, 5, 6, 8 | headline bound on `main` ([#1509](https://github.com/Verified-zkEVM/ArkLib/pull/1509)); exact free-budget variant of Theorem 4.10 open |
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
- [`AffineCombiner/LineEvaluation.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/LineEvaluation.lean)
  defines the three variables, the weighted degrees, and evaluation along an affine challenge line.
- [`AffineCombiner/PersistenceDescent.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/PersistenceDescent.lean)
  descends cross-multiplied explanation identities and discards at most one denominator root.
- [`AffineCombiner/Interpolation.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Interpolation.lean)
  constructs the nonzero interpolant and its vanishing on agreeing candidates.
- [`AffineCombiner/InterpolationParams.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/InterpolationParams.lean)
  defines the interpolation parameters and proves the interpolation surplus.
- [`AffineCombiner/LineRoots.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/LineRoots.lean)
  counts vanishing lines and proves the discriminant and simple-root implications.
- [`AffineCombiner/FrobeniusFactor.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/FrobeniusFactor.lean)
  normalizes an irreducible factor, exports `R^(p^e) = Q(X^(p^e), Y^(p^e), Z)`,
  and transports roots along inverse-Frobenius challenges.
- [`AffineCombiner/TaylorChart.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/TaylorChart.lean)
  reconstructs regular roots in three chart coordinates and bounds the cleared cuts.

- [`AffineCombiner/ChartIncidence.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/ChartIncidence.lean)
  counts nonpersistent challenges through the three-coordinate incidence bound.
- [`AffineCombiner/ExceptionalCount.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/ExceptionalCount.lean)
  combines the content and irreducible-factor counts.
- [`AffineCombiner/Theorem.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Theorem.lean)
  proves the finite interpolation bound and the explicit bound of Theorem 1.1.

- [`AffineCombiner/Computable.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/Computable.lean)
  computes the affine and scalar errors as exact nonnegative rationals and proves their
  equality to the semantic error values.

- [`AffineCombiner/EqualDegree.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegree.lean)
  defines the equal-degree error and proves its reduction to the affine error with the rounded Johnson bound.

- [`AffineCombiner/EqualDegreeSampling.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegreeSampling.lean)
  identifies this error with the supremum of native uniform probabilities over three challenges.

- [`AffineCombiner/EqualDegreeComputable.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegreeComputable.lean)
  computes the equal-degree error as an exact nonnegative rational and proves its equality
  to the semantic error.

- [`AffineCombiner/SubspaceSeparation.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/SubspaceSeparation.lean)
  proves the scalar lower bound with constant fractional agreement loss on additive domains.
  It uses the binary-group decomposition in `BinaryAddSubgroup.lean` and the degree bounds in
  `SubspacePolynomial.lean`.

The Taylor chart uses
[`RationalTaylorJointDegree.lean`](../../../ArkLib/Data/Polynomial/Differential/RationalTaylorJointDegree.lean)
and [`Differential/TaylorChart.lean`](../../../ArkLib/Data/Polynomial/Differential/TaylorChart.lean)
for the coefficient recurrence and polynomial-root reconstruction.
Its Frobenius specialization is in
[`FrobeniusTaylor.lean`](../../../ArkLib/ToMathlib/Polynomial/FrobeniusTaylor.lean).
The degree calculations use
[`CurriedDegree.lean`](../../../ArkLib/ToMathlib/MvPolynomial/CurriedDegree.lean) and
[`OptionWeightedDegree.lean`](../../../ArkLib/ToMathlib/MvPolynomial/OptionWeightedDegree.lean).
The count uses
[`AgreementIncidence.lean`](../../../ArkLib/ToMathlib/RingTheory/Nullstellensatz/AgreementIncidence.lean)
for incidence on the chart hypersurface.
These interfaces supply the algebraic inputs to the final bound.

## Representation Choices

The error values have type `ENNReal` and counting definitions without sampler assumptions.
`ReedSolomon.affineMcaError_eq_iSup_prob` and `ReedSolomon.scalarMcaError_eq_iSup_prob` identify
them with suprema of native uniform probabilities.
`ReedSolomon.scalarMcaError_zero_eq_mcaError` identifies the scalar error at loss zero with
`CoreDefinitions.mcaError` at the matching integer agreement threshold.

`ReedSolomon.affineMcaErrorRat`, `ReedSolomon.scalarMcaErrorRat`, and
`ReedSolomon.equalDegreeMcaErrorRat` compute exact values in `ℚ≥0`.
`ReedSolomon.ofReal_affineMcaErrorRat`, `ReedSolomon.ofReal_scalarMcaErrorRat`, and
`ReedSolomon.ofReal_equalDegreeMcaErrorRat` identify the values with the semantic `ENNReal` errors.
The finite search uses CompPoly arithmetic and degree-bounded coefficient enumerations.
The definitions select no classical decisions or samplers.
Execution requires computable field operations, equality decisions, and finite enumerations.
The exhaustive search can be expensive for large fields or domains.

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

The proof of Claims 4.8 and 4.9 uses three chart coordinates `(y₀, a, b)` over the algebraic
closure, rather than the paper's sets in `K^{d+3}` of dimension at most two.
The chart hypersurface is `R(c, a + cb, y₀) = 0`, of degree at most `h`.
Its agreement cuts have degree at most `2sdh`, where `s = p^e` is the Frobenius exponent.
`card_le_of_agreement_off_excluded_of_hypersurface` supplies the exponent two in the count.
Thus `h(2sdh · n/(A - B))² = 4d²s²h³(n/(A - B))²`, matching the paper's degree budget
`deg Vᵢ ≤ 4d²s²h³` times `v²`, with `v = n/(A - B)`.
The center `c` is an element of the algebraic closure chosen for each finite set of roots,
rather than the paper's transcendental `T₀`.

A positive-dimensional regular locus supplies a second chart point with a different challenge.
The linear descent lemma then supplies base-field identities `H(x) = L(x)g(x)`.
Discarding at most one zero of the nonzero linear denominator retains `B` regular agreements
from `B + 1` common cut points.
The paper instead chooses a second `F_q` triple in an affine space defined over `F_q`.
Both arguments are complete.

## Open Formalization Gaps

The remaining Section 5 results are the linear-claims guarantee in Theorem 5.1 and the
shared-challenge interleaving theorem, Theorem 5.2.
The explicit numerical corollary of the equal-degree bound is not exported as a general theorem.
The Reed–Muller extension in Theorem 7.1 and Appendix A is deferred.

The affine-chart interface for Lemma 3.11 does not export formal-power-series existence and uniqueness.
The interpolant interface omits Lemma 4.2's positive `Z`-degree conclusion.
The general bound associated with Theorem 4.10 uses a stronger sufficient interpolation condition
for free budgets. It also uses an unrounded Johnson factor.
The lower bound from Proposition 6.1 is exported.
Its separate received-word construction, global agreement assertion, and exact-agreement
probability bound are not exported as standalone interfaces.

The paper reports a Lean formalization of Theorem 1.1.
It states that the equal-degree reductions in Section 5 and the Reed–Muller extension in
Section 7 and Appendix A are outside that formalization.
The paper does not cite a formalization artifact.

## Source Access

- Source metadata: [`../sources/CWYZ26/metadata.yml`](../sources/CWYZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
