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
  - ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/SubspaceSeparation.lean
  - ArkLib/Data/CodingTheory/ReedMuller/Grid.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Basic.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Probability.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Separation.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/RationalPair.lean
  - ArkLib/ToMathlib/LinearAlgebra/PiFinsetHyperplane.lean
  - ArkLib/ToMathlib/FieldTheory/Finite/TracePolynomial.lean
  - ArkLib/Data/CodingTheory/ReedMuller/PellikaanWu.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/PellikaanWu.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Persistent.lean
  - ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/PersistenceDescent.lean
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
| Lemma 4.2 | `ReedSolomon.IsMultiplierInterpolant`, `ReedSolomon.exists_isAffineInterpolant`, `ReedSolomon.IsMultiplierInterpolant.vanish_affineMultiplier` | The interpolant exists once the unknowns outnumber the constraints. The paper's bound `deg_Z Q ≥ 1` is not stated, since the later count does not use it. |
| Lemma 4.2, inequality (4.5), and §4.1 parameters | `ReedSolomon.AffineParams`, `ReedSolomon.AffineParams.surplus`, `ReedSolomon.AffineParams.bounds` | The formal sufficient surplus sums constraints over all `s < m`, whereas (4.5) stops at `min(m - 1, M)`. It can be stronger for freely chosen `M`. `AffineParams.surplus` proves it for the chosen parameters. The surplus holds under `1 ≤ d < n`, `0 < η < 1 - √ρ` and `4 / ρ ≤ n η²`. The bounds give `3 ≤ m`, `D ≤ m A`, `d ≤ B < A ≤ n` and `n / (A - B) ≤ 2 / η`. |
| Lemma 4.3, first condition | `ReedSolomon.affineNested`, `ReedSolomon.multiplierEval_eq_nested`, `ReedSolomon.card_filter_multiplierEval_eq_zero_le` | A nonzero `G` free of `Z` vanishes on at most `deg_Y G` multipliers of a family injective on a finite challenge set. Reed–Solomon uses the lines `α + β X`. |
| Lemma 4.3, second condition | `ReedSolomon.affineDiscriminant`, `ReedSolomon.affineDiscriminant_ne_zero`, `ReedSolomon.natDegree_affineDiscriminant_le`, `ReedSolomon.multiplierEval_pderiv_ne_zero` | The `Z`-discriminant is a resultant with declared degrees. It stays valid when the line makes the leading `Z`-coefficient vanish. Its `Y`-degree is at most `h (h - 1)`. The simple-root statement needs `0 < deg_Z R`. |
| Section 4, factorization: `Q_i(X^s, Y^s, Z) = R_i^s` | `ReedSolomon.exists_frobeniusFactor`, `ReedSolomon.map_affineMultiplier` | Over a perfect field of exponential characteristic `p`. The exponent is `s = p^e ≤ deg_Z Q`, and `R` keeps the `(Y, Z)`-degree bound. A root along a multiplier `L` gives a root along `L` with `s`-th-rooted coefficients. For a line this is `α^{1/s} + β^{1/s} X`. |
| Lemma 3.11, coefficients and polynomial-root case | `ReedSolomon.chartCoefficient`, `ReedSolomon.chartNumerator`, `ReedSolomon.chartPolynomial_point`, `ReedSolomon.totalDegree_chartNumerator_le` | At a center with nonzero separant, polynomial roots are reconstructed from the rational Taylor coefficients. The numerator bound is `1 + τ(h - 1)` for `2l - 1 ≤ τ`, where `h` is any upper bound on the `(Y, Z)`-degree. The multiplier is any linear family `∑ⱼ aⱼ θⱼ`, with `θ : κ → E[X]`. Reed–Solomon is the family `(1, X)`. This interface does not state the paper's existence and uniqueness theorem for formal power series. |
| Claim 4.9, chart map and hypersurface | `ReedSolomon.chartPolynomial`, `ReedSolomon.totalDegree_chartEquation_le` | The chart coordinates are `(y₀, a)` with `a : κ → E`; for Reed–Solomon they are `(y₀, a, b)`. The hypersurface has degree at most `h`. The agreement cuts are those of the Appendix A row below, with degree at most `2sdh` for `s = p^r` and positive `d`. |
| Appendix A, "Nonpersistent": chart cuts for the multipliers `y + ∑ⱼ vⱼ θⱼ(W)` | `ReedSolomon.familyMultiplier`, `ReedSolomon.chartFunctionalCut`, `ReedSolomon.aeval_chartFunctionalCut`, `ReedSolomon.totalDegree_chartFunctionalCut_le`, `ReedSolomon.chartAgreementCut`, `ReedSolomon.aeval_chartAgreementCut`, `ReedSolomon.chartAgreementCut_eq_zero_iff`, `ReedSolomon.totalDegree_chartAgreementCut_le` | Appendix A uses the family `(1, θ₁, …, θ_k)` at the coefficient vector `(y, v)`. A cut applies any linear functional `Λ` to the reconstruction, cleared by `S^τ`. An agreement cut also subtracts a cleared target of degree at most `s`. Both have degree at most `2sdh` at `τ = 2sd - 1`. The high cuts carry the Appendix A condition that the reconstruction lies in the image of the trace substitution. |
| Claim 4.8, case `c > B` (Appendix A: `c > B + n/q₀ - 1`), in the chart | `ReedSolomon.SeparatesDegree`, `ReedSolomon.separatesDegree_leval`, `ReedSolomon.chartExcluded`, `ReedSolomon.mem_chartExcluded`, `ReedSolomon.eq_of_separatesDegree`, `ReedSolomon.regularLocus_subset_chartExcluded` | Generic over a family `θ : κ → E[X]`, functionals `Λᵢ`, targets in the challenge coordinates and a list of high cuts. A positive-dimensional prime with `B + e` agreement cuts and every high cut has infinitely many regular points. Two of them lie on different challenges once the functionals determine polynomials of degree at most `d` from `B + e` positions. `e` is `1` for Reed–Solomon and `n/q₀` for Reed–Muller. |
| Claim 4.8, case `c > B`, Reed–Solomon descent | `ReedSolomon.affineChartTarget`, `ReedSolomon.totalDegree_affineChartTarget_le`, `ReedSolomon.eval_map_eq_aeval_affineChartTarget_iff`, `ReedSolomon.isAffinePersistent_of_mem_chartExcluded` | The case `θ = (1, X)`, `e = 1`, with evaluations at the positions and no high cuts. The second triple lives over the algebraic closure, and the descent gives persistence over `F_q`. |
| Claims 4.8 and 4.9, Lemma 4.7 for one factor | `ReedSolomon.card_le_of_regular_chartPoints`, `ReedSolomon.exists_chartExcluded_finset_card_le` | The incidence bound is `h (n · 2 s d h / (A - B - e + 1))^(card κ)`, with natural-number subtraction. Appendix A uses `card κ = k + 1`, `e = n/q₀` and `d = ρn`. The high cuts add no degree factor. Hypotheses: `1 ≤ d`, `1 ≤ s`, `1 ≤ B + e ≤ A ≤ n`, and targets of degree at most `s`. The conclusion is membership in the excluded set at some regular center. |
| Lemma 4.1, without the numerics | `ReedSolomon.exists_factorRoots_finset_card_le`, `ReedSolomon.exists_interpolantRoots_finset_card_le`, `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant` | Generic over an algebraically closed `E` and a finite challenge type with injective multipliers. For each Frobenius exponent, the Frobenius root of each multiplier is assumed to be a family multiplier in chart coordinates. Each code supplies the step from an excluded chart point to its own persistence. The bound is `D² + (2 d M n / (A - B - e + 1))^(card κ) D^(card κ + 1)`, which covers the excluded and nonpersistent parts of Lemma 4.1. Reed–Solomon adds its persistent set and gets `D² + 4 d² M² D³ (n / (A - B))²` beyond it. |
| Theorem 4.10 | `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolation`, `ReedSolomon.affineMcaError_le_of_interpolation` | For `1 ≤ d < n`, `0 < η < 1 - √ρ`, and budgets satisfying the full-constraint surplus described above, with `n (d + 1) < B²`. For free `M`, that sufficient hypothesis can be stronger than the paper's (4.5). `AffineParams.surplus` establishes it for the paper's parameter choice. The paper's `M ≥ 1` and formula for `M` are not needed. The Johnson factor is the real number `n (B - d - 1) / (B² - n (d + 1))`, not its floor. |
| Theorem 1.1 | `ReedSolomon.exists_affineExceptional_finset_card_le`, `ReedSolomon.affineMcaError_le` | The paper's hypotheses `1 ≤ d < n`, `0 < η < 1 - √ρ` and `4 / ρ ≤ n η²`, and its bound `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)`. The crude estimates give a constant below `9824`. |
| Theorem 5.1, first inequality of (5.4) | `ReedSolomon.equalDegreeWord`, `ReedSolomon.IsEqualDegreeExceptional`, `ReedSolomon.equalDegreeMcaError`, `ReedSolomon.equalDegreeMcaError_le_affineMcaError_add` | For loss one and `nd < (A - 1)²`, the error is at most the affine error plus `ℓ₀/q`, with the rounded-down Johnson bound `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`. The linear-claims assertion is not included. |
| Proposition 6.3 | `ReedSolomon.le_scalarMcaError_of_addSubgroup` | In characteristic two, let the domain be an additive subgroup of size `n = 2^k ≥ 16`. For `d = n/4`, `A ≤ 9n/16`, and `s < 3n/16`, the scalar error is at least `(n - 8)/q`. |
| Section 7, bound (7.1) on a hyperplane | `ReedMuller.card_grid_inter_hyperplane_le`, `Fintype.card_filter_piFinset_dotProduct_eq_le` | A hyperplane `a · x = b` with `a ≠ 0` contains at most `n / q₀` points of the grid `K₀ᵏ`. The general form holds on any product `Sᵐ` in a domain. |
| Section 7, after (7.1), affinely independent points | `ReedMuller.exists_subset_card_eq_forall_add_dotProduct_eq_zero`, `ReedMuller.eq_zero_of_forall_mem_add_dotProduct_eq_zero` | More than `n / q₀` grid points contain `k + 1` points on which only the zero affine form vanishes. This is the form Lemma A.1 uses. |
| Schwartz–Zippel on the grid | `ReedMuller.card_grid_eval_eq_zero_le` | A nonzero polynomial of total degree `D` has at most `D q₀ᵏ⁻¹` zeros on the grid. |
| Section 7, the Reed–Muller error `εRM` | `ReedMuller.affineMultiplier`, `ReedMuller.combinedWord`, `ReedMuller.agreementSet`, `ReedMuller.agreementLoss`, `ReedMuller.IsAffineExceptional`, `ReedMuller.affineMcaError`, `ReedMuller.affineMcaError_eq_iSup_prob` | Words on the grid `K₀ᵏ`, challenges `α ∈ F^{k+1}` and the multiplier `α₀ + Σ αᵢXᵢ`. The second witness is admissible when it is zero or has total degree below `d`. |
| Section 7, the exponent `k` cannot be improved | `ReedMuller.le_affineMcaError_of_add_two_le` | For `1 ≤ k`, `d + 2 ≤ q₀` and `A ≤ n`, the error at loss `n / q₀` is at least `q⁻ᵏ`. The paper derives `d ≤ q₀ - 2` from Theorem 7.1. |
| Lemma A.1 | `ReedMuller.card_isAffineExceptional_add_mul_le`, `ReedMuller.card_fractionRing_combination_le`, `ReedMuller.card_isAffineExceptional_fractionRing_le` | At loss `n / q₀`, a polynomial candidate has at most `n choose (k + 1)` exceptional challenges. A rational pair over the fraction field of `F[X₁, …, X_k]` has at most `q`. Together: at most `max q (n choose (k + 1))`. |
| Appendix A, trace polynomials `ψᵢ(X) = Tr(γᵢX)` | `FiniteField.tracePolynomial`, `FiniteField.eval_tracePolynomial`, `FiniteField.natDegree_tracePolynomial`, `FiniteField.aeval_tracePolynomial_add` | Each `ψᵢ` is a polynomial of degree exactly `n/q₀ = q₀^(k-1)` when `γᵢ ≠ 0`. It is additive on every algebra over `F_n`. |
| Appendix A, the bijection `ψ : F_n → F_q₀ᵏ` | `FiniteField.traceCoordinateEquiv`, `FiniteField.traceCoordinateMap_bijective` | The coordinates are traces against the dual basis of any basis `γ`. |
| Appendix A, the substitution `P ↦ P̃` | `ReedMuller.traceSubstitution`, `ReedMuller.natDegree_traceSubstitution_le`, `ReedMuller.eval_traceSubstitution`, `ReedMuller.injOn_traceSubstitution_totalDegree_lt` | `deg P̃ ≤ deg P · q₀^(k-1)`, which is `ρn` at `deg P = d`. `P̃(x) = P(ψ x)`. The substitution is injective on polynomials of degree below `q₀` in each variable, which contains the paper's total-degree case. |
| Appendix A, agreement and the multiplier `L̃_α` | `ReedMuller.card_polynomialAgreementSet_traceSubstitution`, `ReedMuller.natDegree_traceSubstitution_map_affineMultiplier_le`, `ReedMuller.traceSubstitution_map_affineMultiplier_injective` | `P` and `P̃` have the same number of agreements. `L̃_α` has degree at most `n/q₀`, and distinct `α` give distinct `L̃_α`. Words and polynomials over `F_q` are mapped into a common field `F'`. |
| Appendix A, interpolation with weight `(1, n/q₀, ρn)` | `ReedSolomon.multiplierWeight`, `ReedSolomon.multiplierEval`, `ReedSolomon.natDegree_multiplierEval_le`, `ReedSolomon.IsMultiplierInterpolant`, `ReedSolomon.exists_isMultiplierInterpolant` | The multiplier degree is a parameter `e`. Reed–Muller takes `e = q₀^(k-1)`. The interpolant vanishes along every multiplier of degree at most `e`. The surplus condition is a cardinality hypothesis. |
| Appendix A, excluded coefficient vectors, ingredients of `#E ≤ D²` | `ReedSolomon.card_filter_multiplierEval_eq_zero_le`, `ReedSolomon.card_filter_affineDiscriminant_eq_zero_le` | Both counts hold for any family of multipliers injective on the challenges. The Reed–Muller assembly is planned. |
| Appendix A, the persistent count | `ReedMuller.IsAffinePersistent`, `ReedMuller.affinePersistenceSet`, `ReedMuller.card_isAffineExceptional_persistent_le` | Persistence uses `G = H/L_σ` with `σ ≠ 0` and `deg H ≤ d`, counting agreements off the zeros of `L_σ`. At most `ℓ · max{q, C(n, k+1)}` persistent challenges are exceptional, with `ℓ = n(B - (d+1)q₀^(k-1))/(B² - n(d+1)q₀^(k-1))`. This is the paper's `(a - b)/(a² - b)`. Hypotheses: `B > (d+1)n/q₀` and `b < a²`. |
| Appendix A, Claim 4.8 for `c > B + n/q₀ - 1` | `ReedMuller.exists_affineRatioWitness_of_map`, `ReedMuller.isAffinePersistent_of_commonAgreement` | A rational explanation over an extension field descends to `F_q`. Dropping the at most `n/q₀` zeros of `L_σ` on the grid, by (7.1), leaves `B` agreements, so the candidate is persistent. |
| Lemma 3.2 with fibers | `Finset.card_le_of_fiber_card_le_of_inter_card_le` | The Johnson bound times the fiber size. The Reed–Solomon and Reed–Muller persistent counts both use it. |

## Port Ledger

The units describe the port plan, including results without Lean declarations.
A unit is done when its declarations are on `main`.

| Unit | Paper | Content | Depends on | Status |
| --- | --- | --- | --- | --- |
| 1 | §1.1, Definition 3.1, Propositions 6.1–6.2 | Definitions and error lower bounds for scalar combiners with loss `s` and affine combiners without loss | — | done ([#1504](https://github.com/Verified-zkEVM/ArkLib/pull/1504)) |
| 2 | Lemmas 4.4–4.5 | Counts for one rational pair and for persistent exceptional challenges | 1 | done ([#1505](https://github.com/Verified-zkEVM/ArkLib/pull/1505)) |
| 3 | Theorem 5.1 | Equal-degree error `≤ εaff + ℓ₀/q` and linear-claim error `≤ εaff + 2ℓ₀/q` | 1 | equal-degree bound done ([#1506](https://github.com/Verified-zkEVM/ArkLib/pull/1506)); linear claims planned |
| 4 | Proposition 6.3 | Scalar lower bound with constant fractional loss on additive domains | 1 | done ([#1507](https://github.com/Verified-zkEVM/ArkLib/pull/1507)) |
| 5 | Lemma 4.2 | Trivariate interpolation of `(1,e,d)`-weighted degree (Reed–Solomon `e = 1`) below `mA`, with multiplicity `m` along each received line, and vanishing after substitution | 1 | done ([#1508](https://github.com/Verified-zkEVM/ArkLib/pull/1508)) |
| 6 | Section 4 factorization and Lemma 4.3 | Frobenius normalization, excluded challenges `#E ≤ D²`, and simple roots outside `E` | 5 | done ([#1508](https://github.com/Verified-zkEVM/ArkLib/pull/1508)) |
| 7 | Lemma 3.11 | Rational Taylor coefficients `Nⱼ/S^(2j-1)` for `j ≥ 1`, numerator degree bounds, and polynomial-root reconstruction | — | coefficient and polynomial-root interfaces done ([#1508](https://github.com/Verified-zkEVM/ArkLib/pull/1508)); power-series existence and uniqueness open |
| 8 | Claims 4.8–4.9 and Lemma 4.7 | Agreement-hyperplane induction, a cover of dimension at most two, and the nonpersistent count | 2, 6, 7 | done ([#1509](https://github.com/Verified-zkEVM/ArkLib/pull/1509)) |
| 9 | Lemma 4.1 and Theorems 1.1, 4.10 | Parameter bounds and the final affine error bounds | 2, 5, 6, 8 | done ([#1509](https://github.com/Verified-zkEVM/ArkLib/pull/1509)) |
| 10 | Theorem 5.2 | For `k = 2ʳ` rows, shared folding with degree `d + r`, threshold `A + r`, loss `r`, and error at most `rε`, where `ε` bounds every round. The proof packs rows into `F_{q^t}` with base-field challenges | 9 | deferred |
| 11 | Theorem 7.1 and Appendix A | Reed–Muller extension on subfield grids through the Pellikaan–Wu reduction | 9 | definitions, bound (7.1), lower bound `q⁻ᵏ`, Lemma A.1, the Pellikaan–Wu reduction, the persistent count, the multiplier interpolation and the generic nonpersistent count in review; Reed–Muller nonpersistent count and Theorem 7.1 planned |

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

- [`AffineCombiner/EqualDegree.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegree.lean)
  defines the equal-degree error and proves its reduction to the affine error with the rounded Johnson bound.

- [`AffineCombiner/EqualDegreeSampling.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/EqualDegreeSampling.lean)
  identifies this error with the supremum of native uniform probabilities over three challenges.

- [`AffineCombiner/SubspaceSeparation.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/AffineCombiner/SubspaceSeparation.lean)
  proves the scalar lower bound with constant fractional agreement loss on additive domains.
  It uses the binary-group decomposition in `BinaryAddSubgroup.lean` and the degree bounds in
  `SubspacePolynomial.lean`.

- [`ReedMuller/Grid.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/Grid.lean)
  embeds the grid `K₀ᵏ` in `Fᵏ` and proves the hyperplane and Schwartz–Zippel counts.
- [`ReedMuller/AffineCombiner/Basic.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Basic.lean)
  defines the Reed–Muller affine combiner and its error.
- [`ReedMuller/AffineCombiner/Probability.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Probability.lean)
  identifies this error with native probabilities.
- [`ReedMuller/AffineCombiner/Separation.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Separation.lean)
  proves the lower bound `q⁻ᵏ`.
- [`ReedMuller/AffineCombiner/RationalPair.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/RationalPair.lean)
  proves Lemma A.1.
- [`ReedMuller/PellikaanWu.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/PellikaanWu.lean)
  maps Reed–Muller polynomials to univariate ones through the trace polynomials.
- [`ReedMuller/AffineCombiner/PellikaanWu.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/PellikaanWu.lean)
  transports agreement sets and the multiplier along that map.
- [`ReedMuller/AffineCombiner/Persistent.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/Persistent.lean)
  defines Reed–Muller persistence and bounds the persistent exceptional challenges.
- [`ReedMuller/AffineCombiner/PersistenceDescent.lean`](../../../ArkLib/Data/CodingTheory/ReedMuller/AffineCombiner/PersistenceDescent.lean)
  turns common agreements into persistence on the grid.

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

The Taylor chart is stated for any linear multiplier family `∑ⱼ aⱼ θⱼ`, with chart variables `Fin 1 ⊕ κ`.
Reed–Solomon is the family `(1, X)`.
The uniqueness step of Claim 4.8 is a hypothesis: polynomials of degree at most `d` killed by
the high cuts and by `B + e` of the functionals vanish.
Reed–Solomon discharges it with `d < B + 1` distinct evaluation points.
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

The Reed–Muller grid is `Fin k → K₀`, mapped into `Fᵏ` through `[Algebra K₀ F]`.
A challenge is a vector `Fin (k + 1) → F` whose entry `0` is the constant term.
Lemma A.1's affine independence is stated as: only the zero affine form vanishes on the `k + 1` points.
For `k = 1` these definitions match the univariate ones informally; no bridge is formalized.

The Pellikaan–Wu reduction works in any field `F'` containing both `F_q` and `F_n`.
It does not need the smallest such field.
Only three facts are transported: agreement counts, injectivity of `α ↦ L̃_α`, and injectivity of `P ↦ P̃` below degree `q₀`.
Witnesses are not transported, because the proof of Theorem 7.1 builds them on the Reed–Muller side.
Reed–Muller persistence names the denominator by its coefficient vector `σ`.
The zeros of `L_σ` on the grid are left out of the persistence set.
The Johnson factor is written with `q₀^(k-1)` in place of `n/q₀`.

## Open Formalization Gaps

The planned and deferred units in the ledger have no complete formalization in this port.
The affine-chart interface for Lemma 3.11 does not export formal-power-series existence and uniqueness.
The lower bound from Proposition 6.1 is exported, while its constructed received words and
separate global agreement assertion are internal to the proof.

The paper reports a Lean formalization of Theorem 1.1.
It states that the equal-degree reductions in Section 5 and the Reed–Muller extension in
Section 7 and Appendix A are outside that formalization.
The paper does not cite a formalization artifact.

## Source Access

- Source metadata: [`../sources/CWYZ26/metadata.yml`](../sources/CWYZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
