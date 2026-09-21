# Reed–Solomon beyond-Johnson port ledger

This ledger records the review units of the port tracked by
[issue #907](https://github.com/Verified-zkEVM/ArkLib/issues/907): the six first-tranche units
below and the later slices listed after them. Commit
`a5aa2677fee4e3a79d6bb05136631cce4a08587d` is the immutable overarching paper-port snapshot and
the direct source for the weighted-support, exact-list, agreement-list, and pairwise-Johnson units,
and for every later slice unless its entry names another source.
The fraction-field resultant and exact weighted-product units are sourced from their immutable
pull-request donor heads below; those theorem families are not present in `a5aa2677`. Donor heads
are source evidence, not merge bases. Final acceptance uses the main branch containing the Lean
4.34 migration from pull request #903.

Current heads, hosted CI, migration gates, and landing status are maintained in
[issue #907](https://github.com/Verified-zkEVM/ArkLib/issues/907), the canonical live dashboard.

The immutable donor heads for the refreshed pull requests are `f37f25ba3d0d6701f054c00cb53a7b73d363c0d0`
(#857), `8b1698ab6f73d89bcc36b7936a8ce87cd20bc9d4` (#877), and
`0ffecb528a8a63eb9522b68d7061e0b671339a47` (#875).

| Unit | Source declarations | Destination owner | Dependencies and overlap |
| --- | --- | --- | --- |
| Weighted support and substitution (#857) | `restrictWeightedDegree` and the exact inventory below; `MvPolynomial.aeval_shift_mem_restrictDegree` consumer in `EvenAndOdd.lean` | `ArkLib.Data.MvPolynomial.WeightedDegree`; acceptance canaries in `ArkLibTest` | Independent. Does not own exact product or divisor equalities. |
| Fraction-field resultant (#877) | `resultant_derivative_ne_zero_of_separable`, `isCoprime_map_of_resultant_ne_zero`, `separable_map_of_resultant_derivative_ne_zero`, `resultant_derivative_ne_zero_of_fractionField_separable`, `resultant_derivative_ne_zero_of_separable_map_fractionField` | `ArkLib.Data.Polynomial.FractionFieldResultant` | Independent. Reuses Mathlib's padded resultant identity and fraction-ring injection. |
| [Exact-list candidate filtering (#908)](https://github.com/Verified-zkEVM/ArkLib/pull/908), replacing #855 | `MessagePolynomial`, `Decoder`, `IsExactDecoder`, `DecoderCertificate`, `CandidateCertificate`, embeddings and filtered-decoder laws, exactness and oversized-threshold consequences | Generic exact finite-enumeration and candidate-filtering interfaces in `ArkLib.Data.Finset.Enumeration`; Reed–Solomon predicates and adapters in `ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification` | Independent. Replaces admitted hidden-derivative contracts with proved extensional interfaces; makes no running-time claim. |
| [Agreement-list finiteness and incidence (#909)](https://github.com/Verified-zkEVM/ArkLib/pull/909) | `closePolynomialSet`, `exists_closePolynomial_finset_with_incidence_bound`, `closePolynomialSet_finite` | Generic sample-incidence bounds in `ArkLib.Data.Finset.SampleIncidence`; arbitrary-code adapter in `ArkLib.Data.CodingTheory.ListDecodability.SampleIncidence`; Reed–Solomon specialization in `ArkLib.Data.CodingTheory.ReedSolomon.AgreementList`, including the added direct set corollary `closePolynomialSet_ncard_mul_choose_le` | The generic layers are independent. The Reed–Solomon specialization uses `ReedSolomon.polynomialAgreementSet` from #906. The source declarations `agreeingPolynomials`, `agreeingPolynomials_antitone`, `exists_finset_polynomial_list`, and `agreeingPolynomials_eq_empty_of_card_lt` are deferred until an exact-list consumer needs them. |
| [Pairwise Johnson counting and code bound (#910)](https://github.com/Verified-zkEVM/ArkLib/pull/910) | source-private `card_mul_johnsonDenominator_le`; `closePolynomialSet_finite_and_ncard_le_johnsonPairwise` | `Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le` in `ArkLib.Data.Finset.PairwiseIntersection`; arbitrary-alphabet finite-family, complete-set, `Lambda`, and `IsListDecodable` results in `ArkLib.Data.CodingTheory.JohnsonBound.Pairwise`; thin Reed–Solomon specializations in `ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.PairwiseJohnson` | The generic Johnson layer does not depend on agreement-list incidence. Only the Reed–Solomon polynomial specialization imports `AgreementList`. Keeps the sharp `n * (A - D)` numerator and avoids finite-alphabet, MCA, or geometric hypotheses. |
| Exact weighted products and divisors (#875) | `weightedTotalDegree_mul`, `weightedTotalDegree_prod`, `weightedTotalDegree_le_of_dvd`, `sum_weightedTotalDegree_le_of_prod_dvd` | `ArkLib.Data.MvPolynomial.WeightedDegree.Products` | Independent main-based module with direct Mathlib imports. Complements #857 without adding the same file. |

Each final head must pass `./scripts/validate.sh --axioms` without new admissions, native trust,
policy suppressions, or unauthorized dependency-pin changes. Before landing, refresh main, adapt against the merged
Lean 4.34 dependency APIs, rerun the full gate, and record the reviewed head in the pull request.

## Later slices

Each row is one bounded slice of a work package from issue #907. A package is not complete until
its remaining units, listed under deferred scope, are ported or explicitly retired.

| Unit | Source declarations | Destination owner | Generalization and deferred scope |
| --- | --- | --- | --- |
| [P1 slice 1: partial-derivative and weighted-degree laws (#921)](https://github.com/Verified-zkEVM/ArkLib/pull/921) | `degreeOf_pderiv_le_sub_one`, `degreeOf_pderiv_le`, `pderiv_ne_zero_of_degreeOf_pos_of_lt_ringChar`, `degreeOf_pderiv_eq_sub_one_of_lt_ringChar`, `iteratePDeriv`, `degreeOf_iteratePDeriv_le`, `degreeOf_iteratePDeriv_eq_sub_of_lt_ringChar`, `iteratePDeriv_ne_zero_of_lt_ringChar` in `ToMathlib/MvPolynomial/PDeriv.lean`; `pderiv_ne_zero_and_degreeOf_eq_sub_one_of_natCast_ne_zero` in `HiddenDerivative/Interpolation/FirstOrder/HybridDescent.lean`; `weightedTotalDegree_pderiv_le_sub`, `weightedTotalDegree_pderiv_le`, `natDegree_differentialSpecialization_le` in `HiddenDerivative/RootFinding/DegreeBounds/SpecializationDegree.lean` | `MvPolynomial.degreeOf_pderiv_le_sub_one`, `degreeOf_pderiv_le`, `coeff_pderiv_sub_single_one`, `pderiv_ne_zero_of_natCast_ne_zero`, `degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero`, `degreeOf_iterate_pderiv_le_sub`, `degreeOf_iterate_pderiv_le`, `pderiv_eq_zero_of_degreeOf_eq_zero`, `iterate_pderiv_eq_zero_of_degreeOf_lt`, `degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero`, `iterate_pderiv_ne_zero_of_natCast_ne_zero`, and `natCast_ne_zero_of_ringChar_eq_zero_or_lt` in `ArkLib.ToMathlib.MvPolynomial.PDeriv`; `MvPolynomial.weightedTotalDegree_pderiv_le_sub`, `weightedTotalDegree_pderiv_le`, `pderiv_mem_restrictWeightedDegree`, `natDegree_aeval_le_weightedTotalDegree`, `natDegree_aeval_le_weightedTotalDegree_of_le` in `ArkLib.Data.MvPolynomial.WeightedDegree` | The source's `0 < degreeOf i p`, `degreeOf i p < ringChar R` and `[Nontrivial R]` become one cast hypothesis `(degreeOf i p : R) ≠ 0` with `[NoZeroDivisors R]`, which covers characteristic zero; `natCast_ne_zero_of_ringChar_eq_zero_or_lt` converts the old guard. The iterate hypothesis names only the `a` differentiated degrees, so it also covers degrees above the characteristic (for example one derivative of `X^6` over `ZMod 5`) and implies `a ≤ degreeOf i p`; nonvanishing of iterates takes `p ≠ 0`. Iterates are Mathlib's `(pderiv i)^[a]` instead of the source's `iteratePDeriv`. The weighted-derivative bounds hold for any variable type, not only jet variables, and the univariate-substitution bound is the general form behind `natDegree_differentialSpecialization_le`. Deferred: the `_of_lt_ringChar` wrappers (consumers compose with the guard lemma), the jet-specific specialization statement and separant corollaries (P1 PR2), and the root-counting wrappers. |
| P1 slice 2: differential-polynomial core | `JetVariable`, `DifferentialPolynomial`, `differentialSpecializationHom`, `differentialSpecialization`, `jetEvaluation`, `polynomialJet`, `jetDegree`, `separant`, `differentialWeight`, and `differentialWeightedDegree` in `Data/Polynomial/Differential/{Types,Basic}.lean`; `natDegree_differentialVariable_le`, `natDegree_differentialSpecialization_le`, and the two separant specialization bounds in `HiddenDerivative/RootFinding/DegreeBounds/SpecializationDegree.lean`; `jetTotalDegree`, `jetTotalDegree_le_iff`, `jetDegree_le_total`, and `separant_total_le` in `HiddenDerivative/RootFinding/Counting/TotalJetDegreeRootCount.lean`; exponent-level `totalJetDegree` in `HiddenDerivative/Interpolation/Space.lean` | `ArkLib.Data.Polynomial.Differential.Types` owns the shared variable and polynomial abbreviations; `.Basic` owns the specialization homomorphism, generator equations, scalar-jet evaluation, and evaluation comparison; `.JetDegree` owns individual, specialization-weighted, exponent-level, and polynomial total-jet degrees and their bridges. Ordinary-import clients are in `ArkLibTest.Data.Polynomial.Differential.{Basic,JetDegree}`. | The specialization and degree upper bounds hold over any commutative semiring and need no characteristic guard. The exponent-level `totalJetDegree` moves forward from P3 into this generic owner and is definitionally built from the same `jetDegreeWeight` as polynomial `jetTotalDegree`; `totalJetDegree_eq_degree_some` preserves the source interpolation spelling. Zero specialization weights remain valid but do not imply finite-dimensional support. Exact separant nonvanishing continues to use P1 slice 1's cast hypotheses. Deferred: bounded solutions, active/highest jets, regular jets, characteristic certificates, Taylor/contact/multiplicity/descent, partial jet fibers, and every root-counting theorem. |
| [P2 slice 1: row bases and uniform kernel height (#911)](https://github.com/Verified-zkEVM/ArkLib/pull/911) | `Matrix.exists_rows_fin_rank`, `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` in `ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean` | `Matrix.exists_rows_linearIndependent_span_eq` in `ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis` (no polynomial imports); `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT` and `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` in `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` | Arbitrary finite row and column index types replace `Fin`. The principal kernel theorem records `Polynomial.degreeLT` membership, which also constrains zero coordinates; the natural-degree theorem recovers the source statement. Deferred: the intrinsic-rank form `exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq`, primitive kernel vectors (`PrimitivePolynomialKernel.lean`), and column and shifted budgets (`ShiftedDegreeKernel.lean`). |
| [P12a slice 1: finite-submodule avoidance (#912)](https://github.com/Verified-zkEVM/ArkLib/pull/912) | `exists_vector_avoiding_submodules` in `ReedSolomon/Interleaved/PowerAgreement.lean` | `Submodule.exists_forall_notMem_of_card_le` in `ArkLib.ToMathlib.LinearAlgebra.Submodule.Union` | The source assumed a field and a finite nontrivial module. The destination assumes only a finite division ring and an arbitrary module, and keeps the sharp bound of at most `Nat.card K` proper submodules, which Mathlib's strict-cardinality theorem does not cover. It replaces two identical private proofs in `ProximityGap/Errors.lean` and `ProximityGap/LineDecoding.lean`. Deferred: the interleaving projection and the other P12a transfers. |
| [P5 slice 1: agreement double counting after deletion (#919)](https://github.com/Verified-zkEVM/ArkLib/pull/919) | `AffineHilbert.finiteAgreementIncidence_lower_sharp` in `ToMathlib/AlgebraicGeometry/Incidence/SharpRatio.lean`; `AffineHilbert.finiteAgreementIncidence_lower` in `ToMathlib/Combinatorics/FiniteAgreementIncidence.lean` | `Finset.card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff`, `Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff`, `Finset.card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff`, `Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow`, `Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow` in `ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting` (Mathlib imports only) | The source indexed positions by `Fin n` and proved both bounds by separate copies of the same argument. The destination uses Mathlib's `bipartiteAbove`/`bipartiteBelow` vocabulary over an arbitrary type and an arbitrary position set `t`, with the `univ` versions summing over `uᶜ`; the `A - k + 1` form is a corollary of the sharp form and keeps `k ≤ A`, which a test shows is necessary. The source statements follow by `Finset.filter_notMem_eq_sdiff`. Deferred: `goodCuts_div_agreements_le` and the sharp-ratio layer; the consumer `affineAgreementIncidence_bound_aux` stays in the source. |
| [P2 slice 2: intrinsic-rank and primitive polynomial kernels (#914)](https://github.com/Verified-zkEVM/ArkLib/pull/914) | `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in `ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean`; `Matrix.exists_primitive_kernel_vector_preserving_zero`, `Matrix.exists_primitive_kernel_vector`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in `PrimitivePolynomialKernel.lean`; `Matrix.exists_primitive_kernel_vector_degreeLT` in `ShiftedDegreeKernel.lean` | `Matrix.exists_rows_submatrix_mulVec_eq_zero_iff` in `ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis`; `Finset.span_gcd`, `Ideal.span_range_eq_top_iff_univ_gcd_eq_one`, `Ideal.comp_ne_zero_of_span_range_eq_top`, `Matrix.exists_primitive_kernel_vector_eq_smul` in `ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel` (no polynomial imports); `Polynomial.natDegree_le_of_mem_degreeLT_succ`, `Polynomial.mem_degreeLT_of_mul_left` in `ArkLib.ToMathlib.Polynomial.DegreeLT`; `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`, `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le` in `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` | The source fixed the rank exactly, measured it over `RatFunc F`, and used `Fin` indices. The destination takes an upper bound `rank ≤ s` over any field receiving an injective hom, with arbitrary finite indices, so consumers no longer prove monotonicity of `s * b / (c - s)` themselves. The row-kernel transfer holds over any semiring embedded in a field. Primitive normalization is a separate non-polynomial theorem over Bézout rings with a normalized gcd, stated as `v = g • u` with `g ≠ 0` and unit-ideal `u`. The source's zero-preservation, per-coordinate degree, and `eval₂` specialization clauses follow from this factorization, `Polynomial.mem_degreeLT_of_mul_left`, and `Ideal.comp_ne_zero_of_span_range_eq_top` (any nontrivial semiring target, any index type). Not kept as named wrappers: `exists_primitive_kernel_vector_preserving_zero`, `exists_primitive_kernel_vector`, `exists_primitive_kernel_vector_degreeLT`, and the row-count primitive theorem (the rank form with `Matrix.rank_le_card_height`); `ArkLibTest` derives each in a few lines. Deferred: the shifted family (`exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`, `exists_primitive_mulVec_eq_zero_of_shifted_surplus`) and the column family (`exists_ne_zero_mulVec_eq_zero_column_degreeLT`, `_of_rank`, `exists_primitive_mulVec_eq_zero_of_column_surplus`). |
| [P2 slice 3: shifted and column-budget polynomial kernels (#920)](https://github.com/Verified-zkEVM/ArkLib/pull/920) | `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`, `Matrix.exists_primitive_kernel_vector_degreeLT`, `Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus` in `ToMathlib/LinearAlgebra/ShiftedDegreeKernel.lean`; `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`, `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank`, `Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus` in `ColumnDegreeKernel.lean` | `Polynomial.mem_degreeLT_add_one_sub_iff`; `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT` and `_of_natDegree_le`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT` and `_of_natDegree_le`, `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`, `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le` in `ArkLib.ToMathlib.LinearAlgebra.ShiftedPolynomialKernelHeight`; `Matrix.exists_primitive_kernel_vector_degreeLT` in `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` | Arbitrary finite indices replace `Fin`. The source's `hdegree`/`hzero` pair becomes one entry hypothesis `M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i)` (equivalent by `mem_degreeLT_add_one_sub_iff`), required only for columns of weight at most `h`; source-shaped `_of_natDegree_le` forms remain. The column rank form takes `rank (M.map φ) ≤ s` for any injective `φ` into a field instead of the exact rank over `RatFunc F`. The primitive column form keeps each budget `degreeLT F (h + 1 - weight j)` where the source weakened it to `natDegree ≤ h`. `exists_primitive_kernel_vector_degreeLT`, listed as not kept in the #914 row, is restored as a public lemma because both shifted primitive forms and the uniform primitive form now use it. A shifted rank form is omitted: the row-slot sum depends on which rows are selected, so the rank alone does not determine the bound (explained in the module docstring). The `eval₂` specialization clauses follow from `Ideal.comp_ne_zero_of_span_range_eq_top`. Consumers in `HiddenDerivative/Interpolation/Symbolic/{ColumnHeight,CurveColumnHeight}.lean` stay in the source. |
| [P4 slice 1: resultant specialization and specialization avoidance (#915)](https://github.com/Verified-zkEVM/ArkLib/pull/915) | `eval_derivative_ne_zero_of_separableResultant_eval_ne_zero`, `eval_derivative_ne_zero_of_separableResultant_map_ne_zero`, `specialization_separable_of_separableResultant_eval_ne_zero`, `finite_polynomial_specializations_eq_zero_card_le`, `exists_map_evalRingHom_ne_zero_avoiding`, `exists_map_evalRingHom_ne_zero` in `ToMathlib/Polynomial/SeparableResultant.lean`; `paddedDerivativeResultant_map_eq_zero_of_common_root` in `PaddedDerivativeResultantCommonRoot.lean`; `separableResultant_map_eq_zero_of_common_root` in `DerivativeResultantDegree.lean` | `Polynomial.map_resultant_eq_zero_of_common_root`, `eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero`, `natDegree_map_eq_of_resultant_derivative_padded_ne_zero`, `isCoprime_map_of_resultant_padded_ne_zero`, `separable_map_of_resultant_derivative_padded_ne_zero`, `resultant_comm_sub_one` in `ArkLib.Data.Polynomial.ResultantSpecialization`; `Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero`, `exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card`, `exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card`, `exists_map_evalRingHom_ne_zero_avoiding`, `exists_map_evalRingHom_ne_zero` in `ArkLib.Data.Polynomial.SpecializationAvoidance` | The source proves the common-root argument separately for `R[X]` and `R[X][X]` and assumes `IsDomain`. The destination states it once for any ring hom between commutative rings and any declared degrees, and derives the simple-root, coprimality, and separability statements from it. The source's `separableResultant A b = resultant A.derivative A (b - 1) b` equals main's order `resultant A A.derivative b (b - 1)` with no sign (`resultant_comm_sub_one`). A nonzero padded derivative resultant forces `f` to keep degree `m`, so these statements cover a drop in the derivative's degree only. Avoidance is stated from a finite candidate set, which also covers finite fields; the source's infinite-domain theorems keep their statements. Main's `isCoprime_map_of_resultant_ne_zero`, the common-root argument in `KKH26SumSet`, and `resultant_fixed_degree_eq_zero_of_common_root_of_monic_right` now derive from `map_resultant_eq_zero_of_common_root`. Deferred: the total-degree bounds `natDegree_separableResultant_add_sq_le*` and `natDegree_separableResultant_le_totalDegree*`, `separableResultant_ne_zero_of_irreducible`, and the Ordinary root-presentation consumers. |
| [P5 slice 2: retained minimal primes and zero-locus covers (#922)](https://github.com/Verified-zkEVM/ArkLib/pull/922) | `AffineHilbert.minimalPrimesFinset`, `mem_minimalPrimesFinset` in `ToMathlib/AlgebraicGeometry/PrincipalCut/ComponentCoefficient.lean`; `retainedMinimalPrimes`, `mem_retainedMinimalPrimes`, `exists_retainedMinimalPrime_of_mem_zeroLocus`, `mem_zeroLocus_and_eval_ne_zero_iff_retained`, `mem_zeroLocus_and_cut_iff_retained` in `PrincipalOpen/Cuts.lean` | `Ideal.minimalPrimesFinset`, `mem_minimalPrimesFinset`, `coe_minimalPrimesFinset`, `minimalPrimesFinset_eq_empty_iff`, `minimalPrimesFinset_of_isPrime`, `retainedMinimalPrimes`, `mem_retainedMinimalPrimes`, `retainedMinimalPrimes_subset`, `exists_mem_retainedMinimalPrimes_le`, `retainedMinimalPrimes_eq_empty_iff`, `retainedMinimalPrimes_of_isUnit` in `ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian`; `MvPolynomial.mem_zeroLocus_iff_le_ker_aeval`, `zeroLocus_sup`, `mem_zeroLocus_sup_span_singleton_iff`, `exists_retainedMinimalPrime_of_mem_zeroLocus`, `mem_zeroLocus_and_eval_ne_zero_iff_retained`, `mem_zeroLocus_and_cut_iff_retained` in `ArkLib.ToMathlib.RingTheory.Nullstellensatz` | The finite minimal-prime family and the retained filter hold for any Noetherian commutative semiring, not only `MvPolynomial σ F` with finite `σ`; there is one representation (the source had a second `toFinset` in `Cuts.lean`). The algebraic cover step `exists_mem_retainedMinimalPrimes_le` is public; emptiness is characterized by `s ∈ I.radical`. The point covers hold over any field extension, with no algebraic closure. `mem_retainedMinimalPrimes` now takes implicit arguments, so source call sites `(Ideal.mem_retainedMinimalPrimes _ _ _).mp` become `Ideal.mem_retainedMinimalPrimes.mp`. Deferred: `Ideal.lt_of_mem_minimalPrimes_sup_span` and the principal-cut Krull-dimension drop, the `ZeroLocus/ZeroDimensional.lean` finite-quotient results, and the consumers `initialJetPrimeFamily_prime_open`, `exists_mem_initialJetPrimeFamily_of_regular`, `card_filter_cut_le_sum_retained`. |
| [P9 slice 1: discrete weighted-simplex counts (#917)](https://github.com/Verified-zkEVM/ArkLib/pull/917) | `OrdinarySimplex`, `ExactSimplex`, `ordinaryToExact`, `ordinarySimplexEquivSym`, `card_ordinarySimplex` in `ToMathlib/Combinatorics/DiscreteSimplex/Basic.lean`; `ScaledResidue`, `card_scaledResidue`, `ordinaryToScaledWithResidue` and its injectivity theorem, `scaledWithResidueToOrdinary` and its injectivity theorem, `pow_le_factorial_mul_card_ordinarySimplex`, `factorial_mul_card_ordinarySimplex_le_pow`, `scaledExponentCount_factorial_sq_sandwich` in `HiddenDerivative/Parameters/Lattice/ScaledLattice.lean`; `weightedHigherJetTuples`, `higherJetTupleWeight`, `higherJetTuple_apply_le_weight`, `mem_weightedHigherJetTuples` in `HiddenDerivative/Interpolation/Counting.lean`; `ratePartitionTupleCount_factorial_sandwich` and `ratePartitionTupleCount_le_volume` in `RatePartition/RankEstimate.lean` are motivating consumers | `Finset.natWeightedSimplex` and its membership, unit-weight stars-and-bars, binomial comparisons, factorial sandwich, ordered-field upper bound, and `1, …, n` specialization in `ArkLib.Data.Finset.WeightedSimplex`; acceptance cases in `ArkLibTest.Data.Finset.WeightedSimplex` | Arbitrary finite indices and positive natural weights replace `Fin (d - 1)` and weights `i + 1`. Quotient/remainder maps stay private; their public cardinal comparisons retain the sharp binomial bounds. The lower power bound strengthens `W^n` to `(W+1)^n`. The upper bound also handles zero weights, while the finite box keeps the set computable. The ordered-field bound is the form needed by `ratePartitionTupleCount_le_volume`, and the specialization uses `(n+1).choose 2` instead of natural division. Deferred: the public exact-simplex equivalence, `Finsupp` count bridge, shell and good-exponent counts, continuous simplex volumes, floor-cell transfers, and moments. |
| P9 slice 3: continuous simplex volumes and Dirichlet integrals | `integral_pow_mul_sub_pow` in `ToMathlib/Analysis/Simplex/MonomialIntegral.lean` (with `monomialIntegral`, `monomialIntegral_eq`); `standardSimplex`, `simplexMonomial`, `isCompact_standardSimplex`, `integrableOn_simplexMonomial`, `integral_standardSimplex_succ`, `integral_standardSimplex_eq_monomialIntegral`, `integral_standardSimplex_eq`, `volume_standardSimplex` in `VolumeIntegral.lean`; `coordinateWeight`, `weightedSimplex`, `weightedToStandard`, `standardToWeighted`, `weightedStandardLinearEquiv`, `weightedToStandard_det`, `integral_weightedSimplex_eq_standardSimplex`, `volume_weightedSimplex` in `AffinePushforward.lean` | `integral_pow_mul_one_sub_pow`, `integral_pow_mul_sub_pow` in `ArkLib.ToMathlib.Analysis.Simplex.MonomialIntegral`; `Set.standardSimplex`, `MeasureTheory.setIntegral_standardSimplex_comp_equiv`, `setIntegral_standardSimplex_succ`, `integral_standardSimplex_prod_pow_mul_pow`, `volume_real_standardSimplex`, `volume_standardSimplex` in `...Simplex.VolumeIntegral`; `Set.weightedSimplex`, `MeasureTheory.setIntegral_weightedSimplex`, `integral_weightedSimplex_prod_pow_mul_pow`, `volume_real_weightedSimplex`, `volume_weightedSimplex`, `volume_real_weightedSimplex_succ` in `...Simplex.WeightedVolume`; acceptance cases in the matching `ArkLibTest` files | Arbitrary `Fintype` indices and arbitrary positive real weights replace `Fin n` and `i + 1`; the source's weighted volume is the specialization `volume_real_weightedSimplex_succ`. The beta integral comes from Mathlib's `Complex.betaIntegral` and needs no sign condition on `L`; the Fubini step holds for any integrable function. The list-indexed `monomialIntegral` is dropped because the Fubini recurrence evaluates the integral directly; the diagonal change-of-variables maps are private. Tests show that `0 ≤ L`, positive weights, and `0 ≤ W` are each needed. Deferred: `Simplex/Moments.lean` (linear-form moments, weighted radius, expectations), `RatePartition/{OrderedSimplex,Moment,SharpMoment}.lean`, and floor-cell transfers. |
| [P12a slice 2: generic interleaving transfer (#918)](https://github.com/Verified-zkEVM/ArkLib/pull/918) | Source-private `interleaved_powerProjectionBad_card_le` in `ReedSolomon/Interleaved/PowerAgreement.lean`, `interleaved_powerProjectionBadArbitrary_finset_card_le` in `PowerAgreementArbitrary.lean`, and `interleaved_lineProjectionBad_card_le` in `TensorFoldAgreement.lean`, all at `a5aa2677`; main's `ProximityGap.mcaError_interleaved_le` | Seed-free `Code.projectedWord_rowCombination_mem`, `Code.goodRowFunctionals`, and `Code.exists_rowFunctional_forall_notMem` in `ArkLib.Data.CodingTheory.InterleavedCode.Projection`; seedwise and numeric transfer in `ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving` | Depends on #912 for sharp finite-field avoidance. An arbitrary generator with at most `|F|` seeds has `mcaError G (C^⋈κ) δ ≤ mcaError G C δ` for finite `κ` and any real `δ`; the reverse holds for every generator and nonempty `κ`, even infinite. The equality needs both bounds. Existing affine-line inequalities in `ProximityGap.Errors` and `TensorMCA.isMCAGenerator_of_moduleInterleavedCode` now consume these theorems without changing signatures; ordinary-import clients cover powers, empty and nonempty rows, and the seed-free lemma over `ℚ`. Semiring row helpers work at `Type*`; the unified finite/infinite avoidance lemma uses `Field` because pinned Mathlib's infinite-submodule avoidance requires it, while #912's finite lemma works over a division ring. Deferred: the source's scalar exception-set counting and exact-agreement wrappers, Jo26's field-size-weighted case `|S| > |F|`, and the separate tensor-tight theorem. |

## Exact declaration inventory

The P9 discrete-simplex unit owns `Finset.natWeightedSimplex`,
`Finset.weightedSum_le_of_mem_natWeightedSimplex`, `Finset.mem_natWeightedSimplex`,
`Finset.card_natWeightedSimplex_one`, `Finset.choose_le_card_natWeightedSimplex_mul_prod`,
`Finset.card_natWeightedSimplex_mul_prod_le_choose`,
`Finset.succ_pow_le_factorial_mul_prod_mul_card_natWeightedSimplex`,
`Finset.factorial_mul_prod_mul_card_natWeightedSimplex_le`,
`Finset.card_natWeightedSimplex_le`, and `Finset.natWeightedSimplex_succ_sandwich`.
The source revision for this unit is `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

The weighted-support unit owns `restrictWeightedDegree`, `mem_restrictWeightedDegree`,
`mem_restrictWeightedDegree_iff_weightedTotalDegree_le`, `restrictWeightedDegree_mono`,
`restrictWeightedDegree_one`, `mem_restrictDegree_iff_forall_mem_restrictWeightedDegree_piSingle`,
`monomial_mem_restrictWeightedDegree`, `C_mem_restrictWeightedDegree`,
`X_mem_restrictWeightedDegree`, `mul_mem_restrictWeightedDegree`,
`pow_mem_restrictWeightedDegree`, `weightedTotalDegree_mul_le`, `weightedTotalDegree_C`,
`weightedTotalDegree_monomial`, `weightedTotalDegree_pow_le`, `weightedTotalDegree_bind₁_le`,
`weightedTotalDegree_bind₁_le_of_le`, `weightedTotalDegree_aeval_le`,
`weightedTotalDegree_aeval_le_of_le`, `bind₁_mem_restrictWeightedDegree`,
`aeval_mem_restrictWeightedDegree`, `bind₁_comp_mem_restrictWeightedDegree`,
`X_pow_mem_restrictWeightedDegree_zero`, `eq_zero_of_mem_restrictWeightedDegree_zero`,
`eq_C_coeff_zero_of_mem_restrictWeightedDegree_zero`, `weightedDegreeZeroSubalgebra`,
`mem_weightedDegreeZeroSubalgebra`, `basisRestrictWeightedDegree`,
`basisRestrictWeightedDegree_repr_apply`, `restrictWeightedDegreeCoeff`,
`restrictWeightedDegreeCoeff_apply`, `coeff_eq_zero_of_mem_restrictWeightedDegree`,
`weightedDegreeSupport_finite`, `restrictWeightedDegree_fg`, and `finrank_restrictWeightedDegree`.

The P1 partial-derivative unit owns `natCast_ne_zero_of_ringChar_eq_zero_or_lt`,
`MvPolynomial.degreeOf_pderiv_le_sub_one`, `MvPolynomial.degreeOf_pderiv_le`,
`MvPolynomial.coeff_pderiv_sub_single_one`, `MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero`,
`MvPolynomial.degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero`,
`MvPolynomial.degreeOf_iterate_pderiv_le_sub`, `MvPolynomial.degreeOf_iterate_pderiv_le`,
`MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero`,
`MvPolynomial.iterate_pderiv_eq_zero_of_degreeOf_lt`,
`MvPolynomial.degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero`,
`MvPolynomial.iterate_pderiv_ne_zero_of_natCast_ne_zero`,
`MvPolynomial.weightedTotalDegree_pderiv_le_sub`, `MvPolynomial.weightedTotalDegree_pderiv_le`,
`MvPolynomial.pderiv_mem_restrictWeightedDegree`,
`MvPolynomial.natDegree_aeval_le_weightedTotalDegree`, and
`MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le`.
The source revision for this unit is `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

The P1 differential-polynomial core owns `PolynomialDifferential.JetVariable`,
`DifferentialPolynomial`, `differentialSpecializationHom`, `differentialSpecialization`,
`differentialSpecializationHom_apply`, `differentialSpecialization_C`,
`differentialSpecialization_x`, `differentialSpecialization_jet`, `jetEvaluation`,
`polynomialJet`, `eval_differentialSpecialization`, `jetDegree`, `separant`,
`differentialWeight`, `differentialWeight_none`, `differentialWeight_some`,
`differentialWeight_some_pos_of_order_lt_degree`, `differentialWeight_top_eq_zero`,
`differentialWeightedDegree`, `differentialWeightedDegree_map_eq`,
`natDegree_differentialVariable_le`, `natDegree_differentialSpecialization_le`,
`natDegree_differentialSpecialization_separant_le_sub`,
`natDegree_differentialSpecialization_separant_le`, `jetDegreeWeight`,
`jetDegreeWeight_none`, `jetDegreeWeight_some`, `totalJetDegree`, `totalJetDegree_eq_sum`,
`totalJetDegree_eq_degree_some`, `jetTotalDegree`, `jetTotalDegree_le_iff`,
`jetDegree_le_total`, and `separant_total_le`. The source revision for this unit is
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

The exact-list unit owns the generic `Finset.Enumeration`, `Finset.IsExactEnumeration`,
`Finset.EnumerationCertificate`, `Finset.CandidateCertificate`, `Finset.filterCandidates`,
and their membership, cardinality, exactness, soundness, completeness, and empty-enumeration laws.
Its Reed–Solomon adapter owns `MessagePolynomial`, `Decoder`, `IsExactDecoder`,
`DecoderCertificate`, `CandidateCertificate`, `messagePolynomialEmbedding`,
`messagePolynomialValue`, `messagePolynomialValue_apply`,
`CandidateCertificate.filteredDecoder`, `CandidateCertificate.mem_filteredDecoder`,
`CandidateCertificate.filteredDecoder_isExact`, `CandidateCertificate.filteredDecoder_card_le`,
`CandidateCertificate.toDecoderCertificate`, `DecoderCertificate.agreement_le_of_mem`,
`DecoderCertificate.mem_of_agreement_le`, `IsExactDecoder.decoder_eq_empty_of_card_lt`, and
`DecoderCertificate.decoder_eq_empty_of_card_lt`.

The P5 double-counting unit owns `Finset.card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff`,
`Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff`,
`Finset.card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff`,
`Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow`, and
`Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow`.
The source revision for this unit is `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

The row-basis and kernel-height slice owns `Matrix.exists_rows_linearIndependent_span_eq`,
`Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT`, and
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le`. The submodule-avoidance slice owns
`Submodule.exists_forall_notMem_of_card_le`.

The generic interleaving slice owns `Code.projectedWord_rowCombination_mem`,
`Code.goodRowFunctionals`, `Code.mem_goodRowFunctionals_iff`,
`Code.goodRowFunctionals_eq_top_iff`, and `Code.exists_rowFunctional_forall_notMem` in
`ArkLib.Data.CodingTheory.InterleavedCode.Projection`. Its generator layer owns
`CoreDefinitions.exists_forall_isMCA_of_forall_isMCA_interleaved`,
`CoreDefinitions.mcaError_moduleInterleavedCode_le_of_card_le`,
`CoreDefinitions.mcaError_le_mcaError_moduleInterleavedCode`, and
`CoreDefinitions.mcaError_moduleInterleavedCode_eq_of_card_le` in
`ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving`.

The intrinsic-rank and primitive-kernel slice owns
`Matrix.exists_rows_submatrix_mulVec_eq_zero_iff`, `Finset.span_gcd`, `Ideal.span_range_eq_top_iff_univ_gcd_eq_one`,
`Ideal.comp_ne_zero_of_span_range_eq_top`, `Matrix.exists_primitive_kernel_vector_eq_smul`,
`Polynomial.natDegree_le_of_mem_degreeLT_succ`, `Polynomial.mem_degreeLT_of_mul_left`,
`Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`,
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le`, and
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`.

The P2 shifted-kernel unit owns `Polynomial.mem_degreeLT_add_one_sub_iff`,
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`,
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`,
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT`,
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`,
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`,
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`,
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`, and
`Matrix.exists_primitive_kernel_vector_degreeLT`.
The source revision for this unit is `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

The resultant-specialization slice owns `Polynomial.resultant_comm_sub_one`,
`Polynomial.map_resultant_eq_zero_of_common_root`,
`Polynomial.eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero`,
`Polynomial.natDegree_map_eq_of_resultant_derivative_padded_ne_zero`,
`Polynomial.isCoprime_map_of_resultant_padded_ne_zero`,
`Polynomial.separable_map_of_resultant_derivative_padded_ne_zero`,
`Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero`,
`Polynomial.exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card`,
`Polynomial.exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card`,
`Polynomial.exists_map_evalRingHom_ne_zero_avoiding`, and
`Polynomial.exists_map_evalRingHom_ne_zero`.

The P5 minimal-prime unit owns `Ideal.minimalPrimesFinset`, `Ideal.mem_minimalPrimesFinset`,
`Ideal.coe_minimalPrimesFinset`, `Ideal.minimalPrimesFinset_eq_empty_iff`,
`Ideal.minimalPrimesFinset_of_isPrime`, `Ideal.retainedMinimalPrimes`,
`Ideal.mem_retainedMinimalPrimes`, `Ideal.retainedMinimalPrimes_subset`,
`Ideal.exists_mem_retainedMinimalPrimes_le`, `Ideal.retainedMinimalPrimes_eq_empty_iff`,
`Ideal.retainedMinimalPrimes_of_isUnit`, `MvPolynomial.mem_zeroLocus_iff_le_ker_aeval`,
`MvPolynomial.zeroLocus_sup`, `MvPolynomial.mem_zeroLocus_sup_span_singleton_iff`,
`MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus`,
`MvPolynomial.mem_zeroLocus_and_eval_ne_zero_iff_retained`, and
`MvPolynomial.mem_zeroLocus_and_cut_iff_retained`.
The source revision for this unit is `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
