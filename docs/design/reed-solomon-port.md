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
| [P2 slice 1: row bases and uniform kernel height (#911)](https://github.com/Verified-zkEVM/ArkLib/pull/911) | `Matrix.exists_rows_fin_rank`, `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` in `ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean` | `Matrix.exists_rows_linearIndependent_span_eq` in `ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis` (no polynomial imports); `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT` and `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` in `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` | Arbitrary finite row and column index types replace `Fin`. The principal kernel theorem records `Polynomial.degreeLT` membership, which also constrains zero coordinates; the natural-degree theorem recovers the source statement. Deferred: the intrinsic-rank form `exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq`, primitive kernel vectors (`PrimitivePolynomialKernel.lean`), and column and shifted budgets (`ShiftedDegreeKernel.lean`). |
| [P12a slice 1: finite-submodule avoidance (#912)](https://github.com/Verified-zkEVM/ArkLib/pull/912) | `exists_vector_avoiding_submodules` in `ReedSolomon/Interleaved/PowerAgreement.lean` | `Submodule.exists_forall_notMem_of_card_le` in `ArkLib.ToMathlib.LinearAlgebra.Submodule.Union` | The source assumed a field and a finite nontrivial module. The destination assumes only a finite division ring and an arbitrary module, and keeps the sharp bound of at most `Nat.card K` proper submodules, which Mathlib's strict-cardinality theorem does not cover. It replaces two identical private proofs in `ProximityGap/Errors.lean` and `ProximityGap/LineDecoding.lean`. Deferred: the interleaving projection and the other P12a transfers. |
| [P2 slice 2: intrinsic-rank and primitive polynomial kernels (#914)](https://github.com/Verified-zkEVM/ArkLib/pull/914) | `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in `ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean`; `Matrix.exists_primitive_kernel_vector_preserving_zero`, `Matrix.exists_primitive_kernel_vector`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in `PrimitivePolynomialKernel.lean`; `Matrix.exists_primitive_kernel_vector_degreeLT` in `ShiftedDegreeKernel.lean` | `Matrix.exists_rows_submatrix_mulVec_eq_zero_iff` in `ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis`; `Finset.span_gcd`, `Ideal.span_range_eq_top_iff_univ_gcd_eq_one`, `Ideal.comp_ne_zero_of_span_range_eq_top`, `Matrix.exists_primitive_kernel_vector_eq_smul` in `ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel` (no polynomial imports); `Polynomial.natDegree_le_of_mem_degreeLT_succ`, `Polynomial.mem_degreeLT_of_mul_left` in `ArkLib.ToMathlib.Polynomial.DegreeLT`; `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`, `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le`, `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le` in `ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` | The source fixed the rank exactly, measured it over `RatFunc F`, and used `Fin` indices. The destination takes an upper bound `rank ≤ s` over any field receiving an injective hom, with arbitrary finite indices, so consumers no longer prove monotonicity of `s * b / (c - s)` themselves. The row-kernel transfer holds over any semiring embedded in a field. Primitive normalization is a separate non-polynomial theorem over Bézout rings with a normalized gcd, stated as `v = g • u` with `g ≠ 0` and unit-ideal `u`. The source's zero-preservation, per-coordinate degree, and `eval₂` specialization clauses follow from this factorization, `Polynomial.mem_degreeLT_of_mul_left`, and `Ideal.comp_ne_zero_of_span_range_eq_top` (any nontrivial semiring target, any index type). Not kept as named wrappers: `exists_primitive_kernel_vector_preserving_zero`, `exists_primitive_kernel_vector`, `exists_primitive_kernel_vector_degreeLT`, and the row-count primitive theorem (the rank form with `Matrix.rank_le_card_height`); `ArkLibTest` derives each in a few lines. Deferred: the shifted family (`exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`, `exists_primitive_mulVec_eq_zero_of_shifted_surplus`) and the column family (`exists_ne_zero_mulVec_eq_zero_column_degreeLT`, `_of_rank`, `exists_primitive_mulVec_eq_zero_of_column_surplus`). |
| [P4 slice 1: resultant specialization and specialization avoidance (#915)](https://github.com/Verified-zkEVM/ArkLib/pull/915) | `eval_derivative_ne_zero_of_separableResultant_eval_ne_zero`, `eval_derivative_ne_zero_of_separableResultant_map_ne_zero`, `specialization_separable_of_separableResultant_eval_ne_zero`, `finite_polynomial_specializations_eq_zero_card_le`, `exists_map_evalRingHom_ne_zero_avoiding`, `exists_map_evalRingHom_ne_zero` in `ToMathlib/Polynomial/SeparableResultant.lean`; `paddedDerivativeResultant_map_eq_zero_of_common_root` in `PaddedDerivativeResultantCommonRoot.lean`; `separableResultant_map_eq_zero_of_common_root` in `DerivativeResultantDegree.lean` | `Polynomial.map_resultant_eq_zero_of_common_root`, `eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero`, `natDegree_map_eq_of_resultant_derivative_padded_ne_zero`, `isCoprime_map_of_resultant_padded_ne_zero`, `separable_map_of_resultant_derivative_padded_ne_zero`, `resultant_comm_sub_one` in `ArkLib.Data.Polynomial.ResultantSpecialization`; `Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero`, `exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card`, `exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card`, `exists_map_evalRingHom_ne_zero_avoiding`, `exists_map_evalRingHom_ne_zero` in `ArkLib.Data.Polynomial.SpecializationAvoidance` | The source proves the common-root argument separately for `R[X]` and `R[X][X]` and assumes `IsDomain`. The destination states it once for any ring hom between commutative rings and any declared degrees, and derives the simple-root, coprimality, and separability statements from it. The source's `separableResultant A b = resultant A.derivative A (b - 1) b` equals main's order `resultant A A.derivative b (b - 1)` with no sign (`resultant_comm_sub_one`). A nonzero padded derivative resultant forces `f` to keep degree `m`, so these statements cover a drop in the derivative's degree only. Avoidance is stated from a finite candidate set, which also covers finite fields; the source's infinite-domain theorems keep their statements. Main's `isCoprime_map_of_resultant_ne_zero`, the common-root argument in `KKH26SumSet`, and `resultant_fixed_degree_eq_zero_of_common_root_of_monic_right` now derive from `map_resultant_eq_zero_of_common_root`. Deferred: the total-degree bounds `natDegree_separableResultant_add_sq_le*` and `natDegree_separableResultant_le_totalDegree*`, `separableResultant_ne_zero_of_irreducible`, and the Ordinary root-presentation consumers. |
| [P5 slice 1: agreement double counting after deletion (#919)](https://github.com/Verified-zkEVM/ArkLib/pull/919) | `AffineHilbert.finiteAgreementIncidence_lower_sharp` in `ToMathlib/AlgebraicGeometry/Incidence/SharpRatio.lean`; `AffineHilbert.finiteAgreementIncidence_lower` in `ToMathlib/Combinatorics/FiniteAgreementIncidence.lean` | `Finset.card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff`, `Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff`, `Finset.card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff`, `Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow`, `Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow` in `ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting` (Mathlib imports only) | The source indexed positions by `Fin n` and proved both bounds by separate copies of the same argument. The destination uses Mathlib's `bipartiteAbove`/`bipartiteBelow` vocabulary over an arbitrary type and an arbitrary position set `t`, with the `univ` versions summing over `uᶜ`; the `A - k + 1` form is a corollary of the sharp form and keeps `k ≤ A`, which a test shows is necessary. The source statements follow by `Finset.filter_notMem_eq_sdiff`. Deferred: `goodCuts_div_agreements_le` and the sharp-ratio layer; the consumer `affineAgreementIncidence_bound_aux` stays in the source. |

## Exact declaration inventory

The P5 double-counting unit owns `Finset.card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff`,
`Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff`,
`Finset.card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff`,
`Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow`, and
`Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow`.
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

The row-basis and kernel-height slice owns `Matrix.exists_rows_linearIndependent_span_eq`,
`Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT`, and
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le`. The submodule-avoidance slice owns
`Submodule.exists_forall_notMem_of_card_le`.

The intrinsic-rank and primitive-kernel slice owns
`Matrix.exists_rows_submatrix_mulVec_eq_zero_iff`, `Finset.span_gcd`, `Ideal.span_range_eq_top_iff_univ_gcd_eq_one`,
`Ideal.comp_ne_zero_of_span_range_eq_top`, `Matrix.exists_primitive_kernel_vector_eq_smul`,
`Polynomial.natDegree_le_of_mem_degreeLT_succ`, `Polynomial.mem_degreeLT_of_mul_left`,
`Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`,
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le`, and
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`.

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
