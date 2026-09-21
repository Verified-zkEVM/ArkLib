# Reed–Solomon first-tranche port ledger

This ledger records the six review units tracked by
[issue #907](https://github.com/Verified-zkEVM/ArkLib/issues/907). Commit
`a5aa2677fee4e3a79d6bb05136631cce4a08587d` is the immutable overarching paper-port snapshot and
the direct source for the weighted-support, exact-list, agreement-list, and pairwise-Johnson units.
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
| [Pairwise Johnson counting and code bound (#910)](https://github.com/Verified-zkEVM/ArkLib/pull/910) | source-private `card_mul_johnsonDenominator_le`; `closePolynomialSet_finite_and_ncard_le_johnsonPairwise` | `Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le` in `ArkLib.Data.Finset.PairwiseIntersection`; arbitrary-alphabet finite-family, complete-set, `Lambda`, and `IsListDecodable` results in `ArkLib.Data.CodingTheory.JohnsonBound.Pairwise`; thin Reed–Solomon specializations in `ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.PairwiseJohnson` | The generic Johnson layer does not depend on agreement-list incidence. The PR is stacked on #909 only because its Reed–Solomon polynomial specialization imports `AgreementList`. Keeps the sharp `n * (A - D)` numerator and avoids finite-alphabet, MCA, or geometric hypotheses. |
| Exact weighted products and divisors (#875) | `weightedTotalDegree_mul`, `weightedTotalDegree_prod`, `weightedTotalDegree_le_of_dvd`, `sum_weightedTotalDegree_le_of_prod_dvd` | `ArkLib.Data.MvPolynomial.WeightedDegree.Products` | Independent main-based module with direct Mathlib imports. Complements #857 without adding the same file. |

Each final head must pass `./scripts/validate.sh --axioms` without new admissions, native trust,
policy suppressions, or unauthorized dependency-pin changes. Before landing, refresh main, adapt against the merged
Lean 4.34 dependency APIs, rerun the full gate, and record the reviewed head in the pull request.

## Exact declaration inventory

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
