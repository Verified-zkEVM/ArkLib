# Paper Audit: BCIKS20 Appendix A Rational Functions

This page tracks the local ArkLib status of Appendix A of `BCIKS20`, which supplies the
rational-function and Hensel-lifting machinery used by the list-decoding branch of the
Reed-Solomon proximity-gap formalization.

## Scope

The relevant Lean surface is
[`ArkLib/Data/Polynomial/RationalFunctions.lean`](../../../ArkLib/Data/Polynomial/RationalFunctions.lean).
Downstream users include the BCIKS20 list-decoding agreement files under
[`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding).

## Status Legend

- `present`: the item is formalized without a local `sorry`.
- `present-but-incomplete`: the declaration exists but still has a local `sorry`.
- `infrastructure`: supporting API is present, but it is not itself a paper theorem.
- `missing`: no close declaration was found.

## Appendix A Matrix

| Paper item | Status | Lean refs | Notes |
| --- | --- | --- | --- |
| Monicization `H_tilde` over `F(Z)[T]` | present | `H_tilde` | Defines the function-field-side monicization. |
| Polynomial representative `H_tilde'` over `F[Z][T]` | present | `H_tilde'` | The coefficient indexing and zero-degree branch were corrected in #470. |
| Agreement between `H_tilde'` and `H_tilde` | present | `map_H_tilde'_eq_H_tilde` | Proved after the corrected definition. |
| Positive-degree monicity of `H_tilde'` | present | `H_tilde'_monic` | Explicitly requires `0 < H.natDegree`, matching the `modByMonic` API. |
| Regular ring `𝒪` and function field `𝕃` | infrastructure | `𝒪`, `𝕃`, `functionFieldT`, `embeddingOf𝒪Into𝕃` | Gives the quotient rings, the function-field `T` variable, and the embedding used by Appendix A. |
| Canonical representatives in `𝒪` | infrastructure | `canonicalRepOf𝒪`, `mk_canonicalRepOf𝒪`, `canonicalRepOf𝒪_degree_lt`, `canonicalRepOf𝒪_natDegree_le` | The representative API is now explicit about positive `Y`-degree. |
| `Λ`-weight on regular elements | infrastructure | `weight_Λ`, `weight_Λ_over_𝒪` | Basic zero and constructor/reduced-representative lemmas exist; more algebraic weight lemmas are still useful. |
| Lemma A.1 | present-but-incomplete | `lemmaA1_embedding_eq_zero_of_many_rational_roots` | Main regular-function vanishing criterion remains open; the statement is now in a standalone field section, matching the reference proof setting. |
| Claim A.2 regularity of `ξ` | present | `RationalFunctions.HenselNumerators.ξ_regular`, `RationalFunctions.HenselNumerators.embeddingOf𝒪Into𝕃_ξ` | The total Lean form of `ξ` has a concrete quotient representative `ξ_pre`; the paper weight theorem separately assumes `2 ≤ R.natDegree`. |
| Claim A.2 bound for `ξ` | present-but-incomplete | `RationalFunctions.HenselNumerators.ξ_weight_le` | Now has the needed low-degree guard; depends on the canonical quotient-weight argument and the divisibility `H ∣ R(x₀,Y,Z)`. |
| Claim A.2 regular numerator elements `β` | present-but-incomplete | `RationalFunctions.HenselNumerators.exists_hensel_numerator_sequence`, `RationalFunctions.HenselNumerators.IsHenselNumeratorSequence` | No longer vacuous: the open theorem now asserts Hensel semantics plus the numerator weight bound. |
| Hensel-lift coefficients `α`, `γ` | present-but-incomplete | `RationalFunctions.HenselNumerators.α`, `RationalFunctions.HenselNumerators.α'`, `RationalFunctions.HenselNumerators.γ`, `RationalFunctions.HenselNumerators.γ'`, `RationalFunctions.HenselNumerators.βSeq_spec` | Definitions are stable, but their semantic content is supplied by the open `exists_hensel_numerator_sequence`. |

## Near-Term Work

The next useful proof work is not to restate all of Appendix A at once. It is to add small reusable
facts around regular elements, canonical representatives, and `Λ`-weights:

- denominator-clearing lemmas for evaluating polynomials at `functionFieldT / W`;
- weight bounds for constants and monomials;
- weight behavior under addition and multiplication by powers of `X`;
- reduced-representative rewrites that avoid unfolding quotient representatives manually.

These lemmas should make `RationalFunctions.HenselNumerators.ξ_weight_le` and `exists_hensel_numerator_sequence` more approachable while keeping
each PR reviewable.
