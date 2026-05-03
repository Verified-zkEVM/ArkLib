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
| Agreement between `H_tilde'` and `H_tilde` | present | `H_tilde_equiv_H_tilde'` | Proved after the corrected definition. |
| Positive-degree monicity of `H_tilde'` | present | `H_tilde'_monic` | Explicitly requires `0 < H.natDegree`, matching the `modByMonic` API. |
| Regular ring `𝒪` and function field `𝕃` | infrastructure | `𝒪`, `𝕃`, `functionFieldT`, `embeddingOf𝒪Into𝕃` | Gives the quotient rings, the function-field `T` variable, and the embedding used by Appendix A. |
| Canonical representatives in `𝒪` | infrastructure | `canonicalRepOf𝒪`, `mk_canonicalRepOf𝒪`, `canonicalRepOf𝒪_degree_lt`, `canonicalRepOf𝒪_natDegree_le` | The representative API is now explicit about positive `Y`-degree. |
| `Λ`-weight on regular elements | infrastructure | `weight_Λ`, `weight_Λ_over_𝒪` | Basic zero and constructor/reduced-representative lemmas exist; more algebraic weight lemmas are still useful. |
| Lemma A.1 | present-but-incomplete | `Lemma_A_1` | Main regular-function vanishing criterion remains open. |
| Claim A.2 regularity of `ξ` | present-but-incomplete | `ClaimA2.ξ_regular`, `ClaimA2.ζ_regular_of_derivative_evalX_eq_C`, `ClaimA2.ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one` | The full regularity proof remains open, but the `ζ` substitution now uses the function-field `T` variable and the constant-derivative low-degree case has a concrete witness. |
| Claim A.2 bound for `ξ` | present-but-incomplete | `ClaimA2.weight_ξ_bound` | Depends on stronger `Λ`-weight calculus. |
| Claim A.2 regular numerator elements `β` | present-but-incomplete | `ClaimA2.β_regular` | Depends on the Hensel-lift and weight-bound layer. |
| Hensel-lift coefficients `α`, `γ` | present | `ClaimA2.α`, `ClaimA2.α'`, `ClaimA2.γ`, `ClaimA2.γ'` | The definitions exist and are consumed by the list-decoding agreement file. |

## Near-Term Work

The next useful proof work is not to restate all of Appendix A at once. It is to add small reusable
facts around regular elements, canonical representatives, and `Λ`-weights:

- denominator-clearing lemmas for evaluating polynomials at `functionFieldT / W`;
- weight bounds for constants and monomials;
- weight behavior under addition and multiplication by powers of `X`;
- reduced-representative rewrites that avoid unfolding quotient representatives manually.

These lemmas should make `ClaimA2.weight_ξ_bound` and `β_regular` more approachable while keeping
each PR reviewable.
