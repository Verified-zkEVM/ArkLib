# Paper Audit: BCIKS20 Appendix A Rational Functions

This page tracks the local ArkLib status of Appendix A of `BCIKS20`, which supplies the
rational-function and Hensel-lifting machinery used by the list-decoding branch of the
Reed-Solomon proximity-gap formalization.

## Scope

The relevant Lean surface is
[`ArkLib/Data/Polynomial/RationalFunctions/`](../../../ArkLib/Data/Polynomial/RationalFunctions),
re-exported by
[`ArkLib/Data/Polynomial/RationalFunctions.lean`](../../../ArkLib/Data/Polynomial/RationalFunctions.lean):

- `FunctionField.lean` — monicization, `𝕃`, `𝒪`, canonical representatives;
- `Lifts.lean` — coefficient/bivariate lifts and denominator clearing;
- `Weight.lean` — the `Λ`-weight calculus;
- `RationalRootVanishing.lean` — Lemma A.1;
- `HenselNumerators/{Setup,Hensel,Weight,Sequence}.lean` — Claim A.2.

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
| Monicization `monicizeRatFunc` over `F(Z)[T]` | present | `monicizeRatFunc` | Defines the function-field-side monicization. |
| Polynomial representative `monicize` over `F[Z][T]` | present | `monicize` | The coefficient indexing and zero-degree branch were corrected in #470. |
| Agreement between `monicize` and `monicizeRatFunc` | present | `map_monicize_eq_monicizeRatFunc` | Proved after the corrected definition. |
| Positive-degree monicity of `monicize` | present | `monicize_monic` | Explicitly requires `0 < H.natDegree`, matching the `modByMonic` API. |
| Regular ring `𝒪` and function field `𝕃` | infrastructure | `𝒪`, `𝕃`, `functionFieldT`, `embeddingOf𝒪Into𝕃`, `embeddingOf𝒪Into𝕃_injective` | Gives the quotient rings, the function-field `T` variable, and the embedding used by Appendix A. |
| Canonical representatives in `𝒪` | infrastructure | `canonicalRepOf𝒪`, `mk_canonicalRepOf𝒪`, `canonicalRepOf𝒪_degree_lt`, `canonicalRepOf𝒪_natDegree_le` | The representative API is now explicit about positive `Y`-degree. |
| `Λ`-weight on regular elements | infrastructure | `weight`, `regularWeight`, `RegularWeightLe` (`.mono/.mul/.add/.neg/.pow/.sum/.prod`) | Full calculus, including the `𝕃`-side `RegularWeightLe` certificates used by Claim A.2. |
| Lemma A.1 | present-but-incomplete | `lemmaA1_embedding_eq_zero_of_many_rational_roots` | Main regular-function vanishing criterion remains open; the statement is now in a standalone field section, matching the reference proof setting. |
| Claim A.2 Hensel lift exists (`α₀ = T/W`, `R(X, γ, Z) = 0`) | present | `exists_hensel_alpha_sequence`, `formalHenselAlphaSequence` | Axiom-clean. |
| Claim A.2 regularity of `ξ` | present | `xi_regular`, `embeddingOf𝒪Into𝕃_xi` | The total Lean form of `ξ` has a concrete quotient representative `xiPre`. |
| Claim A.2 bound for `ξ` | present | `xi_weight_le` | Assumes `2 ≤ natDegreeY R`, which is the paper's standing assumption in A.4 (see below). |
| Claim A.2 regular numerators `βₜ` exist | present | `exists_hensel_numerator_sequence`, `IsHenselNumeratorSequence`, `exists_regular_numerator_shape`, `henselCoeffResidual_regular_after_clearing` | Axiom-clean, and deliberately *free of the weight conjunct* so that `betaSeq`/`α`/`γ` do not depend on the open quantitative step. |
| Claim A.2 sharp weight bound `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)` | present-but-incomplete | `numerator_shape_weight_sharp`, `hensel_numerator_weight_sharp_le`, `betaSeq_weight_sharp_le` | One open summand (`henselClearedTerm_weight`, boundary case). This is the form Claim 5.10 needs. |
| Claim A.2 loose weight bound `Λ(βₜ) ≤ (2t+1)dD` | present-but-incomplete | `numerator_shape_weight_bound`, `hensel_numerator_weight_le`, `betaSeq_weight_le` | Weakening of the sharp bound (`numeratorShapeSharp_le_loose` is proved); inherits the same open summand. |
| Claim A.2 as stated in the paper | present-but-incomplete | `claimA2_exists_numerators_with_weight_bounds` | Bundles existence with both weight bounds. |
| Hensel-lift coefficients `α`, `γ` | present | `alpha`, `alpha'`, `gamma`, `gamma'`, `beta`, `betaSeq`, `betaSeq_spec` | Now defined from the qualitative existence theorem alone, hence axiom-clean. |

## Two findings on Appendix A.4

### 1. Claim A.2 presupposes `2 ≤ d = degY R`

The claim sets `ξ = W(Z)^{d-2}·ζ ∈ 𝒪`, which carries a negative power of `W` when `d < 2`, and
its bound `Λ(ξ) ≤ (D-1) + (d-2)Λ(W) ≤ (d-1)(D-dH+1)` degenerates to `Λ(ξ) ≤ 0`. In Lean the
truncated subtraction silently reads `W^{d-2}` as `1` for `d ≤ 2`, so a `d`-unrestricted statement
would be *stronger* than the paper's and false: with `d = dH = 1` one gets `ξ = ζ` of weight up to
`D - 1`, while the `(d-1)` factor erases the `ξ` contribution from the bound. `xi_weight_le`,
`numerator_shape_weight_sharp` and everything above therefore carry `2 ≤ natDegreeY R`.

Consumers must supply this. Claim 5.7
(`exists_factors_with_large_common_root_set`) does not currently expose it, so whoever closes
Claim 5.7 should add the conjunct.

### 2. The `(A.1)` recursion route cannot prove the weight bound

`Λ(βₜ)`'s bound is stated by the paper and then justified twice: "can be shown by induction using
the recursion (A.1), but an easier way ... is by considering the weight of `αₜ`". The induction
route is *exactly tight* and does not close:

- Expanding (A.1) for the `i₁ = 0` terms gives `Λ(βₜ) ≤ D + (t+d-1)Λ(W) + (2t-2)Λ(ξ)`, which
  meets the claimed `1 + (t+1)Λ(W) + eₜΛ(ξ)` only if `Λ(ξ) = (D-1) + (d-2)Λ(W)`, i.e. only if
  `Λ(ξ)` attains its own upper bound.
- In the formalization the same tightness appears as a single unreachable summand of
  `henselClearedTerm_weight` (`p.1 = 0`, `j = d`, `p.2 = t+1`), where the `W`-budget is short by
  one. The leading-coefficient divisibility `W ∣ leadingCoeff R(x₀,·,Z)` supplies the missing `W`
  but then charges `c.natDegree` with `c = leadingCoeff R(x₀,·,Z) / W`, leaving a deficit of
  exactly `c.natDegree`. Raising the `ξ`-charge to cover it breaks the loose bound the paper
  quotes: `d = 2, dH = 1, D = 100, Λ(W) = 0, t = 5` gives `2377 > 2200 = (2t+1)dD`.

Note also that the per-summand budget of `henselClearedTerm_weight` is very likely *too strong*,
not merely hard: `R(x₀,·,Z) = H · q` makes the deficit `Λ(leadingCoeff q)`, which is unbounded.
`numerator_shape_weight_sharp` can still hold, because `Λ` of the sum over `j` only has to bound
the max after the cancellations (A.1) produces. So the fix is to weaken that lemma and recover the
total elsewhere, not to grind the boundary case.

The paper's second route needs `Λ(αₜ) = Λ(Y) = 1`, i.e. a weight function on the function field
`𝕃` (not just on `𝒪`) plus the fact that the Hensel coefficients lie in the same graded piece as
`Y`. Note that route needs care too: with the paper's *exact* `Λ(W)`, `Λ(α₀) = Λ(T/W) = (D-dH+1) -
Λ(W)` exceeds `1` unless `Λ(W) = D - dH`, so the claim's `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)` already
fails at `t = 0` when `Λ(W) < D - dH`. The Lean statement substitutes the paper's own bounds
`Λ(W) ≤ D - dH` and `Λ(ξ) ≤ (d-1)(D-dH+1)` into the right-hand side, which is the reading under
which the base case is true (and is proved here). See the in-proof comment at the boundary `sorry`.

## Near-Term Work

1. Extend `Λ` from `𝒪` to `𝕃` and prove `Λ(αₜ) ≤ Λ(T) - Λ(W)`, which closes the boundary summand
   and hence the whole of Claim A.2 (finding 2 above).
2. Lemma A.1 (`lemmaA1_embedding_eq_zero_of_many_rational_roots`) — the remaining Appendix A
   theorem, needed by Claim 5.10.
3. Add `2 ≤ natDegreeY R` to Claim 5.7's conclusion (finding 1 above).
