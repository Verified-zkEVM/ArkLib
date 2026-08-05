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
| Canonical representatives in `𝒪` | infrastructure | `canonicalRepOf𝒪`, `mk_canonicalRepOf𝒪`, `canonicalRepOf𝒪_degree_lt`, `canonicalRepOf𝒪_natDegree_lt_H` | The representative API is now explicit about positive `Y`-degree. |
| `Λ`-weight on regular elements | infrastructure | `weight`, `regularWeight`, `RegularWeightLe` (`.mono/.mul/.add/.neg/.pow/.sum/.prod`) | Full calculus, including the `𝕃`-side `RegularWeightLe` certificates used by Claim A.2. |
| A.2 exact weight of `H̃`: `Λ(H̃) = d(D+1-d)` | present | `weight_monicize` | Upper bound plus the leading monomial `Tᵈ`. |
| A.2 `Λ(α)` minimal over representatives | present | `regularWeight_le_of_mk_eq`, `regularWeight_mk_le` | Attained at `canonicalRepOf𝒪` by definition. |
| A.3 rational substitutions `π_z` on `𝒪` | present | `piZ`, `piZLift`, `piZ_eq_eval_canonicalRepOf𝒪`, `piZ_mk_C` | |
| A.3 extension of `π_z` to `β / C(Z) ∈ 𝕃` | present | `piZOfDiv`, `piZOfDiv_congr`, `piZOfDiv_one`, `piZOfDiv_eq_zero_iff` | Well defined on the quotient, not just the presentation. Needed by §5, which substitutes into `β(x) / (W^{k+1} ξ^{e_k})`. |
| Lemma A.1 | present | `lemmaA1_embedding_eq_zero_of_many_rational_roots` | Proved and axiom-clean, via the resultant/Sylvester route of the paper (`natDegree_resultant_le_weight_bound`, `rationalVanishingSet_subset_resultant_roots`). |
| Claim A.2 Hensel lift exists (`α₀ = T/W`, `R(X, γ, Z) = 0`) | present | `exists_hensel_alpha_sequence`, `formalHenselAlphaSequence` | Axiom-clean. |
| A.4 uniqueness of the lift | present | `hensel_alpha_sequence_unique`, `IsHenselNumeratorSequence.unique`, `IsHenselNumeratorSequence.eq_betaSeq` | Axiom-clean. Needed by [BCIKS20] Claim 5.9; also makes `betaSeq` canonical rather than an arbitrary choice. |
| Claim A.2 regularity of `ξ` | present | `xi_regular`, `embeddingOf𝒪Into𝕃_xi` | The total Lean form of `ξ` has a concrete quotient representative `xiPre`. |
| Claim A.2 bound for `ξ` | present | `xi_weight_le` | Assumes `2 ≤ natDegreeY R`, which is the paper's standing assumption in A.4 (see below). |
| Claim A.2 regular numerators `βₜ` exist | present | `exists_hensel_numerator_sequence`, `IsHenselNumeratorSequence`, `exists_regular_numerator_shape`, `henselCoeffResidual_regular_after_clearing` | Axiom-clean, and deliberately *free of the weight conjunct* so that `betaSeq`/`α`/`γ` do not depend on the open quantitative step. |
| Claim A.2 sharp weight bound `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)` | present-but-incomplete | `numerator_shape_weight_sharp`, `hensel_numerator_weight_sharp_le`, `betaSeq_weight_sharp_le` | One open summand (`henselClearedTerm_weight`, boundary case). This is the form Claim 5.10 needs. |
| Claim A.2 loose weight bound `Λ(βₜ) ≤ (2t+1)dD` | present-but-incomplete | `numerator_shape_weight_bound`, `hensel_numerator_weight_le`, `betaSeq_weight_le` | Weakening of the sharp bound (`numeratorShapeSharp_le_loose` is proved); inherits the same open summand. |
| Claim A.2 as stated in the paper | present-but-incomplete | `claimA2_exists_numerators_with_weight_bounds` | Bundles existence with both weight bounds. |
| Hensel-lift coefficients `α`, `γ` | present | `alpha`, `alpha'`, `gamma`, `gamma'`, `betaSeq`, `betaSeq_spec` | Now defined from the qualitative existence theorem alone, hence axiom-clean. |

## Three findings on Appendix A.4

### 1. Claim A.2 presupposes `2 ≤ d = degY R`

The claim sets `ξ = W(Z)^{d-2}·ζ ∈ 𝒪`, which carries a negative power of `W` when `d < 2`, and
its bound `Λ(ξ) ≤ (D-1) + (d-2)Λ(W) ≤ (d-1)(D-dH+1)` degenerates to `Λ(ξ) ≤ 0`. In Lean the
truncated subtraction silently reads `W^{d-2}` as `1` for `d ≤ 2`, so a `d`-unrestricted statement
would be *stronger* than the paper's and false: with `d = dH = 1` one gets `ξ = ζ` of weight up to
`D - 1`, while the `(d-1)` factor erases the `ξ` contribution from the bound. `xi_weight_le`,
`numerator_shape_weight_sharp` and everything above therefore carry `2 ≤ natDegreeY R`.

Consumers must supply this — but **not from Claim 5.7**. An earlier version of this page said the
conjunct should be added to Claim 5.7's conclusion; that is wrong, and would be unprovable. `R` is
an arbitrary irreducible factor of `Q` at that point, and `deg_Y R = 1` is precisely the *target* of
the whole §5 argument: "our goal will be to show that `Q` has a factor of the form `Y - P(X, Z)` …
and in fact `R` is this factor" (start of Appendix A). So `2 ≤ deg_Y R` must be discharged by a case
split inside §5: in the `deg_Y R = 1` branch `R` already has the desired shape and the Claim A.2
weight machinery is not needed (there `ζ = ∂R/∂Y` is constant in `Y` and the lift is exact); the
`≥ 2` branch is the one that consumes Claim A.2.

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

### 3. The paper's sharper `Λ(ξ)` bound also assumes `Λ(W) = D - dH`

A.4 states `Λ(ξ) ≤ (D-1) + (d-2)Λ(W) ≤ (d-1)(D-dH+1)`. Only the second, weaker form is formalized
(`xi_weight_le`), and the first is *not* provable as stated. With `ξ`'s explicit representative
`xiPre = ∑_{i<d-1} C(Pᵢ W^{d-2-i}) Tⁱ + C(P_{d-1}/W) T^{d-1}` (`P = ∂R/∂Y(x₀,·,Z)`, so
`deg_Z Pᵢ ≤ D-1-i`), the `i`-th monomial has weight `i·(D-dH+1) + (D-1-i) + (d-2-i)Λ(W)`, and
requiring that to be `≤ (D-1) + (d-2)Λ(W)` for all `i` reduces to `D - dH ≤ Λ(W)` — the same hidden
assumption as in finding 2, since `Λ(W) ≤ D - dH` always. Under that assumption the two forms agree
up to `d - dH`; in general only the weaker one holds, and it is the one used here.

## Near-Term Work

1. Weaken the per-summand budget of `henselClearedTerm_weight` and recover the total, or extend `Λ`
   to `𝕃` (finding 2 above), to close the last `sorry`.
2. Case-split on `deg_Y R` in §5 to discharge `2 ≤ natDegreeY R` (finding 1 above).
3. `Λ` is proved sub-additive (`weight_mul_le'`); A.2 also states *full* additivity on `F[Z][T]`.
   That is true — the associated graded ring of the weight filtration is a polynomial ring, hence a
   domain, so leading forms multiply — but it needs a leading-form development (~150 lines) and has
   no consumer here, so only the `≤` direction is formalized.
