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
| Polynomial representative `monicize` over `F[Z][T]` | present | `monicize` | Coefficient indexing and the zero-degree branch are both handled. |
| Agreement between `monicize` and `monicizeRatFunc` | present | `map_monicize_eq_monicizeRatFunc` | Proved after the corrected definition. |
| Positive-degree monicity of `monicize` | present | `monicize_monic` | Explicitly requires `0 < H.natDegree`, matching the `modByMonic` API. |
| Regular ring `𝒪` and function field `𝕃` | infrastructure | `𝒪`, `𝕃`, `functionFieldT`, `embeddingOf𝒪Into𝕃`, `embeddingOf𝒪Into𝕃_injective` | Gives the quotient rings, the function-field `T` variable, and the embedding used by Appendix A. |
| Canonical representatives in `𝒪` | infrastructure | `canonicalRepOf𝒪`, `mk_canonicalRepOf𝒪`, `canonicalRepOf𝒪_degree_lt`, `canonicalRepOf𝒪_natDegree_lt_H` | The representative API is now explicit about positive `Y`-degree. |
| A.2 full additivity `Λ(AB) = Λ(A) + Λ(B)` on `F[Z][T]` | present | `weight_mul` (sub-additive form: `weight_mul_le'`) | Needs `IsDomain F`, which is exactly what makes it true. |
| `Λ`-weight on regular elements | infrastructure | `weight`, `regularWeight`, `RegularWeightLe` (`.mono/.mul/.add/.neg/.pow/.sum/.prod`) | Full calculus, including the `𝕃`-side `RegularWeightLe` certificates used by Claim A.2. |
| A.2 exact weight of `H̃`: `Λ(H̃) = d(D+1-d)` | present | `weight_monicize` | Upper bound plus the leading monomial `Tᵈ`. |
| A.2 `Λ(α)` minimal over representatives | present | `regularWeight_le_of_mk_eq`, `regularWeight_mk_le` | Attained at `canonicalRepOf𝒪` by definition. |
| A.3 rational substitutions `π_z` on `𝒪` | present | `piZ`, `piZLift`, `piZ_eq_eval_canonicalRepOf𝒪`, `piZ_mk_C` | |
| A.3 extension of `π_z` to `β / C(Z) ∈ 𝕃` | present | `piZOfDiv`, `piZOfDiv_congr`, `piZOfDiv_one`, `piZOfDiv_eq_zero_iff` | Well defined on the quotient, not just the presentation. Needed by §5, which substitutes into `β(x) / (W^{k+1} ξ^{e_k})`. |
| Lemma A.1 | present | `embedding_eq_zero_of_many_rational_roots` | Proved and axiom-clean, via the resultant/Sylvester route of the paper (`natDegree_resultant_le_weight_bound`, `rationalVanishingSet_subset_resultant_roots`). |
| Claim A.2 Hensel lift exists (`α₀ = T/W`, `R(X, γ, Z) = 0`) | present | `exists_hensel_alpha_sequence`, `formalHenselAlphaSequence` | Axiom-clean. |
| A.4 uniqueness of the lift | present | `hensel_alpha_sequence_unique`, `IsHenselNumeratorSequence.unique`, `IsHenselNumeratorSequence.eq_betaSeq` | Axiom-clean. Needed by [BCIKS20] Claim 5.9; also makes `betaSeq` canonical rather than an arbitrary choice. |
| Claim A.2 regularity of `ξ` | present | `xi_regular`, `embeddingOf𝒪Into𝕃_xi` | The total Lean form of `ξ` has a concrete quotient representative `xiPre`. |
| Claim A.2 bound for `ξ` | present | `xi_weight_le` | Assumes `2 ≤ natDegreeY R`, which is the paper's standing assumption in A.4 (see below). |
| Claim A.2 regular numerators `βₜ` exist | present | `exists_hensel_numerator_sequence`, `IsHenselNumeratorSequence`, `exists_regular_numerator_shape`, `henselCoeffResidual_regular_after_clearing` | Axiom-clean, and deliberately *free of the weight conjunct* so that `betaSeq`/`α`/`γ` do not depend on the open quantitative step. |
| Claim A.2 sharp weight bound | present | `numerator_shape_weight_sharp`, `hensel_numerator_weight_sharp_le`, `betaSeq_weight_sharp_le` | Proved, with a correction term relative to the paper's stated inequality — see finding 2. This is the form Claim 5.10 needs. |
| Claim A.2 loose weight bound `Λ(βₜ) ≤ (2t+1)dD` | present | `numerator_shape_weight_bound`, `hensel_numerator_weight_le`, `betaSeq_weight_le` | Weakening of the sharp bound via `numeratorShapeSharp_le_loose`; unaffected by the correction, so Claim 5.10 gets exactly what the paper gives it. |
| Claim A.2 as stated in the paper | present | `exists_hensel_numerators_with_weight_bounds` | Bundles existence with both weight bounds. Axiom-clean. |
| Hensel-lift coefficients `α`, `γ` | present | `alpha`, `alpha'`, `gamma`, `gamma'`, `betaSeq`, `betaSeq_spec` | Now defined from the qualitative existence theorem alone, hence axiom-clean. |

## Three findings on Appendix A.4

### 1. Claim A.2 presupposes `2 ≤ d = degY R`

The claim sets `ξ = W(Z)^{d-2}·ζ ∈ 𝒪`, which carries a negative power of `W` when `d < 2`, and
its bound `Λ(ξ) ≤ (D-1) + (d-2)Λ(W) ≤ (d-1)(D-dH+1)` degenerates to `Λ(ξ) ≤ 0`. In Lean the
truncated subtraction silently reads `W^{d-2}` as `1` for `d ≤ 2`, so a `d`-unrestricted statement
would be *stronger* than the paper's and false: with `d = dH = 1` one gets `ξ = ζ` of weight up to
`D - 1`, while the `(d-1)` factor erases the `ξ` contribution from the bound. `xi_weight_le`,
`numerator_shape_weight_sharp` and everything above therefore carry `2 ≤ natDegreeY R`.

The hypothesis is load-bearing, not an artefact. A concrete `dY = 1` instance falsifies the
conclusion of `xi_weight_le`: take `R = (1+Z)Y + 1 + ZX`, `x₀ = 0`, `H = (1+Z)Y + 1` (irreducible,
degree 1, coprime coefficients). Then `dY = dH = 1`, `W = 1+Z`, `D = 2`, and
`ξ = W^{dY-2}·ζ = ζ = 1+Z`, whose canonical representative mod `H̃ = Y+1` is itself, so
`Λ(ξ) = 1`. The claimed bound at `dY = 1` is `(dY-1)(D-dH+1) = 0`.

Consumers must supply this — but **not from Claim 5.7**. An earlier version of this page said the
conjunct should be added to Claim 5.7's conclusion; that is wrong, and would be unprovable. `R` is
an arbitrary irreducible factor of `Q` at that point, and `deg_Y R = 1` is precisely the *target* of
the whole §5 argument: "our goal will be to show that `Q` has a factor of the form `Y - P(X, Z)` …
and in fact `R` is this factor" (start of Appendix A). So `2 ≤ deg_Y R` must be discharged by a case
split inside §5: in the `deg_Y R = 1` branch `R` already has the desired shape and the Claim A.2
weight machinery is not needed (there `ζ = ∂R/∂Y` is constant in `Y` and the lift is exact); the
`≥ 2` branch is the one that consumes Claim A.2. The obligation is recorded in the docstring of
`hensel_lift_hypotheses` in `BCIKS20/ListDecoding/Agreement.lean`, where §5 will meet it.

### 2. The paper's stated sharp bound needs a correction term

Claim A.2 states `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)`. That inequality is **not provable by the
recursion `(A.1)` the claim itself offers**, and `numeratorShapeSharp` therefore proves

```
Λ(βₜ) ≤ 1 + (t+1)(D - dH) + eₜ·(dY-1)(D - dH + 1) + (t-1)·(D - dY)
```

with the final term as the correction. The reason is an asymmetry between charging and saving a
factor of `W`:

- Every `W` the recursion *charges* costs the bound `Λ(W) ≤ D - dH`, and the base case forces
  exactly that charge: `Λ(β₀) = Λ(T) = D - dH + 1` is fixed by the definition of the `Λ`-grading,
  so no smaller `W`-charge survives `t = 0`.
- The recursion also *saves* one `W`, from `W ∣ leadingCoeff R(x₀,·,Z)`. A saved `W` is worth only
  its **exact** degree `deg W`, which has no lower bound: writing the coefficient as `W · c` leaves
  `Λ(c) = Λ(coeff) - deg W ≤ D - dY`.
- The paper's derivation writes `Λ(B₀,λ) = (D - Σλ) + (d - 1 - Σλ)Λ(W)`, crediting the saved `W` at
  `Λ(W)` while using `D` as an upper bound elsewhere — i.e. subtracting an upper bound. The
  resulting deficit is exactly `Λ(c)`.

The correction pays that deficit and is superadditive on precisely the configuration where the
deficit occurs. The boundary summand needs `p.2 = t+1` split into `d` parts each `≤ t`, hence at
least two nonzero parts `S₁ ≥ 2`, and then
`t·(D - dY) - ∑ᵢ (lᵢ-1)·(D - dY) = (S₁-1)·(D - dY) ≥ D - dY ≥ Λ(c)`.
Every other summand has `∑ᵢ (lᵢ-1) ≤ t`, so the correction is free there. Simply raising the
`ξ`-charge instead would *not* work: it breaks the loose bound the paper quotes
(`d = 2, dH = 1, D = 100, Λ(W) = 0, t = 5` gives `2377 > 2200 = (2t+1)dD`).

**Nothing downstream is weakened.** `numeratorShapeSharp_le_loose` still yields `(2t+1)·dY·D`, and
that is the only form Claim 5.10 consumes: its telescoping maximizes at `t = k`, giving
`max_t (sharp t + (k-t)Λ(W) + (e_k-eₜ)Λ(ξ)) = sharp k ≤ (2k+1)·dY·D`.

The paper's *literal* inequality would follow from its other route — `Λ(αₜ) = Λ(Y)`, i.e. a weight
function on `𝕃` rather than on `𝒪`, which gives `Λ(T) + t·deg W ≤ 1 + (t+1)(D - dH)` with no
correction. Defining such a `Λ_𝕃(b/c) := Λ(b) - deg c` is now possible (well-definedness follows
from `weight_mul`, since multiplying by an `F[Z]`-element never triggers reduction modulo `H̃`), but
the crux is open: bounding `αₜ = -cₜ/ζ` requires a **lower** bound on `Λ(ζ)`, and only upper bounds
are available. Newton-polygon reasoning has the same shape — bounding root degrees needs a lower
bound on the leading coefficient. That is what the paper's one-line "γ has the same weight as Y,
since X and x₀ have weight 0" conceals. Since both routes deliver the same usable consequence, this
is a fidelity question only.

### 3. The paper's sharper `Λ(ξ)` bound also assumes `Λ(W) = D - dH`

A.4 states `Λ(ξ) ≤ (D-1) + (d-2)Λ(W) ≤ (d-1)(D-dH+1)`. Only the second, weaker form is formalized
(`xi_weight_le`), and the first is *not* provable as stated. With `ξ`'s explicit representative
`xiPre = ∑_{i<d-1} C(Pᵢ W^{d-2-i}) Tⁱ + C(P_{d-1}/W) T^{d-1}` (`P = ∂R/∂Y(x₀,·,Z)`, so
`deg_Z Pᵢ ≤ D-1-i`), the `i`-th monomial has weight `i·(D-dH+1) + (D-1-i) + (d-2-i)Λ(W)`, and
requiring that to be `≤ (D-1) + (d-2)Λ(W)` for all `i` reduces to `D - dH ≤ Λ(W)` — the same hidden
assumption as in finding 2, since `Λ(W) ≤ D - dH` always. Under that assumption the two forms agree
up to `d - dH`; in general only the weaker one holds, and it is the one used here.

## Near-Term Work

1. Case-split on `deg_Y R` in §5 to discharge `2 ≤ natDegreeY R` (finding 1 above).
2. Optional, fidelity only: extend `Λ` to `𝕃` and prove `Λ(αₜ) ≤ Λ(T) - Λ(W)` to obtain the
   paper's uncorrected sharp inequality (finding 2 above). No downstream consequence.

**Appendix A is otherwise complete**: every declaration in
`ArkLib/Data/Polynomial/RationalFunctions/` is axiom-clean (266 declarations, zero `sorryAx`, zero
non-standard axioms), including Lemma A.1 and all of Claim A.2.
