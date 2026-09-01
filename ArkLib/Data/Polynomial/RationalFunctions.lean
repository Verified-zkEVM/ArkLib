/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.RationalFunctions.FunctionField
import ArkLib.Data.Polynomial.RationalFunctions.Weight
import ArkLib.Data.Polynomial.RationalFunctions.RationalRootVanishing
import ArkLib.Data.Polynomial.RationalFunctions.Lifts
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Setup
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Hensel
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Weight
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Sequence

/-!
# Appendix A of [BCIKS20]: Function Fields, Weights, and Hensel Lifts

Umbrella import for the `RationalFunctions` package, which formalizes Appendix A of [BCIKS20] —
the algebraic machinery behind the list-decoding half of the Reed-Solomon proximity-gap proof.
Import this file for all of it, or an individual module for a narrower dependency.

## Setting

`H : F[X][Y]` plays the role of the paper's `H(Y, Z)`: the outer variable is `Y` and the
coefficient variable is the paper's `Z`. For the trivariate `R : F[X][X][Y]` the outer variable is
`Y`, the middle one is the paper's `X` and the innermost is `Z`, so `Trivariate.evalAtX x₀ R`
(definitionally the existing `Bivariate.evalX (C x₀) R` expressions in this package) is the
specialization `R(x₀, Y, Z)`. Generic bivariate operations on `R.coeff i` are intentional: that
coefficient is genuinely bivariate in `(Z, X)`.

## Layout

* `FunctionField` (A.1) — monicization `monicizeRatFunc`/`monicize` (the paper's `H̃`), the
  function field `𝕃 H = F(Z)[T]/(H̃)`, its ring of regular elements `𝒪 H = F[Z][T]/(H̃)`, the
  injective embedding `𝒪 H ↪ 𝕃 H`, canonical representatives, and the substitutions `π_z` of A.3.
* `Lifts` (A.1) — coefficient and bivariate lifts into `𝕃`, the image `T` of the polynomial
  variable, denominator clearing for `W^k · P(T/W)`, and the extension of `π_z` to quotients
  `β / C(Z)`.
* `Weight` (A.2) — the weight `Λ` (`weight`, `regularWeight`) and its calculus: sub-additivity,
  *full* additivity on `F[Z][T]`, invariance under reduction modulo `H̃`, exact `Λ(H̃)`.
* `RationalRootVanishing` (A.3) — Lemma A.1: a regular `β` killed by more than `deg_Y H · Λ(β)`
  substitutions is zero.
* `HenselNumerators/Setup` (A.4) — hypotheses of the lift, `ζ = ∂R/∂Y(x₀, T/W, Z)`, its cleared
  form `ξ = W^{d-2}·ζ ∈ 𝒪`, and the bound on `Λ(ξ)`.
* `HenselNumerators/Hensel` (A.4) — the formal Hensel iteration: existence, uniqueness, and
  regularity of the numerators.
* `HenselNumerators/Weight` (A.4) — the quantitative half of Claim A.2: the `RegularWeightLe`
  calculus and the weight induction.
* `HenselNumerators/Sequence` (A.4) — Claim A.2 assembled: `betaSeq`, `alpha`, `gamma`, and the
  weight bounds.

## Main results

* `embedding_eq_zero_of_many_rational_roots` — Lemma A.1.
* `HenselNumerators.exists_hensel_numerator_sequence` — the qualitative half of Claim A.2. The data
  `betaSeq`, `alpha`, `gamma` is defined from this rather than from the bundled statement, so that
  downstream definitions do not depend on the quantitative argument.
* `HenselNumerators.IsHenselNumeratorSequence.unique` — uniqueness of the lift, which A.4 asserts
  and [BCIKS20] §5 invokes in Claim 5.9. It makes `betaSeq` canonical rather than an arbitrary
  choice.
* `HenselNumerators.exists_hensel_numerators_with_weight_bounds` — Claim A.2 as the paper states
  it: existence together with both weight bounds.

Everything in this package is proved: no `sorry`, and no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.

## Deviations from the paper

1. The weight bounds assume `2 ≤ deg_Y R`, which is A.4's own standing assumption — it writes
   `ξ = W^{d-2}·ζ ∈ 𝒪`, meaningless for `d < 2`. The hypothesis is load-bearing rather than
   cosmetic: at `deg_Y R = 1` the conclusion of `xi_weight_le` is false, witnessed by
   `R = (1+Z)Y + 1 + ZX`, `x₀ = 0`, `H = (1+Z)Y + 1`, where `D = 2` and `ξ = ζ = 1+Z` has
   `Λ(ξ) = 1` against a claimed bound of `0`. Consumers must case-split on `deg_Y R`.
2. `numeratorShapeSharp` carries a correction term relative to the inequality A.4 states, because
   a factor of `W` that the recursion *saves* is worth only `deg W` while one it *charges* costs
   the bound `D - dH`. The loose bound `(2t+1)·d·D` is unaffected, so consumers of that bound see
   no difference. See `numeratorShapeSharp`'s docstring for the full accounting.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.
-/
