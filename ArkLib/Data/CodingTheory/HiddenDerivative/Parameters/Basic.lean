/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Parameters of the hidden-derivative interpolation argument

The hidden-derivative list-decoding argument interpolates at block length `n`, agreement fraction
`ε`, and a slack `θ`, with a derivative order `d` chosen separately. This file defines the rounded
natural-number parameters of the argument as functions of `(d, ε, θ, n)`. The order `d` is an
explicit input and no definition ties it to `ε`, so one order can be used for every rate at a
fixed additive gap to capacity.

The parameters, with `m`, `A`, `K`, `B`, `W`, `C`, `H` the names used in
`Interpolation/Space.lean` and `Interpolation/Dimension.lean`, are:

```text
m = d³                                     multiplicity
A = ⌈ε n⌉                                  agreement threshold
K = ⌊(1 - θ) ε n⌋                          ambient dimension
B = ⌈m A / (K - 1)⌉                        jet-degree budget
W = ⌊(1 + θ/2) d m / (1 + log d)⌋          higher-jet weight budget
C = ⌊(1 + 3θ/4) m⌋                         higher-jet degree budget
H = ⌊θ m / 16⌋                             box width
```

All roundings are natural-number floors and ceilings (`Nat.floor`, `Nat.ceil`), so a negative
real argument rounds to `0`, and the natural subtraction `K - 1` is `0` when `K = 0`.

## Main definitions

* `multiplicity`, `agreementThreshold`, `ambientDimension`, `interpolationDegreeBudget`,
  `interpolationWeightBudget`, `higherJetDegreeBudget`, `interpolationBoxWidth`: the parameters
  above.
* `coarseListBound`: the source's list-size expression `q ^ (4 d + 6)`, as a definition only.

The rounded inequalities between these parameters are in `Parameters/FreeOrder.lean`.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Basic.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which adapts Kai Zhe Zheng's
`rs-ld-mca` formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with permission;
the free-order extension was contributed by Pratyush Mishra. All eight definitions
(`multiplicity`, `agreementThreshold`, `ambientDimension`, `interpolationDegreeBudget`,
`interpolationWeightBudget`, `higherJetDegreeBudget`, `interpolationBoxWidth`,
`coarseListBound`) are ported unchanged, with the same formulas and constants.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26].
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The multiplicity `m = d³`: the contact order imposed at each agreement point, at derivative
order `d`. It is positive exactly when `d` is. -/
def multiplicity (d : ℕ) : ℕ := d ^ 3

/-- The agreement threshold `A = ⌈ε n⌉`: the number of agreement points that a listed codeword
must have with the received word. It is `0` when `ε n ≤ 0`. -/
def agreementThreshold (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈ε * n⌉₊

/-- The ambient dimension `K = ⌊(1 - θ) ε n⌋`. The interpolation space charges every jet weight
`K - 1`, the degree of a polynomial in dimension `K`, so the slack `θ` reserves a `θ` fraction
of `ε n` for the higher jets. It is `0` when `(1 - θ) ε n < 1`. -/
def ambientDimension (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - θ) * ε * n⌋₊

/-- The jet-degree budget `B = ⌈m A / (K - 1)⌉`: the bound on the total jet degree of an
eligible exponent. It is chosen so that `m A ≤ B (K - 1)`, which needs `K - 1 > 0`; the later
theorems assume `0 < d < K` for this. When `K ≤ 1` the division is by `0` and `B = 0`. -/
def interpolationDegreeBudget (d : ℕ) (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌈(((multiplicity d * agreementThreshold ε n : ℕ) : ℝ) /
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ))⌉₊

/-- The higher-jet weight budget `W = ⌊(1 + θ/2) d m / (1 + log d)⌋`: the bound on the
anisotropic weight `∑_{j ≥ 2} (j - 1) b_j` of the higher-jet exponents. -/
def interpolationWeightBudget (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊((1 + θ / 2) * (d : ℝ) * (multiplicity d : ℝ)) / (1 + Real.log (d : ℝ))⌋₊

/-- The higher-jet degree budget `C = ⌊(1 + 3θ/4) m⌋`: the bound on the ordinary degree
`∑_{j ≥ 2} b_j` of the higher-jet exponents. -/
def higherJetDegreeBudget (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 + 3 * θ / 4) * (multiplicity d : ℝ)⌋₊

/-- The box width `H = ⌊θ m / 16⌋`: the side length of the rectangle of exponents of `Y₀`, `Y₁`,
and of the `X` blocks, in the rectangular lower bound on the interpolation dimension. -/
def interpolationBoxWidth (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊θ * (multiplicity d : ℝ) / 16⌋₊

/-- The source's coarse list-size expression `q ^ (4 d + 6)` over a field of size `q`. This is
parameter data only: no theorem here or in the source proves that it bounds a list, since that
needs a root-counting theorem of Kopparty that is not formalized. -/
def coarseListBound (q d : ℕ) : ℕ :=
  q ^ (4 * d + 6)

end

end ReedSolomon.HiddenDerivative
